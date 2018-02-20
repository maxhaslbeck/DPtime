theory DP
imports "../Imperative_HOL_Time/SepLogicTime/SepAuto" "../Imperative_HOL_Time/SepLogicTime/Asymptotics_1D"
begin

(* auxiliaries *)


lemma H[forward]: "i < length xs \<Longrightarrow> Suc i \<le> length xs" by auto

lemma weaken_pre: "<P> f <Q>\<^sub>t \<Longrightarrow> P' \<Longrightarrow>\<^sub>A P * true  \<Longrightarrow> <P'> f <\<lambda>x. Q x >\<^sub>t"
proof -
  have u: "\<And>R x. Q x * true * true = Q x * true" using top_assn_reduce assn_times_assoc by auto
  from pre_rule''[where Q="%x. Q x * true" and R="true"]
  show "<P> f <Q>\<^sub>t \<Longrightarrow> P' \<Longrightarrow>\<^sub>A P * true \<Longrightarrow> <P'> f <\<lambda>x. Q x >\<^sub>t" unfolding u . 
qed


section "nth Fibonacci number by Dynamic Programming"

subsection "definition of functional version of Fibonacci numbers"


fun fib :: "nat \<Rightarrow> nat" where
  "fib 0 = 1"
| "fib (Suc 0) = 1"
| "fib (Suc (Suc n)) = fib (Suc n) + fib n"
declare fib.simps [rewrite]

subsection "setup for memoizaition in a functional list"

definition consistent_list where [rewrite]:
  "consistent_list xs= (\<forall>i<length xs. xs!i \<noteq> None \<longrightarrow> xs!i = Some (fib i))"


subsection "definition of functional version of Fibonacci numbers with memoization in a functional list"

fun fib_fun :: "nat \<Rightarrow> (nat option) list \<Rightarrow> (nat option) list * nat" where
  "fib_fun 0 xs = (let
      x = xs ! 0 in
      (case x of None \<Rightarrow> let v = fib 0;
                             xs' =  xs[0:= (Some v)] in (xs',v)
            | Some v \<Rightarrow> (xs, v)))"
| 
  "fib_fun (Suc 0) xs = (let
      x = xs ! 1 in
      (case x of None \<Rightarrow> let v = fib (Suc 0);
                             xs' =  xs[1:= (Some v)] in (xs',v)
            | Some v \<Rightarrow> (xs, v)))"
| "fib_fun (Suc (Suc n)) xs = (let
      x = xs ! (Suc (Suc n)) in
      (case x of None \<Rightarrow> let (xs',a) = fib_fun (Suc n)  xs;
                            (xs'',b) = fib_fun n xs';
                             v = a + b;
                             xs''' =  xs''[(Suc (Suc n)):= (Some v)] in (xs''',v)
            | Some v \<Rightarrow> (xs, v)))"
declare fib_fun.simps(1,2) [rewrite]
declare fib_fun.simps(3) [unfold]
setup {* add_fun_induct_rule (@{term fib_fun}, @{thm fib_fun.induct}) *}
setup {* register_wellform_data ("fib_fun i xs", ["i < length xs"]) *}


lemma fib_fun_stays[rewrite]: "n < length xs \<Longrightarrow> xs ! n \<noteq> None \<Longrightarrow> (fst (fib_fun n xs)) = xs"
  apply(induct rule: fib_fun.induct) apply auto done

lemma fib_fun_length [rewrite]: "i < length xs \<Longrightarrow> length (fst (fib_fun i xs)) = length xs"
@proof @fun_induct "fib_fun i xs"  @with
  @subgoal "(i = 0, xs = xs)"
    @case "xs ! 0 = None"
  @endgoal
  @subgoal "(i = Suc 0, xs = xs)"
    @case "xs ! Suc 0 = None"
  @endgoal
  @subgoal "(i = Suc (Suc n), xs = xs)"
    @unfold "fib_fun (Suc (Suc n)) xs"
    @case "xs ! (Suc (Suc n)) \<noteq> None"
  @endgoal @end
@qed

(* the statemet of this lemma should be independent of the function (here fib) that is computed,
  also the structure of the proof should be the same, only potentially more recursive calls
  must be adressed.
  Need to extract the over all/generic structure! *)
lemma fib_fun_effect: "i < length xs \<Longrightarrow> consistent_list xs  
      \<Longrightarrow> (fst (fib_fun i xs)) ! i = Some (fib i) \<and> snd (fib_fun i xs) = fib i \<and> consistent_list (fst (fib_fun i xs))"
proof (induction i xs rule: fib_fun.induct)
  case (1 xs)
  then show ?case apply(auto simp: consistent_list_def fib_fun_length split: option.split prod.split)
    by (metis "1.prems"(1) One_nat_def fib.simps(1) nth_list_update option.inject)
next
  case (2 xs)
  then show ?case apply(auto simp: consistent_list_def fib_fun_length split: option.split prod.split)
    by (metis One_nat_def fib.simps(2) nth_list_update option.inject)    
next
  case (3 n xs)
  show ?case 
  proof (cases "xs ! Suc (Suc n) = None")
    case True  
    let ?xs' = "fst (fib_fun (Suc n) xs)"
    from True 3 have "?xs' ! Suc n = Some (fib (Suc n))"
        and a: "snd (fib_fun (Suc n) xs) = fib (Suc n)"
        and c: "consistent_list ?xs'" by auto

    let ?xs'' = "fst (fib_fun n ?xs')"
 
    from True c 3(2)[of None "fib_fun (Suc n) xs" "fst (fib_fun (Suc n) xs)"]
    have "n < length (fst (fib_fun (Suc n) xs)) \<Longrightarrow> ?xs'' ! n = Some (fib n) \<and> snd (fib_fun n ?xs') = fib n \<and>
      consistent_list ?xs''"
      using prod.collapse by fastforce
    with 3(3) have "?xs'' ! n = Some (fib n)" and b: "snd (fib_fun n ?xs') = fib n" and c'': "consistent_list ?xs''"
      by (auto simp: fib_fun_length)      

    have c''': "consistent_list (?xs''[Suc (Suc n) := Some (fib (Suc (Suc n)))] )"
      using c'' unfolding consistent_list_def apply auto
        subgoal for i y apply(cases "i=Suc (Suc n)") by auto done

    have t: "length ?xs'' = length xs" using 3(3) by (auto simp: fib_fun_length)
    thm prod_def
    from True show ?thesis apply(auto simp: split_beta split: option.split)
      subgoal using t by (metis "3.prems"(1) a b fst_conv nth_list_update_eq) 
      subgoal using t by (metis a b snd_conv) 
      using c''' apply(auto simp add: a b) by (metis fst_conv) 
    
  next
    case False
    with 3(3-4) show ?thesis unfolding consistent_list_def by auto
  qed  
qed  
(* dont know how to add this in a sensible way to auto2's rules, maybe do some
corollaries for each conjunct ? *)

corollary fib_fun_effect_snd: "i < length xs \<Longrightarrow> consistent_list xs  
      \<Longrightarrow>  snd (fib_fun i xs) = fib i" using fib_fun_effect by metis

corollary fib_fun_effect_consist[backward]: "i < length xs \<Longrightarrow> consistent_list xs  
      \<Longrightarrow> consistent_list (fst (fib_fun i xs))" using  fib_fun_effect by metis

lemma tailor[rewrite]: "xs ! Suc (Suc n) = None \<Longrightarrow> Suc (Suc n) < length xs  \<Longrightarrow> consistent_list xs \<Longrightarrow>
      fst (fib_fun (Suc (Suc n)) xs) = fst (fib_fun n (fst (fib_fun (Suc n) xs)))[Suc (Suc n) := Some (fib (n+2))]"
  apply (auto split: prod.split)
  using fib_fun_effect_snd[where xs="fst (fib_fun (Suc n) xs)" and i=n]
        fib_fun_effect_snd[where xs=xs and i="n+1"]
        fib_fun_effect_consist[where xs=xs and i="n+1"] apply (auto simp: fib_fun_length )
  using fib_fun_length by (metis Suc_lessD fst_conv) 

lemma fib_fun_untouched[rewrite]: "j \<le> length xs \<Longrightarrow> i < j \<Longrightarrow> (fst (fib_fun i xs)) ! j = xs ! j"
  apply(induction i xs rule: fib_fun.induct) apply simp
    apply (auto simp: fib_fun_length split: option.split prod.split)
  using  fib_fun_length   
  by (metis Suc_lessD fst_conv less_le_trans nat_neq_iff nth_list_update_neq)


subsection "imperative Implementation of memoized computation of Fibonacci numbers"

fun fibH :: "nat \<Rightarrow> nat option array \<Rightarrow> nat Heap" where
  "fibH 0 M = do {
     x \<leftarrow> Array.nth M 0;
     case x of None \<Rightarrow> do { v \<leftarrow> return (fib 0);
                            Array.upd 0 (Some v) M;
                            return v }
             | Some v \<Rightarrow> return v}"
| "fibH (Suc 0) M = do {
     x \<leftarrow> Array.nth M 1;
     case x of None \<Rightarrow> do { v \<leftarrow> return (fib 1);
                            Array.upd 1 (Some v) M;
                            return v }
             | Some v \<Rightarrow> return v}"
| "fibH (Suc (Suc n)) M = do {
     x \<leftarrow> Array.nth M (Suc (Suc n));
     case x of None \<Rightarrow> do {
           a \<leftarrow> fibH (Suc n) M;
           b \<leftarrow> fibH n M;
           v \<leftarrow> return (a + b);
           Array.upd (Suc (Suc n)) (Some v) M;
           return v
          }
             | Some v \<Rightarrow> return v}"
declare fibH.simps [sep_proc]
setup {* add_fun_induct_rule (@{term fibH}, @{thm fibH.induct}) *}


subsubsection "(recombination) costs for DP computation of fib" 
(*
fun comcost :: "nat \<Rightarrow> nat" where 
  "comcost 0 = 2"
| "comcost (Suc 0) = 2"
| "comcost (Suc (Suc n)) = 6" *)
fun comcost :: "nat \<Rightarrow> nat" where 
  "comcost n = 6"
declare comcost.simps [rewrite]

lemma comcost_ub: "comcost n \<le> 6" apply(induct n rule: comcost.induct) by auto


subsubsection "the potential for the memoization Table"

definition memtableP :: " nat option list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "memtableP xs A B = sum (\<lambda>i. case xs!i of None \<Rightarrow> comcost i | Some _ \<Rightarrow> 0) {A..<B}"
 
lemma empty_ub[rewrite]: "memtableP (replicate x None) 0 x = x * 6"
  unfolding memtableP_def by auto  
(*
lemma extract_from_sum: fixes i :: nat shows
  "A \<le> i \<Longrightarrow> i < B \<Longrightarrow> sum g {A..B} = sum g ({A..B}-{i}) + g i"
proof -
  assume inbounds: "A \<le> i" "i < B"  
  then have u: "(({A..B}-{i}) \<union> {i}) = {A..B}" by auto
  have "sum g (({A..B}-{i}) \<union> {i}) = sum g ({A..B}-{i}) + sum g {i}" 
    apply(rule sum.union_disjoint) by auto
  then show ?thesis unfolding u by auto
qed *)
 

lemma assumes "A\<le>C" "C \<le> B" "B \<le> length xs"
  shows memtableP_split[backward]: "memtableP xs A B = memtableP xs A C + memtableP xs C B"
proof -
  let ?g = "(\<lambda>i. case xs!i of None \<Rightarrow> comcost i | Some _ \<Rightarrow> 0)"
  from assms(1,2) have k: "({A..<B}-{A..<C}) \<union> {A..<C} = {A..<B}" by auto
  from assms(1,2) have l: "{A..<B}-{A..<C} = {C..<B}" by auto
  have "memtableP xs A B = sum ?g {A..<B}" unfolding memtableP_def by simp
  also have "\<dots> = sum ?g (({A..<B}-{A..<C}) \<union> {A..<C})" using k by auto
  also have "\<dots> = sum ?g ({A..<B}-{A..<C}) + sum ?g {A..<C}"  apply(rule sum.union_disjoint) by auto
  also have "\<dots> = sum ?g {A..<C} + sum ?g {C..<B}" using l by auto
  finally show ?thesis unfolding memtableP_def .
qed

lemma memtableP_pays: "i<length xs \<Longrightarrow> xs ! i = None \<Longrightarrow> memtableP xs i (Suc i) = comcost i"
  unfolding memtableP_def by auto

lemma memtableP_doesnt_pay: "i<length xs \<Longrightarrow> consistent_list xs \<Longrightarrow> memtableP (fst (fib_fun i xs)) i (Suc i) = 0"
  unfolding memtableP_def apply auto using fib_fun_effect by auto 

(* Key result for memtableP: if xs ! i = None, then updating xs ! i to Some v allows
   extracting comcost i credit from the potential. *)
lemma memtableP_correct [rewrite_back]:
  assumes "A \<le> i" "i < B" "B \<le> length xs" "xs ! i = None"
  shows "memtableP xs A B = memtableP xs A i + comcost i + memtableP xs (Suc i) B"
proof - 
  have "memtableP xs A B = memtableP xs A (Suc i) + memtableP xs (Suc i) B"
    apply(rule memtableP_split) using assms by auto
  also have "memtableP xs A (Suc i) = memtableP xs A i + memtableP xs i (Suc i)"
    apply(rule memtableP_split) using assms by auto
  also have "memtableP xs i (Suc i) = comcost i"
    apply(rule memtableP_pays) using assms by auto
  finally show ?thesis .
qed 


lemma recombine[rewrite_back]: assumes "A \<le> i " "  i < B " " B \<le> length xs " " xs ! i = None"
    "consistent_list xs"
  shows "memtableP (fst (fib_fun i xs)) A B = memtableP (fst (fib_fun i xs)) A i + memtableP xs (Suc i) B"
proof -
  have "memtableP (fst (fib_fun i xs)) A B = memtableP (fst (fib_fun i xs)) A (Suc i) + memtableP (fst (fib_fun i xs)) (Suc i) B" 
    apply(rule memtableP_split) using assms by (auto simp: fib_fun_length)
  also have "memtableP (fst (fib_fun i xs)) (Suc i) B = memtableP xs (Suc i) B"
    using assms(3) by(auto  simp: fib_fun_untouched memtableP_def)
  also have "memtableP (fst (fib_fun i xs)) A (Suc i) = memtableP (fst (fib_fun i xs)) A i + memtableP (fst (fib_fun i xs)) i (Suc i)"
    apply(rule memtableP_split) using assms by (auto simp: fib_fun_length)
  also have "memtableP (fst (fib_fun i xs)) i (Suc i) = 0" using memtableP_doesnt_pay assms by auto
  finally show ?thesis by simp
qed 

lemma outofreach[rewrite]: "memtableP (xs[i:=v]) 0 i = memtableP xs 0 i"
  unfolding memtableP_def by auto

thm recombine[where i="n"
        and xs="(fst (fib_fun (Suc n) xs))" and A=0 and B ="Suc (Suc n)"]

lemma outofreachlower[rewrite]: "n+2 \<le> length xs \<Longrightarrow> memtableP (fst (fib_fun n xs)) (n+1) (n+2) = memtableP xs (n+1) (n+2)"
  unfolding memtableP_def apply(rule sum.cong)
  by (auto simp: fib_fun_untouched)

subsubsection "the consistency of an memoization Array"

definition consistent :: "nat option array \<Rightarrow> nat option list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> assn" where [rewrite_ent]:
  "consistent M xs A B = M \<mapsto>\<^sub>a xs * $(memtableP xs A B) * \<up>(consistent_list xs)"

lemma i[rewrite]: "memtableP xs i i = 0" unfolding memtableP_def by auto
(*lemma ii[rewrite]: "i < length xs \<Longrightarrow> memtableP (fst (fib_fun i xs )) 0 i = memtableP xs 0 i" unfolding memtableP_def sorry *)

(* declare [[print_trace]] *)


subsubsection "proving the correctness and time consumption of the imperative Program"

lemma fibH_rule[hoare_triple]:
  "i < length xs \<Longrightarrow> consistent_list xs \<Longrightarrow>
   <M \<mapsto>\<^sub>a xs * $(memtableP xs 0 (Suc i) + 2)>
   fibH i M
   <\<lambda>r. \<up>(r = fib i) * consistent M (fst (fib_fun i xs)) 0 (Suc i)>\<^sub>t"
@proof @fun_induct "fibH i M" arbitrary xs @with
  @subgoal "(i = Suc (Suc n), M = M)"
    @let "x = xs ! (Suc (Suc n))"
    @case "x = None" @with 
      @have "Suc (Suc (Suc n)) \<le> length xs"
      @have "Suc (Suc n) < Suc (Suc (Suc n))"
      @have "(Suc (Suc n)) < length xs"
      @have "xs ! (Suc (Suc n)) = None"
      @have "memtableP xs 0 (Suc (Suc (Suc n))) \<ge>\<^sub>t memtableP xs 0 (Suc (Suc n)) + comcost (Suc (Suc n)) + memtableP xs (Suc (Suc (Suc n))) (Suc (Suc (Suc n)))"
      @have "comcost (Suc (Suc n)) \<ge>\<^sub>t 6"
      @have "0\<le>Suc n"
      @have "Suc n\<le>Suc (Suc n)"
      @have "Suc (Suc n)\<le> length (fst (fib_fun (n+1) xs))"
      @have "memtableP (fst (fib_fun (n+1) xs)) 0 (n+2) = memtableP (fst (fib_fun (n+1) xs)) 0 (n+1) + memtableP (fst (fib_fun (n+1) xs)) (n+1) (n+2)"

      @have "memtableP (fst (fib_fun (Suc n) xs)) 0 (Suc (Suc n)) \<ge>\<^sub>t memtableP (fst (fib_fun (Suc n) xs)) 0 (Suc n) + memtableP (fst (fib_fun (Suc n) xs)) (Suc n) (Suc (Suc n))"
 (*     @have "memtableP xs 0 (Suc (Suc n)) = memtableP (fst (fib_fun (Suc (Suc n)) xs)) 0 (Suc (Suc n))"
      @have "memtableP (fst (fib_fun (Suc (Suc n)) xs)) 0 (Suc (Suc n)) + memtableP xs (Suc (Suc n)) (Suc (Suc n)) \<ge>\<^sub>t  memtableP (fst (fib_fun (Suc (Suc n)) xs)) 0 (Suc (Suc (Suc n)))" 
 *)   

      @have "consistent_list (fst (fib_fun (n+2) xs))"  
      @have "fst (fib_fun (Suc (Suc n)) xs) = fst (fib_fun n (fst (fib_fun (Suc n) xs)))[Suc (Suc n) := Some (fib (n+2))]"



      @have "memtableP xs (Suc (Suc (Suc n))) (Suc (Suc (Suc n))) + memtableP (fst (fib_fun (Suc n) xs)) (Suc n) (Suc (Suc n)) +
                  memtableP (fst (fib_fun n (fst (fib_fun (Suc n) xs)))) 0 (Suc n)
            \<ge>\<^sub>t memtableP (fst (fib_fun (n+2) xs)) 0 (n+3)" @with 
        @have "memtableP xs (Suc (Suc (Suc n))) (Suc (Suc (Suc n))) + memtableP (fst (fib_fun (Suc n) xs)) (Suc n) (Suc (Suc n)) +
                    memtableP (fst (fib_fun n (fst (fib_fun (Suc n) xs)))) 0 (Suc n)
              = memtableP (fst (fib_fun (n+2) xs)) 0 (n+3)" @with
          @have "memtableP (fst (fib_fun (n+2) xs)) 0 (n+2) = memtableP (fst (fib_fun (Suc n) xs)) (Suc n) (Suc (Suc n)) +
                  memtableP (fst (fib_fun n (fst (fib_fun (Suc n) xs)))) 0 (Suc n)" @with 
            
            @have "memtableP (fst (fib_fun (n+2) xs)) 0 (n+2) = memtableP (fst (fib_fun n (fst (fib_fun (n+1) xs)))) 0 (n+2)"
              @with
              @have "xs ! (Suc (Suc n)) = None"
              @have "fst (fib_fun (n+2) xs) = (fst (fib_fun n (fst (fib_fun (n+1) xs))))[n+2:= Some (snd (fib_fun n (fst (fib_fun (n+1) xs))) + (snd (fib_fun (n+1) xs)))]" @with
                @unfold "fib_fun (Suc (Suc n)) xs"
              @end
            @end
    
            @have "memtableP (fst (fib_fun n (fst (fib_fun (n+1) xs)))) (n+1) (n+2) = memtableP (fst (fib_fun (n+1) xs)) (n+1) (n+2)"
            @have "memtableP (fst (fib_fun n (fst (fib_fun (n+1) xs)))) 0 (n+2) = 
                    memtableP (fst (fib_fun n (fst (fib_fun (n+1) xs)))) 0 (n+1) + memtableP (fst (fib_fun n (fst (fib_fun (n+1) xs)))) (n+1) (n+2)"
          @end

          @have "memtableP (fst (fib_fun (n+2) xs)) 0 (n+3) = memtableP (fst (fib_fun (n+2) xs)) 0 (n+2) + memtableP xs (n+3) (n+3)"
        @end 
        @end (* hint \<ge>\<^sub>t *)

        
        
      @end (* case *)
      @have "xs ! (n+2) = Some (fib (n+2))"
      @have "consistent_list (fst (fib_fun (Suc (Suc n)) xs))"
      @have "(fst (fib_fun (n+2) xs)) = xs"
  @endgoal                          
  @subgoal "(i = 0, M = M)"
  @let "x = xs ! 0"
  @case "x = None" @with  
      @have "memtableP xs 0 (Suc 0) \<ge>\<^sub>t memtableP xs 0 0 + comcost 0 + memtableP xs 1 1"
      @have "comcost 0 \<ge>\<^sub>t 2"
      @have "memtableP xs 0 0 = memtableP (fst (fib_fun 0 xs)) 0 0"
      @have "memtableP xs 0 0 + memtableP xs 1 1 \<ge>\<^sub>t  memtableP (fst (fib_fun 0 xs)) 0 1"
    @end
  @endgoal
  @subgoal "(i = Suc 0, M = M)"
    @let "x = xs ! 1"
    @case "x = None" @with
      @have "memtableP xs 0 2 \<ge>\<^sub>t memtableP xs 0 1 + comcost 1 + memtableP xs 2 2"
      @have "comcost 1 \<ge>\<^sub>t 2"
      @have "memtableP xs 0 1 = memtableP (fst (fib_fun 1 xs)) 0 1"
      @have "memtableP xs 0 1 + memtableP xs 2 2 \<ge>\<^sub>t  memtableP (fst (fib_fun 1 xs)) 0 2" 
    @end
    @endgoal
 @end
@qed




subsection "Wrap it up with an initialization phase and show run time complexity"

thm new_rule fibH_rule
fun fib_impl :: "nat \<Rightarrow> nat Heap" where 
  "fib_impl n = do {
        M <- Array.new (n+1) None;
        fibH n M
      }"
declare fib_impl.simps [sep_proc]


lemma empty_consistent: "consistent_list (replicate (n+1) None) = True" by auto2


definition fib_time :: "nat \<Rightarrow> nat" where [rewrite]: 
  "fib_time n = 6*(n+1) + (n+2) + 2"
 
(* the last two lemmas are the important result that is reported to the outside world *)

lemma fib_impl_rule[hoare_triple]: "<$(fib_time n)> fib_impl n <\<lambda>r. \<up> (r = fib n)>\<^sub>t"
@proof 
  @have "fib_time n \<ge>\<^sub>t memtableP (replicate (n+1) None) 0 (n+1) + (n+2) + 2"
@qed

lemma fib_bound[asym_bound]: "(\<lambda>n. fib_time n) \<in> \<Theta>(%n. n)" unfolding fib_time_def by auto2









 
end
