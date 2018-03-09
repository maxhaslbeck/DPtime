theory DP
imports "../Imperative_HOL_Time/SepLogicTime/SepAuto" "../Imperative_HOL_Time/SepLogicTime/Asymptotics_1D"
begin

no_notation Ref.update ("_ := _" 62)

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
setup {* add_fun_induct_rule (@{term fib_fun}, @{thm fib_fun.induct}) *}
setup {* register_wellform_data ("fib_fun i xs", ["i < length xs"]) *}

lemma fib_fun_stays[rewrite]: "n < length xs \<Longrightarrow> xs ! n \<noteq> None \<Longrightarrow> (fst (fib_fun n xs)) = xs"
  by(induction rule: fib_fun.induct) auto

lemma fib_fun_length [rewrite]: "i < length xs \<Longrightarrow> length (fst (fib_fun i xs)) = length xs"
  by (induction i xs rule: fib_fun.induct) (auto split: option.split prod.split simp: Let_def)

lemma consistent_list_update:
  "consistent_list (xs[i:= Some v])" if "v = fib i" "consistent_list xs" "i < length xs"
  using that by (auto simp add: consistent_list_def nth_list_update)

(* the statemet of this lemma should be independent of the function (here fib) that is computed,
  also the structure of the proof should be the same, only potentially more recursive calls
  must be adressed.
  Need to extract the over all/generic structure! *)
lemma fib_fun_effect: "i < length xs \<Longrightarrow> consistent_list xs  
      \<Longrightarrow> (fst (fib_fun i xs)) ! i = Some (fib i) \<and> snd (fib_fun i xs) = fib i \<and> consistent_list (fst (fib_fun i xs))"
proof (induction i xs rule: fib_fun.induct)
  case (1 xs)
  then show ?case
    by (auto simp: consistent_list_def fib_fun_length nth_list_update split: option.split)
next
  case (2 xs)
  then show ?case
    by (auto simp: consistent_list_def fib_fun_length nth_list_update split: option.split)
next
  case (3 n xs)
  show ?case
  proof (cases "xs ! Suc (Suc n) = None")
    case True  

    let ?xs' = "fst (fib_fun (Suc n) xs)"
    from True 3 have "?xs' ! Suc n = Some (fib (Suc n))"
        and a: "snd (fib_fun (Suc n) xs) = fib (Suc n)"
        and "consistent_list ?xs'" by auto

    let ?xs'' = "fst (fib_fun n ?xs')"
    from 3(2)[OF HOL.refl True HOL.refl prod.collapse] \<open>consistent_list ?xs'\<close> 3(3) have
      "?xs'' ! n = Some (fib n)" and b: "snd (fib_fun n ?xs') = fib n" and "consistent_list ?xs''"
      by (auto simp: fib_fun_length)

    then have c: "consistent_list (?xs''[Suc (Suc n) := Some (fib (Suc (Suc n)))] )"
      using 3(3) by (auto simp: fib_fun_length intro: consistent_list_update)

    from True show ?thesis
      apply(auto simp: Let_def split_beta 3 split: option.split)
      using c 3(3) by (auto simp: a b fib_fun_length)
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

setup {* add_fun_induct_rule (@{term fibH}, @{thm fibH.induct}) *}

 
subsection "definition of time function"

fun f_time :: "nat \<Rightarrow> (nat option) list \<Rightarrow> nat" where
  "f_time 0 xs = (let
      x = xs ! 0 in
      (case x of None \<Rightarrow> 4
            | Some v \<Rightarrow> 2))"
| 
  "f_time (Suc 0) xs = (let
      x = xs ! 1 in
      (case x of None \<Rightarrow> 4
            | Some v \<Rightarrow> 2))"
| "f_time (Suc (Suc n)) xs = (let
      x = xs ! (Suc (Suc n)) in
      (case x of None \<Rightarrow> let (xs',a) = fib_fun (Suc n) xs;
                            (xs'',b) = fib_fun n xs'  in 
                            4 + f_time (Suc n) xs + f_time n (xs')
            | Some v \<Rightarrow> 2))"
declare f_time.simps [rewrite]
thm f_time.induct

subsubsection "the potential for the memoization Table"
        
definition "C = 8"
definition phi :: "(nat option) list \<Rightarrow> nat set \<Rightarrow> nat" where
  "phi xs S =  sum (\<lambda>i. case xs!i of None \<Rightarrow> C | Some _ \<Rightarrow> 0) S"
 
lemma assumes "(\<forall>i\<in>S. i<length xs) " "x\<in>S" "xs!x = None" "finite S"
  shows phi_update_extract: "phi (xs[x:=Some v]) S + C = phi xs S"
proof -
  from assms(2,4) have p: "C = sum (\<lambda>i. if i=x then C else 0) S"
    by simp
  let ?g ="\<lambda>i. case xs[x := Some v] ! i of None \<Rightarrow> C | Some x \<Rightarrow> 0"
  have "(\<Sum>i\<in>S. case xs[x := Some v] ! i of None \<Rightarrow> C | Some x \<Rightarrow> 0) + C 
      = sum ?g S + sum (\<lambda>i. if i=x then C else 0) S"
    apply(subst (2) p) by simp
  also have "\<dots> = sum (\<lambda>i. ?g i + (\<lambda>i. if i=x then C else 0) i) S" by(rule sum.distrib[symmetric])
  also have "\<dots> = (\<Sum>i\<in>S. case xs ! i of None \<Rightarrow> C | Some x \<Rightarrow> 0)" 
    apply(rule sum.cong)
     apply simp
    subgoal for x' apply(cases "x=x'") using assms(1,2,3) by auto done
  finally show ?thesis unfolding phi_def .
qed 

lemma fib_fun_untouched_safe: "x'< y \<Longrightarrow>  y<length xs \<Longrightarrow>fst (fib_fun x' xs) ! y = xs ! y"
proof(induct x' xs rule: fib_fun.induct)
case (1 xs)
  then show ?case
    apply(cases "xs!0 = None") by auto 
next
  case (2 xs)
  then show ?case 
    apply(cases "xs!1 = None") by auto 
next
  case (3 n xs)
  then show ?case
    apply(cases "xs!(Suc (Suc n)) = None")
     apply (auto simp: fib_fun_length split: prod.split) 
    by (metis Suc_lessD fib_fun_length fst_conv less_irrefl less_le_trans less_trans_Suc nth_list_update_neq)

qed
    

subsubsection "proving the potential"

lemma fib_time_amor: "S={0..M} \<Longrightarrow> i\<le>M \<Longrightarrow> M < length xs  \<Longrightarrow> f_time i xs + phi (fst (fib_fun i xs)) S \<le> 4 + phi xs S"
proof(induct i xs rule: f_time.induct)
  case (1 xs)
  then show ?case apply(cases "xs!0") apply (auto simp: phi_def) 
    apply(rule sum_mono) subgoal for i apply(cases "i=0") apply auto apply(subst nth_list_update_eq) apply auto done done
next
  case (2 xs)
  then show ?case apply(cases "xs!1") apply (auto simp: phi_def) 
    apply(rule sum_mono) subgoal for i apply(cases "i=1") apply auto   done done
next
  case (3 n xs)
  show ?case
  proof (cases "xs ! Suc (Suc n) = None")
    case True
    then have r: "f_time (Suc (Suc n)) xs
        = 4 + f_time (Suc n) xs + f_time n (fst (fib_fun (Suc n) xs))"
      apply auto using split_beta by blast  
    let ?xs' = "(fst (fib_fun (Suc n) xs))"
    let ?v' = "(snd (fib_fun (Suc n) xs))"
    let ?xs'' = "(fst (fib_fun n ?xs'))"
    let ?v'' = "(snd (fib_fun n ?xs'))"
    from 3(1)[OF _ True] 3(3-5) have 2: "f_time (Suc n) xs + phi ?xs' S \<le> 4 + phi xs S"        
      by (metis Suc_leD old.prod.exhaust) 
    have t: "length ?xs' = length xs" using fib_fun_length 3 by auto
    have *: "f_time n ?xs' + phi ?xs'' S \<le> 4 + phi ?xs' S" 
      apply(rule 3(2))
      using True 3(3-5) apply(auto simp add: t split: prod.split)  
      apply(rule prod.collapse) apply(rule prod.collapse) done
    let ?xs''' = "?xs''[Suc (Suc n) := Some (?v'+?v'')]"
    have tp: "(fst (fib_fun (Suc (Suc n)) xs)) = ?xs'''" using True by (auto simp: Let_def split: prod.split) 

    have k: "phi ?xs''' S + C
        = phi ?xs'' S" 
      apply(rule phi_update_extract)
      using 3(3-5) apply (auto simp: fib_fun_length fib_fun_untouched_safe) 
      using True by auto 

    have "f_time (Suc (Suc n)) xs + phi (fst (fib_fun (Suc (Suc n)) xs)) S + C
        = 4 + f_time (Suc n) xs + f_time n ?xs' + (phi ?xs''' S + C)"
      by (simp only: r tp) 
    also have "\<dots> = 4 + f_time (Suc n) xs + f_time n ?xs' + phi ?xs'' S" by (simp only: k)
    also have "\<dots> \<le> f_time (Suc n) xs + phi ?xs' S + 8"
      using * by auto 
    also have "\<dots> \<le> 4 + phi xs S + C" using 2 by (auto simp: C_def)
    finally show ?thesis by auto
  next
    case False
    then show ?thesis by auto
  qed
qed

corollary fib_time[backward]: assumes "S={0..<M+1}" "i\<le>M" "M < length xs"
  shows "f_time i xs \<le> 4 + phi xs S" 
proof - 
  have S: "S={0..M}" using assms by auto
  have "f_time i xs + phi (fst (fib_fun i xs)) {0..M} \<le> 4 + phi xs {0..M}"    
    apply(rule fib_time_amor) using assms by auto
  then have "f_time i xs  \<le> 4 + phi xs {0..M}" by auto   
  thus ?thesis using S by auto
qed

subsubsection "proving the correctness and time consumption of the imperative Program"

lemma fibH_rule[hoare_triple]:
  "i < length xs \<Longrightarrow> consistent_list xs \<Longrightarrow>
   <M \<mapsto>\<^sub>a xs * $(f_time i xs)>
   fibH i M
   <\<lambda>r. \<up>(r = fib i) * M \<mapsto>\<^sub>a (fst (fib_fun i xs))  * \<up>(consistent_list (fst (fib_fun i xs))) >\<^sub>t"
@proof @fun_induct "fibH i M" arbitrary xs @with                      
  @subgoal "(i = 0, M = M)"
  @let "x = xs ! 0"
  @case "x = None" @with  
    @end
  @endgoal 
  @subgoal "(i = Suc 0, M = M)"
    @let "x = xs ! 1"
    @case "x = None" @with
    @end
  @endgoal
  @subgoal "(i = Suc (Suc n), M = M)"
    @let "x = xs ! (Suc (Suc n))"
    @case "x = None" @with 
      @have "(Suc (Suc n)) < length xs"
      @have "Suc (Suc n)\<le> length (fst (fib_fun (Suc n) xs))"
      @have "consistent_list (fst (fib_fun (Suc (Suc n)) xs))"  
      @have "fst (fib_fun (Suc (Suc n)) xs) = fst (fib_fun n (fst (fib_fun (Suc n) xs)))[Suc (Suc n) := Some (fib (Suc (Suc n)))]"
    @end (* case *)
    @have "xs ! (Suc (Suc n)) = Some (fib (Suc (Suc n)))"
    @have "consistent_list (fst (fib_fun (Suc (Suc n)) xs))"
    @have "(fst (fib_fun (Suc (Suc n)) xs)) = xs"
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

lemma empty_consistent: "consistent_list (replicate (n+1) None) = True" by auto2

lemma "i \<le> n \<Longrightarrow> replicate (n+1) x ! i = x" apply(rule nth_replicate) by auto

lemma phi_empty_ub [rewrite]: "phi (replicate n None) {0..<n} = C * n"
  unfolding phi_def by auto 


definition fib_time :: "nat \<Rightarrow> nat" where [rewrite]: 
  "fib_time n = (n+2) + 4 + C * (n+1)"
 
(* the last two lemmas are the important result that is reported to the outside world *)

lemma fib_impl_rule[hoare_triple]: "<$(fib_time n)> fib_impl n <\<lambda>r. \<up> (r = fib n)>\<^sub>t"
@proof 
  @have "fib_time n \<ge>\<^sub>t (n+2) + 4 + phi (replicate (n+1) None) {0..<n+1}"
  @have "4 + phi (replicate (n+1) None) {0..<n+1} \<ge>\<^sub>t f_time n (replicate (n+1) None)"
@qed

lemma fib_bound[asym_bound]: "(\<lambda>n. fib_time n) \<in> \<Theta>(%n. n)" unfolding C_def fib_time_def by auto2

 
end
