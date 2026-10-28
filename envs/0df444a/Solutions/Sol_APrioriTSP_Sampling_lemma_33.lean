-- Prove2me | solution 1 for APrioriTSP.Sampling.lemma_33
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-28T12:02:50.915407+00:00
-- url     : https://prove2.me/submissions/ca59523f-634d-48b2-859d-8a30abc07761

import Mathlib
import Definitions.Def_APrioriTSP_Sampling_Setting

section
open APrioriTSP.Sampling
namespace Queelius.CycleShortcut
variable {V : Type} (c : V → V → ℝ)
def path (a : V) : List V → ℝ
  | [] => 0
  | b::l => c a b + path b l
lemma zip_path (a z : V) (l : List V) :
    ((a::l).zipWith c (l++[z])).sum = path c a (l++[z]) := by
  induction l generalizing a with
  | nil => simp [path]
  | cons b l ih => simpa [path] using congrArg (fun x : ℝ => c a b+x) (ih b)
lemma cycle_path (a : V) (l : List V) : cycleCost c (a::l) = path c a (l++[a]) := by
  rw [cycleCost,List.map_zip_eq_zipWith]
  cases l with
  | nil => simp [path]
  | cons b l =>
    rw [List.zipWith_rotate_one,List.sum_cons,zip_path]
    rfl
lemma change_start (ht : ∀ a b z, c a z ≤ c a b+c b z) (a b z : V) (l : List V) :
    path c a (l++[z]) ≤ c a b+path c b (l++[z]) := by
  cases l with
  | nil => simpa [path] using ht a b z
  | cons d l =>
    simp only [List.cons_append,path]
    linarith [ht a b d]
lemma change_end (ht : ∀ a b z, c a z ≤ c a b+c b z) (a b z : V) (l : List V) :
    path c a (l++[z]) ≤ path c a (l++[b])+c b z := by
  induction l generalizing a with
  | nil => simpa [path] using ht a b z
  | cons d l ih =>
    simp only [List.cons_append,path]
    linarith [ih d]
lemma path_sublist (ht : ∀ a b z, c a z ≤ c a b+c b z)
    {l k : List V} (h : l.Sublist k) (a z : V) :
    path c a (l++[z]) ≤ path c a (k++[z]) := by
  induction h generalizing a with
  | slnil => rfl
  | cons b h ih =>
    calc
      _ ≤ c a b+path c b (_++[z]) := change_start c ht a b z _
      _ ≤ _ := by simpa [path] using add_le_add_left (ih b) (c a b)
  | cons_cons b h ih => simpa [path] using add_le_add_left (ih b) (c a b)
lemma cycle_cons_le (h0 : ∀ a, c a a=0) (ht : ∀ a b z, c a z ≤ c a b+c b z)
    (hn : ∀ a b, 0 ≤ c a b) (a : V) (l : List V) : cycleCost c l ≤ cycleCost c (a::l) := by
  cases l with
  | nil => simp [cycleCost,h0]
  | cons b l =>
    rw [cycle_path,cycle_path]
    have hh := change_end c ht b a b l
    simpa [path,add_comm,add_left_comm,add_assoc] using hh
lemma cycle_sublist (h0 : ∀ a, c a a=0) (ht : ∀ a b z, c a z ≤ c a b+c b z)
    (hn : ∀ a b, 0 ≤ c a b) {l k : List V} (h : l.Sublist k) :
    cycleCost c l ≤ cycleCost c k := by
  induction h with
  | slnil => rfl
  | cons b h ih => exact ih.trans (cycle_cons_le c h0 ht hn b _)
  | cons_cons b h ih =>
    rw [cycle_path,cycle_path]
    exact path_sublist c ht h b b
lemma cycle_filter_mono [DecidableEq V] (h0 : ∀ a, c a a=0)
    (ht : ∀ a b z, c a z ≤ c a b+c b z) (hn : ∀ a b, 0 ≤ c a b)
    (T : List V) {A B : Finset V} (hAB : A ⊆ B) :
    cycleCost c (T.filter (· ∈ A)) ≤ cycleCost c (T.filter (· ∈ B)) := by
  apply cycle_sublist c h0 ht hn
  induction T with
  | nil => simp
  | cons a T ih =>
    by_cases ha : a ∈ A
    · have hb := hAB ha
      simpa [ha,hb] using List.Sublist.cons_cons a ih
    · by_cases hb : a ∈ B
      · simpa [ha,hb] using List.Sublist.cons a ih
      · simpa [ha,hb] using ih
end Queelius.CycleShortcut

end

section
open Finset APrioriTSP.Sampling
namespace Queelius.FiniteBernoulli
variable {V : Type} [DecidableEq V]
noncomputable def weight (S : Finset V) (q : V → ℝ) (A : Finset V) : ℝ :=
  (∏ v ∈ A, q v) * ∏ v ∈ S \ A, (1-q v)
noncomputable def expect (S : Finset V) (q : V → ℝ) (F : Finset V → ℝ) : ℝ :=
  ∑ A ∈ S.powerset, weight S q A * F A
lemma weight_nonneg (S : Finset V) (q : V → ℝ) (hq : ∀ v, q v ∈ Set.Icc (0:ℝ) 1)
    (A : Finset V) : 0 ≤ weight S q A := by
  apply mul_nonneg
  · exact Finset.prod_nonneg (fun v _ => (hq v).1)
  · exact Finset.prod_nonneg (fun v _ => sub_nonneg.mpr (hq v).2)
lemma weight_insert_absent (S : Finset V) (q : V → ℝ) (a : V) (ha : a ∉ S)
    (A : Finset V) (hA : A ⊆ S) :
    weight (insert a S) q A = (1-q a)*weight S q A := by
  have haA : a ∉ A := fun h => ha (hA h)
  have he : insert a S \ A = insert a (S \ A) := by
    ext v
    by_cases hv : v=a <;> simp [hv,ha,haA]
  rw [weight,he,Finset.prod_insert (by simp [ha])]
  unfold weight
  ring
lemma weight_insert_present (S : Finset V) (q : V → ℝ) (a : V) (ha : a ∉ S)
    (A : Finset V) (hA : A ⊆ S) :
    weight (insert a S) q (insert a A) = q a*weight S q A := by
  have haA : a ∉ A := fun h => ha (hA h)
  have he : insert a S \ insert a A = S \ A := by
    ext v
    by_cases hv : v=a <;> simp [hv,ha,haA]
  rw [weight,he,Finset.prod_insert haA]
  unfold weight
  ring

lemma expect_insert (S : Finset V) (q : V → ℝ) (F : Finset V → ℝ) (a : V) (ha : a ∉ S) :
    expect (insert a S) q F = (1-q a)*expect S q F + q a*expect S q (fun A => F (insert a A)) := by
  rw [expect,Finset.sum_powerset_insert ha]
  have he0 : (∑ A ∈ S.powerset, weight (insert a S) q A*F A) = (1-q a)*expect S q F := by
    unfold expect
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro A hA
    rw [weight_insert_absent S q a ha A (Finset.mem_powerset.mp hA)]
    ring
  have he1 : (∑ A ∈ S.powerset, weight (insert a S) q (insert a A)*F (insert a A)) = q a*expect S q (fun A => F (insert a A)) := by
    unfold expect
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro A hA
    rw [weight_insert_present S q a ha A (Finset.mem_powerset.mp hA)]
    ring
  rw [he0,he1]
lemma expect_mono_fun (S : Finset V) (q : V → ℝ) (hq : ∀ v, q v ∈ Set.Icc (0:ℝ) 1)
    (F G : Finset V → ℝ) (hFG : ∀ A, F A ≤ G A) : expect S q F ≤ expect S q G := by
  apply Finset.sum_le_sum
  intro A _
  exact mul_le_mul_of_nonneg_left (hFG A) (weight_nonneg S q hq A)
lemma expect_mono_prob (S : Finset V) (p q : V → ℝ)
    (hp : ∀ v, p v ∈ Set.Icc (0:ℝ) 1) (hq : ∀ v, q v ∈ Set.Icc (0:ℝ) 1)
    (hpq : ∀ v, p v ≤ q v) (F : Finset V → ℝ) (hF : Monotone F) :
    expect S p F ≤ expect S q F := by
  induction S using Finset.induction_on generalizing F with
  | empty => simp [expect,weight]
  | @insert a S ha ih =>
    rw [expect_insert S p F a ha,expect_insert S q F a ha]
    have h0 := ih F hF
    have h1 := ih (fun A => F (insert a A)) (by
      intro A B hAB
      exact hF (Finset.insert_subset_insert a hAB))
    have h01 : expect S q F ≤ expect S q (fun A => F (insert a A)) :=
      expect_mono_fun S q hq F _ (fun A => hF (Finset.subset_insert a A))
    have hh0 := mul_le_mul_of_nonneg_left h0 (sub_nonneg.mpr (hp a).2)
    have hh1 := mul_le_mul_of_nonneg_left h1 (hp a).1
    have hh2 := mul_nonneg (sub_nonneg.mpr (hpq a)) (sub_nonneg.mpr h01)
    nlinarith
lemma expect_univ [Fintype V] (q : V → ℝ) (F : Finset V → ℝ) :
    expect Finset.univ q F = ∑ A : Finset V, subsetProb q A*F A := by
  simp [expect,weight,subsetProb]
end Queelius.FiniteBernoulli

end

open APrioriTSP.Sampling
namespace Queelius.TSPMonotone
lemma metric_nonneg {V : Type} [Fintype V] [DecidableEq V] (c : V → V → ℝ)
    (p : V → ℝ) (d : V) (h : IsDepotInstance c p d) (a b : V) : 0 ≤ c a b := by
  have hh := h.c_triangle a b a
  rw [h.c_self,h.c_symm b a] at hh
  linarith
lemma cycle_nonneg {V : Type} (c : V → V → ℝ) (hn : ∀ a b, 0 ≤ c a b) (l : List V) :
    0 ≤ cycleCost c l := by
  apply List.sum_nonneg
  intro x hx
  obtain ⟨e,_,rfl⟩ := List.mem_map.mp hx
  exact hn e.1 e.2
lemma cost_nonneg {V : Type} [Fintype V] [DecidableEq V]
    (c : V → V → ℝ) (hn : ∀ a b, 0 ≤ c a b) (p : V → ℝ)
    (hp : ∀ v, p v ∈ Set.Icc (0:ℝ) 1) (T : List V) : 0 ≤ aPrioriCost c p T := by
  apply Finset.sum_nonneg
  intro A _
  exact mul_nonneg (Queelius.FiniteBernoulli.weight_nonneg Finset.univ p hp A)
    (cycle_nonneg c hn _)
lemma cost_mono {V : Type} [Fintype V] [DecidableEq V]
    (c : V → V → ℝ) (h0 : ∀ a, c a a=0) (ht : ∀ a b z, c a z ≤ c a b+c b z)
    (hn : ∀ a b, 0 ≤ c a b) (p q : V → ℝ)
    (hp : ∀ v, p v ∈ Set.Icc (0:ℝ) 1) (hq : ∀ v, q v ∈ Set.Icc (0:ℝ) 1)
    (hpq : ∀ v, p v ≤ q v) (T : List V) : aPrioriCost c p T ≤ aPrioriCost c q T := by
  have hF : Monotone (fun A : Finset V => cycleCost c (T.filter (· ∈ A))) := by
    intro A B hAB
    exact Queelius.CycleShortcut.cycle_filter_mono c h0 ht hn T hAB
  have hh := Queelius.FiniteBernoulli.expect_mono_prob Finset.univ p q hp hq hpq _ hF
  simpa only [Queelius.FiniteBernoulli.expect_univ,aPrioriCost] using hh
end Queelius.TSPMonotone
open Queelius.TSPMonotone in
 theorem solution {V : Type} [Fintype V] [DecidableEq V]
    (c : V → V → ℝ) (p p' : V → ℝ) (d : V) (hI : IsDepotInstance c p d)
    (hp' : ∀ v, 0 < p' v ∧ p' v ≤ 1) (hle : ∀ v, p' v ≤ p v) (hd : p' d = 1)
    (T : List V) (hT : IsTour T)
    (hopt : ∀ T' : List V, IsTour T' → aPrioriCost c p T ≤ aPrioriCost c p T') :
    aPrioriOpt c p' ≤ aPrioriCost c p' T ∧ aPrioriCost c p' T ≤ aPrioriCost c p T ∧
      aPrioriCost c p T = aPrioriOpt c p := by
  have hn : ∀ a b, 0 ≤ c a b := metric_nonneg c p d hI
  have hpb : ∀ v, p v ∈ Set.Icc (0:ℝ) 1 := fun v => ⟨(hI.p_pos v).le,hI.p_le_one v⟩
  have hpb' : ∀ v, p' v ∈ Set.Icc (0:ℝ) 1 := fun v => ⟨(hp' v).1.le,(hp' v).2⟩
  have hb (q : V → ℝ) (hq : ∀ v, q v ∈ Set.Icc (0:ℝ) 1) :
      BddBelow (aPrioriCost c q '' {l : List V | IsTour l}) := by
    refine ⟨0,?_⟩
    rintro _ ⟨l,_,rfl⟩
    exact cost_nonneg c hn q hq l
  refine ⟨csInf_le (hb p' hpb') ⟨T,hT,rfl⟩,
    cost_mono c hI.c_self hI.c_triangle hn p' p hpb' hpb hle T,?_⟩
  apply le_antisymm
  · apply le_csInf
    · exact ⟨_,T,hT,rfl⟩
    · rintro _ ⟨l,hl,rfl⟩
      exact hopt l hl
  · exact csInf_le (hb p hpb) ⟨T,hT,rfl⟩

namespace Queelius.FiniteBernoulli
lemma zero_probability_control {V : Type} [DecidableEq V] (S : Finset V) (F : Finset V → ℝ) :
    expect S (fun _ => 0) F = F ∅ := by
  induction S using Finset.induction_on generalizing F with
  | empty => simp [expect,weight]
  | insert a S ha ih => simp [expect_insert S _ F a ha,ih]
lemma one_probability_control {V : Type} [DecidableEq V] (S : Finset V) (F : Finset V → ℝ) :
    expect S (fun _ => 1) F = F S := by
  induction S using Finset.induction_on generalizing F with
  | empty => simp [expect,weight]
  | insert a S ha ih => simp [expect_insert S _ F a ha,ih]
lemma probability_mass_control {V : Type} [DecidableEq V] (S : Finset V) (q : V → ℝ) :
    expect S q (fun _ => 1) = 1 := by
  induction S using Finset.induction_on with
  | empty => simp [expect,weight]
  | insert a S ha ih => rw [expect_insert S _ _ a ha,ih];ring
end Queelius.FiniteBernoulli
