-- Prove2me | solution 1 for AC02Frege.lemma_4_19_two_counts
-- status  : ACCEPTED   (prove)
-- author  : @Henry Yuen
-- created : 2026-11-18T03:36:58.029875+00:00
-- url     : https://prove2.me/submissions/327318d6-1dcf-4587-a395-0d46612058f6

import Definitions.Def_AC02Frege_majorityExpansion
import Definitions.Def_SemAC02_multiplierSpace
import Definitions.Def_AC02Frege_PC
import Definitions.Def_AC02Frege_ML
import Definitions.Def_AC02Frege_lift
import Definitions.Def_SemAC02_Ble
import Mathlib
import Definitions.Def_AC02Frege_rankCounts
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Distributions.Bernoulli

section
-- Inlined Solutions.HeavyBlockCounting

set_option maxHeartbeats 1000000

namespace AC02Frege.HeavyBlockCounting

def blockUnion {n ℓ : ℕ} (J : Finset (Fin n)) : Finset (Fin n × Fin ℓ) :=
  J ×ˢ Finset.univ

def flipBlocks {n ℓ : ℕ} (T : Finset (Fin n × Fin ℓ)) (J : Finset (Fin n)) :
    Finset (Fin n × Fin ℓ) := symmDiff T (blockUnion J)

def fold {n ℓ : ℕ} (T : Finset (Fin n × Fin ℓ)) : Finset (Fin n × Fin ℓ) :=
  flipBlocks T (heavyBlocks T)

theorem sum_block_card {n ℓ : ℕ} (T : Finset (Fin n × Fin ℓ)) :
    ∑ i : Fin n, (blockPart T i).card = T.card := by
  exact (Finset.card_eq_sum_card_fiberwise (f:=Prod.fst) (s:=T) (t:=Finset.univ)
    (fun v hv => Finset.mem_univ v.1)).symm

theorem block_univ_card {n ℓ : ℕ} (i : Fin n) :
    (blockPart (Finset.univ : Finset (Fin n × Fin ℓ)) i).card = ℓ := by
  have he : blockPart (Finset.univ : Finset (Fin n × Fin ℓ)) i = {i} ×ˢ Finset.univ := by
    ext ⟨v,a⟩
    simp [blockPart,eq_comm]
  rw [he]
  simp

theorem block_card_le {n ℓ : ℕ} (T : Finset (Fin n × Fin ℓ)) (i : Fin n) :
    (blockPart T i).card ≤ ℓ := by
  calc
    _ ≤ (blockPart (Finset.univ : Finset (Fin n × Fin ℓ)) i).card := by
      apply Finset.card_le_card
      intro v hv
      simp only [blockPart,Finset.mem_filter,Finset.mem_univ,true_and] at hv ⊢
      exact hv.2
    _ = _ := block_univ_card i

theorem block_inter_union {n ℓ : ℕ} (T : Finset (Fin n × Fin ℓ)) (J : Finset (Fin n)) (i : Fin n) :
    blockPart (T ∩ blockUnion J) i = if i ∈ J then blockPart T i else ∅ := by
  by_cases hi : i ∈ J
  · rw [if_pos hi]
    ext v
    by_cases hvi : v.1 = i <;> simp_all [blockPart,blockUnion]
  · rw [if_neg hi]
    ext v
    by_cases hvi : v.1 = i <;> simp_all [blockPart,blockUnion]

theorem inter_union_card {n ℓ : ℕ} (T : Finset (Fin n × Fin ℓ)) (J : Finset (Fin n)) :
    (T ∩ blockUnion J).card = ∑ i ∈ J, (blockPart T i).card := by
  rw [← sum_block_card]
  simp_rw [block_inter_union]
  simp only [apply_ite Finset.card,Finset.card_empty,Finset.sum_ite_mem,Finset.univ_inter]

theorem flipBlocks_involution {n ℓ : ℕ} (T : Finset (Fin n × Fin ℓ)) (J : Finset (Fin n)) :
    flipBlocks (flipBlocks T J) J = T := symmDiff_symmDiff_cancel_right _ _

theorem block_flip {n ℓ : ℕ} (T : Finset (Fin n × Fin ℓ)) (J : Finset (Fin n)) (i : Fin n) :
    blockPart (flipBlocks T J) i = if i ∈ J then
      blockPart (Finset.univ : Finset (Fin n × Fin ℓ)) i \ blockPart T i else blockPart T i := by
  by_cases hi : i ∈ J
  · rw [if_pos hi]
    ext v
    by_cases hvi : v.1 = i <;> by_cases hvT : v ∈ T <;>
      simp_all [blockPart,flipBlocks,blockUnion,Finset.mem_symmDiff]
  · rw [if_neg hi]
    ext v
    by_cases hvi : v.1 = i <;> by_cases hvT : v ∈ T <;>
      simp_all [blockPart,flipBlocks,blockUnion,Finset.mem_symmDiff]

theorem fold_block_card {n ℓ : ℕ} (T : Finset (Fin n × Fin ℓ)) (i : Fin n) :
    (blockPart (fold T) i).card = if ℓ/2 < (blockPart T i).card then
      ℓ-(blockPart T i).card else (blockPart T i).card := by
  have hsub : blockPart T i ⊆ blockPart (Finset.univ : Finset (Fin n × Fin ℓ)) i := by
    intro v hv
    simp only [blockPart,Finset.mem_filter,Finset.mem_univ,true_and] at hv ⊢
    exact hv.2
  simp only [fold,block_flip,heavyBlocks,Finset.mem_filter,Finset.mem_univ,true_and]
  split_ifs
  · rw [Finset.card_sdiff_of_subset hsub,block_univ_card]
  · rfl

theorem fold_light {n ℓ : ℕ} (T : Finset (Fin n × Fin ℓ)) : fold T ∈ lightSets n ℓ := by
  simp only [lightSets,Finset.mem_filter,Finset.mem_univ,true_and]
  intro i
  rw [fold_block_card]
  have h := block_card_le T i
  split_ifs <;> omega

theorem fold_card_le {n ℓ : ℕ} (T : Finset (Fin n × Fin ℓ)) : (fold T).card ≤ T.card := by
  rw [← sum_block_card,← sum_block_card T]
  apply Finset.sum_le_sum
  intro i hi
  rw [fold_block_card]
  split_ifs <;> omega

theorem fold_encoding_injective {n ℓ : ℕ} :
    Function.Injective (fun T : Finset (Fin n × Fin ℓ) => (fold T,heavyBlocks T)) := by
  intro T S h
  have hfold := congrArg Prod.fst h
  have hheavy := congrArg Prod.snd h
  change fold T = fold S at hfold
  change heavyBlocks T = heavyBlocks S at hheavy
  have hT := flipBlocks_involution T (heavyBlocks T)
  have hS := flipBlocks_involution S (heavyBlocks S)
  change flipBlocks (fold T) (heavyBlocks T) = T at hT
  change flipBlocks (fold S) (heavyBlocks S) = S at hS
  rw [hfold,hheavy,hS] at hT
  exact hT.symm

end AC02Frege.HeavyBlockCounting
end

section
-- Inlined Solutions.PCOperations

open MvPolynomial

namespace AC02Frege.Support

theorem derivation_append {σ K : Type*} [Field K]
    (red : MvPolynomial σ K →ₗ[K] MvPolynomial σ K)
    (P : Set (MvPolynomial σ K))
    {π ρ : List (MvPolynomial σ K)}
    (hπ : PCNonBool.IsDerivation red P π)
    (hρ : PCNonBool.IsDerivation red P ρ) :
    PCNonBool.IsDerivation red P (π ++ ρ) := by
  intro k hk
  by_cases h : k < π.length
  · rcases hπ k h with ha | hc | hm
    · left
      simpa only [List.getElem_append_left h] using ha
    · right; left
      obtain ⟨i, j, hi, hj, a, b, hab⟩ := hc
      refine ⟨i, j, hi, hj, a, b, ?_⟩
      simpa only [List.getElem_append_left h,
        List.getElem_append_left (hi.trans h),
        List.getElem_append_left (hj.trans h)] using hab
    · right; right
      obtain ⟨i, hi, v, hiv⟩ := hm
      refine ⟨i, hi, v, ?_⟩
      simpa only [List.getElem_append_left h,
        List.getElem_append_left (hi.trans h)] using hiv
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt h)
    have hk' : k < ρ.length := by simp only [List.length_append] at hk; omega
    have hget (t : ℕ) (ht : t < ρ.length) :
        (π ++ ρ)[π.length + t]'(by simp only [List.length_append]; omega) = ρ[t] := by
      rw [List.getElem_append_right (Nat.le_add_right π.length t)]
      simp only [Nat.add_sub_cancel_left]
    rcases hρ k hk' with ha | hc | hm
    · left
      obtain ⟨a, ha, c, hac⟩ := ha
      exact ⟨a, ha, c, (hget k hk').trans hac⟩
    · right; left
      obtain ⟨i, j, hi, hj, a, b, hab⟩ := hc
      refine ⟨π.length + i, π.length + j, by omega, by omega, a, b, ?_⟩
      rw [hget k hk', hget i (hi.trans hk'), hget j (hj.trans hk')]
      exact hab
    · right; right
      obtain ⟨i, hi, v, hiv⟩ := hm
      refine ⟨π.length + i, by omega, v, ?_⟩
      rw [hget k hk', hget i (hi.trans hk')]
      exact hiv

theorem derivation_snoc {σ K : Type*} [Field K]
    (red : MvPolynomial σ K →ₗ[K] MvPolynomial σ K)
    (P : Set (MvPolynomial σ K)) {π : List (MvPolynomial σ K)}
    (hπ : PCNonBool.IsDerivation red P π) (p : MvPolynomial σ K)
    (hp :
      (∃ a ∈ P, ∃ c : K, p = c • red a) ∨
      (∃ (i j : ℕ) (hi : i < π.length) (hj : j < π.length) (a b : K),
        p = a • π[i] + b • π[j]) ∨
      (∃ (i : ℕ) (hi : i < π.length) (v : σ), p = red (X v * π[i]))) :
    PCNonBool.IsDerivation red P (π ++ [p]) := by
  intro k hk
  by_cases h : k < π.length
  · rcases hπ k h with ha | hc | hm
    · left; simpa only [List.getElem_append_left h] using ha
    · right; left
      obtain ⟨i, j, hi, hj, a, b, hab⟩ := hc
      refine ⟨i, j, hi, hj, a, b, ?_⟩
      simpa only [List.getElem_append_left h,
        List.getElem_append_left (hi.trans h),
        List.getElem_append_left (hj.trans h)] using hab
    · right; right
      obtain ⟨i, hi, v, hiv⟩ := hm
      refine ⟨i, hi, v, ?_⟩
      simpa only [List.getElem_append_left h,
        List.getElem_append_left (hi.trans h)] using hiv
  · have heq : k = π.length := by simp only [List.length_append, List.length_singleton] at hk; omega
    subst k
    have hlast : (π ++ [p])[π.length] = p := by
      rw [List.getElem_append_right (Nat.le_refl _)]
      simp only [Nat.sub_self, List.getElem_cons_zero]
    rcases hp with ha | hc | hm
    · left; simpa only [hlast] using ha
    · right; left
      obtain ⟨i, j, hi, hj, a, b, hab⟩ := hc
      refine ⟨i, j, hi, hj, a, b, ?_⟩
      simpa only [hlast, List.getElem_append_left hi, List.getElem_append_left hj] using hab
    · right; right
      obtain ⟨i, hi, v, hiv⟩ := hm
      refine ⟨i, hi, v, ?_⟩
      simpa only [hlast, List.getElem_append_left hi] using hiv

theorem pc_zero {n : ℕ} (F : LiftSAParity.CNF (Fin n)) (D : ℕ) :
    PCDerivable F D 0 := Or.inl rfl

theorem pc_degree {n : ℕ} {F : LiftSAParity.CNF (Fin n)} {D : ℕ}
    {p : MvPolynomial (Fin n) (ZMod 2)} (hp : PCDerivable F D p) : p.totalDegree ≤ D := by
  rcases hp with rfl | ⟨π, _, hdeg, hp⟩
  · simp
  · exact hdeg p hp

theorem pc_smul {n : ℕ} (F : LiftSAParity.CNF (Fin n)) (D : ℕ)
    {p : MvPolynomial (Fin n) (ZMod 2)} (hp : PCDerivable F D p) (c : ZMod 2) :
    PCDerivable F D (c • p) := by
  rcases hp with rfl | ⟨π, hπ, hdeg, hp⟩
  · simp only [smul_zero]; exact pc_zero F D
  · obtain ⟨i, hi, hpi⟩ := List.mem_iff_getElem.mp hp
    refine Or.inr ⟨π ++ [c • p], ?_, ?_, by simp⟩
    · apply derivation_snoc _ _ hπ
      right; left
      exact ⟨i, i, hi, hi, c, 0, by simp only [hpi, zero_smul, add_zero]⟩
    · intro q hq
      rcases List.mem_append.mp hq with hq | hq
      · exact hdeg q hq
      · have heq : q = c • p := List.mem_singleton.mp hq
        subst q
        exact (totalDegree_smul_le c p).trans (hdeg p hp)

theorem pc_add {n : ℕ} (F : LiftSAParity.CNF (Fin n)) (D : ℕ)
    {p q : MvPolynomial (Fin n) (ZMod 2)}
    (hp : PCDerivable F D p) (hq : PCDerivable F D q) :
    PCDerivable F D (p + q) := by
  rcases hp with rfl | ⟨π, hπ, hπdeg, hp⟩
  · simpa only [zero_add] using hq
  rcases hq with rfl | ⟨ρ, hρ, hρdeg, hq⟩
  · simpa only [add_zero] using (show PCDerivable F D p from Or.inr ⟨π, hπ, hπdeg, hp⟩)
  have hboth := derivation_append _ _ hπ hρ
  have hp' : p ∈ π ++ ρ := List.mem_append_left _ hp
  have hq' : q ∈ π ++ ρ := List.mem_append_right _ hq
  obtain ⟨i, hi, hpi⟩ := List.mem_iff_getElem.mp hp'
  obtain ⟨j, hj, hqj⟩ := List.mem_iff_getElem.mp hq'
  refine Or.inr ⟨(π ++ ρ) ++ [p + q], ?_, ?_, by simp⟩
  · apply derivation_snoc _ _ hboth
    right; left
    exact ⟨i, j, hi, hj, 1, 1, by simp only [hpi, hqj, one_smul]⟩
  · intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · rcases List.mem_append.mp hr with hr | hr
      · exact hπdeg r hr
      · exact hρdeg r hr
    · have heq : r = p + q := List.mem_singleton.mp hr
      subst r
      exact (totalDegree_add p q).trans (max_le (hπdeg p hp) (hρdeg q hq))

theorem pc_mul_X {n : ℕ} (F : LiftSAParity.CNF (Fin n)) (D : ℕ)
    {p : MvPolynomial (Fin n) (ZMod 2)} (hp : PCDerivable F D p)
    (v : Fin n) (hdeg : p.totalDegree + 1 ≤ D) :
    PCDerivable F D (p * X v) := by
  rcases hp with rfl | ⟨π, hπ, hπdeg, hp⟩
  · simp only [zero_mul]; exact pc_zero F D
  obtain ⟨i, hi, hpi⟩ := List.mem_iff_getElem.mp hp
  refine Or.inr ⟨π ++ [p * X v], ?_, ?_, by simp⟩
  · apply derivation_snoc _ _ hπ
    right; right
    exact ⟨i, hi, v, by simp only [hpi, LinearMap.id_apply, mul_comm]⟩
  · intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact hπdeg q hq
    · have heq : q = p * X v := List.mem_singleton.mp hq
      subst q
      exact (totalDegree_mul p (X v)).trans (by simpa only [totalDegree_X] using hdeg)

theorem pc_axiom {n : ℕ} (F : LiftSAParity.CNF (Fin n)) (D : ℕ)
    (p : MvPolynomial (Fin n) (ZMod 2)) (hp : p ∈ pcAxioms F)
    (hdeg : p.totalDegree ≤ D) : PCDerivable F D p := by
  refine Or.inr ⟨[p], ?_, by simpa using hdeg, by simp⟩
  intro k hk
  have heq : k = 0 := by simpa using hk
  subst k
  left
  exact ⟨p, hp, 1, by simp⟩

end AC02Frege.Support
end

section
-- Inlined Solutions.BooleanAlgebra

open MvPolynomial AC02Frege
namespace AC02Frege.BooleanAlgebra

theorem ml_monomial {V : Type*} (s : V →₀ ℕ) (c : ZMod 2) :
    ML (monomial s c) = monomial (sqfree s) c := by
  have h := (basisMonomials V (ZMod 2)).constr_basis (ZMod 2)
    (fun t => monomial (sqfree t) (1 : ZMod 2)) s
  have hc : monomial s c = c • monomial s (1 : ZMod 2) := by
    simp only [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  rw [hc, map_smul]
  change c • ((basisMonomials V (ZMod 2)).constr (ZMod 2)
    (fun t => monomial (sqfree t) (1 : ZMod 2)) (monomial s 1)) = _
  rw [show monomial s (1 : ZMod 2) = basisMonomials V (ZMod 2) s by rfl]
  rw [h]
  simp only [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]

theorem ml_multilinear {V : Type*} (p : MvPolynomial V (ZMod 2)) :
    IsMultilinear (ML p) := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial s c =>
    rw [ml_monomial]
    intro t ht v
    have ht' : t = sqfree s := (Finset.mem_singleton.mp (support_monomial_subset ht))
    subst t
    simp [sqfree, Finsupp.mapRange_apply]
  | add p q hp hq =>
    rw [map_add]
    intro s hs v
    rcases Finset.mem_union.mp (support_add hs) with hs | hs
    · exact hp s hs v
    · exact hq s hs v


theorem sqfree_support {V : Type*} (s : V →₀ ℕ) : (sqfree s).support = s.support := by
  classical
  ext i
  simp only [Finsupp.mem_support_iff, sqfree, Finsupp.mapRange_apply]
  omega

theorem sqfree_eq_self {V : Type*} (s : V →₀ ℕ) (hs : ∀ i, s i ≤ 1) : sqfree s = s := by
  ext i
  simp only [sqfree, Finsupp.mapRange_apply, min_eq_left (hs i)]

theorem ml_of_multilinear {V : Type*} (p : MvPolynomial V (ZMod 2))
    (hp : IsMultilinear p) : ML p = p := by
  classical
  conv_lhs => rw [p.as_sum]
  simp only [map_sum, ml_monomial]
  conv_rhs => rw [p.as_sum]
  apply Finset.sum_congr rfl
  intro s hs
  rw [sqfree_eq_self s (hp s hs)]

theorem ml_idempotent {V : Type*} (p : MvPolynomial V (ZMod 2)) : ML (ML p) = ML p :=
  ml_of_multilinear _ (ml_multilinear p)

theorem eval_ml {V : Type*} (p : MvPolynomial V (ZMod 2)) (x : V → ZMod 2) :
    eval x (ML p) = eval x p := by
  classical
  have hpow (a : ZMod 2) (k : ℕ) : a ^ min k 1 = a ^ k := by
    fin_cases a
    · change (0 : ZMod 2) ^ min k 1 = (0 : ZMod 2) ^ k
      cases k <;> simp
    · change (1 : ZMod 2) ^ min k 1 = (1 : ZMod 2) ^ k
      simp
  induction p using MvPolynomial.induction_on' with
  | monomial s c =>
    rw [ml_monomial, eval_monomial, eval_monomial]
    congr 1
    simp only [Finsupp.prod, sqfree_support]
    apply Finset.prod_congr rfl
    intro i _
    simpa only [sqfree, Finsupp.mapRange_apply] using hpow (x i) (s i)
  | add p q hp hq => simp only [map_add, hp, hq]

theorem multilinear_ext {V : Type} [Finite V]
    {p q : MvPolynomial V (ZMod 2)}
    (hp : IsMultilinear p) (hq : IsMultilinear q)
    (h : ∀ x : V → ZMod 2, eval x p = eval x q) : p = q := by
  apply sub_eq_zero.mp
  apply MvPolynomial.eq_zero_of_eval_eq_zero V (ZMod 2) (p - q)
  · intro x; simp only [map_sub, h x, sub_self]
  · have hp' : p ∈ restrictDegree V (ZMod 2) 1 := (mem_restrictDegree V p 1).mpr hp
    have hq' : q ∈ restrictDegree V (ZMod 2) 1 := (mem_restrictDegree V q 1).mpr hq
    simpa only [ZMod.card, Nat.reduceSub] using (restrictDegree V (ZMod 2) 1).sub_mem hp' hq'

theorem ml_mul_left {V : Type} [Finite V] (p q : MvPolynomial V (ZMod 2)) :
    ML (ML p * q) = ML (p * q) := by
  apply multilinear_ext (ml_multilinear _) (ml_multilinear _)
  intro x
  simp only [eval_ml, map_mul]

theorem ml_mul_right {V : Type} [Finite V] (p q : MvPolynomial V (ZMod 2)) :
    ML (p * ML q) = ML (p * q) := by
  rw [mul_comm p (ML q), ml_mul_left, mul_comm]

theorem xMon_eq_monomial {V : Type*} (S : Finset V) :
    xMon S = monomial (Finsupp.indicator S (fun _ _ => 1)) (1 : ZMod 2) := by
  classical
  simpa only [xMon, pow_one] using (prod_X_pow (R := ZMod 2) (fun _ : V => 1) S)

theorem indicator_support {V : Type*} (S : Finset V) :
    (Finsupp.indicator S (fun _ _ => (1 : ℕ))).support = S := by
  classical
  ext i
  simp only [Finsupp.mem_support_iff, Finsupp.indicator_apply]
  split_ifs <;> simp_all

theorem xMon_multilinear {V : Type*} (S : Finset V) : IsMultilinear (xMon S) := by
  classical
  rw [xMon_eq_monomial]
  intro s hs i
  have heq := Finset.mem_singleton.mp (support_monomial_subset hs)
  subst s
  simp only [Finsupp.indicator_apply]
  split_ifs <;> omega

theorem xMon_eval {V : Type*} (S : Finset V) (x : V → ZMod 2) :
    eval x (xMon S) = ∏ i ∈ S, x i := by
  simp only [xMon, map_prod, eval_X]

theorem xMon_totalDegree {V : Type*} (S : Finset V) : (xMon S).totalDegree = S.card := by
  classical
  rw [xMon_eq_monomial, totalDegree_monomial _ (one_ne_zero : (1 : ZMod 2) ≠ 0)]
  simp only [Finsupp.sum, indicator_support]
  have heq : (∑ i ∈ S, (Finsupp.indicator S (fun _ _ => (1 : ℕ))) i) = ∑ _i ∈ S, 1 := by
    apply Finset.sum_congr rfl
    intro i hi
    simp [Finsupp.indicator_apply, hi]
  rw [heq]
  simp

theorem xMon_linearIndependent {V : Type*} :
    LinearIndependent (ZMod 2) (fun S : Finset V => xMon S) := by
  classical
  have hinj : Function.Injective (fun S : Finset V => Finsupp.indicator S (fun _ _ => (1 : ℕ))) := by
    intro S T h
    have := congrArg Finsupp.support h
    simpa only [indicator_support] using this
  have h := (basisMonomials V (ZMod 2)).linearIndependent.comp
    (fun S : Finset V => Finsupp.indicator S (fun _ _ => (1 : ℕ))) hinj
  simpa only [Function.comp_def, coe_basisMonomials, xMon_eq_monomial] using h

end AC02Frege.BooleanAlgebra
end

section
-- Inlined Solutions.MajorityFoundation

open MvPolynomial AC02Frege
open AC02Frege.BooleanAlgebra

namespace AC02Frege.MajorityFoundation

open Classical

noncomputable def pointPoly {V : Type} [Fintype V] [DecidableEq V] (S : Finset V) : MvPolynomial V (ZMod 2) :=
  ∏ i : V, if i ∈ S then X i else 1 + X i

theorem pointPoly_indicator {V : Type} [Fintype V] [DecidableEq V] (S : Finset V) :
    pointPoly S = MvPolynomial.indicator (fun i : V => if i ∈ S then (1 : ZMod 2) else 0) := by
  classical
  unfold pointPoly MvPolynomial.indicator
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i ∈ S <;> simp only [hi, ↓reduceIte, ZMod.card, Nat.reduceSub, pow_one]
  · simp only [map_one, CharTwo.sub_eq_add]
    calc
      X i = X i + (1 + 1) := by rw [CharTwo.add_self_eq_zero, add_zero]
      _ = 1 + (X i + 1) := by abel
  · simp [CharTwo.sub_eq_add]

theorem pointPoly_multilinear {V : Type} [Fintype V] [DecidableEq V] (S : Finset V) :
    IsMultilinear (pointPoly S) := by
  rw [pointPoly_indicator]
  apply (mem_restrictDegree V _ 1).mp
  simpa only [ZMod.card, Nat.reduceSub] using indicator_mem_restrictDegree
    (fun i : V => if i ∈ S then (1 : ZMod 2) else 0)

theorem pointPoly_eval {V : Type} [Fintype V] [DecidableEq V] (S : Finset V) (x : V → ZMod 2) :
    eval x (pointPoly S) =
      if x = (fun i => if i ∈ S then (1 : ZMod 2) else 0) then 1 else 0 := by
  classical
  rw [pointPoly_indicator]
  split_ifs with h
  · subst x; exact eval_indicator_apply_eq_one _
  · exact eval_indicator_apply_eq_zero _ _ h

theorem multilinear_sum {V ι : Type} (S : Finset ι) (f : ι → MvPolynomial V (ZMod 2))
    (hf : ∀ i ∈ S, IsMultilinear (f i)) : IsMultilinear (∑ i ∈ S, f i) := by
  apply (mem_restrictDegree V _ 1).mp
  exact Submodule.sum_mem _ (fun i hi => (mem_restrictDegree V (f i) 1).mpr (hf i hi))

theorem majOne_multilinear (ℓ : ℕ) : IsMultilinear (majOne ℓ) := by
  unfold majOne
  apply multilinear_sum
  intro S _
  simpa only [pointPoly] using pointPoly_multilinear S

theorem eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · left; rfl
  · right; rfl

theorem point_of_ones {V : Type} [Fintype V] [DecidableEq V] (x : V → ZMod 2) :
    (fun i => if i ∈ Finset.univ.filter (fun i => x i = 1) then (1 : ZMod 2) else 0) = x := by
  classical
  funext i
  rcases eq_zero_or_one (x i) with hi | hi <;> simp [hi]

theorem ones_of_point {V : Type} [Fintype V] [DecidableEq V] (S : Finset V) :
    Finset.univ.filter (fun i => (if i ∈ S then (1 : ZMod 2) else 0) = 1) = S := by
  classical
  ext i
  simp

theorem majOne_eval (ℓ : ℕ) (x : Fin ℓ → ZMod 2) :
    eval x (majOne ℓ) = if ℓ / 2 < (Finset.univ.filter (fun i => x i = 1)).card
      then 1 else 0 := by
  classical
  unfold majOne
  simp only [map_sum]
  have hev (S : Finset (Fin ℓ)) := pointPoly_eval S x
  simp only [pointPoly] at hev
  simp only [hev]
  have heq (S : Finset (Fin ℓ)) :
      x = (fun i => if i ∈ S then (1 : ZMod 2) else 0) ↔
        S = Finset.univ.filter (fun i => x i = 1) := by
    constructor
    · intro hx; rw [hx, ones_of_point]
    · intro hS; subst S; exact (point_of_ones x).symm
  simp only [heq]
  simp

theorem heavy_monomial_absorbs_majority (ℓ : ℕ) (S : Finset (Fin ℓ))
    (hS : ℓ / 2 < S.card) : ML (xMon S * majOne ℓ) = xMon S := by
  apply multilinear_ext (ml_multilinear _) (xMon_multilinear S)
  intro x
  simp only [eval_ml, map_mul]
  by_cases hx : eval x (xMon S) = 0
  · rw [hx, zero_mul]
  · have hsub : S ⊆ Finset.univ.filter (fun i => x i = 1) := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hxi : x i ≠ 0 := by
        intro hz
        apply hx
        rw [xMon_eval]
        exact Finset.prod_eq_zero hi hz
      rcases eq_zero_or_one (x i) with hz | ho
      · exact False.elim (hxi hz)
      · exact ho
    have hcard := Finset.card_le_card hsub
    rw [majOne_eval, if_pos (by omega), mul_one]

theorem pointPoly_factor {V : Type} [Fintype V] [DecidableEq V] (S : Finset V) :
    pointPoly S = xMon S * ∏ i ∈ Finset.univ.filter (fun i : V => i ∉ S),
      (1 + X i : MvPolynomial V (ZMod 2)) := by
  simp only [pointPoly, Finset.prod_ite]
  congr 1
  rw [xMon]
  apply Finset.prod_congr
  · ext i; simp
  · intro i _; rfl

theorem support_mul_xMon_degree {V : Type} [Fintype V] [DecidableEq V]
    (S : Finset V) (p : MvPolynomial V (ZMod 2))
    (s : V →₀ ℕ) (hs : s ∈ (xMon S * p).support) : S.card ≤ s.sum (fun _ e => e) := by
  classical
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.mem_add.mp (support_mul (xMon S) p hs)
  have haeq : a = Finsupp.indicator S (fun _ _ => (1 : ℕ)) := by
    rw [xMon_eq_monomial] at ha
    exact Finset.mem_singleton.mp (support_monomial_subset ha)
  subst a
  have hsum : (Finsupp.indicator S (fun _ _ => (1 : ℕ))).sum (fun _ e => e) = S.card := by
    simp only [Finsupp.sum, indicator_support]
    have heq : (∑ i ∈ S, (Finsupp.indicator S (fun _ _ => (1 : ℕ))) i) = ∑ _i ∈ S, 1 := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [Finsupp.indicator_apply, hi]
    rw [heq]; simp
  rw [← hab]
  rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), hsum]
  omega

theorem majOne_support_heavy (ℓ : ℕ) (s : Fin ℓ →₀ ℕ)
    (hs : s ∈ (majOne ℓ).support) : ℓ / 2 < s.sum (fun _ e => e) := by
  classical
  unfold majOne at hs
  obtain ⟨S, hS, hsS⟩ := Finset.mem_biUnion.mp (support_sum hs)
  have hheavy := (Finset.mem_filter.mp hS).2
  change s ∈ (pointPoly S).support at hsS
  rw [pointPoly_factor] at hsS
  exact lt_of_lt_of_le hheavy (support_mul_xMon_degree S _ s hsS)

end AC02Frege.MajorityFoundation
end

section
-- Inlined Solutions.BooleanBasis

open MvPolynomial AC02Frege
open AC02Frege.BooleanAlgebra AC02Frege.MajorityFoundation

namespace AC02Frege.BooleanBasis

theorem squarefree_eq_indicator {V : Type*} (s : V →₀ ℕ) (hs : ∀ i, s i ≤ 1) :
    s = Finsupp.indicator s.support (fun _ _ => 1) := by
  classical
  ext i
  by_cases hi : i ∈ s.support
  · simp only [Finsupp.indicator_apply, dif_pos hi]
    have hpos := Finsupp.mem_support_iff.mp hi
    exact Nat.le_antisymm (hs i) (by omega)
  · simpa only [Finsupp.indicator_apply, dif_neg hi] using (by simpa only [Finsupp.mem_support_iff, not_not] using hi : s i = 0)

theorem squarefree_monomial {V : Type*} (s : V →₀ ℕ) (c : ZMod 2)
    (hs : ∀ i, s i ≤ 1) : monomial s c = c • xMon s.support := by
  rw [xMon_eq_monomial, smul_monomial, smul_eq_mul, mul_one,
    ← squarefree_eq_indicator s hs]

theorem squarefree_sum {V : Type*} (s : V →₀ ℕ) (hs : ∀ i, s i ≤ 1) :
    s.sum (fun _ e => e) = s.support.card := by
  have heq := squarefree_monomial s (1 : ZMod 2) hs
  have hd := congrArg MvPolynomial.totalDegree heq
  simpa only [totalDegree_monomial _ one_ne_zero, one_smul, xMon_totalDegree] using hd

noncomputable def monomialSpan {V : Type*} (P : Finset V → Prop) :
    Submodule (ZMod 2) (MvPolynomial V (ZMod 2)) :=
  Submodule.span (ZMod 2) {p | ∃ S : Finset V, P S ∧ p = xMon S}

theorem mem_monomialSpan_iff {V : Type*} (P : Finset V → Prop)
    (p : MvPolynomial V (ZMod 2)) : p ∈ monomialSpan P ↔
      IsMultilinear p ∧ ∀ s ∈ p.support, P s.support := by
  classical
  let M := restrictSupport (ZMod 2) {s : V →₀ ℕ | (∀ i, s i ≤ 1) ∧ P s.support}
  have heq : monomialSpan P = M := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro q ⟨S, hS, rfl⟩
      rw [xMon_eq_monomial]
      apply (monomial_mem_restrictSupport (ZMod 2)).mpr
      left
      refine ⟨?_, ?_⟩
      · intro i
        simp only [Finsupp.indicator_apply]
        split_ifs <;> omega
      · simpa only [indicator_support] using hS
    · intro q hq
      have hq' : ∀ s ∈ q.support, (∀ i, s i ≤ 1) ∧ P s.support := hq
      rw [q.as_sum]
      apply Submodule.sum_mem
      intro s hs
      obtain ⟨hml, hP⟩ := hq' s hs
      rw [squarefree_monomial s _ hml]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨s.support, hP, rfl⟩)
  rw [heq, mem_restrictSupport_iff (ZMod 2)]
  constructor
  · intro hp
    exact ⟨fun s hs i => (hp hs).1 i, fun s hs => (hp hs).2⟩
  · rintro ⟨hml, hP⟩ s hs
    exact ⟨hml s hs, hP s hs⟩

theorem mem_light_iff {V : Type*} (m : ℕ) (p : MvPolynomial V (ZMod 2)) :
    p ∈ monomialSpan (fun S : Finset V => S.card ≤ m) ↔
      IsMultilinear p ∧ p.totalDegree ≤ m := by
  rw [mem_monomialSpan_iff]
  constructor
  · rintro ⟨hp, hP⟩
    refine ⟨hp, Finset.sup_le fun s hs => ?_⟩
    rw [squarefree_sum s (hp s hs)]
    exact hP s hs
  · rintro ⟨hp, hd⟩
    refine ⟨hp, fun s hs => ?_⟩
    rw [← squarefree_sum s (hp s hs)]
    exact (le_totalDegree hs).trans hd

theorem point_interpolation {V : Type} [Fintype V] [DecidableEq V]
    (p : MvPolynomial V (ZMod 2)) (hp : IsMultilinear p) :
    p = ∑ S : Finset V, eval (fun i => if i ∈ S then (1 : ZMod 2) else 0) p • pointPoly S := by
  apply multilinear_ext hp
    (multilinear_sum _ _ (fun S _ =>
      (mem_restrictDegree V _ 1).mp ((restrictDegree V (ZMod 2) 1).smul_mem _
        ((mem_restrictDegree V _ 1).mpr (pointPoly_multilinear S)))))
  intro x
  simp only [map_sum, smul_eval, pointPoly_eval]
  have heq (S : Finset V) :
      x = (fun i => if i ∈ S then (1 : ZMod 2) else 0) ↔
        S = Finset.univ.filter (fun i => x i = 1) := by
    constructor
    · intro h; rw [h, ones_of_point]
    · intro h; subst S; exact (point_of_ones x).symm
  simp only [heq]
  simp
  have hx : (fun i => if x i = 1 then (1 : ZMod 2) else 0) = x := by
    funext i
    rcases eq_zero_or_one (x i) with hi | hi <;> simp [hi]
  rw [hx]

end AC02Frege.BooleanBasis
end

section
-- Inlined Solutions.BooleanFlip

open MvPolynomial AC02Frege
open AC02Frege.BooleanAlgebra AC02Frege.MajorityFoundation AC02Frege.BooleanBasis

namespace AC02Frege.BooleanFlip

theorem ml_totalDegree_le {V : Type*} (p : MvPolynomial V (ZMod 2)) :
    (ML p).totalDegree ≤ p.totalDegree := by
  classical
  conv_lhs => rw [p.as_sum]
  simp only [map_sum, ml_monomial]
  apply totalDegree_finsetSum_le
  intro s hs
  apply (totalDegree_monomial_le _ _).trans
  apply le_trans ?_ (le_totalDegree hs)
  simp only [Finsupp.sum, sqfree_support]
  apply Finset.sum_le_sum
  intro i _
  simp only [sqfree, Finsupp.mapRange_apply]
  exact min_le_left _ _

theorem bind_linear_totalDegree_le {V W : Type*} (f : V → MvPolynomial W (ZMod 2))
    (hf : ∀ i, (f i).totalDegree ≤ 1) (p : MvPolynomial V (ZMod 2)) :
    (bind₁ f p).totalDegree ≤ p.totalDegree := by
  classical
  conv_lhs => rw [p.as_sum]
  simp only [map_sum, bind₁_monomial]
  apply totalDegree_finsetSum_le
  intro s hs
  apply le_trans (totalDegree_mul _ _)
  simp only [totalDegree_C, zero_add]
  apply (totalDegree_finsetProd _ _).trans
  apply le_trans ?_ (le_totalDegree hs)
  apply Finset.sum_le_sum
  intro i _
  exact (totalDegree_pow _ _).trans (by simpa using Nat.mul_le_mul_left (s i) (hf i))

noncomputable def flip {V : Type*} (p : MvPolynomial V (ZMod 2)) :
    MvPolynomial V (ZMod 2) := ML (bind₁ (fun i => 1 + X i) p)

theorem flip_multilinear {V : Type*} (p : MvPolynomial V (ZMod 2)) :
    IsMultilinear (flip p) := ml_multilinear _

theorem flip_degree_le {V : Type*} (p : MvPolynomial V (ZMod 2)) :
    (flip p).totalDegree ≤ p.totalDegree := by
  apply (ml_totalDegree_le _).trans
  apply bind_linear_totalDegree_le
  intro i
  exact (totalDegree_add _ _).trans (by simp)

theorem flip_eval {V : Type*} (p : MvPolynomial V (ZMod 2)) (x : V → ZMod 2) :
    eval x (flip p) = eval (fun i => 1 + x i) p := by
  rw [flip, eval_ml]
  simp only [eval, eval₂Hom_bind₁, map_add, map_one, eval₂Hom_X']

theorem flip_involution {V : Type} [Finite V] (p : MvPolynomial V (ZMod 2))
    (hp : IsMultilinear p) : flip (flip p) = p := by
  apply multilinear_ext (flip_multilinear _) hp
  intro x
  simp only [flip_eval, CharTwo.add_cancel_left]

end AC02Frege.BooleanFlip
end

section
-- Inlined Solutions.BooleanPC

open MvPolynomial AC02Frege
open AC02Frege.Support AC02Frege.BooleanAlgebra AC02Frege.BooleanFlip

namespace SemAC02.BooleanPC

def Derivable {n : ℕ} (P : Set (MvPolynomial (Fin n) (ZMod 2))) (D : ℕ)
    (p : MvPolynomial (Fin n) (ZMod 2)) : Prop :=
  p = 0 ∨ ∃ π : List (MvPolynomial (Fin n) (ZMod 2)),
    PCNonBool.IsDerivation ML P π ∧ (∀ q ∈ π, q.totalDegree ≤ D) ∧ p ∈ π

theorem pc_zero {n : ℕ} (P : Set (MvPolynomial (Fin n) (ZMod 2))) (D : ℕ) :
    Derivable P D 0 := Or.inl rfl

theorem pc_degree {n : ℕ} {P : Set (MvPolynomial (Fin n) (ZMod 2))} {D : ℕ}
    {p : MvPolynomial (Fin n) (ZMod 2)} (hp : Derivable P D p) : p.totalDegree ≤ D := by
  rcases hp with rfl | ⟨π, _, hdeg, hp⟩
  · simp
  · exact hdeg p hp

theorem pc_smul {n : ℕ} (P : Set (MvPolynomial (Fin n) (ZMod 2))) (D : ℕ)
    {p : MvPolynomial (Fin n) (ZMod 2)} (hp : Derivable P D p) (c : ZMod 2) :
    Derivable P D (c • p) := by
  rcases hp with rfl | ⟨π, hπ, hdeg, hp⟩
  · simp only [smul_zero]; exact pc_zero P D
  · obtain ⟨i, hi, hpi⟩ := List.mem_iff_getElem.mp hp
    refine Or.inr ⟨π ++ [c • p], ?_, ?_, by simp⟩
    · apply derivation_snoc _ _ hπ
      right; left
      exact ⟨i, i, hi, hi, c, 0, by simp only [hpi, zero_smul, add_zero]⟩
    · intro q hq
      rcases List.mem_append.mp hq with hq | hq
      · exact hdeg q hq
      · have heq : q = c • p := List.mem_singleton.mp hq
        subst q
        exact (totalDegree_smul_le c p).trans (hdeg p hp)

theorem pc_add {n : ℕ} (P : Set (MvPolynomial (Fin n) (ZMod 2))) (D : ℕ)
    {p q : MvPolynomial (Fin n) (ZMod 2)}
    (hp : Derivable P D p) (hq : Derivable P D q) :
    Derivable P D (p + q) := by
  rcases hp with rfl | ⟨π, hπ, hπdeg, hp⟩
  · simpa only [zero_add] using hq
  rcases hq with rfl | ⟨ρ, hρ, hρdeg, hq⟩
  · simpa only [add_zero] using (show Derivable P D p from Or.inr ⟨π, hπ, hπdeg, hp⟩)
  have hboth := derivation_append _ _ hπ hρ
  have hp' : p ∈ π ++ ρ := List.mem_append_left _ hp
  have hq' : q ∈ π ++ ρ := List.mem_append_right _ hq
  obtain ⟨i, hi, hpi⟩ := List.mem_iff_getElem.mp hp'
  obtain ⟨j, hj, hqj⟩ := List.mem_iff_getElem.mp hq'
  refine Or.inr ⟨(π ++ ρ) ++ [p + q], ?_, ?_, by simp⟩
  · apply derivation_snoc _ _ hboth
    right; left
    exact ⟨i, j, hi, hj, 1, 1, by simp only [hpi, hqj, one_smul]⟩
  · intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · rcases List.mem_append.mp hr with hr | hr
      · exact hπdeg r hr
      · exact hρdeg r hr
    · have heq : r = p + q := List.mem_singleton.mp hr
      subst r
      exact (totalDegree_add p q).trans (max_le (hπdeg p hp) (hρdeg q hq))

theorem pc_mul_X {n : ℕ} (P : Set (MvPolynomial (Fin n) (ZMod 2))) (D : ℕ)
    {p : MvPolynomial (Fin n) (ZMod 2)} (hp : Derivable P D p)
    (v : Fin n) (hdeg : p.totalDegree + 1 ≤ D) :
    Derivable P D (ML (X v * p)) := by
  rcases hp with rfl | ⟨π, hπ, hπdeg, hp⟩
  · simp only [mul_zero, map_zero]; exact pc_zero P D
  obtain ⟨i, hi, hpi⟩ := List.mem_iff_getElem.mp hp
  refine Or.inr ⟨π ++ [ML (X v * p)], ?_, ?_, by simp⟩
  · apply derivation_snoc _ _ hπ
    right; right
    exact ⟨i, hi, v, by rw [hpi]⟩
  · intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact hπdeg q hq
    · have heq : q = ML (X v * p) := List.mem_singleton.mp hq
      subst q
      exact (ml_totalDegree_le _).trans ((totalDegree_mul (X v) p).trans (by simpa only [totalDegree_X, Nat.add_comm] using hdeg))

theorem pc_axiom {n : ℕ} (P : Set (MvPolynomial (Fin n) (ZMod 2))) (D : ℕ)
    (p : MvPolynomial (Fin n) (ZMod 2)) (hp : p ∈ P)
    (hdeg : (ML p).totalDegree ≤ D) : Derivable P D (ML p) := by
  refine Or.inr ⟨[ML p], ?_, by simpa using hdeg, by simp⟩
  intro k hk
  have heq : k = 0 := by simpa using hk
  subst k
  left
  exact ⟨p, hp, 1, by simp⟩

theorem pc_mono {n : ℕ} {P : Set (MvPolynomial (Fin n) (ZMod 2))} {D E : ℕ}
    (hDE : D ≤ E) {p : MvPolynomial (Fin n) (ZMod 2)} (hp : Derivable P D p) :
    Derivable P E p := by
  rcases hp with h | ⟨π, hπ, hdeg, hp⟩
  · exact Or.inl h
  · exact Or.inr ⟨π, hπ, fun q hq => (hdeg q hq).trans hDE, hp⟩

noncomputable def consequenceSpace {n : ℕ} (P : Set (MvPolynomial (Fin n) (ZMod 2))) (D : ℕ) :
    Submodule (ZMod 2) (MvPolynomial (Fin n) (ZMod 2)) where
  carrier := {p | Derivable P D p}
  zero_mem' := pc_zero P D
  add_mem' := pc_add P D
  smul_mem' := fun a _ hp => pc_smul P D hp a

end SemAC02.BooleanPC
end

section
-- Inlined Solutions.RelativePC

open MvPolynomial AC02Frege SemAC02
open AC02Frege.Support AC02Frege.BooleanAlgebra AC02Frege.BooleanFlip

namespace SemAC02.RelativePC

def Derivable {n : ℕ} (P : Set (MvPolynomial (Fin n) (ZMod 2)))
    (U : Submodule (ZMod 2) (MvPolynomial (Fin n) (ZMod 2)))
    (p : MvPolynomial (Fin n) (ZMod 2)) : Prop :=
  p = 0 ∨ ∃ π : List (MvPolynomial (Fin n) (ZMod 2)),
    PCNonBool.IsDerivation ML P π ∧ (∀ q ∈ π, q ∈ U) ∧ p ∈ π

theorem pc_zero {n : ℕ} (P : Set (MvPolynomial (Fin n) (ZMod 2)))
    (U : Submodule (ZMod 2) (MvPolynomial (Fin n) (ZMod 2))) : Derivable P U 0 := Or.inl rfl

theorem pc_mem {n : ℕ} {P : Set (MvPolynomial (Fin n) (ZMod 2))}
    {U : Submodule (ZMod 2) (MvPolynomial (Fin n) (ZMod 2))}
    {p : MvPolynomial (Fin n) (ZMod 2)} (hp : Derivable P U p) : p ∈ U := by
  rcases hp with rfl | ⟨π,_,hmem,hp⟩
  · exact U.zero_mem
  · exact hmem p hp

theorem pc_smul {n : ℕ} (P : Set (MvPolynomial (Fin n) (ZMod 2)))
    (U : Submodule (ZMod 2) (MvPolynomial (Fin n) (ZMod 2)))
    {p : MvPolynomial (Fin n) (ZMod 2)} (hp : Derivable P U p) (c : ZMod 2) :
    Derivable P U (c • p) := by
  rcases hp with rfl | ⟨π,hπ,hmem,hp⟩
  · simp only [smul_zero]; exact pc_zero P U
  obtain ⟨i,hi,hpi⟩ := List.mem_iff_getElem.mp hp
  refine Or.inr ⟨π ++ [c • p], ?_, ?_, by simp⟩
  · apply derivation_snoc _ _ hπ
    right; left
    exact ⟨i,i,hi,hi,c,0,by simp only [hpi,zero_smul,add_zero]⟩
  · intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact hmem q hq
    · have he : q = c • p := List.mem_singleton.mp hq
      rw [he]
      exact U.smul_mem c (hmem p hp)

theorem pc_add {n : ℕ} (P : Set (MvPolynomial (Fin n) (ZMod 2)))
    (U : Submodule (ZMod 2) (MvPolynomial (Fin n) (ZMod 2)))
    {p q : MvPolynomial (Fin n) (ZMod 2)} (hp : Derivable P U p) (hq : Derivable P U q) :
    Derivable P U (p+q) := by
  rcases hp with rfl | ⟨π,hπ,hπmem,hp⟩
  · simpa only [zero_add] using hq
  rcases hq with rfl | ⟨ρ,hρ,hρmem,hq⟩
  · simpa only [add_zero] using (show Derivable P U p from Or.inr ⟨π,hπ,hπmem,hp⟩)
  have hboth := derivation_append _ _ hπ hρ
  have hp' : p ∈ π ++ ρ := List.mem_append_left _ hp
  have hq' : q ∈ π ++ ρ := List.mem_append_right _ hq
  obtain ⟨i,hi,hpi⟩ := List.mem_iff_getElem.mp hp'
  obtain ⟨j,hj,hqj⟩ := List.mem_iff_getElem.mp hq'
  refine Or.inr ⟨(π ++ ρ) ++ [p+q], ?_, ?_, by simp⟩
  · apply derivation_snoc _ _ hboth
    right; left
    exact ⟨i,j,hi,hj,1,1,by simp only [hpi,hqj,one_smul]⟩
  · intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · rcases List.mem_append.mp hr with hr | hr
      · exact hπmem r hr
      · exact hρmem r hr
    · have he : r = p+q := List.mem_singleton.mp hr
      rw [he]
      exact U.add_mem (hπmem p hp) (hρmem q hq)

theorem pc_mul_X {n : ℕ} (P : Set (MvPolynomial (Fin n) (ZMod 2)))
    (U : Submodule (ZMod 2) (MvPolynomial (Fin n) (ZMod 2)))
    {p : MvPolynomial (Fin n) (ZMod 2)} (hp : Derivable P U p) (v : Fin n)
    (hmem : ML (X v * p) ∈ U) : Derivable P U (ML (X v * p)) := by
  rcases hp with rfl | ⟨π,hπ,hπmem,hp⟩
  · simp only [mul_zero,map_zero]; exact pc_zero P U
  obtain ⟨i,hi,hpi⟩ := List.mem_iff_getElem.mp hp
  refine Or.inr ⟨π ++ [ML (X v * p)], ?_, ?_, by simp⟩
  · apply derivation_snoc _ _ hπ
    right; right
    exact ⟨i,hi,v,by rw [hpi]⟩
  · intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact hπmem q hq
    · rwa [List.mem_singleton.mp hq]

theorem pc_axiom {n : ℕ} (P : Set (MvPolynomial (Fin n) (ZMod 2)))
    (U : Submodule (ZMod 2) (MvPolynomial (Fin n) (ZMod 2)))
    (p : MvPolynomial (Fin n) (ZMod 2)) (hp : p ∈ P) (hmem : ML p ∈ U) :
    Derivable P U (ML p) := by
  refine Or.inr ⟨[ML p], ?_, by simpa using hmem, by simp⟩
  intro k hk
  have he : k = 0 := by simpa using hk
  subst k
  left
  exact ⟨p,hp,1,by simp⟩

end SemAC02.RelativePC
end

section
-- Inlined Solutions.RelativePCPolynomialMultiplication

open MvPolynomial AC02Frege
open AC02Frege.BooleanAlgebra AC02Frege.BooleanFlip

namespace SemAC02.RelativePC

theorem pc_polynomial_mul {n : ℕ} (P : Set (MvPolynomial (Fin n) (ZMod 2)))
    (U : Submodule (ZMod 2) (MvPolynomial (Fin n) (ZMod 2)))
    (u v : MvPolynomial (Fin n) (ZMod 2)) (hu : Derivable P U u) (huml : IsMultilinear u)
    (hmem : ∀ w : MvPolynomial (Fin n) (ZMod 2), w.totalDegree ≤ v.totalDegree → ML (u*w) ∈ U) :
    Derivable P U (ML (u*v)) := by
  classical
  induction v using MvPolynomial.induction_on'' with
  | C c =>
    have he : u * C c = c • u := by rw [smul_eq_C_mul, mul_comm]
    rw [he, map_smul, ml_of_multilinear u huml]
    exact pc_smul P U hu c
  | monomial_add s c p hnot hc ihp ihm =>
    have hdis : Disjoint (monomial s c).support p.support := by
      apply disjoint_support_monomial
      · exact hnot
      · exact hc
    have hsupp : (monomial s c + p).support = (monomial s c).support ∪ p.support := by
      exact Finsupp.support_add_eq hdis
    have hdm : (monomial s c).totalDegree ≤ (monomial s c + p).totalDegree := by
      apply totalDegree_le_of_support_subset
      rw [hsupp]
      exact Finset.subset_union_left
    have hdp : p.totalDegree ≤ (monomial s c + p).totalDegree := by
      apply totalDegree_le_of_support_subset
      rw [hsupp]
      exact Finset.subset_union_right
    rw [mul_add, map_add]
    exact pc_add P U (ihm (fun w hw => hmem w (hw.trans hdm)))
      (ihp (fun w hw => hmem w (hw.trans hdp)))
  | mul_X p i ih =>
    have hle : p.totalDegree ≤ (p * X i).totalDegree := by
      by_cases hp : p = 0
      · simp [hp]
      · rw [totalDegree_mul_of_isDomain hp (X_ne_zero i), totalDegree_X]
        omega
    have hi := ih (fun w hw => hmem w (hw.trans hle))
    have he : ML (u * (p * X i)) = ML (X i * ML (u*p)) := by
      rw [ml_mul_right]
      congr 1
      ring
    rw [he]
    apply pc_mul_X P U hi i
    rw [← he]
    exact hmem _ le_rfl

end SemAC02.RelativePC
end

section
-- Inlined Solutions.BooleanLocality

open Module MvPolynomial AC02Frege
open AC02Frege.BooleanAlgebra AC02Frege.BooleanBasis

namespace SemAC02.BooleanLocality

theorem multilinear_degree_le_card {V : Type} [Fintype V]
    (p : MvPolynomial V (ZMod 2)) (hp : IsMultilinear p) : p.totalDegree ≤ Fintype.card V := by
  classical
  apply Finset.sup_le
  intro s hs
  rw [squarefree_sum s (hp s hs)]
  exact Finset.card_le_univ _

noncomputable def extendAssignment {V : Type} (J : Finset V) (x : J → ZMod 2) : V → Bool := by
  classical
  exact fun i => if hi : i ∈ J then decide (x ⟨i, hi⟩ = 1) else false

theorem represents_local_function {V : Type} [Fintype V] (J : Finset V)
    (f : (V → Bool) → ZMod 2)
    (hf : ∀ z z' : V → Bool, (∀ i ∈ J, z i = z' i) → f z = f z') :
    ∃ r : MvPolynomial V (ZMod 2), r.totalDegree ≤ J.card ∧
      ∀ z : V → Bool, eval (toF2 z) r = f z := by
  classical
  let η : (J → ZMod 2) → ZMod 2 := fun x => f (extendAssignment J x)
  obtain ⟨p, hp⟩ := LinearMap.range_eq_top.mp (MvPolynomial.range_evalᵢ J (ZMod 2)) η
  let p' : restrictDegree J (ZMod 2) (Fintype.card (ZMod 2) - 1) := p
  have hml : IsMultilinear p'.1 := by
    apply (mem_restrictDegree J _ 1).mp
    simpa only [ZMod.card, Nat.reduceSub] using p'.2
  refine ⟨rename Subtype.val p'.1, ?_, ?_⟩
  · apply (totalDegree_rename_le _ _).trans
    simpa only [Fintype.card_coe] using multilinear_degree_le_card p'.1 hml
  · intro z
    rw [eval_rename]
    have he := congrFun hp (fun j : J => toF2 z j.1)
    change eval (fun j : J => toF2 z j.1) p'.1 = f (extendAssignment J (fun j : J => toF2 z j.1)) at he
    change eval (fun j : J => toF2 z j.1) p'.1 = f z
    rw [he]
    apply hf
    intro i hi
    simp only [extendAssignment, dif_pos hi]
    cases h : z i <;> simp [toF2, h]

end SemAC02.BooleanLocality
end

section
-- Inlined Solutions.BooleanRestrictions

open MvPolynomial AC02Frege
open AC02Frege.BooleanAlgebra AC02Frege.MajorityFoundation
open AC02Frege.BooleanBasis AC02Frege.BooleanFlip

namespace AC02Frege.BooleanRestrictions

theorem xMon_eval_point {V : Type*} [DecidableEq V] (S T : Finset V) :
    eval (fun i => if i ∈ T then (1 : ZMod 2) else 0) (xMon S) =
      if S ⊆ T then 1 else 0 := by
  classical
  rw [xMon_eval]
  by_cases h : S ⊆ T
  · rw [if_pos h]
    apply Finset.prod_eq_one
    intro i hi
    simp [h hi]
  · rw [if_neg h]
    obtain ⟨i, hi, hit⟩ := Finset.not_subset.mp h
    exact Finset.prod_eq_zero hi (by simp [hit])

theorem multilinear_exponent_ext {V : Type*} (s t : V →₀ ℕ)
    (hs : ∀ i, s i ≤ 1) (ht : ∀ i, t i ≤ 1) (hst : s.support = t.support) : s = t := by
  rw [squarefree_eq_indicator s hs, squarefree_eq_indicator t ht, hst]

theorem eq_zero_of_support_point_eval_zero {V : Type} [DecidableEq V]
    (p : MvPolynomial V (ZMod 2)) (hp : IsMultilinear p)
    (hv : ∀ s ∈ p.support,
      eval (fun i => if i ∈ s.support then (1 : ZMod 2) else 0) p = 0) : p = 0 := by
  classical
  by_contra hne
  obtain ⟨s, hs, hmin⟩ := p.support.exists_min_image
    (fun t => t.support.card) (support_nonempty.mpr hne)
  have heval : eval (fun i => if i ∈ s.support then (1 : ZMod 2) else 0) p = p.coeff s := by
    have hsum : eval (fun i => if i ∈ s.support then (1 : ZMod 2) else 0) p =
        ∑ t ∈ p.support, p.coeff t * (if t.support ⊆ s.support then (1 : ZMod 2) else 0) := by
      conv_lhs => rw [p.as_sum]
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro t ht
      rw [squarefree_monomial t _ (hp t ht), smul_eval, xMon_eval_point]
    rw [hsum, Finset.sum_eq_single s]
    · simp
    · intro t ht hts
      have hnot : ¬ t.support ⊆ s.support := by
        intro hsub
        have heq : t.support = s.support := Finset.eq_of_subset_of_card_le hsub (hmin t ht)
        exact hts (multilinear_exponent_ext t s (hp t ht) (hp s hs) heq)
      rw [if_neg hnot, mul_zero]
    · intro hnot
      exact False.elim (hnot hs)
  have hz := hv s hs
  rw [heval] at hz
  exact (mem_support_iff.mp hs) hz

theorem eval_injective_on_monomialSpan {V : Type} [DecidableEq V]
    (P : Finset V → Prop) (p : MvPolynomial V (ZMod 2))
    (hp : p ∈ monomialSpan P)
    (hv : ∀ S : Finset V, P S →
      eval (fun i => if i ∈ S then (1 : ZMod 2) else 0) p = 0) : p = 0 := by
  obtain ⟨hml, hP⟩ := (mem_monomialSpan_iff P p).mp hp
  exact eq_zero_of_support_point_eval_zero p hml (fun s hs => hv s.support (hP s hs))

theorem ml_vars_subset {V : Type} (p : MvPolynomial V (ZMod 2)) :
    (ML p).vars ⊆ p.vars := by
  classical
  intro i hi
  obtain ⟨s, hs, his⟩ := (mem_vars_iff_mem_support i).mp hi
  have hexp : ML p = ∑ t ∈ p.support, monomial (sqfree t) (p.coeff t) := by
    conv_lhs => rw [p.as_sum]
    simp only [map_sum, ml_monomial]
  rw [hexp] at hs
  obtain ⟨t, ht, hst⟩ := Finset.mem_biUnion.mp (support_sum hs)
  have heq := Finset.mem_singleton.mp (support_monomial_subset hst)
  subst s
  rw [sqfree_support] at his
  exact (mem_vars_iff_mem_support i).mpr ⟨t, ht, his⟩

theorem flip_vars_subset {V : Type} (p : MvPolynomial V (ZMod 2)) :
    (BooleanFlip.flip p).vars ⊆ p.vars := by
  classical
  intro i hi
  obtain ⟨j, hj, hij⟩ := Finset.mem_biUnion.mp
    (vars_bind₁ (fun j => 1 + X j) p (ml_vars_subset _ hi))
  have hsub : (1 + X j : MvPolynomial V (ZMod 2)).vars ⊆ {j} := by
    simpa using vars_add_subset (1 : MvPolynomial V (ZMod 2)) (X j)
  have heq := Finset.mem_singleton.mp (hsub hij)
  simpa only [heq] using hj

noncomputable def complementMap {V : Type} :
    MvPolynomial V (ZMod 2) →ₗ[ZMod 2] MvPolynomial V (ZMod 2) where
  toFun := BooleanFlip.flip
  map_add' p q := by simp only [BooleanFlip.flip, map_add]
  map_smul' c p := by simp only [BooleanFlip.flip, map_smul, RingHom.id_apply]

theorem flip_mem_monomialSpan {V : Type} (P : Finset V → Prop)
    (hP : ∀ S T, T ⊆ S → P S → P T)
    (p : MvPolynomial V (ZMod 2)) (hp : p ∈ monomialSpan P) :
    BooleanFlip.flip p ∈ monomialSpan P := by
  classical
  have hle : monomialSpan P ≤ (monomialSpan P).comap complementMap := by
    apply Submodule.span_le.mpr
    rintro q ⟨S, hS, rfl⟩
    apply (mem_monomialSpan_iff P _).mpr
    refine ⟨flip_multilinear _, ?_⟩
    intro s hs
    have hsub : s.support ⊆ S := by
      apply (support_subset_vars_of_mem_support hs).trans
      apply (flip_vars_subset _).trans
      rw [xMon_eq_monomial, vars_monomial one_ne_zero, indicator_support]
    exact hP S s.support hsub hS
  exact hle hp

theorem monomialSpan_span_range {V : Type} (P : Finset V → Prop) :
    monomialSpan P = Submodule.span (ZMod 2)
      (Set.range (fun S : {S : Finset V // P S} => xMon S.1)) := by
  apply congrArg (Submodule.span (ZMod 2))
  ext p
  constructor
  · rintro ⟨S, hS, rfl⟩
    exact ⟨⟨S, hS⟩, rfl⟩
  · rintro ⟨S, rfl⟩
    exact ⟨S.1, S.2, rfl⟩

end AC02Frege.BooleanRestrictions
end

section
-- Inlined Solutions.CommonBasis

open MvPolynomial AC02Frege
open AC02Frege.BooleanAlgebra AC02Frege.MajorityFoundation
open AC02Frege.BooleanBasis AC02Frege.BooleanFlip AC02Frege.BooleanRestrictions

namespace SemAC02.CommonBasis

def ones {m : ℕ} (X : Fin m → Bool) : Finset (Fin m) :=
  Finset.univ.filter (fun i => X i = true)

theorem indicator_ones {m : ℕ} (X : Fin m → Bool) : indicatorVec (ones X) = X := by
  funext i
  cases h : X i <;> simp [indicatorVec, ones, h]

theorem ones_indicator {m : ℕ} (S : Finset (Fin m)) : ones (indicatorVec S) = S := by
  ext i
  simp [indicatorVec, ones]

theorem toF2_indicator {m : ℕ} (S : Finset (Fin m)) :
    toF2 (indicatorVec S) = fun i => if i ∈ S then (1 : ZMod 2) else 0 := by
  funext i
  simp [toF2, indicatorVec]

theorem flip_eval_bool {m : ℕ} (p : MvPolynomial (Fin m) (ZMod 2)) (X : Fin m → Bool) :
    eval (toF2 X) (BooleanFlip.flip p) = eval (toF2 (fun i => !X i)) p := by
  rw [flip_eval]
  have heq : (fun i => 1 + toF2 X i) = toF2 (fun i => !X i) := by
    funext i
    cases h : X i <;> simp [toF2, h, CharTwo.add_self_eq_zero]
  rw [heq]

noncomputable def supportEquiv (m : ℕ) (g : (Fin m → Bool) → Bool) :
    {S : Finset (Fin m) // g (indicatorVec S) = true} ≃
      {X : Fin m → Bool // g X = true} where
  toFun S := ⟨indicatorVec S.1, S.2⟩
  invFun X := ⟨ones X.1, by simpa only [indicator_ones] using X.2⟩
  left_inv S := Subtype.ext (ones_indicator S.1)
  right_inv X := Subtype.ext (indicator_ones X.1)

def complementEquiv (m : ℕ) (g : (Fin m → Bool) → Bool) :
    {X : Fin m → Bool // g X = true} ≃
      {X : Fin m → Bool // g (fun i => !X i) = true} where
  toFun X := ⟨fun i => !X.1 i, by simpa only [Bool.not_not] using X.2⟩
  invFun X := ⟨fun i => !X.1 i, X.2⟩
  left_inv X := Subtype.ext (by funext i; simp)
  right_inv X := Subtype.ext (by funext i; simp)

noncomputable def restriction {m : ℕ} (Ω : Set (Fin m → Bool)) :
    MvPolynomial (Fin m) (ZMod 2) →ₗ[ZMod 2] (Ω → ZMod 2) where
  toFun p X := eval (toF2 X.1) p
  map_add' p q := by ext X; simp
  map_smul' c p := by ext X; simp

theorem downclosed {m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g) :
    ∀ S T : Finset (Fin m), T ⊆ S → g (indicatorVec S) = true →
      g (indicatorVec T) = true := by
  intro S T hTS hS
  have hle : indicatorVec T ≤ indicatorVec S := by
    intro i
    by_cases hi : i ∈ T
    · simp [indicatorVec, hi, hTS hi]
    · simp [indicatorVec, hi]
  have h := hg hle
  rw [hS] at h
  exact Bool.eq_true_of_true_le h

theorem restriction_zero (m : ℕ) (g : (Fin m → Bool) → Bool)
    (p : MvPolynomial (Fin m) (ZMod 2))
    (hp : p ∈ monomialSpan (fun S : Finset (Fin m) => g (indicatorVec S) = true))
    (hv : restriction {X : Fin m → Bool | g X = true} p = 0) : p = 0 := by
  apply eval_injective_on_monomialSpan _ p hp
  intro S hS
  have h := congrFun hv ⟨indicatorVec S, hS⟩
  change eval (toF2 (indicatorVec S)) p = 0 at h
  simpa only [toF2_indicator] using h

theorem restriction_complement_zero (m : ℕ) (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (p : MvPolynomial (Fin m) (ZMod 2))
    (hp : p ∈ monomialSpan (fun S : Finset (Fin m) => g (indicatorVec S) = true))
    (hv : restriction {X : Fin m → Bool | g (fun i => !X i) = true} p = 0) : p = 0 := by
  have hf : BooleanFlip.flip p ∈ monomialSpan (fun S : Finset (Fin m) => g (indicatorVec S) = true) :=
    flip_mem_monomialSpan _ (downclosed g hg) p hp
  have hvan : restriction {X : Fin m → Bool | g X = true} (BooleanFlip.flip p) = 0 := by
    funext X
    change eval (toF2 X.1) (BooleanFlip.flip p) = 0
    rw [flip_eval_bool]
    have h := congrFun hv ⟨fun i => !X.1 i, by simpa only [Set.mem_ofPred_eq, Bool.not_not] using X.2⟩
    exact h
  have hz := restriction_zero m g _ hf hvan
  have hml := ((mem_monomialSpan_iff _ _).mp hp).1
  calc
    p = BooleanFlip.flip (BooleanFlip.flip p) := (flip_involution p hml).symm
    _ = BooleanFlip.flip 0 := congrArg (BooleanFlip.flip (V := Fin m)) hz
    _ = 0 := by simp [BooleanFlip.flip]

theorem restriction_independent (m : ℕ) (P : Finset (Fin m) → Prop) (Ω : Set (Fin m → Bool))
    (hinj : ∀ p : MvPolynomial (Fin m) (ZMod 2), p ∈ monomialSpan P → restriction Ω p = 0 → p = 0) :
    LinearIndependent (ZMod 2) (fun S : {S : Finset (Fin m) // P S} => restriction Ω (xMon S.1)) := by
  apply (xMon_linearIndependent.comp Subtype.val Subtype.val_injective).map_injOn
  intro v hv w hw heq
  have hv' : v ∈ monomialSpan P := by rwa [monomialSpan_span_range]
  have hw' : w ∈ monomialSpan P := by rwa [monomialSpan_span_range]
  apply sub_eq_zero.mp
  apply hinj (v - w) (Submodule.sub_mem _ hv' hw')
  rw [map_sub, heq, sub_self]

end SemAC02.CommonBasis
end

section
-- Inlined Theorems.Thm_SemAC02_lemma_8_5_common_basis


open MvPolynomial AC02Frege SemAC02 SemAC02.CommonBasis


/-- **Lemma 8.5 (Common monomial basis)** (Alekseev–Gryaznov–Itsykson–Pitassi–Robere–Tzameret, *Hard Instances for Strong Semantic Proof
Systems*, manuscript (STOC 2027 submission), Lemma 8.5, p.64): with
`L = {S ⊆ [m] : g₀(1_S) = 1}`, `Ω₀ = {X : g₀(X) = 1}` and `Ω₁ = {X : g₁(X) = 1}`,
`g₁(X) = g₀(X̄)`, the monomials `x_S = ∏_{j∈S} x_j`, `S ∈ L`, give a basis of both `𝔽₂^{Ω₀}`
and `𝔽₂^{Ω₁}`.

**Formalization Note** Stated for every antitone Boolean function `g₀` on `{0,1}^m` (the
paper's `g₀ = g` from §8.1 is one). "Basis" is linear independence of the restrictions of the
`x_S` to `Ω_b` together with spanning all functions `Ω_b → 𝔽₂`. -/
theorem SemAC02.lemma_8_5_common_basis {m : ℕ} (g₀ : (Fin m → Bool) → Bool) (hg₀ : Antitone g₀) :
    (LinearIndependent (ZMod 2)
        (fun S : {S : Finset (Fin m) // g₀ (indicatorVec S) = true} =>
          fun X : {X : Fin m → Bool // g₀ X = true} =>
            MvPolynomial.eval (toF2 X.1) (AC02Frege.xMon S.1)) ∧
      Submodule.span (ZMod 2) (Set.range
        (fun S : {S : Finset (Fin m) // g₀ (indicatorVec S) = true} =>
          fun X : {X : Fin m → Bool // g₀ X = true} =>
            MvPolynomial.eval (toF2 X.1) (AC02Frege.xMon S.1))) = ⊤) ∧
    (LinearIndependent (ZMod 2)
        (fun S : {S : Finset (Fin m) // g₀ (indicatorVec S) = true} =>
          fun X : {X : Fin m → Bool // g₀ (fun j => !X j) = true} =>
            MvPolynomial.eval (toF2 X.1) (AC02Frege.xMon S.1)) ∧
      Submodule.span (ZMod 2) (Set.range
        (fun S : {S : Finset (Fin m) // g₀ (indicatorVec S) = true} =>
          fun X : {X : Fin m → Bool // g₀ (fun j => !X j) = true} =>
            MvPolynomial.eval (toF2 X.1) (AC02Frege.xMon S.1))) = ⊤) := by
  classical
  let P : Finset (Fin m) → Prop := fun S => g₀ (indicatorVec S) = true
  let Ω₀ : Set (Fin m → Bool) := {X | g₀ X = true}
  let Ω₁ : Set (Fin m → Bool) := {X | g₀ (fun i => !X i) = true}
  have hli0 : LinearIndependent (ZMod 2)
      (fun S : {S : Finset (Fin m) // P S} => restriction Ω₀ (xMon S.1)) :=
    restriction_independent m P Ω₀ (restriction_zero m g₀)
  have hli1 : LinearIndependent (ZMod 2)
      (fun S : {S : Finset (Fin m) // P S} => restriction Ω₁ (xMon S.1)) :=
    restriction_independent m P Ω₁ (restriction_complement_zero m g₀ hg₀)
  have hspan0 := hli0.span_eq_top_of_card_eq_finrank' (by
    rw [Module.finrank_fintype_fun_eq_card]
    exact Fintype.card_congr (supportEquiv m g₀))
  have hspan1 := hli1.span_eq_top_of_card_eq_finrank' (by
    rw [Module.finrank_fintype_fun_eq_card]
    exact Fintype.card_congr ((supportEquiv m g₀).trans (complementEquiv m g₀)))
  exact ⟨⟨hli0, hspan0⟩, ⟨hli1, hspan1⟩⟩

end

section
-- Inlined Solutions.ProductFunctionBasis

open Module
open scoped TensorProduct

namespace ProofComplexity

open PiTensorProduct

noncomputable def functionTensorEquiv
    {R ι : Type*} [CommSemiring R] [Fintype ι]
    (X : ι → Type*) [∀ i, Fintype (X i)] :
    (⨂[R] i, (X i → R)) ≃ₗ[R] (((i : ι) → X i) → R) := by
  classical
  exact (PiTensorProduct.congr (fun i => (Finsupp.linearEquivFunOnFinite R R (X i)).symm)) ≪≫ₗ
    (PiTensorProduct.ofFinsuppEquiv' (R := R) (κ := X)) ≪≫ₗ
    Finsupp.linearEquivFunOnFinite R R ((i : ι) → X i)

@[simp] theorem functionTensorEquiv_tprod
    {R ι : Type*} [CommSemiring R] [Fintype ι]
    (X : ι → Type*) [∀ i, Fintype (X i)] (f : (i : ι) → X i → R) (x : (i : ι) → X i) :
    functionTensorEquiv X (⨂ₜ[R] i, f i) x = ∏ i, f i (x i) := by
  classical
  simp [functionTensorEquiv]

noncomputable def productFunctionBasis
    {R ι : Type*} [CommSemiring R] [Fintype ι]
    {X : ι → Type*} [∀ i, Fintype (X i)] {κ : ι → Type*}
    (b : (i : ι) → Basis (κ i) R (X i → R)) :
    Basis ((i : ι) → κ i) R (((i : ι) → X i) → R) :=
  (Basis.piTensorProduct b).map (functionTensorEquiv X)

@[simp] theorem productFunctionBasis_apply
    {R ι : Type*} [CommSemiring R] [Fintype ι]
    {X : ι → Type*} [∀ i, Fintype (X i)] {κ : ι → Type*}
    (b : (i : ι) → Basis (κ i) R (X i → R)) (k : (i : ι) → κ i) (x : (i : ι) → X i) :
    productFunctionBasis b k x = ∏ i, b i (k i) (x i) := by
  classical
  simp [productFunctionBasis]

theorem productFunctionBasis_repr
    {R ι : Type*} [CommSemiring R] [Fintype ι]
    {X : ι → Type*} [∀ i, Fintype (X i)] {κ : ι → Type*}
    (b : (i : ι) → Basis (κ i) R (X i → R)) (f : (i : ι) → X i → R)
    (k : (i : ι) → κ i) :
    (productFunctionBasis b).repr (fun x => ∏ i, f i (x i)) k =
      ∏ i, (b i).repr (f i) (k i) := by
  classical
  have hfun : (fun x => ∏ i, f i (x i)) = functionTensorEquiv X (⨂ₜ[R] i, f i) := by
    funext x
    exact (functionTensorEquiv_tprod X f x).symm
  rw [hfun]
  change (Basis.piTensorProduct b).repr
    ((functionTensorEquiv X).symm (functionTensorEquiv X (⨂ₜ[R] i, f i))) k = _
  rw [LinearEquiv.symm_apply_apply]
  exact Basis.piTensorProduct_repr_tprod_apply b f k

end ProofComplexity
end

section
-- Inlined Solutions.SemanticFibreBasis

open Module MvPolynomial AC02Frege
open AC02Frege.BooleanAlgebra

namespace SemAC02.FibreBasis

abbrev BlockIndex {m : ℕ} (g : (Fin m → Bool) → Bool) :=
  {S : Finset (Fin m) // g (indicatorVec S) = true}

abbrev BlockFibre {m : ℕ} (g : (Fin m → Bool) → Bool) (b : Bool) :=
  {X : Fin m → Bool // if b then g (fun j => !X j) = true else g X = true}

noncomputable def blockBasis {m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g) (b : Bool) :
    Basis (BlockIndex g) (ZMod 2) (BlockFibre g b → ZMod 2) := by
  have h := lemma_8_5_common_basis g hg
  cases b with
  | false => exact Basis.mk h.1.1 h.1.2.ge
  | true => exact Basis.mk h.2.1 h.2.2.ge

@[simp] theorem blockBasis_apply {m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (b : Bool) (S : BlockIndex g) (X : BlockFibre g b) :
    blockBasis g hg b S X = eval (toF2 X.1) (xMon S.1) := by
  cases b <;> simp [blockBasis, Basis.mk_apply]

abbrev GlobalIndex {m : ℕ} (g : (Fin m → Bool) → Bool) (n : ℕ) :=
  {A : Finset (Fin n × Fin m) // IsLnSupport g A}

def assemble {n m : ℕ} {g : (Fin m → Bool) → Bool} (S : Fin n → BlockIndex g) :
    Finset (Fin n × Fin m) := Finset.univ.filter (fun v => v.2 ∈ (S v.1).1)

@[simp] theorem section_assemble {n m : ℕ} {g : (Fin m → Bool) → Bool}
    (S : Fin n → BlockIndex g) (i : Fin n) : blockSection (assemble S) i = (S i).1 := by
  ext j
  simp [blockSection, assemble]

def sections {n m : ℕ} {g : (Fin m → Bool) → Bool} (A : GlobalIndex g n) (i : Fin n) :
    BlockIndex g := ⟨blockSection A.1 i, A.2 i⟩

@[simp] theorem assemble_sections {n m : ℕ} {g : (Fin m → Bool) → Bool}
    (A : GlobalIndex g n) : assemble (sections A) = A.1 := by
  ext v
  simp [assemble, sections, blockSection]

def indexEquiv (n : ℕ) {m : ℕ} (g : (Fin m → Bool) → Bool) :
    (Fin n → BlockIndex g) ≃ GlobalIndex g n where
  toFun S := ⟨assemble S, by
    intro i
    rw [section_assemble]
    exact (S i).2⟩
  invFun A := sections A
  left_inv S := by funext i; apply Subtype.ext; exact section_assemble S i
  right_inv A := Subtype.ext (assemble_sections A)

abbrev Fibre {n m : ℕ} (g : (Fin m → Bool) → Bool) (z : Fin n → Bool) :=
  {X : Fin n × Fin m → Bool // InFiber g z X}

def curryEquiv {n m : ℕ} (g : (Fin m → Bool) → Bool) (z : Fin n → Bool) :
    Fibre g z ≃ ((i : Fin n) → BlockFibre g (z i)) where
  toFun X i := ⟨fun j => X.1 (i, j), X.2 i⟩
  invFun X := ⟨fun v => (X v.1).1 v.2, fun i => (X i).2⟩
  left_inv X := Subtype.ext (by funext v; rfl)
  right_inv X := by funext i; apply Subtype.ext; rfl

noncomputable def fibreBasis {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (z : Fin n → Bool) : Basis (GlobalIndex g n) (ZMod 2) (Fibre g z → ZMod 2) :=
  ((ProofComplexity.productFunctionBasis (fun i : Fin n => blockBasis g hg (z i))).reindex
    (indexEquiv n g)).map (LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) (curryEquiv g z))

theorem xMon_eval_blocks {n m : ℕ} (A : Finset (Fin n × Fin m))
    (X : Fin n × Fin m → Bool) : eval (toF2 X) (xMon A) =
      ∏ i : Fin n, eval (toF2 (fun j => X (i, j))) (xMon (blockSection A i)) := by
  classical
  simp only [xMon_eval, blockSection, Finset.prod_filter, toF2]
  rw [← Finset.prod_product']
  simp only [Finset.univ_product_univ]
  rw [← Finset.prod_filter]
  simp

@[simp] theorem fibreBasis_apply {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (z : Fin n → Bool) (A : GlobalIndex g n) (X : Fibre g z) :
    fibreBasis g hg z A X = eval (toF2 X.1) (xMon A.1) := by
  classical
  rw [fibreBasis, Basis.map_apply, Basis.reindex_apply]
  change ProofComplexity.productFunctionBasis (fun i : Fin n => blockBasis g hg (z i))
    (sections A) (curryEquiv g z X) = _
  rw [ProofComplexity.productFunctionBasis_apply, xMon_eval_blocks]
  apply Finset.prod_congr rfl
  intro i _
  rw [blockBasis_apply]
  rfl

end SemAC02.FibreBasis
end

section
-- Inlined Solutions.SemanticFibreCoordinates

open Module MvPolynomial AC02Frege
open SemAC02 SemAC02.FibreBasis

namespace SemAC02.FibreCoordinates

noncomputable def coordinates {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (p : MvPolynomial (Fin n × Fin m) (ZMod 2)) (S : GlobalIndex g n) (z : Fin n → Bool) : ZMod 2 :=
  (fibreBasis g hg z).equivFun (fun X => eval (toF2 X.1) p) S

theorem coordinates_expansion {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (p : MvPolynomial (Fin n × Fin m) (ZMod 2)) (z : Fin n → Bool) (X : Fibre g z) :
    eval (toF2 X.1) p = ∑ S : GlobalIndex g n, coordinates g hg p S z *
      eval (toF2 X.1) (xMon S.1) := by
  classical
  have h := congrFun ((fibreBasis g hg z).equivFun.symm_apply_apply (fun X => eval (toF2 X.1) p)) X
  rw [Basis.equivFun_symm_apply] at h
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, fibreBasis_apply, coordinates] using h.symm

theorem coordinates_unique {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (p : MvPolynomial (Fin n × Fin m) (ZMod 2))
    (c : GlobalIndex g n → (Fin n → Bool) → ZMod 2)
    (hc : ∀ (z : Fin n → Bool) (X : Fin n × Fin m → Bool), InFiber g z X →
      eval (toF2 X) p = ∑ S, c S z * eval (toF2 X) (xMon S.1)) :
    ∀ S z, c S z = coordinates g hg p S z := by
  classical
  intro S z
  have he : (fun X : Fibre g z => eval (toF2 X.1) p) =
      (fibreBasis g hg z).equivFun.symm (fun S => c S z) := by
    rw [Basis.equivFun_symm_apply]
    funext X
    rw [hc z X.1 X.2]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, fibreBasis_apply]
  have h := congrArg (fibreBasis g hg z).equivFun he
  rw [LinearEquiv.apply_symm_apply] at h
  exact (congrFun h S).symm

theorem coordinates_add {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (p q : MvPolynomial (Fin n × Fin m) (ZMod 2)) (S : GlobalIndex g n) (z : Fin n → Bool) :
    coordinates g hg (p + q) S z = coordinates g hg p S z + coordinates g hg q S z := by
  have he : (fun X : Fibre g z => eval (toF2 X.1) (p + q)) =
      (fun X => eval (toF2 X.1) p) + (fun X => eval (toF2 X.1) q) := by
    funext X
    exact map_add _ _ _
  unfold coordinates
  rw [he, map_add]
  rfl

theorem coordinates_smul {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (a : ZMod 2) (p : MvPolynomial (Fin n × Fin m) (ZMod 2))
    (S : GlobalIndex g n) (z : Fin n → Bool) :
    coordinates g hg (a • p) S z = a * coordinates g hg p S z := by
  have he : (fun X : Fibre g z => eval (toF2 X.1) (a • p)) =
      a • (fun X => eval (toF2 X.1) p) := by
    funext X
    simp only [smul_eval, Pi.smul_apply, smul_eq_mul]
  unfold coordinates
  rw [he, map_smul]
  rfl

end SemAC02.FibreCoordinates
end

section
-- Inlined Solutions.SemanticProductCoordinates

open Module MvPolynomial AC02Frege
open AC02Frege.BooleanAlgebra
open SemAC02 SemAC02.FibreBasis SemAC02.FibreCoordinates

namespace SemAC02.ProductCoordinates

noncomputable def blockCoefficient {m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (S T : BlockIndex g) (U : Finset (Fin m)) (b : Bool) : ZMod 2 :=
  (blockBasis g hg b).repr (fun X => eval (toF2 X.1) (xMon T.1 * xMon U)) S

theorem blockCoefficient_empty {m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (S T : BlockIndex g) (b : Bool) :
    blockCoefficient g hg S T ∅ b = if S = T then 1 else 0 := by
  classical
  have he : (fun X : BlockFibre g b => eval (toF2 X.1) (xMon T.1 * xMon ∅)) =
      blockBasis g hg b T := by
    funext X
    simp only [xMon, Finset.prod_empty, mul_one, blockBasis_apply]
  unfold blockCoefficient
  rw [he, Basis.repr_self]
  by_cases hST : S = T
  · subst S
    rw [Finsupp.single_eq_same, if_pos rfl]
  · rw [Finsupp.single_eq_of_ne hST, if_neg hST]

theorem coordinates_product {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (S T : GlobalIndex g n) (U : Finset (Fin n × Fin m)) (z : Fin n → Bool) :
    coordinates g hg (xMon T.1 * xMon U) S z =
      ∏ i : Fin n, blockCoefficient g hg (sections S i) (sections T i) (blockSection U i) (z i) := by
  have he : (fun X : Fibre g z => eval (toF2 X.1) (xMon T.1 * xMon U)) =
      (LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) (curryEquiv g z))
        (fun X : (i : Fin n) → BlockFibre g (z i) =>
          ∏ i : Fin n, eval (toF2 (X i).1) (xMon (blockSection T.1 i) * xMon (blockSection U i))) := by
    funext X
    change eval (toF2 X.1) (xMon T.1 * xMon U) =
      ∏ i : Fin n, eval (toF2 (fun j => X.1 (i, j)))
        (xMon (blockSection T.1 i) * xMon (blockSection U i))
    simp only [map_mul, xMon_eval_blocks, Finset.prod_mul_distrib]
  unfold coordinates
  rw [he]
  change (ProofComplexity.productFunctionBasis (fun i : Fin n => blockBasis g hg (z i))).repr
    ((LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) (curryEquiv g z)).symm
      ((LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) (curryEquiv g z)) _)) ((indexEquiv n g).symm S) = _
  rw [LinearEquiv.symm_apply_apply]
  exact ProofComplexity.productFunctionBasis_repr (fun i : Fin n => blockBasis g hg (z i))
    (fun i X => eval (toF2 X.1) (xMon (blockSection T.1 i) * xMon (blockSection U i))) (sections S)

theorem blockSection_empty {n m : ℕ} (U : Finset (Fin n × Fin m)) (i : Fin n)
    (hi : i ∉ U.image Prod.fst) : blockSection U i = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro j hj
  apply hi
  have hij : (i, j) ∈ U := (Finset.mem_filter.mp hj).2
  exact Finset.mem_image.mpr ⟨(i, j), hij, rfl⟩

theorem coordinates_product_local {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (S T : GlobalIndex g n) (U : Finset (Fin n × Fin m))
    (z z' : Fin n → Bool) (hz : ∀ i ∈ U.image Prod.fst, z i = z' i) :
    coordinates g hg (xMon T.1 * xMon U) S z = coordinates g hg (xMon T.1 * xMon U) S z' := by
  classical
  rw [coordinates_product, coordinates_product]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i ∈ U.image Prod.fst
  · rw [hz i hi]
  · rw [blockSection_empty U i hi, blockCoefficient_empty, blockCoefficient_empty]

end SemAC02.ProductCoordinates
end

section
-- Inlined Solutions.SemanticCoordinateSpaces

open Module MvPolynomial AC02Frege
open SemAC02 SemAC02.FibreBasis SemAC02.FibreCoordinates

namespace SemAC02.CoordinateSpaces

noncomputable def booleanEvaluation (n : ℕ) :
    MvPolynomial (Fin n) (ZMod 2) →ₗ[ZMod 2] ((Fin n → Bool) → ZMod 2) where
  toFun p z := eval (toF2 z) p
  map_add' p q := by funext z; exact map_add _ _ _
  map_smul' a p := by funext z; simp only [smul_eval, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]

noncomputable def degreeSpace (n D : ℕ) :
    Submodule (ZMod 2) ((Fin n → Bool) → ZMod 2) :=
  (restrictTotalDegree (Fin n) (ZMod 2) D).map (booleanEvaluation n)

theorem mem_degreeSpace {n D : ℕ} (u : (Fin n → Bool) → ZMod 2) :
    u ∈ degreeSpace n D ↔ ∃ r : MvPolynomial (Fin n) (ZMod 2), r.totalDegree ≤ D ∧
      ∀ z : Fin n → Bool, eval (toF2 z) r = u z := by
  constructor
  · rintro ⟨r, hr, heq⟩
    exact ⟨r, (mem_restrictTotalDegree (Fin n) D r).mp hr, fun z => congrFun heq z⟩
  · rintro ⟨r, hr, heq⟩
    exact ⟨r, (mem_restrictTotalDegree (Fin n) D r).mpr hr, funext heq⟩

def localSpace {n : ℕ} (J : Finset (Fin n)) :
    Submodule (ZMod 2) ((Fin n → Bool) → ZMod 2) where
  carrier := {u | ∀ z z', (∀ i ∈ J, z i = z' i) → u z = u z'}
  zero_mem' := by intro z z' hz; rfl
  add_mem' := by intro f h hf hh z z' hz; exact congrArg₂ (· + ·) (hf z z' hz) (hh z z' hz)
  smul_mem' := by intro a f hf z z' hz; exact congrArg (fun x => a • x) (hf z z' hz)

theorem localSpace_mono {n : ℕ} {I J : Finset (Fin n)} (hIJ : I ⊆ J) :
    localSpace I ≤ localSpace J := by
  intro f hf z z' hz
  exact hf z z' (fun i hi => hz i (hIJ hi))

noncomputable def coordinateMap {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (S : GlobalIndex g n) :
    MvPolynomial (Fin n × Fin m) (ZMod 2) →ₗ[ZMod 2] ((Fin n → Bool) → ZMod 2) where
  toFun p := coordinates g hg p S
  map_add' p q := by funext z; exact coordinates_add g hg p q S z
  map_smul' a p := by
    funext z
    simpa only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply] using coordinates_smul g hg a p S z

end SemAC02.CoordinateSpaces
end

section
-- Inlined Solutions.BooleanFunctionPolynomials

open MvPolynomial AC02Frege
open AC02Frege.BooleanAlgebra AC02Frege.BooleanFlip

namespace SemAC02.BooleanFunctionPolynomials

theorem toF2_surjective {V : Type} (x : V → ZMod 2) : ∃ X : V → Bool, toF2 X = x := by
  refine ⟨fun v => decide (x v = 1), ?_⟩
  funext v
  have h : x v = 0 ∨ x v = 1 := by
    have h01 := AC02Frege.MajorityFoundation.eq_zero_or_one (x v)
    exact h01
  rcases h with h | h <;> simp [toF2, h]

theorem multilinear_ext_bool {V : Type} [Finite V] {p q : MvPolynomial V (ZMod 2)}
    (hp : IsMultilinear p) (hq : IsMultilinear q)
    (he : ∀ X : V → Bool, eval (toF2 X) p = eval (toF2 X) q) : p = q := by
  apply multilinear_ext hp hq
  intro x
  obtain ⟨X, rfl⟩ := toF2_surjective x
  exact he X

theorem exists_polynomial (n : ℕ) (u : (Fin n → Bool) → ZMod 2) :
    ∃ r : MvPolynomial (Fin n) (ZMod 2),
      ∀ z : Fin n → Bool, eval (toF2 z) r = u z := by
  classical
  obtain ⟨r, _, hr⟩ := BooleanLocality.represents_local_function Finset.univ u
    (fun z z' h => congrArg u (funext (fun i => h i (Finset.mem_univ i))))
  exact ⟨r, hr⟩

noncomputable def polynomial {n : ℕ} (u : (Fin n → Bool) → ZMod 2) :
    MvPolynomial (Fin n) (ZMod 2) := ML (Classical.choose (exists_polynomial n u))

theorem polynomial_multilinear {n : ℕ} (u : (Fin n → Bool) → ZMod 2) :
    IsMultilinear (polynomial u) := ml_multilinear _

@[simp] theorem eval_polynomial {n : ℕ} (u : (Fin n → Bool) → ZMod 2) (z : Fin n → Bool) :
    eval (toF2 z) (polynomial u) = u z := by
  rw [polynomial, eval_ml]
  exact Classical.choose_spec (exists_polynomial n u) z

theorem polynomial_eq {n : ℕ} (u : (Fin n → Bool) → ZMod 2)
    (r : MvPolynomial (Fin n) (ZMod 2))
    (hr : ∀ z : Fin n → Bool, eval (toF2 z) r = u z) : polynomial u = ML r := by
  apply multilinear_ext_bool
    (polynomial_multilinear u) (ml_multilinear r)
  intro z
  rw [eval_polynomial, eval_ml, hr]

noncomputable def polynomialMap (n : ℕ) :
    ((Fin n → Bool) → ZMod 2) →ₗ[ZMod 2] MvPolynomial (Fin n) (ZMod 2) where
  toFun := polynomial
  map_add' u v := by
    refine multilinear_ext_bool (polynomial_multilinear _) ?_ ?_
    · exact (mem_restrictDegree (Fin n) _ 1).mp
        (Submodule.add_mem _ ((mem_restrictDegree (Fin n) _ 1).mpr (polynomial_multilinear u))
          ((mem_restrictDegree (Fin n) _ 1).mpr (polynomial_multilinear v)))
    · intro z
      simp only [eval_polynomial, map_add, Pi.add_apply]
  map_smul' a u := by
    refine multilinear_ext_bool (polynomial_multilinear _) ?_ ?_
    · exact (mem_restrictDegree (Fin n) _ 1).mp
        (Submodule.smul_mem _ a ((mem_restrictDegree (Fin n) _ 1).mpr (polynomial_multilinear u)))
    · intro z
      simp only [eval_polynomial, smul_eval, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]

theorem polynomial_degree {n D : ℕ} (u : (Fin n → Bool) → ZMod 2)
    (hu : u ∈ SemAC02.CoordinateSpaces.degreeSpace n D) : (polynomial u).totalDegree ≤ D := by
  obtain ⟨r, hr, he⟩ := SemAC02.CoordinateSpaces.mem_degreeSpace u |>.mp hu
  rw [polynomial_eq u r he]
  exact (ml_totalDegree_le r).trans hr

end SemAC02.BooleanFunctionPolynomials
end

section
-- Inlined Solutions.SemanticMonomialLocality

open Module MvPolynomial AC02Frege
open AC02Frege.BooleanAlgebra AC02Frege.BooleanBasis
open SemAC02 SemAC02.FibreBasis SemAC02.FibreCoordinates
open SemAC02.ProductCoordinates SemAC02.CoordinateSpaces SemAC02.BooleanLocality

namespace SemAC02.MonomialLocality

theorem eval_monomial_squarefree {V : Type} (s : V →₀ ℕ) (a : ZMod 2) (x : V → ZMod 2) :
    eval x (monomial s a) = a * eval x (xMon s.support) := by
  calc
    eval x (monomial s a) = eval x (ML (monomial s a)) := (eval_ml _ _).symm
    _ = a * eval x (xMon s.support) := by
      rw [ml_monomial, squarefree_monomial (sqfree s) a (fun i => by simp [sqfree, Finsupp.mapRange_apply]),
        sqfree_support, smul_eval]

theorem coordinate_monomial {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (S T : GlobalIndex g n) (s : (Fin n × Fin m) →₀ ℕ) (a : ZMod 2) :
    coordinateMap g hg S (xMon T.1 * monomial s a) =
      a • coordinateMap g hg S (xMon T.1 * xMon s.support) := by
  funext z
  have he : (fun X : Fibre g z => eval (toF2 X.1) (xMon T.1 * monomial s a)) =
      a • (fun X : Fibre g z => eval (toF2 X.1) (xMon T.1 * xMon s.support)) := by
    funext X
    simp only [map_mul, eval_monomial_squarefree, Pi.smul_apply, smul_eq_mul]
    ring
  change (fibreBasis g hg z).equivFun (fun X => eval (toF2 X.1) (xMon T.1 * monomial s a)) S = _
  rw [he, map_smul]
  rfl

theorem support_card_le_sum {V : Type} (s : V →₀ ℕ) : s.support.card ≤ s.sum (fun _ e => e) := by
  classical
  change s.support.card ≤ ∑ i ∈ s.support, s i
  calc
    s.support.card = ∑ _i ∈ s.support, 1 := by simp
    _ ≤ ∑ i ∈ s.support, s i := Finset.sum_le_sum (fun i hi =>
      Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi))

theorem degreeSpace_mono {n D E : ℕ} (hDE : D ≤ E) : degreeSpace n D ≤ degreeSpace n E := by
  intro u hu
  obtain ⟨r, hr, he⟩ := (mem_degreeSpace u).mp hu
  exact (mem_degreeSpace u).mpr ⟨r, hr.trans hDE, he⟩

theorem squarefree_local {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (S T : GlobalIndex g n) (U : Finset (Fin n × Fin m)) :
    coordinateMap g hg S (xMon T.1 * xMon U) ∈ localSpace (U.image Prod.fst) := by
  exact coordinates_product_local g hg S T U

theorem squarefree_degree {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (S T : GlobalIndex g n) (U : Finset (Fin n × Fin m)) :
    coordinateMap g hg S (xMon T.1 * xMon U) ∈ degreeSpace n U.card := by
  have hl := squarefree_local g hg S T U
  obtain ⟨r, hr, he⟩ := represents_local_function (U.image Prod.fst)
    (coordinateMap g hg S (xMon T.1 * xMon U)) hl
  exact (mem_degreeSpace _).mpr ⟨r, hr.trans (Finset.card_image_le), he⟩

theorem monomial_local {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (S T : GlobalIndex g n) (s : (Fin n × Fin m) →₀ ℕ) (a : ZMod 2) :
    coordinateMap g hg S (xMon T.1 * monomial s a) ∈ localSpace (s.support.image Prod.fst) := by
  rw [coordinate_monomial]
  exact Submodule.smul_mem _ a (squarefree_local g hg S T s.support)

theorem monomial_degree {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (S T : GlobalIndex g n) (s : (Fin n × Fin m) →₀ ℕ) (a : ZMod 2) :
    coordinateMap g hg S (xMon T.1 * monomial s a) ∈ degreeSpace n (s.sum (fun _ e => e)) := by
  rw [coordinate_monomial]
  apply Submodule.smul_mem
  exact degreeSpace_mono (support_card_le_sum s) (squarefree_degree g hg S T s.support)

end SemAC02.MonomialLocality
end

section
-- Inlined Solutions.SemanticCoefficientControl

open Module MvPolynomial AC02Frege
open SemAC02 SemAC02.FibreBasis SemAC02.FibreCoordinates
open SemAC02.CoordinateSpaces SemAC02.MonomialLocality

namespace SemAC02.CoefficientControl

theorem coordinate_polynomial_sum {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (S : GlobalIndex g n) (f p : MvPolynomial (Fin n × Fin m) (ZMod 2)) :
    coordinateMap g hg S (f * p) = ∑ s ∈ p.support,
      coordinateMap g hg S (f * monomial s (p.coeff s)) := by
  classical
  conv_lhs => rw [p.as_sum]
  rw [Finset.mul_sum, map_sum]

theorem basis_polynomial_degree {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (S T : GlobalIndex g n) (p : MvPolynomial (Fin n × Fin m) (ZMod 2)) :
    coordinateMap g hg S (xMon T.1 * p) ∈ degreeSpace n p.totalDegree := by
  classical
  rw [coordinate_polynomial_sum]
  apply Submodule.sum_mem
  intro s hs
  exact degreeSpace_mono (le_totalDegree hs) (monomial_degree g hg S T s (p.coeff s))

theorem basis_polynomial_local {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (S T : GlobalIndex g n) (p : MvPolynomial (Fin n × Fin m) (ZMod 2))
    (J : Finset (Fin n)) (hp : ∀ v ∈ p.vars, v.1 ∈ J) :
    coordinateMap g hg S (xMon T.1 * p) ∈ localSpace J := by
  classical
  rw [coordinate_polynomial_sum]
  apply Submodule.sum_mem
  intro s hs
  have hsub : s.support.image Prod.fst ⊆ J := by
    intro i hi
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hi
    exact hp v ((support_subset_vars_of_mem_support hs) hv)
  exact localSpace_mono hsub (monomial_local g hg S T s (p.coeff s))

theorem coefficient_degree {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (f : MvPolynomial (Fin n × Fin m) (ZMod 2)) (hf : f ∈ lnSpan g n)
    (p : MvPolynomial (Fin n × Fin m) (ZMod 2)) (S : GlobalIndex g n) :
    coordinateMap g hg S (f * p) ∈ degreeSpace n p.totalDegree := by
  let L : MvPolynomial (Fin n × Fin m) (ZMod 2) →ₗ[ZMod 2] ((Fin n → Bool) → ZMod 2) :=
    (coordinateMap g hg S).comp (LinearMap.mulRight (ZMod 2) p)
  have hle : lnSpan g n ≤ (degreeSpace n p.totalDegree).comap L := by
    apply Submodule.span_le.mpr
    rintro q ⟨T, hT, rfl⟩
    exact basis_polynomial_degree g hg S ⟨T, hT⟩ p
  exact hle hf

theorem coefficient_locality {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (f : MvPolynomial (Fin n × Fin m) (ZMod 2)) (hf : f ∈ lnSpan g n)
    (p : MvPolynomial (Fin n × Fin m) (ZMod 2))
    (J : Finset (Fin n)) (hp : ∀ v ∈ p.vars, v.1 ∈ J) (S : GlobalIndex g n) :
    coordinateMap g hg S (f * p) ∈ localSpace J := by
  let L : MvPolynomial (Fin n × Fin m) (ZMod 2) →ₗ[ZMod 2] ((Fin n → Bool) → ZMod 2) :=
    (coordinateMap g hg S).comp (LinearMap.mulRight (ZMod 2) p)
  have hle : lnSpan g n ≤ (localSpace J).comap L := by
    apply Submodule.span_le.mpr
    rintro q ⟨T, hT, rfl⟩
    exact basis_polynomial_local g hg S ⟨T, hT⟩ p J hp
  exact hle hf

end SemAC02.CoefficientControl
end

section
-- Inlined Solutions.SemanticCoefficientPolynomials

open Module MvPolynomial AC02Frege
open AC02Frege.BooleanAlgebra AC02Frege.BooleanFlip
open SemAC02.FibreBasis SemAC02.FibreCoordinates SemAC02.CoordinateSpaces
open SemAC02.BooleanFunctionPolynomials SemAC02.CoefficientControl

namespace SemAC02.CoefficientPolynomials

noncomputable def coefficientMap {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (S : GlobalIndex g n) :
    MvPolynomial (Fin n × Fin m) (ZMod 2) →ₗ[ZMod 2] MvPolynomial (Fin n) (ZMod 2) :=
  (polynomialMap n).comp (coordinateMap g hg S)

theorem coefficient_multilinear {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (S : GlobalIndex g n) (p : MvPolynomial (Fin n × Fin m) (ZMod 2)) :
    IsMultilinear (coefficientMap g hg S p) := polynomial_multilinear _

@[simp] theorem eval_coefficient {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (S : GlobalIndex g n) (p : MvPolynomial (Fin n × Fin m) (ZMod 2)) (z : Fin n → Bool) :
    eval (toF2 z) (coefficientMap g hg S p) = coordinates g hg p S z := eval_polynomial _ _

theorem coefficient_congr {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (S : GlobalIndex g n) (p q : MvPolynomial (Fin n × Fin m) (ZMod 2))
    (he : ∀ X : Fin n × Fin m → Bool, eval (toF2 X) p = eval (toF2 X) q) :
    coefficientMap g hg S p = coefficientMap g hg S q := by
  apply multilinear_ext_bool (coefficient_multilinear g hg S p) (coefficient_multilinear g hg S q)
  intro z
  simp only [eval_coefficient, coordinates]
  exact congrArg (fun u => (fibreBasis g hg z).equivFun u S)
    (funext (fun X : Fibre g z => he X.1))

@[simp] theorem coefficient_ml {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (S : GlobalIndex g n) (p : MvPolynomial (Fin n × Fin m) (ZMod 2)) :
    coefficientMap g hg S (ML p) = coefficientMap g hg S p :=
  coefficient_congr g hg S _ _ (fun _ => eval_ml _ _)

theorem coefficient_degree_product {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (f : MvPolynomial (Fin n × Fin m) (ZMod 2)) (hf : f ∈ lnSpan g n)
    (p : MvPolynomial (Fin n × Fin m) (ZMod 2)) (S : GlobalIndex g n) :
    (coefficientMap g hg S (f * p)).totalDegree ≤ p.totalDegree :=
  polynomial_degree _ (coefficient_degree g hg f hf p S)

theorem ble_degree {V : Type} (D : ℕ) (p : MvPolynomial V (ZMod 2)) (hp : p ∈ Ble V D) :
    p.totalDegree ≤ D := by
  classical
  have hle : Ble V D ≤ restrictTotalDegree V (ZMod 2) D := by
    apply Submodule.span_le.mpr
    rintro _ ⟨A, hA, rfl⟩
    exact (mem_restrictTotalDegree V D _).mpr ((xMon_totalDegree A).trans_le hA)
  exact (mem_restrictTotalDegree V D p).mp (hle hp)

theorem coefficient_degree_multSpace {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (f : MvPolynomial (Fin n × Fin m) (ZMod 2)) (hf : f ∈ lnSpan g n)
    (D : ℕ) (p : MvPolynomial (Fin n × Fin m) (ZMod 2)) (hp : p ∈ multSpace f D)
    (S : GlobalIndex g n) : (coefficientMap g hg S p).totalDegree ≤ D := by
  obtain ⟨q, hq, rfl⟩ := hp
  change (coefficientMap g hg S (ML (f * q))).totalDegree ≤ D
  rw [coefficient_ml]
  exact (coefficient_degree_product g hg f hf q S).trans (ble_degree D q hq)

theorem coordinates_mul {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (p v : MvPolynomial (Fin n × Fin m) (ZMod 2)) (S : GlobalIndex g n) (z : Fin n → Bool) :
    coordinates g hg (p * v) S z = ∑ T : GlobalIndex g n,
      coordinates g hg p T z * coordinates g hg (xMon T.1 * v) S z := by
  classical
  have he : (fun X : Fibre g z => eval (toF2 X.1) (p * v)) =
      ∑ T : GlobalIndex g n, coordinates g hg p T z •
        (fun X : Fibre g z => eval (toF2 X.1) (xMon T.1 * v)) := by
    funext X
    simp only [map_mul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [coordinates_expansion g hg p z X, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro T _
    ring
  change (fibreBasis g hg z).equivFun (fun X => eval (toF2 X.1) (p * v)) S = _
  rw [he, map_sum]
  simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, coordinates]

theorem coefficient_mul {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (p v : MvPolynomial (Fin n × Fin m) (ZMod 2)) (S : GlobalIndex g n) :
    coefficientMap g hg S (p * v) = ∑ T : GlobalIndex g n,
      ML (coefficientMap g hg T p * coefficientMap g hg S (xMon T.1 * v)) := by
  classical
  refine multilinear_ext_bool (coefficient_multilinear g hg S _) ?_ ?_
  · exact (mem_restrictDegree (Fin n) _ 1).mp
      (Submodule.sum_mem _ (fun _ _ => (mem_restrictDegree (Fin n) _ 1).mpr (ml_multilinear _)))
  · intro z
    simp only [eval_coefficient, map_sum, eval_ml, map_mul]
    exact coordinates_mul g hg p v S z

end SemAC02.CoefficientPolynomials
end

section
-- Inlined Solutions.RelativeSpaceAlgebra

open MvPolynomial AC02Frege SemAC02
open AC02Frege.BooleanAlgebra AC02Frege.BooleanFlip AC02Frege.BooleanBasis

namespace SemAC02.RelativeSpaceAlgebra

theorem mem_Ble_iff {V : Type} (D : ℕ) (p : MvPolynomial V (ZMod 2)) :
    p ∈ Ble V D ↔ IsMultilinear p ∧ p.totalDegree ≤ D := by
  have he : Ble V D = monomialSpan (fun A : Finset V => A.card ≤ D) := by
    unfold Ble monomialSpan
    congr 1
    ext q
    constructor
    · rintro ⟨A,hA,rfl⟩
      exact ⟨A,hA,rfl⟩
    · rintro ⟨A,hA,rfl⟩
      exact ⟨A,hA,rfl⟩
  rw [he, mem_light_iff]

theorem mem_multSpace_of_degree {V : Type} [Finite V]
    (f Q : MvPolynomial V (ZMod 2)) (D : ℕ) (hQ : Q.totalDegree ≤ D) :
    mulML f Q ∈ multSpace f D := by
  refine ⟨ML Q, (mem_Ble_iff D _).mpr ⟨ml_multilinear _, (ml_totalDegree_le _).trans hQ⟩, ?_⟩
  change ML (f * ML Q) = ML (f * Q)
  exact ml_mul_right f Q

theorem multSpace_multilinear {V : Type} (f p : MvPolynomial V (ZMod 2)) (D : ℕ)
    (hp : p ∈ multSpace f D) : IsMultilinear p := by
  obtain ⟨Q,_,rfl⟩ := hp
  exact ml_multilinear _

theorem multSpace_degree {V : Type} (f p : MvPolynomial V (ZMod 2)) (k D : ℕ)
    (hf : f ∈ Ble V k) (hp : p ∈ multSpace f D) : p.totalDegree ≤ k+D := by
  obtain ⟨Q,hQ,rfl⟩ := hp
  change (ML (f*Q)).totalDegree ≤ k+D
  exact (ml_totalDegree_le _).trans ((totalDegree_mul f Q).trans
    (Nat.add_le_add ((mem_Ble_iff k f).mp hf).2 ((mem_Ble_iff D Q).mp hQ).2))

theorem relative_polynomial_mul {n : ℕ} (P : Set (MvPolynomial (Fin n) (ZMod 2)))
    (f Q v : MvPolynomial (Fin n) (ZMod 2)) (D : ℕ)
    (hp : RelativePC.Derivable P (multSpace f D) (mulML f Q))
    (hdeg : Q.totalDegree + v.totalDegree ≤ D) :
    RelativePC.Derivable P (multSpace f D) (ML (mulML f Q * v)) := by
  apply RelativePC.pc_polynomial_mul P (multSpace f D) (mulML f Q) v hp (ml_multilinear _)
  intro w hw
  have he : ML (mulML f Q * w) = mulML f (Q*w) := by
    change ML (ML (f*Q) * w) = ML (f*(Q*w))
    rw [ml_mul_left, mul_assoc]
  rw [he]
  apply mem_multSpace_of_degree
  exact (totalDegree_mul Q w).trans (by omega)

end SemAC02.RelativeSpaceAlgebra
end

section
-- Inlined Solutions.BooleanDimension

open Module MvPolynomial AC02Frege
open AC02Frege.BooleanAlgebra

namespace SemAC02.BooleanDimension

abbrev DegreeIndex (n D : ℕ) := {A : Finset (Fin n) // A.card ≤ D}

theorem span_degree_monomials (n D : ℕ) :
    Submodule.span (ZMod 2) (Set.range (fun A : DegreeIndex n D => xMon A.1)) = Ble (Fin n) D := by
  congr 1
  ext p
  constructor
  · rintro ⟨A,rfl⟩
    exact ⟨A.1,A.2,rfl⟩
  · rintro ⟨A,hA,rfl⟩
    exact ⟨⟨A,hA⟩,rfl⟩

noncomputable def degreeBasis (n D : ℕ) : Basis (DegreeIndex n D) (ZMod 2) (Ble (Fin n) D) :=
  (Basis.span (xMon_linearIndependent.comp (fun A : DegreeIndex n D => A.1) Subtype.val_injective)).map
    (LinearEquiv.ofEq _ _ (span_degree_monomials n D))

instance finite_Ble (n D : ℕ) : Module.Finite (ZMod 2) (Ble (Fin n) D) :=
  Module.Finite.of_basis (degreeBasis n D)

def degreeIndexEquiv (n D : ℕ) : DegreeIndex n D ≃
    (j : Fin (min D n + 1)) × {A : Finset (Fin n) // A.card = j.1} where
  toFun A := ⟨⟨A.1.card, by
    have hcard := Finset.card_le_univ A.1
    simp only [Fintype.card_fin] at hcard
    omega⟩,A.1,rfl⟩
  invFun B := ⟨B.2.1,by have := B.1.2; have := B.2.2; omega⟩
  left_inv A := by apply Subtype.ext; rfl
  right_inv B := by
    rcases B with ⟨⟨j,hj⟩,A,hA⟩
    cases hA
    rfl

theorem finrank_Ble (n D : ℕ) : finrank (ZMod 2) (Ble (Fin n) D) = Hn n D := by
  classical
  rw [Module.finrank_eq_card_basis (degreeBasis n D), Fintype.card_congr (degreeIndexEquiv n D), Fintype.card_sigma]
  simp only [Fintype.card_finset_len, Fintype.card_fin]
  exact Fin.sum_univ_eq_sum_range _ _

theorem Hn_pos (n D : ℕ) : 0 < Hn n D := by
  unfold Hn
  apply lt_of_lt_of_le (show 0 < n.choose 0 by simp)
  exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (by simp)

end SemAC02.BooleanDimension
end

section
-- Inlined Solutions.MultiplierSupportCount

set_option maxHeartbeats 1000000

open Module MvPolynomial AC02Frege AC02Frege.BooleanAlgebra

namespace SemAC02.MultiplierSupportCount

abbrev MultiplierIndex {m : ℕ} (g : (Fin m → Bool) → Bool) (n k : ℕ) :=
  {S : Finset (Fin n × Fin m) // S.card ≤ k ∧ IsLnSupport g S}

theorem multiplier_span {m : ℕ} (g : (Fin m → Bool) → Bool) (n k : ℕ) :
    Submodule.span (ZMod 2) (Set.range (fun S : MultiplierIndex g n k => xMon S.1)) =
      multiplierSpace g n k := by
  unfold multiplierSpace
  congr 1
  ext p
  constructor
  · rintro ⟨S,rfl⟩
    exact ⟨S.1,S.2,rfl⟩
  · rintro ⟨S,hS,rfl⟩
    exact ⟨⟨S,hS⟩,rfl⟩

noncomputable def multiplierBasis {m : ℕ} (g : (Fin m → Bool) → Bool) (n k : ℕ) :
    Basis (MultiplierIndex g n k) (ZMod 2) (multiplierSpace g n k) :=
  (Basis.span (xMon_linearIndependent.comp (fun S : MultiplierIndex g n k => S.1) Subtype.val_injective)).map
    (LinearEquiv.ofEq _ _ (multiplier_span g n k))

instance finite_multiplierSpace {m : ℕ} (g : (Fin m → Bool) → Bool) (n k : ℕ) :
    Module.Finite (ZMod 2) (multiplierSpace g n k) := Module.Finite.of_basis (multiplierBasis g n k)

theorem finrank_multiplier {m : ℕ} (g : (Fin m → Bool) → Bool) (n k : ℕ) :
    finrank (ZMod 2) (multiplierSpace g n k) =
      (Finset.univ.filter (fun S : Finset (Fin n × Fin m) => S.card ≤ k ∧ IsLnSupport g S)).card := by
  rw [Module.finrank_eq_card_basis (multiplierBasis g n k)]
  exact Fintype.card_subtype _

abbrev LowIndex (V : Type) (k : ℕ) := {S : Finset V // S.card ≤ k}

def lowIndexEquiv (V : Type) [Fintype V] [DecidableEq V] (k : ℕ) :
    LowIndex V k ≃ (j : Fin (min k (Fintype.card V)+1)) × {S : Finset V // S.card = j.1} where
  toFun S := ⟨⟨S.1.card,by have := Finset.card_le_univ S.1; omega⟩,S.1,rfl⟩
  invFun T := ⟨T.2.1,by have := T.1.2; have := T.2.2; omega⟩
  left_inv S := by apply Subtype.ext; rfl
  right_inv T := by rcases T with ⟨⟨j,hj⟩,S,hS⟩; cases hS; rfl

theorem low_support_card (V : Type) [Fintype V] [DecidableEq V] (k : ℕ) :
    (Finset.univ.filter (fun S : Finset V => S.card ≤ k)).card = Hn (Fintype.card V) k := by
  rw [← Fintype.card_subtype,Fintype.card_congr (lowIndexEquiv V k),Fintype.card_sigma]
  simp only [Fintype.card_finset_len]
  exact Fin.sum_univ_eq_sum_range _ _

end SemAC02.MultiplierSupportCount
end

section
-- Inlined Solutions.MajorityLightCount

set_option maxHeartbeats 1000000

open MvPolynomial Module
open AC02Frege.BooleanAlgebra

namespace AC02Frege.MajorityLightCount

open HeavyBlockCounting

def lightFamily (n ℓ K : ℕ) : Finset (Finset (Fin n × Fin ℓ)) :=
  Finset.univ.filter (fun T => T ∈ lightSets n ℓ ∧ T.card ≤ K)

theorem light_count (n ℓ K : ℕ) :
    SemAC02.Hn (n*ℓ) K ≤ (lightFamily n ℓ K).card*2^n := by
  let A := (Finset.univ : Finset (Finset (Fin n × Fin ℓ))).filter (fun T => T.card ≤ K)
  let B := lightFamily n ℓ K ×ˢ (Finset.univ : Finset (Finset (Fin n)))
  have hmap : Set.MapsTo (fun T : Finset (Fin n × Fin ℓ) => (fold T,heavyBlocks T)) (↑A) (↑B) := by
    intro T hT
    have hTK : T.card ≤ K := (Finset.mem_filter.mp hT).2
    refine Finset.mem_product.mpr ⟨?_,Finset.mem_univ _⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,fold_light T,(fold_card_le T).trans hTK⟩
  have h := Finset.card_le_card_of_injOn (fun T => (fold T,heavyBlocks T)) hmap fold_encoding_injective.injOn
  have hA : A.card = SemAC02.Hn (n*ℓ) K := by
    simpa only [A,Fintype.card_prod,Fintype.card_fin] using
      SemAC02.MultiplierSupportCount.low_support_card (Fin n × Fin ℓ) K
  rw [hA] at h
  simpa only [B,Finset.card_product,Finset.card_univ,Fintype.card_finset,Fintype.card_fin] using h

theorem light_count_real (n ℓ K : ℕ) :
    (SemAC02.Hn (n*ℓ) K : ℝ)/2^n ≤ ((lightFamily n ℓ K).card : ℝ) := by
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2^n)).mpr
  exact_mod_cast light_count n ℓ K

abbrev LightIndex (n ℓ K : ℕ) :=
  {T : Finset (Fin n × Fin ℓ) // T ∈ lightSets n ℓ ∧ T.card ≤ K}

noncomputable def lightSpace (n ℓ K : ℕ) :
    Submodule (ZMod 2) (MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) :=
  Submodule.span (ZMod 2) (xMon '' {T | T ∈ lightSets n ℓ ∧ T.card ≤ K})

theorem light_span (n ℓ K : ℕ) :
    Submodule.span (ZMod 2) (Set.range (fun T : LightIndex n ℓ K => xMon T.1)) = lightSpace n ℓ K := by
  unfold lightSpace
  congr 1
  ext p
  constructor
  · rintro ⟨T,rfl⟩; exact ⟨T.1,T.2,rfl⟩
  · rintro ⟨T,hT,rfl⟩; exact ⟨⟨T,hT⟩,rfl⟩

noncomputable def lightBasis (n ℓ K : ℕ) : Basis (LightIndex n ℓ K) (ZMod 2) (lightSpace n ℓ K) :=
  (Basis.span (xMon_linearIndependent.comp (fun T : LightIndex n ℓ K => T.1) Subtype.val_injective)).map
    (LinearEquiv.ofEq _ _ (light_span n ℓ K))

instance finite_lightSpace (n ℓ K : ℕ) : Module.Finite (ZMod 2) (lightSpace n ℓ K) :=
  Module.Finite.of_basis (lightBasis n ℓ K)

theorem finrank_lightSpace (n ℓ K : ℕ) :
    finrank (ZMod 2) (lightSpace n ℓ K) = (lightFamily n ℓ K).card := by
  rw [Module.finrank_eq_card_basis (lightBasis n ℓ K)]
  exact Fintype.card_subtype _

end AC02Frege.MajorityLightCount
end

section
-- Inlined Solutions.MajorityIdeal

open MvPolynomial AC02Frege
open AC02Frege.BooleanAlgebra AC02Frege.MajorityFoundation
open AC02Frege.BooleanBasis AC02Frege.BooleanFlip

namespace AC02Frege.MajorityIdeal

noncomputable def majorityMul (ℓ : ℕ) :
    MvPolynomial (Fin ℓ) (ZMod 2) →ₗ[ZMod 2] MvPolynomial (Fin ℓ) (ZMod 2) where
  toFun p := ML (majOne ℓ * p)
  map_add' p q := by rw [mul_add, map_add]
  map_smul' c p := by simp only [mul_smul_comm, map_smul, RingHom.id_apply]

theorem ideal_eq_vanishing (ℓ : ℕ) (p : MvPolynomial (Fin ℓ) (ZMod 2)) :
    p ∈ (majorityMul ℓ).range ↔ IsMultilinear p ∧
      ∀ x : Fin ℓ → ZMod 2, (Finset.univ.filter (fun i => x i = 1)).card ≤ ℓ / 2 →
        eval x p = 0 := by
  classical
  constructor
  · rintro ⟨q, rfl⟩
    change IsMultilinear (ML (majOne ℓ * q)) ∧ _
    refine ⟨ml_multilinear _, ?_⟩
    intro x hx
    change eval x (ML (majOne ℓ * q)) = 0
    rw [eval_ml, map_mul, majOne_eval, if_neg (by omega), zero_mul]
  · rintro ⟨hp, hv⟩
    refine ⟨p, ?_⟩
    change ML (majOne ℓ * p) = p
    apply multilinear_ext (ml_multilinear _) hp
    intro x
    change eval x (ML (majOne ℓ * p)) = eval x p
    rw [eval_ml, map_mul, majOne_eval]
    split_ifs with hx
    · rw [one_mul]
    · rw [zero_mul, hv x (by omega)]

theorem pointPoly_mem_heavy (ℓ : ℕ) (S : Finset (Fin ℓ)) (hS : ℓ / 2 < S.card) :
    pointPoly S ∈ monomialSpan (fun T : Finset (Fin ℓ) => ℓ / 2 < T.card) := by
  apply (mem_monomialSpan_iff _ _).mpr
  refine ⟨pointPoly_multilinear S, ?_⟩
  intro s hs
  have hml := pointPoly_multilinear S s hs
  rw [pointPoly_factor] at hs
  have hd := support_mul_xMon_degree S _ s hs
  rw [squarefree_sum s hml] at hd
  omega

theorem vanishing_mem_heavy (ℓ : ℕ) (p : MvPolynomial (Fin ℓ) (ZMod 2))
    (hp : IsMultilinear p)
    (hv : ∀ x : Fin ℓ → ZMod 2,
      (Finset.univ.filter (fun i => x i = 1)).card ≤ ℓ / 2 → eval x p = 0) :
    p ∈ monomialSpan (fun T : Finset (Fin ℓ) => ℓ / 2 < T.card) := by
  classical
  rw [point_interpolation p hp]
  apply Submodule.sum_mem
  intro S _
  by_cases hS : ℓ / 2 < S.card
  · exact Submodule.smul_mem _ _ (pointPoly_mem_heavy ℓ S hS)
  · have hz := hv (fun i => if i ∈ S then (1 : ZMod 2) else 0)
      (by simpa only [ones_of_point] using Nat.le_of_not_gt hS)
    rw [hz, zero_smul]
    exact Submodule.zero_mem _

theorem ideal_eq_heavy (ℓ : ℕ) :
    (majorityMul ℓ).range = monomialSpan (fun T : Finset (Fin ℓ) => ℓ / 2 < T.card) := by
  apply le_antisymm
  · intro p hp
    obtain ⟨hml, hv⟩ := (ideal_eq_vanishing ℓ p).mp hp
    exact vanishing_mem_heavy ℓ p hml hv
  · apply Submodule.span_le.mpr
    rintro p ⟨S, hS, rfl⟩
    refine ⟨xMon S, ?_⟩
    change ML (majOne ℓ * xMon S) = xMon S
    rw [mul_comm]
    exact heavy_monomial_absorbs_majority ℓ S hS

theorem light_inter_ideal (ℓ : ℕ) (p : MvPolynomial (Fin ℓ) (ZMod 2))
    (hp : p ∈ monomialSpan (fun S : Finset (Fin ℓ) => S.card ≤ ℓ / 2))
    (hi : p ∈ (majorityMul ℓ).range) : p = 0 := by
  rw [ideal_eq_heavy] at hi
  obtain ⟨_, hl⟩ := (mem_monomialSpan_iff _ _).mp hp
  obtain ⟨_, hh⟩ := (mem_monomialSpan_iff _ _).mp hi
  apply MvPolynomial.support_eq_empty.mp
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro s hs
  have := hl s hs
  have := hh s hs
  omega

end AC02Frege.MajorityIdeal
end

section
-- Inlined Solutions.MajorityInjective

open MvPolynomial AC02Frege
open AC02Frege.BooleanAlgebra AC02Frege.MajorityFoundation
open AC02Frege.BooleanBasis AC02Frege.BooleanFlip AC02Frege.MajorityIdeal

namespace AC02Frege.MajorityInjective

theorem flipped_weight (ℓ : ℕ) (x : Fin ℓ → ZMod 2) :
    (Finset.univ.filter (fun i => 1 + x i = 1)).card +
      (Finset.univ.filter (fun i => x i = 1)).card = ℓ := by
  classical
  have heq : Finset.univ.filter (fun i => 1 + x i = 1) =
      (Finset.univ.filter (fun i => x i = 1))ᶜ := by
    ext i
    rcases eq_zero_or_one (x i) with hi | hi <;> simp [hi, CharTwo.add_self_eq_zero]
  rw [heq, Finset.card_compl]
  have hc := Finset.card_le_univ (Finset.univ.filter (fun i => x i = 1))
  simp only [Fintype.card_fin] at *
  omega

theorem vanishing_H1_degree (ℓ : ℕ) (hℓ : Odd ℓ)
    (p : MvPolynomial (Fin ℓ) (ZMod 2)) (hp : IsMultilinear p) (hne : p ≠ 0)
    (hv : ∀ x : Fin ℓ → ZMod 2,
      ℓ / 2 < (Finset.univ.filter (fun i => x i = 1)).card → eval x p = 0) :
    ℓ / 2 + 1 ≤ p.totalDegree := by
  classical
  by_contra hd
  have hfdeg : (flip p).totalDegree ≤ ℓ / 2 := (flip_degree_le p).trans (by omega)
  have hfml := flip_multilinear p
  have hflight := (mem_light_iff (ℓ / 2) (flip p)).mpr ⟨hfml, hfdeg⟩
  have hfideal : flip p ∈ (majorityMul ℓ).range := by
    apply (ideal_eq_vanishing ℓ (flip p)).mpr
    refine ⟨hfml, ?_⟩
    intro x hx
    rw [flip_eval]
    apply hv
    have hc := flipped_weight ℓ x
    rcases hℓ with ⟨k, hk⟩
    omega
  have hz := light_inter_ideal ℓ (flip p) hflight hfideal
  apply hne
  calc
    p = flip (flip p) := (flip_involution p hp).symm
    _ = flip 0 := congrArg (BooleanFlip.flip (V := Fin ℓ)) hz
    _ = 0 := by simp [BooleanFlip.flip]

theorem majority_injective_light (ℓ : ℕ) (hℓ : Odd ℓ)
    (v w : MvPolynomial (Fin ℓ) (ZMod 2))
    (hv : IsMultilinear v) (hdv : v.totalDegree ≤ ℓ / 2)
    (hw : IsMultilinear w) (hdw : w.totalDegree ≤ ℓ / 2)
    (heq : majorityMul ℓ v = majorityMul ℓ w) : v = w := by
  classical
  have hsum : IsMultilinear (v + w) :=
    (mem_restrictDegree (Fin ℓ) _ 1).mp ((restrictDegree (Fin ℓ) (ZMod 2) 1).add_mem
      ((mem_restrictDegree (Fin ℓ) _ 1).mpr hv) ((mem_restrictDegree (Fin ℓ) _ 1).mpr hw))
  have hd : (v + w).totalDegree ≤ ℓ / 2 :=
    (totalDegree_add _ _).trans (max_le hdv hdw)
  have hz : v + w = 0 := by
    by_contra hne
    have hl := vanishing_H1_degree ℓ hℓ (v + w) hsum hne ?_
    · omega
    · intro x hx
      have he := congrArg (eval x) heq
      change eval x (ML (majOne ℓ * v)) = eval x (ML (majOne ℓ * w)) at he
      simp only [eval_ml, map_mul, majOne_eval, if_pos hx, one_mul] at he
      rw [map_add, he, CharTwo.add_self_eq_zero]
  have he := congrArg (fun p => p + w) hz
  simpa only [CharTwo.add_cancel_right, zero_add] using he

end AC02Frege.MajorityInjective
end

section
-- Inlined Solutions.MajorityBasis

open MvPolynomial AC02Frege
open AC02Frege.BooleanAlgebra AC02Frege.MajorityFoundation
open AC02Frege.BooleanBasis AC02Frege.BooleanFlip AC02Frege.MajorityIdeal
open AC02Frege.MajorityInjective

namespace AC02Frege.MajorityBasis

theorem monomialSpan_eq_span_range {V : Type*} (P : Finset V → Prop) :
    monomialSpan P = Submodule.span (ZMod 2)
      (Set.range (fun S : {S : Finset V // P S} => xMon S.1)) := by
  have hset : {p : MvPolynomial V (ZMod 2) | ∃ S : Finset V, P S ∧ p = xMon S} =
      Set.range (fun S : {S : Finset V // P S} => xMon S.1) := by
    ext p
    constructor
    · rintro ⟨S, hS, rfl⟩
      exact ⟨⟨S, hS⟩, rfl⟩
    · rintro ⟨S, rfl⟩
      exact ⟨S.1, S.2, rfl⟩
  exact congrArg (Submodule.span (ZMod 2)) hset

theorem monomialSpan_linearIndependent {V : Type*} (P : Finset V → Prop) :
    LinearIndependent (ZMod 2) (fun S : {S : Finset V // P S} => xMon S.1) :=
  xMon_linearIndependent.comp Subtype.val Subtype.val_injective

theorem split_light_heavy (ℓ : ℕ) (p : MvPolynomial (Fin ℓ) (ZMod 2))
    (hp : IsMultilinear p) :
    ∃ u ∈ monomialSpan (fun S : Finset (Fin ℓ) => S.card ≤ ℓ / 2),
      ∃ w ∈ (majorityMul ℓ).range, p = u + w := by
  classical
  let L := monomialSpan (fun S : Finset (Fin ℓ) => S.card ≤ ℓ / 2)
  let H := monomialSpan (fun S : Finset (Fin ℓ) => ℓ / 2 < S.card)
  have hmem : p ∈ L ⊔ H := by
    rw [p.as_sum]
    apply Submodule.sum_mem
    intro s hs
    rw [squarefree_monomial s _ (hp s hs)]
    apply Submodule.smul_mem
    by_cases hd : s.support.card ≤ ℓ / 2
    · exact (show L ≤ L ⊔ H from le_sup_left) (Submodule.subset_span ⟨s.support, hd, rfl⟩)
    · exact (show H ≤ L ⊔ H from le_sup_right)
        (Submodule.subset_span ⟨s.support, by omega, rfl⟩)
  obtain ⟨u, hu, w, hw, heq⟩ := Submodule.mem_sup.mp hmem
  refine ⟨u, hu, w, ?_, heq.symm⟩
  rw [ideal_eq_heavy]
  exact hw

noncomputable def lightHeavyEquiv (ℓ : ℕ) (hℓ : Odd ℓ) :
    {S : Finset (Fin ℓ) // S.card ≤ ℓ / 2} ≃
      {T : Finset (Fin ℓ) // ℓ / 2 < T.card} where
  toFun S := ⟨S.1ᶜ, by
    rw [Finset.card_compl]
    have hc := Finset.card_le_univ S.1
    have hS := S.2
    simp only [Fintype.card_fin] at *
    rcases hℓ with ⟨k, hk⟩
    omega⟩
  invFun T := ⟨T.1ᶜ, by
    rw [Finset.card_compl]
    have hc := Finset.card_le_univ T.1
    have hT := T.2
    simp only [Fintype.card_fin] at *
    rcases hℓ with ⟨k, hk⟩
    omega⟩
  left_inv S := Subtype.ext (compl_compl _)
  right_inv T := Subtype.ext (compl_compl _)

theorem majority_basis_independent (ℓ : ℕ) (hℓ : Odd ℓ) :
    LinearIndependent (ZMod 2)
      (fun S : {S : Finset (Fin ℓ) // S.card ≤ ℓ / 2} => majorityMul ℓ (xMon S.1)) := by
  apply (monomialSpan_linearIndependent (fun S : Finset (Fin ℓ) => S.card ≤ ℓ / 2)).map_injOn
  intro v hv w hw heq
  have hv' : v ∈ monomialSpan (fun S : Finset (Fin ℓ) => S.card ≤ ℓ / 2) := by
    rwa [monomialSpan_eq_span_range]
  have hw' : w ∈ monomialSpan (fun S : Finset (Fin ℓ) => S.card ≤ ℓ / 2) := by
    rwa [monomialSpan_eq_span_range]
  obtain ⟨hvm, hvd⟩ := (mem_light_iff _ _).mp hv'
  obtain ⟨hwm, hwd⟩ := (mem_light_iff _ _).mp hw'
  exact majority_injective_light ℓ hℓ v w hvm hvd hwm hwd heq

theorem majority_basis_span (ℓ : ℕ) (hℓ : Odd ℓ) :
    (majorityMul ℓ).range = Submodule.span (ZMod 2)
      (Set.range (fun S : {S : Finset (Fin ℓ) // S.card ≤ ℓ / 2} => majorityMul ℓ (xMon S.1))) := by
  classical
  let H := monomialSpan (fun T : Finset (Fin ℓ) => ℓ / 2 < T.card)
  let B := Submodule.span (ZMod 2)
    (Set.range (fun S : {S : Finset (Fin ℓ) // S.card ≤ ℓ / 2} => majorityMul ℓ (xMon S.1)))
  have hH : H = Submodule.span (ZMod 2)
      (Set.range (fun T : {T : Finset (Fin ℓ) // ℓ / 2 < T.card} => xMon T.1)) :=
    monomialSpan_eq_span_range _
  letI : FiniteDimensional (ZMod 2) H := by
    rw [hH]
    exact FiniteDimensional.span_of_finite (ZMod 2) (Set.finite_range _)
  have hle : B ≤ H := by
    apply Submodule.span_le.mpr
    rintro p ⟨S, rfl⟩
    change majorityMul ℓ (xMon S.1) ∈ monomialSpan (fun T : Finset (Fin ℓ) => ℓ / 2 < T.card)
    rw [← ideal_eq_heavy]
    exact LinearMap.mem_range_self _ _
  have heq : Module.finrank (ZMod 2) B = Module.finrank (ZMod 2) H := by
    rw [show Module.finrank (ZMod 2) B =
      Fintype.card {S : Finset (Fin ℓ) // S.card ≤ ℓ / 2} from
        finrank_span_eq_card (majority_basis_independent ℓ hℓ)]
    rw [hH, finrank_span_eq_card (monomialSpan_linearIndependent _)]
    exact Fintype.card_congr (lightHeavyEquiv ℓ hℓ)
  have hBH := Submodule.eq_of_le_of_finrank_eq hle heq
  rw [ideal_eq_heavy]
  exact hBH.symm

theorem ideal_has_light_preimage (ℓ : ℕ) (hℓ : Odd ℓ)
    (p : MvPolynomial (Fin ℓ) (ZMod 2)) (hp : p ∈ (majorityMul ℓ).range) :
    ∃ v, IsMultilinear v ∧ v.totalDegree ≤ ℓ / 2 ∧ majorityMul ℓ v = p := by
  classical
  let L := monomialSpan (fun S : Finset (Fin ℓ) => S.card ≤ ℓ / 2)
  have heq : L.map (majorityMul ℓ) = (majorityMul ℓ).range := by
    rw [show L = Submodule.span (ZMod 2)
      (Set.range (fun S : {S : Finset (Fin ℓ) // S.card ≤ ℓ / 2} => xMon S.1)) from
        monomialSpan_eq_span_range _]
    rw [Submodule.map_span, ← Set.range_comp, majority_basis_span ℓ hℓ]
    rfl
  rw [← heq] at hp
  obtain ⟨v, hv, rfl⟩ := hp
  obtain ⟨hml, hd⟩ := (mem_light_iff _ _).mp hv
  exact ⟨v, hml, hd, rfl⟩

end AC02Frege.MajorityBasis
end

section
-- Inlined Solutions.MajorityExpansion

open MvPolynomial AC02Frege
open AC02Frege.BooleanAlgebra AC02Frege.MajorityFoundation
open AC02Frege.BooleanBasis AC02Frege.BooleanFlip AC02Frege.MajorityIdeal
open AC02Frege.MajorityInjective AC02Frege.MajorityBasis

namespace AC02Frege.MajorityExpansion

theorem unique_expansion (ℓ : ℕ) (hℓ : Odd ℓ)
    (p : MvPolynomial (Fin ℓ) (ZMod 2)) (hp : IsMultilinear p) :
    ∃! uv : MvPolynomial (Fin ℓ) (ZMod 2) × MvPolynomial (Fin ℓ) (ZMod 2),
      IsMultilinear uv.1 ∧ IsMultilinear uv.2 ∧ uv.1.totalDegree ≤ ℓ / 2 ∧
        uv.2.totalDegree ≤ ℓ / 2 ∧ p = uv.1 + majorityMul ℓ uv.2 := by
  classical
  obtain ⟨u, hu, w, hw, heq⟩ := split_light_heavy ℓ p hp
  obtain ⟨hum, hud⟩ := (mem_light_iff _ _).mp hu
  obtain ⟨v, hvm, hvd, hvp⟩ := ideal_has_light_preimage ℓ hℓ w hw
  have hpuv : p = u + majorityMul ℓ v := by rw [hvp]; exact heq
  refine ⟨(u, v), ⟨hum, hvm, hud, hvd, hpuv⟩, ?_⟩
  rintro ⟨u', v'⟩ ⟨hu'm, hv'm, hu'd, hv'd, heq'⟩
  have hrel : u' - u = majorityMul ℓ v - majorityMul ℓ v' := by
    apply sub_eq_sub_iff_add_eq_add.mpr
    exact heq'.symm.trans (hpuv.trans (add_comm _ _))
  have hlight : u' - u ∈ monomialSpan (fun S : Finset (Fin ℓ) => S.card ≤ ℓ / 2) :=
    Submodule.sub_mem _ ((mem_light_iff _ _).mpr ⟨hu'm, hu'd⟩) hu
  have hideal : u' - u ∈ (majorityMul ℓ).range := by
    rw [hrel]
    exact Submodule.sub_mem _ (LinearMap.mem_range_self _ _) (LinearMap.mem_range_self _ _)
  have hu'eq : u' = u := sub_eq_zero.mp (light_inter_ideal ℓ (u' - u) hlight hideal)
  have hveq : majorityMul ℓ v' = majorityMul ℓ v := by
    apply add_left_cancel (a := u)
    rw [← hpuv, ← hu'eq]
    exact heq'.symm
  exact Prod.ext hu'eq (majority_injective_light ℓ hℓ v' v hv'm hv'd hvm hvd hveq)

end AC02Frege.MajorityExpansion
end

section
-- Inlined Solutions.MajorityFunctionBasis

open MvPolynomial AC02Frege Module
open AC02Frege.BooleanAlgebra AC02Frege.MajorityFoundation AC02Frege.BooleanBasis
open AC02Frege.MajorityIdeal AC02Frege.MajorityInjective AC02Frege.MajorityBasis
open AC02Frege.MajorityExpansion

namespace AC02Frege.MajorityFunctionBasis

abbrev LightIndex (ℓ : ℕ) := {S : Finset (Fin ℓ) // S.card ≤ ℓ / 2}

noncomputable abbrev LightSpace (ℓ : ℕ) :=
  monomialSpan (fun S : Finset (Fin ℓ) => S.card ≤ ℓ / 2)

noncomputable def lightBasis (ℓ : ℕ) :
    Basis (LightIndex ℓ) (ZMod 2) (LightSpace ℓ) := by
  let b := Basis.span (monomialSpan_linearIndependent (fun S : Finset (Fin ℓ) => S.card ≤ ℓ / 2))
  exact b.map (LinearEquiv.ofEq _ _ (monomialSpan_eq_span_range _).symm)

@[simp] theorem lightBasis_coe (ℓ : ℕ) (S : LightIndex ℓ) :
    ((lightBasis ℓ S : LightSpace ℓ) : MvPolynomial (Fin ℓ) (ZMod 2)) = xMon S.1 := by
  simp only [lightBasis, Basis.map_apply]
  rw [LinearEquiv.coe_ofEq_apply]
  exact Basis.coe_span_apply _ _

noncomputable def pairEvaluation (ℓ : ℕ) :
    LightSpace ℓ × LightSpace ℓ →ₗ[ZMod 2] ((Fin ℓ → ZMod 2) → ZMod 2) where
  toFun uv x := eval x ((uv.1 : MvPolynomial (Fin ℓ) (ZMod 2)) + majorityMul ℓ uv.2)
  map_add' u v := by
    ext x
    simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, map_add, Pi.add_apply]
    abel
  map_smul' c u := by
    ext x
    simp only [Prod.smul_fst, Prod.smul_snd, Submodule.coe_smul, map_smul,
      ← smul_add, RingHom.id_apply, Pi.smul_apply]
    rw [smul_eval]
    rfl

theorem pair_polynomial_multilinear (ℓ : ℕ) (uv : LightSpace ℓ × LightSpace ℓ) :
    IsMultilinear ((uv.1 : MvPolynomial (Fin ℓ) (ZMod 2)) + majorityMul ℓ uv.2) := by
  have hu := ((mem_light_iff _ _).mp uv.1.2).1
  have hv : IsMultilinear (majorityMul ℓ uv.2) := by
    change IsMultilinear (ML (majOne ℓ * (uv.2 : MvPolynomial (Fin ℓ) (ZMod 2))))
    exact ml_multilinear _
  exact (mem_restrictDegree (Fin ℓ) _ 1).mp ((restrictDegree (Fin ℓ) (ZMod 2) 1).add_mem
    ((mem_restrictDegree (Fin ℓ) _ 1).mpr hu) ((mem_restrictDegree (Fin ℓ) _ 1).mpr hv))

theorem pairEvaluation_injective (ℓ : ℕ) (hℓ : Odd ℓ) : Function.Injective (pairEvaluation ℓ) := by
  intro u v huv
  have hpoly : (u.1 : MvPolynomial (Fin ℓ) (ZMod 2)) + majorityMul ℓ u.2 =
      (v.1 : MvPolynomial (Fin ℓ) (ZMod 2)) + majorityMul ℓ v.2 := by
    apply multilinear_ext (pair_polynomial_multilinear ℓ u) (pair_polynomial_multilinear ℓ v)
    intro x
    exact congrFun huv x
  obtain ⟨hu1m, hu1d⟩ := (mem_light_iff _ _).mp u.1.2
  obtain ⟨hu2m, hu2d⟩ := (mem_light_iff _ _).mp u.2.2
  obtain ⟨hv1m, hv1d⟩ := (mem_light_iff _ _).mp v.1.2
  obtain ⟨hv2m, hv2d⟩ := (mem_light_iff _ _).mp v.2.2
  have heq := (unique_expansion ℓ hℓ _ (pair_polynomial_multilinear ℓ u)).unique
    (y₁ := ((u.1 : MvPolynomial (Fin ℓ) (ZMod 2)), (u.2 : MvPolynomial (Fin ℓ) (ZMod 2))))
    (y₂ := ((v.1 : MvPolynomial (Fin ℓ) (ZMod 2)), (v.2 : MvPolynomial (Fin ℓ) (ZMod 2))))
    ⟨hu1m, hu2m, hu1d, hu2d, rfl⟩ ⟨hv1m, hv2m, hv1d, hv2d, hpoly⟩
  exact Prod.ext (Subtype.ext (congrArg Prod.fst heq)) (Subtype.ext (congrArg Prod.snd heq))

theorem pairEvaluation_surjective (ℓ : ℕ) (hℓ : Odd ℓ) : Function.Surjective (pairEvaluation ℓ) := by
  intro f
  obtain ⟨p, hp⟩ := LinearMap.range_eq_top.mp (MvPolynomial.range_evalᵢ (Fin ℓ) (ZMod 2)) f
  let p' : restrictDegree (Fin ℓ) (ZMod 2) (Fintype.card (ZMod 2) - 1) := p
  have hml : IsMultilinear p'.1 := by
    apply (mem_restrictDegree (Fin ℓ) _ 1).mp
    simpa only [ZMod.card, Nat.reduceSub] using p'.2
  obtain ⟨uv, huv, _⟩ := unique_expansion ℓ hℓ p'.1 hml
  obtain ⟨hum, hvm, hud, hvd, heq⟩ := huv
  refine ⟨(⟨uv.1, (mem_light_iff _ _).mpr ⟨hum, hud⟩⟩,
    ⟨uv.2, (mem_light_iff _ _).mpr ⟨hvm, hvd⟩⟩), ?_⟩
  ext x
  change eval x (uv.1 + majorityMul ℓ uv.2) = f x
  rw [← heq]
  exact congrFun hp x

noncomputable def pairEvaluationEquiv (ℓ : ℕ) (hℓ : Odd ℓ) :
    (LightSpace ℓ × LightSpace ℓ) ≃ₗ[ZMod 2] ((Fin ℓ → ZMod 2) → ZMod 2) :=
  LinearEquiv.ofBijective (pairEvaluation ℓ)
    ⟨pairEvaluation_injective ℓ hℓ, pairEvaluation_surjective ℓ hℓ⟩

noncomputable def blockFunctionBasis (ℓ : ℕ) (hℓ : Odd ℓ) :
    Basis (LightIndex ℓ ⊕ LightIndex ℓ) (ZMod 2) ((Fin ℓ → ZMod 2) → ZMod 2) :=
  ((lightBasis ℓ).prod (lightBasis ℓ)).map (pairEvaluationEquiv ℓ hℓ)

@[simp] theorem blockFunctionBasis_inl (ℓ : ℕ) (hℓ : Odd ℓ)
    (S : LightIndex ℓ) (x : Fin ℓ → ZMod 2) :
    blockFunctionBasis ℓ hℓ (Sum.inl S) x = eval x (xMon S.1) := by
  change eval x
    (((((lightBasis ℓ).prod (lightBasis ℓ)) (Sum.inl S)).1 : MvPolynomial (Fin ℓ) (ZMod 2)) +
      majorityMul ℓ ((((lightBasis ℓ).prod (lightBasis ℓ)) (Sum.inl S)).2)) = _
  simp only [Basis.prod_apply_inl_fst, Basis.prod_apply_inl_snd, Submodule.coe_zero,
    map_zero, add_zero, lightBasis_coe]

@[simp] theorem blockFunctionBasis_inr (ℓ : ℕ) (hℓ : Odd ℓ)
    (S : LightIndex ℓ) (x : Fin ℓ → ZMod 2) :
    blockFunctionBasis ℓ hℓ (Sum.inr S) x = eval x (majOne ℓ) * eval x (xMon S.1) := by
  change eval x
    (((((lightBasis ℓ).prod (lightBasis ℓ)) (Sum.inr S)).1 : MvPolynomial (Fin ℓ) (ZMod 2)) +
      majorityMul ℓ ((((lightBasis ℓ).prod (lightBasis ℓ)) (Sum.inr S)).2)) = _
  simp only [Basis.prod_apply_inr_fst, Basis.prod_apply_inr_snd, Submodule.coe_zero,
    zero_add, lightBasis_coe]
  change eval x (ML (majOne ℓ * xMon S.1)) = _
  rw [eval_ml, map_mul]

noncomputable def allBlockFunctionBasis (n ℓ : ℕ) (hℓ : Odd ℓ) :
    Basis (Fin n → LightIndex ℓ ⊕ LightIndex ℓ) (ZMod 2)
      ((Fin n → Fin ℓ → ZMod 2) → ZMod 2) :=
  ProofComplexity.productFunctionBasis (fun _ : Fin n => blockFunctionBasis ℓ hℓ)

theorem allBlockFunctionBasis_apply (n ℓ : ℕ) (hℓ : Odd ℓ)
    (k : Fin n → LightIndex ℓ ⊕ LightIndex ℓ) (x : Fin n → Fin ℓ → ZMod 2) :
    allBlockFunctionBasis n ℓ hℓ k x = ∏ i, blockFunctionBasis ℓ hℓ (k i) (x i) := by
  exact ProofComplexity.productFunctionBasis_apply _ _ _

end AC02Frege.MajorityFunctionBasis
end

section
-- Inlined Solutions.MajorityTensorIndex

open Module MvPolynomial AC02Frege
open AC02Frege.MajorityFunctionBasis

namespace AC02Frege.MajorityTensorIndex

def tensorSection {n ℓ : ℕ} (A : Finset (Fin n × Fin ℓ)) (i : Fin n) : Finset (Fin ℓ) :=
  Finset.univ.filter (fun a => (i, a) ∈ A)

theorem section_image {n ℓ : ℕ} (A : Finset (Fin n × Fin ℓ)) (i : Fin n) :
    (tensorSection A i).image (fun a => (i, a)) = blockPart A i := by
  ext v
  rcases v with ⟨j, a⟩
  simp only [Finset.mem_image, tensorSection, Finset.mem_filter, Finset.mem_univ, true_and,
    Prod.mk.injEq, blockPart]
  constructor
  · rintro ⟨b, hb, hij, hba⟩
    subst j; subst b
    exact ⟨hb, rfl⟩
  · rintro ⟨ha, rfl⟩
    exact ⟨a, ha, rfl, rfl⟩

theorem section_card {n ℓ : ℕ} (A : Finset (Fin n × Fin ℓ)) (i : Fin n) :
    (tensorSection A i).card = (blockPart A i).card := by
  rw [← section_image]
  exact (Finset.card_image_of_injective _ (fun a b h => congrArg Prod.snd h)).symm

abbrev GlobalLight (n ℓ : ℕ) := {A : Finset (Fin n × Fin ℓ) // A ∈ lightSets n ℓ}

def sections {n ℓ : ℕ} (A : GlobalLight n ℓ) (i : Fin n) : LightIndex ℓ :=
  ⟨tensorSection A.1 i, by
    rw [section_card]
    exact (Finset.mem_filter.mp A.2).2 i⟩

def assemble {n ℓ : ℕ} (S : Fin n → LightIndex ℓ) : Finset (Fin n × Fin ℓ) :=
  Finset.univ.filter (fun v => v.2 ∈ (S v.1).1)

@[simp] theorem section_assemble {n ℓ : ℕ} (S : Fin n → LightIndex ℓ) (i : Fin n) :
    tensorSection (assemble S) i = (S i).1 := by
  ext a
  simp [tensorSection, assemble]

@[simp] theorem assemble_sections {n ℓ : ℕ} (A : GlobalLight n ℓ) :
    assemble (sections A) = A.1 := by
  ext v
  simp [assemble, sections, tensorSection]

def lightSetEquiv (n ℓ : ℕ) : (Fin n → LightIndex ℓ) ≃ GlobalLight n ℓ where
  toFun S := ⟨assemble S, by
    simp only [lightSets, Finset.mem_filter, Finset.mem_univ, true_and]
    intro i
    rw [← section_card, section_assemble]
    exact (S i).2⟩
  invFun A := sections A
  left_inv S := by funext i; apply Subtype.ext; exact section_assemble S i
  right_inv A := Subtype.ext (assemble_sections A)

def pack {n ℓ : ℕ} (A : GlobalLight n ℓ) (J : Finset (Fin n)) :
    Fin n → LightIndex ℓ ⊕ LightIndex ℓ :=
  fun i => if i ∈ J then Sum.inr (sections A i) else Sum.inl (sections A i)

def unpackSupports {n ℓ : ℕ} (k : Fin n → LightIndex ℓ ⊕ LightIndex ℓ) :
    Fin n → LightIndex ℓ := fun i => Sum.elim id id (k i)

def unpackHeavy {n ℓ : ℕ} (k : Fin n → LightIndex ℓ ⊕ LightIndex ℓ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => (k i).isRight = true)

def tensorIndexEquiv (n ℓ : ℕ) :
    (Fin n → LightIndex ℓ ⊕ LightIndex ℓ) ≃ GlobalLight n ℓ × Finset (Fin n) where
  toFun k := (lightSetEquiv n ℓ (unpackSupports k), unpackHeavy k)
  invFun AJ := pack AJ.1 AJ.2
  left_inv k := by
    funext i
    change (if i ∈ unpackHeavy k then
      Sum.inr (sections (lightSetEquiv n ℓ (unpackSupports k)) i)
      else Sum.inl (sections (lightSetEquiv n ℓ (unpackSupports k)) i)) = k i
    have hs : sections (lightSetEquiv n ℓ (unpackSupports k)) i = unpackSupports k i := by
      exact congrFun ((lightSetEquiv n ℓ).left_inv (unpackSupports k)) i
    rw [hs]
    cases h : k i <;> simp [unpackHeavy, unpackSupports, h]
  right_inv AJ := by
    rcases AJ with ⟨A, J⟩
    have hs : unpackSupports (pack A J) = sections A := by
      funext i
      simp only [unpackSupports, pack]
      split_ifs <;> rfl
    apply Prod.ext
    · change lightSetEquiv n ℓ (unpackSupports (pack A J)) = A
      rw [hs]
      exact (lightSetEquiv n ℓ).right_inv A
    · ext i
      by_cases hi : i ∈ J <;> simp [unpackHeavy, pack, hi]

end AC02Frege.MajorityTensorIndex
end

section
-- Inlined Solutions.BooleanCoordinates

open Module MvPolynomial AC02Frege
open AC02Frege.BooleanAlgebra AC02Frege.BooleanBasis AC02Frege.BooleanRestrictions

namespace ProofComplexity.BooleanCoordinates

theorem all_monomials_span (V : Type) :
    Submodule.span (ZMod 2) (Set.range (fun S : Finset V => xMon S)) =
      restrictDegree V (ZMod 2) 1 := by
  have heq : monomialSpan (fun _S : Finset V => True) = restrictDegree V (ZMod 2) 1 := by
    ext p
    simp only [mem_monomialSpan_iff, mem_restrictDegree]
    simp only [and_true, implies_true]
    rfl
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro p ⟨S, rfl⟩
    exact (mem_restrictDegree V _ 1).mpr (xMon_multilinear S)
  · rw [← heq]
    apply Submodule.span_le.mpr
    rintro p ⟨S, _, rfl⟩
    exact Submodule.subset_span ⟨S, rfl⟩

noncomputable def booleanBasis (V : Type) :
    Basis (Finset V) (ZMod 2) (restrictDegree V (ZMod 2) 1) :=
  (Basis.span xMon_linearIndependent).map (LinearEquiv.ofEq _ _ (all_monomials_span V))

@[simp] theorem booleanBasis_coe (V : Type) (S : Finset V) :
    ((booleanBasis V S : restrictDegree V (ZMod 2) 1) : MvPolynomial V (ZMod 2)) = xMon S := by
  simp only [booleanBasis, Basis.map_apply, LinearEquiv.coe_ofEq_apply]
  exact Basis.coe_span_apply _ _

noncomputable def monoPoly {V : Type} [Fintype V] (c : Finset V → ZMod 2) :
    MvPolynomial V (ZMod 2) :=
  ((booleanBasis V).equivFun.symm c).1

noncomputable def monoCoeffs {V : Type} [Fintype V] (p : MvPolynomial V (ZMod 2)) :
    Finset V → ZMod 2 :=
  (booleanBasis V).equivFun ⟨ML p, (mem_restrictDegree V _ 1).mpr (ml_multilinear p)⟩

theorem monoPoly_multilinear {V : Type} [Fintype V] (c : Finset V → ZMod 2) :
    IsMultilinear (monoPoly c) :=
  (mem_restrictDegree V _ 1).mp ((booleanBasis V).equivFun.symm c).2

theorem monoPoly_coeffs {V : Type} [Fintype V] (p : MvPolynomial V (ZMod 2)) :
    monoPoly (monoCoeffs p) = ML p := by
  exact congrArg Subtype.val ((booleanBasis V).equivFun.symm_apply_apply _)

theorem monoCoeffs_poly {V : Type} [Fintype V] (c : Finset V → ZMod 2) :
    monoCoeffs (monoPoly c) = c := by
  have hsub : (⟨ML (monoPoly c), (mem_restrictDegree V _ 1).mpr
      (ml_multilinear (monoPoly c))⟩ : restrictDegree V (ZMod 2) 1) =
      (booleanBasis V).equivFun.symm c := by
    apply Subtype.ext
    exact ml_of_multilinear _ (monoPoly_multilinear c)
  exact (congrArg (booleanBasis V).equivFun hsub).trans
    ((booleanBasis V).equivFun.apply_symm_apply c)

theorem monoPoly_sum {V : Type} [Fintype V] (c : Finset V → ZMod 2) :
    monoPoly c = ∑ S : Finset V, c S • xMon S := by
  classical
  have h := (booleanBasis V).equivFun_symm_apply c
  have hv := congrArg (fun p : restrictDegree V (ZMod 2) 1 => (p : MvPolynomial V (ZMod 2))) h
  simpa only [monoPoly, Submodule.coe_sum, Submodule.coe_smul, booleanBasis_coe] using hv

theorem monoCoeffs_sum {V : Type} [Fintype V] (p : MvPolynomial V (ZMod 2))
    (hp : IsMultilinear p) : p = ∑ S : Finset V, monoCoeffs p S • xMon S := by
  rw [← monoPoly_sum, monoPoly_coeffs, ml_of_multilinear p hp]

end ProofComplexity.BooleanCoordinates
end

section
-- Inlined Solutions.MajorityCoordinateBasis

open Module MvPolynomial AC02Frege
open AC02Frege.BooleanAlgebra AC02Frege.MajorityFunctionBasis AC02Frege.MajorityTensorIndex

namespace AC02Frege.MajorityCoordinateBasis

noncomputable def uncurryFunctions (n ℓ : ℕ) :
    ((Fin n → Fin ℓ → ZMod 2) → ZMod 2) ≃ₗ[ZMod 2]
      ((Fin n × Fin ℓ → ZMod 2) → ZMod 2) where
  toFun f x := f (fun i a => x (i, a))
  invFun f x := f (fun v => x v.1 v.2)
  left_inv f := by funext x; rfl
  right_inv f := by funext x; rfl
  map_add' f g := rfl
  map_smul' c f := rfl

noncomputable def coordinateBasis (n ℓ : ℕ) (hℓ : Odd ℓ) :
    Basis (GlobalLight n ℓ × Finset (Fin n)) (ZMod 2)
      ((Fin n × Fin ℓ → ZMod 2) → ZMod 2) :=
  ((allBlockFunctionBasis n ℓ hℓ).reindex (tensorIndexEquiv n ℓ)).map (uncurryFunctions n ℓ)

theorem xMon_eval_blocks {n ℓ : ℕ} (A : Finset (Fin n × Fin ℓ))
    (x : Fin n × Fin ℓ → ZMod 2) :
    eval x (xMon A) = ∏ i : Fin n, eval (fun a => x (i, a)) (xMon (tensorSection A i)) := by
  classical
  simp only [xMon_eval, tensorSection, Finset.prod_filter]
  rw [← Finset.prod_product']
  simp only [Finset.univ_product_univ]
  rw [← Finset.prod_filter]
  simp

theorem hBlock_eval {n ℓ : ℕ} (i : Fin n) (x : Fin n × Fin ℓ → ZMod 2) :
    eval x (hBlock i) = eval (fun a => x (i, a)) (majOne ℓ) := by
  exact eval_rename_prod_mk _ _ _

theorem coordinateBasis_apply {n ℓ : ℕ} (hℓ : Odd ℓ) (A : GlobalLight n ℓ)
    (J : Finset (Fin n)) (x : Fin n × Fin ℓ → ZMod 2) :
    coordinateBasis n ℓ hℓ (A, J) x =
      eval x (xMon A.1) * ∏ i ∈ J, eval x (hBlock i) := by
  classical
  rw [coordinateBasis, Basis.map_apply, Basis.reindex_apply]
  change allBlockFunctionBasis n ℓ hℓ (pack A J) (fun i a => x (i, a)) = _
  rw [allBlockFunctionBasis_apply]
  have hf (i : Fin n) : blockFunctionBasis ℓ hℓ (pack A J i) (fun a => x (i, a)) =
      eval (fun a => x (i, a)) (xMon (tensorSection A.1 i)) *
        (if i ∈ J then eval x (hBlock i) else 1) := by
    unfold pack
    split_ifs with hi
    · rw [blockFunctionBasis_inr, hBlock_eval]
      exact mul_comm _ _
    · rw [blockFunctionBasis_inl, mul_one]
      rfl
  simp only [hf]
  rw [Finset.prod_mul_distrib, ← xMon_eval_blocks, ← Finset.prod_filter]
  simp

theorem eval_bind_majority {n ℓ : ℕ} (p : MvPolynomial (Fin n) (ZMod 2))
    (x : Fin n × Fin ℓ → ZMod 2) :
    eval x (bind₁ (fun i => hBlock (ℓ := ℓ) i) p) = eval (fun i => eval x (hBlock i)) p := by
  exact eval₂Hom_bind₁ _ _ _ _

theorem coordinateBasis_polynomial {n ℓ : ℕ} (hℓ : Odd ℓ) (A : GlobalLight n ℓ)
    (J : Finset (Fin n)) (x : Fin n × Fin ℓ → ZMod 2) :
    coordinateBasis n ℓ hℓ (A, J) x =
      eval x (xMon A.1 * bind₁ (fun i => hBlock (ℓ := ℓ) i) (xMon J)) := by
  rw [map_mul, eval_bind_majority, xMon_eval J, coordinateBasis_apply]

end AC02Frege.MajorityCoordinateBasis
end

section
-- Inlined Solutions.MajorityExpansionCoordinates

open Module MvPolynomial AC02Frege
open AC02Frege.BooleanAlgebra AC02Frege.MajorityTensorIndex AC02Frege.MajorityCoordinateBasis
open ProofComplexity.BooleanCoordinates

namespace AC02Frege.MajorityExpansionCoordinates

noncomputable def familyCoeffs {n ℓ : ℕ}
    (q : Finset (Fin n × Fin ℓ) → MvPolynomial (Fin n) (ZMod 2)) :
    GlobalLight n ℓ × Finset (Fin n) → ZMod 2 :=
  fun AJ => monoCoeffs (q AJ.1.1) AJ.2

noncomputable def coeffFamily {n ℓ : ℕ}
    (c : GlobalLight n ℓ × Finset (Fin n) → ZMod 2) :
    Finset (Fin n × Fin ℓ) → MvPolynomial (Fin n) (ZMod 2) :=
  fun A => if hA : A ∈ lightSets n ℓ then monoPoly (fun J => c (⟨A, hA⟩, J)) else 0

theorem coeffFamily_multilinear {n ℓ : ℕ}
    (c : GlobalLight n ℓ × Finset (Fin n) → ZMod 2) :
    ∀ A, IsMultilinear (coeffFamily c A) := by
  intro A
  unfold coeffFamily
  split_ifs
  · exact monoPoly_multilinear _
  · simpa only [map_zero] using ml_multilinear (0 : MvPolynomial (Fin n) (ZMod 2))

theorem coeffFamily_off_light {n ℓ : ℕ}
    (c : GlobalLight n ℓ × Finset (Fin n) → ZMod 2) :
    ∀ A ∉ lightSets n ℓ, coeffFamily c A = 0 := by
  intro A hA
  simp only [coeffFamily, dif_neg hA]

theorem familyCoeffs_coeffFamily {n ℓ : ℕ}
    (c : GlobalLight n ℓ × Finset (Fin n) → ZMod 2) :
    familyCoeffs (coeffFamily c) = c := by
  classical
  funext AJ
  rcases AJ with ⟨A, J⟩
  simp only [familyCoeffs, coeffFamily, dif_pos A.2, monoCoeffs_poly]

theorem coeffFamily_familyCoeffs {n ℓ : ℕ}
    (q : Finset (Fin n × Fin ℓ) → MvPolynomial (Fin n) (ZMod 2))
    (hq : ∀ A, IsMultilinear (q A)) (hz : ∀ A ∉ lightSets n ℓ, q A = 0) :
    coeffFamily (familyCoeffs q) = q := by
  classical
  funext A
  unfold coeffFamily
  split_ifs with hA
  · change monoPoly (monoCoeffs (q A)) = q A
    rw [monoPoly_coeffs, ml_of_multilinear _ (hq A)]
  · exact (hz A hA).symm

theorem eval_as_monoCoeffs {V : Type} [Fintype V]
    (p : MvPolynomial V (ZMod 2)) (hp : IsMultilinear p) (x : V → ZMod 2) :
    eval x p = ∑ S : Finset V, monoCoeffs p S * ∏ i ∈ S, x i := by
  classical
  conv_lhs => rw [monoCoeffs_sum p hp]
  simp only [map_sum, smul_eval, xMon_eval]

theorem eval_expand_as_basis {n ℓ : ℕ} (hℓ : Odd ℓ)
    (q : Finset (Fin n × Fin ℓ) → MvPolynomial (Fin n) (ZMod 2))
    (hq : ∀ A, IsMultilinear (q A)) :
    (fun x : Fin n × Fin ℓ → ZMod 2 => eval x (expand q)) =
      (coordinateBasis n ℓ hℓ).equivFun.symm (familyCoeffs q) := by
  classical
  rw [Basis.equivFun_symm_apply]
  funext x
  simp only [expand, eval_ml, map_sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Fintype.sum_prod_type]
  rw [← Finset.sum_coe_sort (lightSets n ℓ)]
  apply Finset.sum_congr rfl
  intro A _
  rw [map_mul, eval_bind_majority, eval_as_monoCoeffs _ (hq A.1), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro J _
  rw [coordinateBasis_apply]
  change eval x (xMon A.1) * (monoCoeffs (q A.1) J * _) =
    monoCoeffs (q A.1) J * (eval x (xMon A.1) * _)
  ring

theorem majority_expansion {n ℓ : ℕ} (hℓ : Odd ℓ)
    (p : MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) : ∃! q, IsExpansion p q := by
  classical
  let b := coordinateBasis n ℓ hℓ
  let f : (Fin n × Fin ℓ → ZMod 2) → ZMod 2 := fun x => eval x p
  let c := b.equivFun f
  have heval : (fun x : Fin n × Fin ℓ → ZMod 2 => eval x (expand (coeffFamily c))) = f := by
    rw [eval_expand_as_basis hℓ _ (coeffFamily_multilinear c), familyCoeffs_coeffFamily]
    exact b.equivFun.symm_apply_apply f
  refine ⟨coeffFamily c, ⟨coeffFamily_multilinear c, coeffFamily_off_light c, ?_⟩, ?_⟩
  · apply multilinear_ext (ml_multilinear _) (ml_multilinear _)
    intro x
    rw [eval_ml p x]
    exact congrFun heval x
  · intro q hq
    obtain ⟨hml, hz, hexp⟩ := hq
    have hcrepr : familyCoeffs q = c := by
      apply b.equivFun.symm.injective
      rw [← eval_expand_as_basis hℓ q hml]
      change (fun x : Fin n × Fin ℓ → ZMod 2 => eval x (expand q)) = b.equivFun.symm (b.equivFun f)
      rw [b.equivFun.symm_apply_apply]
      funext x
      rw [hexp, eval_ml]
    calc
      q = coeffFamily (familyCoeffs q) := (coeffFamily_familyCoeffs q hml hz).symm
      _ = coeffFamily c := congrArg coeffFamily hcrepr

end AC02Frege.MajorityExpansionCoordinates
end

section
-- Inlined Solutions.MajorityGrading

open Module MvPolynomial AC02Frege
open AC02Frege.BooleanAlgebra AC02Frege.BooleanBasis AC02Frege.MajorityFoundation
open AC02Frege.MajorityIdeal AC02Frege.MajorityBasis AC02Frege.MajorityFunctionBasis
open AC02Frege.MajorityTensorIndex AC02Frege.MajorityCoordinateBasis

namespace AC02Frege.MajorityGrading

theorem light_block_repr_inr (ℓ : ℕ) (hℓ : Odd ℓ) (S : Finset (Fin ℓ))
    (hS : S.card ≤ ℓ / 2) (T : LightIndex ℓ) :
    (blockFunctionBasis ℓ hℓ).repr (fun x => eval x (xMon S)) (Sum.inr T) = 0 := by
  have heq : (fun x => eval x (xMon S)) = blockFunctionBasis ℓ hℓ (Sum.inl ⟨S, hS⟩) := by
    funext x
    exact (blockFunctionBasis_inl ℓ hℓ ⟨S, hS⟩ x).symm
  rw [heq, Basis.repr_self]
  simp

theorem heavy_block_repr_inl (ℓ : ℕ) (hℓ : Odd ℓ) (S : Finset (Fin ℓ))
    (hS : ℓ / 2 < S.card) (T : LightIndex ℓ) :
    (blockFunctionBasis ℓ hℓ).repr (fun x => eval x (xMon S)) (Sum.inl T) = 0 := by
  have hideal : xMon S ∈ (majorityMul ℓ).range := by
    rw [ideal_eq_heavy]
    exact Submodule.subset_span ⟨S, hS, rfl⟩
  obtain ⟨v, hvm, hvd, hveq⟩ := ideal_has_light_preimage ℓ hℓ (xMon S) hideal
  let v' : LightSpace ℓ := ⟨v, (mem_light_iff _ _).mpr ⟨hvm, hvd⟩⟩
  have heq : (fun x => eval x (xMon S)) = pairEvaluationEquiv ℓ hℓ (0, v') := by
    funext x
    change eval x (xMon S) = eval x (0 + majorityMul ℓ v)
    rw [zero_add, hveq]
  rw [heq]
  change ((lightBasis ℓ).prod (lightBasis ℓ)).repr
    ((pairEvaluationEquiv ℓ hℓ).symm ((pairEvaluationEquiv ℓ hℓ) (0, v'))) (Sum.inl T) = 0
  rw [LinearEquiv.symm_apply_apply, Basis.prod_repr_inl]
  simp

theorem block_repr_zero_wrong_flag (ℓ : ℕ) (hℓ : Odd ℓ) (S : Finset (Fin ℓ))
    (k : LightIndex ℓ ⊕ LightIndex ℓ)
    (hk : k.isRight ≠ decide (ℓ / 2 < S.card)) :
    (blockFunctionBasis ℓ hℓ).repr (fun x => eval x (xMon S)) k = 0 := by
  classical
  cases k with
  | inl T =>
    have hS : ℓ / 2 < S.card := by simpa using hk
    exact heavy_block_repr_inl ℓ hℓ S hS T
  | inr T =>
    have hS : S.card ≤ ℓ / 2 := by simpa using hk
    exact light_block_repr_inr ℓ hℓ S hS T

theorem scalar_monomial_coordinate {n ℓ : ℕ} (hℓ : Odd ℓ) (T : Finset (Fin n × Fin ℓ))
    (A : GlobalLight n ℓ) (J : Finset (Fin n)) :
    (coordinateBasis n ℓ hℓ).repr (fun x => eval x (xMon T)) (A, J) =
      ∏ i : Fin n, (blockFunctionBasis ℓ hℓ).repr
        (fun x => eval x (xMon (tensorSection T i))) (pack A J i) := by
  have hfun : (fun x : Fin n × Fin ℓ → ZMod 2 => eval x (xMon T)) =
      uncurryFunctions n ℓ (fun x => ∏ i : Fin n, eval (x i) (xMon (tensorSection T i))) := by
    funext x
    exact xMon_eval_blocks T x
  rw [hfun]
  change (allBlockFunctionBasis n ℓ hℓ).repr
    ((uncurryFunctions n ℓ).symm ((uncurryFunctions n ℓ) _)) ((tensorIndexEquiv n ℓ).symm (A, J)) = _
  rw [LinearEquiv.symm_apply_apply]
  exact ProofComplexity.productFunctionBasis_repr
    (fun _ : Fin n => blockFunctionBasis ℓ hℓ)
    (fun i x => eval x (xMon (tensorSection T i))) (pack A J)

theorem scalar_monomial_zero_other_grade {n ℓ : ℕ} (hℓ : Odd ℓ)
    (T : Finset (Fin n × Fin ℓ)) (A : GlobalLight n ℓ) (J : Finset (Fin n))
    (hJ : J ≠ heavyBlocks T) :
    (coordinateBasis n ℓ hℓ).repr (fun x => eval x (xMon T)) (A, J) = 0 := by
  classical
  rw [scalar_monomial_coordinate]
  have hex : ∃ i : Fin n, (pack A J i).isRight ≠ decide (ℓ / 2 < (tensorSection T i).card) := by
    by_contra hn
    push Not at hn
    apply hJ
    ext i
    have hi := hn i
    rw [section_card] at hi
    by_cases hij : i ∈ J <;> simp [pack, hij, heavyBlocks] at hi ⊢
    · exact hi
    · exact hi
  obtain ⟨i, hi⟩ := hex
  exact Finset.prod_eq_zero (Finset.mem_univ i) (block_repr_zero_wrong_flag ℓ hℓ _ _ hi)

end AC02Frege.MajorityGrading
end

section
-- Inlined Solutions.BooleanCoordinateDegree

open Module MvPolynomial AC02Frege
open AC02Frege.BooleanAlgebra AC02Frege.BooleanBasis

namespace ProofComplexity.BooleanCoordinates

theorem indicator_injective {V : Type} :
    Function.Injective (fun S : Finset V => Finsupp.indicator S (fun _ _ => (1 : ℕ))) := by
  intro S T h
  have hs := congrArg Finsupp.support h
  simpa only [indicator_support] using hs

theorem monoCoeffs_eq_coeff {V : Type} [Fintype V] (p : MvPolynomial V (ZMod 2))
    (S : Finset V) : monoCoeffs p S = (ML p).coeff (Finsupp.indicator S (fun _ _ => 1)) := by
  classical
  have h := congrArg (fun q : MvPolynomial V (ZMod 2) =>
    q.coeff (Finsupp.indicator S (fun _ _ => 1))) (monoPoly_coeffs p)
  rw [monoPoly_sum] at h
  simp only [coeff_sum, coeff_smul, xMon_eq_monomial, coeff_monomial,
    indicator_injective.eq_iff] at h
  simpa using h

theorem multilinear_degree_le_iff {V : Type} [Fintype V]
    (p : MvPolynomial V (ZMod 2)) (hp : IsMultilinear p) (Q : ℕ) :
    p.totalDegree ≤ Q ↔ ∀ S : Finset V, monoCoeffs p S ≠ 0 → S.card ≤ Q := by
  classical
  constructor
  · intro hd S hS
    rw [monoCoeffs_eq_coeff, ml_of_multilinear _ hp] at hS
    have hs := le_totalDegree (mem_support_iff.mpr hS)
    have hsq : ∀ i, (Finsupp.indicator S (fun _ _ => (1 : ℕ))) i ≤ 1 := by
      intro i
      simp only [Finsupp.indicator_apply]
      split_ifs <;> omega
    rw [squarefree_sum _ hsq, indicator_support] at hs
    omega
  · intro hc
    conv_lhs => rw [monoCoeffs_sum p hp]
    apply totalDegree_finsetSum_le
    intro S _
    by_cases hS : monoCoeffs p S = 0
    · simp only [hS, zero_smul, totalDegree_zero, zero_le]
    · exact (totalDegree_smul_le _ _).trans (by rw [xMon_totalDegree]; exact hc S hS)

theorem monoCoeffs_zero {V : Type} [Fintype V] :
    monoCoeffs (0 : MvPolynomial V (ZMod 2)) = 0 := by
  simp [monoCoeffs]

theorem monoPoly_zero {V : Type} [Fintype V] :
    monoPoly (0 : Finset V → ZMod 2) = 0 := by
  simp [monoPoly]

theorem monoCoeffs_eq_zero_iff {V : Type} [Fintype V]
    (p : MvPolynomial V (ZMod 2)) (hp : IsMultilinear p) : monoCoeffs p = 0 ↔ p = 0 := by
  constructor
  · intro h
    have heq := congrArg monoPoly h
    simpa only [monoPoly_coeffs, ml_of_multilinear _ hp, monoPoly_zero] using heq
  · rintro rfl
    exact monoCoeffs_zero

end ProofComplexity.BooleanCoordinates
end

section
-- Inlined Solutions.MajorityGradeProjection

open Module MvPolynomial AC02Frege
open AC02Frege.BooleanAlgebra AC02Frege.MajorityTensorIndex AC02Frege.MajorityCoordinateBasis
open AC02Frege.MajorityExpansionCoordinates AC02Frege.MajorityGrading
open ProofComplexity.BooleanCoordinates

namespace AC02Frege.MajorityGradeProjection

noncomputable def coords {n ℓ : ℕ} (hℓ : Odd ℓ) (p : MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) :
    GlobalLight n ℓ × Finset (Fin n) → ZMod 2 :=
  (coordinateBasis n ℓ hℓ).equivFun (fun x => eval x p)

theorem coords_scalar_sum {n ℓ : ℕ} (hℓ : Odd ℓ)
    (p : MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) (hp : IsMultilinear p)
    (A : GlobalLight n ℓ) (J : Finset (Fin n)) :
    coords hℓ p (A, J) = ∑ T : Finset (Fin n × Fin ℓ), monoCoeffs p T *
      (coordinateBasis n ℓ hℓ).repr (fun x => eval x (xMon T)) (A, J) := by
  classical
  have heval : (fun x : Fin n × Fin ℓ → ZMod 2 => eval x p) =
      ∑ T : Finset (Fin n × Fin ℓ), monoCoeffs p T • (fun x => eval x (xMon T)) := by
    funext x
    conv_lhs => rw [monoCoeffs_sum p hp]
    simp only [map_sum, smul_eval, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  unfold coords
  rw [heval, map_sum]
  simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Basis.equivFun_apply,
    Finsupp.coe_finsetSum, Finsupp.coe_smul]

noncomputable def gradePart {n ℓ : ℕ}
    (p : MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) (H : Finset (Fin n)) :
    MvPolynomial (Fin n × Fin ℓ) (ZMod 2) :=
  monoPoly (fun T => if heavyBlocks T = H then monoCoeffs p T else 0)

theorem gradePart_multilinear {n ℓ : ℕ}
    (p : MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) (H : Finset (Fin n)) :
    IsMultilinear (gradePart p H) := monoPoly_multilinear _

theorem gradePart_coeffs {n ℓ : ℕ}
    (p : MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) (H : Finset (Fin n))
    (T : Finset (Fin n × Fin ℓ)) :
    monoCoeffs (gradePart p H) T = if heavyBlocks T = H then monoCoeffs p T else 0 := by
  exact congrFun (monoCoeffs_poly _) T

theorem coords_gradePart {n ℓ : ℕ} (hℓ : Odd ℓ)
    (p : MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) (hp : IsMultilinear p)
    (H : Finset (Fin n)) (A : GlobalLight n ℓ) (J : Finset (Fin n)) :
    coords hℓ (gradePart p H) (A, J) = if J = H then coords hℓ p (A, J) else 0 := by
  classical
  rw [coords_scalar_sum hℓ _ (gradePart_multilinear p H)]
  simp only [gradePart_coeffs]
  by_cases hJ : J = H
  · rw [if_pos hJ, coords_scalar_sum hℓ p hp]
    apply Finset.sum_congr rfl
    intro T _
    by_cases hT : heavyBlocks T = H
    · rw [if_pos hT]
    · rw [if_neg hT, zero_mul, scalar_monomial_zero_other_grade hℓ T A J (by simpa [hJ] using Ne.symm hT),
        mul_zero]
  · rw [if_neg hJ]
    apply Finset.sum_eq_zero
    intro T _
    by_cases hT : heavyBlocks T = H
    · rw [if_pos hT, scalar_monomial_zero_other_grade hℓ T A J (by simpa [hT] using hJ), mul_zero]
    · rw [if_neg hT, zero_mul]

theorem coords_zero_iff {n ℓ : ℕ} (hℓ : Odd ℓ)
    (p : MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) (hp : IsMultilinear p) :
    coords hℓ p = 0 ↔ p = 0 := by
  constructor
  · intro h
    have he : (fun x : Fin n × Fin ℓ → ZMod 2 => eval x p) = 0 := by
      exact (coordinateBasis n ℓ hℓ).equivFun.injective (by simpa only [coords, map_zero] using h)
    apply multilinear_ext hp
      (by simpa only [map_zero] using ml_multilinear (0 : MvPolynomial (Fin n × Fin ℓ) (ZMod 2)))
    intro x
    simpa only [map_zero, Pi.zero_apply] using congrFun he x
  · rintro rfl
    have heval : (fun x : Fin n × Fin ℓ → ZMod 2 =>
        eval x (0 : MvPolynomial (Fin n × Fin ℓ) (ZMod 2))) = 0 := by
      funext x
      exact map_zero _
    rw [coords, heval, map_zero]

theorem grading_bound_iff {n ℓ : ℕ} (hℓ : Odd ℓ)
    (p : MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) (hp : IsMultilinear p) (Q : ℕ) :
    (∀ A : GlobalLight n ℓ, ∀ J : Finset (Fin n), coords hℓ p (A, J) ≠ 0 → J.card ≤ Q) ↔
      ∀ T : Finset (Fin n × Fin ℓ), monoCoeffs p T ≠ 0 → (heavyBlocks T).card ≤ Q := by
  classical
  constructor
  · intro hc T hT
    by_contra hd
    have hz : coords hℓ (gradePart p (heavyBlocks T)) = 0 := by
      funext AJ
      rcases AJ with ⟨A, J⟩
      rw [coords_gradePart hℓ p hp]
      split_ifs with hJ
      · have hzero : coords hℓ p (A, J) = 0 := by
          by_contra hne
          have := hc A J hne
          rw [hJ] at this
          exact hd this
        exact hzero
      · rfl
    have hpzero := (coords_zero_iff hℓ _ (gradePart_multilinear p _)).mp hz
    have hm := congrArg (fun q => monoCoeffs q T) hpzero
    rw [gradePart_coeffs, if_pos rfl, monoCoeffs_zero] at hm
    exact hT hm
  · intro hm A J hc
    by_contra hd
    apply hc
    rw [coords_scalar_sum hℓ p hp]
    apply Finset.sum_eq_zero
    intro T _
    by_cases hT : heavyBlocks T = J
    · have hzero : monoCoeffs p T = 0 := by
        by_contra hne
        have := hm T hne
        rw [hT] at this
        exact hd this
      rw [hzero, zero_mul]
    · rw [scalar_monomial_zero_other_grade hℓ T A J (Ne.symm hT), mul_zero]

end AC02Frege.MajorityGradeProjection
end

section
-- Inlined Solutions.MajorityCoefficientDegree

open Module MvPolynomial AC02Frege
open AC02Frege.BooleanAlgebra AC02Frege.BooleanBasis AC02Frege.MajorityTensorIndex
open AC02Frege.MajorityCoordinateBasis AC02Frege.MajorityExpansionCoordinates
open AC02Frege.MajorityGradeProjection ProofComplexity.BooleanCoordinates

namespace AC02Frege.MajorityCoefficientDegree

theorem coeffPoly_expansion {n ℓ : ℕ} (hℓ : Odd ℓ)
    (p : MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) : IsExpansion p (coeffPoly p) := by
  classical
  have he := majority_expansion hℓ p
  unfold coeffPoly
  rw [dif_pos he]
  exact he.choose_spec.1

theorem coeffPoly_coords {n ℓ : ℕ} (hℓ : Odd ℓ)
    (p : MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) :
    familyCoeffs (coeffPoly p) = coords hℓ p := by
  obtain ⟨hml, _, hexp⟩ := coeffPoly_expansion hℓ p
  apply (coordinateBasis n ℓ hℓ).equivFun.symm.injective
  rw [← eval_expand_as_basis hℓ _ hml]
  change (fun x : Fin n × Fin ℓ → ZMod 2 => eval x (expand (coeffPoly p))) =
    (coordinateBasis n ℓ hℓ).equivFun.symm
      ((coordinateBasis n ℓ hℓ).equivFun (fun x => eval x p))
  rw [LinearEquiv.symm_apply_apply]
  funext x
  rw [hexp, eval_ml]

theorem sup_poly_degree_le_iff {I V : Type} [Fintype V] (s : Finset I)
    (q : I → MvPolynomial V (ZMod 2)) (Q : ℕ) :
    s.sup (fun A => if q A = 0 then (⊥ : WithBot ℕ) else ((q A).totalDegree : WithBot ℕ)) ≤ (Q : WithBot ℕ) ↔
      ∀ A ∈ s, (q A).totalDegree ≤ Q := by
  classical
  rw [Finset.sup_le_iff]
  constructor
  · intro h A hA
    by_cases hz : q A = 0
    · simp only [hz, totalDegree_zero, zero_le]
    · have hd := h A hA
      rw [if_neg hz] at hd
      exact_mod_cast hd
  · intro h A hA
    by_cases hz : q A = 0
    · simp only [if_pos hz, bot_le]
    · rw [if_neg hz]
      exact_mod_cast h A hA

theorem coeffDeg_le_iff_coords {n ℓ : ℕ} (hℓ : Odd ℓ)
    (p : MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) (Q : ℕ) :
    coeffDeg p ≤ (Q : WithBot ℕ) ↔
      ∀ A : GlobalLight n ℓ, ∀ J : Finset (Fin n), coords hℓ p (A, J) ≠ 0 → J.card ≤ Q := by
  classical
  have hml := (coeffPoly_expansion hℓ p).1
  have hc (A : GlobalLight n ℓ) (J : Finset (Fin n)) :
      monoCoeffs (coeffPoly p A.1) J = coords hℓ p (A, J) :=
    congrFun (coeffPoly_coords hℓ p) (A, J)
  rw [coeffDeg, Finset.sup_le_iff]
  constructor
  · intro hd A J hJ
    have hdeg : (coeffPoly p A.1).totalDegree ≤ Q := by
      by_cases hz : coeffPoly p A.1 = 0
      · simp only [hz, totalDegree_zero, zero_le]
      · have hb := hd A.1 A.2
        rw [if_neg hz] at hb
        exact_mod_cast hb
    apply (multilinear_degree_le_iff _ (hml A.1) Q).mp hdeg J
    rw [hc]
    exact hJ
  · intro hd A hA
    by_cases hz : coeffPoly p A = 0
    · rw [if_pos hz]
      exact bot_le
    · rw [if_neg hz]
      apply WithBot.coe_le_coe.mpr
      apply (multilinear_degree_le_iff _ (hml A) Q).mpr
      intro J hJ
      exact hd ⟨A, hA⟩ J (by rwa [← hc ⟨A, hA⟩ J])

theorem scalar_coords_bound_iff {n ℓ : ℕ}
    (p : MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) (hp : IsMultilinear p) (Q : ℕ) :
    (∀ T : Finset (Fin n × Fin ℓ), monoCoeffs p T ≠ 0 → (heavyBlocks T).card ≤ Q) ↔
      ∀ s ∈ p.support, (heavyBlocks s.support).card ≤ Q := by
  classical
  constructor
  · intro h s hs
    apply h s.support
    rw [monoCoeffs_eq_coeff, ml_of_multilinear _ hp, ← squarefree_eq_indicator s (hp s hs)]
    exact mem_support_iff.mp hs
  · intro h T hT
    rw [monoCoeffs_eq_coeff, ml_of_multilinear _ hp] at hT
    have hs := h _ (mem_support_iff.mpr hT)
    simpa only [indicator_support] using hs

theorem coeffDeg_threshold {n ℓ : ℕ} (hℓ : Odd ℓ)
    (p : MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) (hp : IsMultilinear p) (Q : ℕ) :
    coeffDeg p ≤ (Q : WithBot ℕ) ↔ ∀ s ∈ p.support, (heavyBlocks s.support).card ≤ Q :=
  (coeffDeg_le_iff_coords hℓ p Q).trans
    ((grading_bound_iff hℓ p hp Q).trans (scalar_coords_bound_iff p hp Q))

theorem coeffDeg_ne_bot {n ℓ : ℕ} (hℓ : Odd ℓ)
    (p : MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) (hp : IsMultilinear p) (hne : p ≠ 0) :
    coeffDeg p ≠ ⊥ := by
  classical
  have hcne : coords hℓ p ≠ 0 := by
    intro hz
    exact hne ((coords_zero_iff hℓ p hp).mp hz)
  obtain ⟨⟨A, J⟩, hAJ⟩ := Function.ne_iff.mp hcne
  have hqne : coeffPoly p A.1 ≠ 0 := by
    intro hz
    have hc := congrFun (coeffPoly_coords hℓ p) (A, J)
    change monoCoeffs (coeffPoly p A.1) J = coords hℓ p (A, J) at hc
    rw [hz, monoCoeffs_zero] at hc
    exact hAJ hc.symm
  have hle := Finset.le_sup (s := lightSets n ℓ)
    (f := fun A => if coeffPoly p A = 0 then (⊥ : WithBot ℕ) else (coeffPoly p A).totalDegree) A.2
  rw [if_neg hqne] at hle
  intro hbot
  change ((coeffPoly p A.1).totalDegree : WithBot ℕ) ≤ coeffDeg p at hle
  rw [hbot] at hle
  simpa using hle

theorem coeffDeg_scalar {n ℓ : ℕ} (hℓ : Odd ℓ)
    (p : MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) (hp : IsMultilinear p) (hne : p ≠ 0) :
    coeffDeg p = ((p.support.sup (fun s => (heavyBlocks s.support).card) : ℕ) : WithBot ℕ) := by
  classical
  obtain ⟨d, hd⟩ := WithBot.ne_bot_iff_exists.mp (coeffDeg_ne_bot hℓ p hp hne)
  have hupper : coeffDeg p ≤
      ((p.support.sup (fun s => (heavyBlocks s.support).card) : ℕ) : WithBot ℕ) :=
    (coeffDeg_threshold hℓ p hp _).mpr (fun s hs => Finset.le_sup (f := fun s => (heavyBlocks s.support).card) hs)
  have hdu : d ≤ p.support.sup (fun s => (heavyBlocks s.support).card) := by
    rw [← hd] at hupper
    exact WithBot.coe_le_coe.mp hupper
  have hlower : p.support.sup (fun s => (heavyBlocks s.support).card) ≤ d := by
    apply Finset.sup_le
    exact (coeffDeg_threshold hℓ p hp d).mp (by rw [← hd]; exact le_rfl)
  rw [← hd, Nat.le_antisymm hdu hlower]
  rfl

end AC02Frege.MajorityCoefficientDegree
end

section
-- Inlined Solutions.MajorityFibreModel

open Module MvPolynomial AC02Frege SemAC02
open AC02Frege.BooleanAlgebra AC02Frege.MajorityFoundation AC02Frege.MajorityTensorIndex
open AC02Frege.MajorityCoordinateBasis AC02Frege.MajorityCoefficientDegree

namespace AC02Frege.MajorityFibreModel

def ones {ℓ : ℕ} (X : Fin ℓ → Bool) : Finset (Fin ℓ) :=
  Finset.univ.filter (fun i => X i = true)

def minorityZero (ℓ : ℕ) : (Fin ℓ → Bool) → Bool :=
  fun X => decide ((ones X).card ≤ ℓ / 2)

theorem minorityZero_antitone (ℓ : ℕ) : Antitone (minorityZero ℓ) := by
  intro X Y hXY
  apply Bool.le_iff_imp.mpr
  intro hY
  simp only [minorityZero, decide_eq_true_eq] at hY ⊢
  have hsub : ones X ⊆ ones Y := by
    intro i hi
    simp only [ones, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    have hle := hXY i
    rw [hi] at hle
    exact Bool.eq_true_of_true_le hle
  exact (Finset.card_le_card hsub).trans hY

theorem ones_indicator (ℓ : ℕ) (S : Finset (Fin ℓ)) : ones (indicatorVec S) = S := by
  ext i
  simp [ones, indicatorVec]

theorem minorityZero_indicator (ℓ : ℕ) (S : Finset (Fin ℓ)) :
    minorityZero ℓ (indicatorVec S) = true ↔ S.card ≤ ℓ / 2 := by
  simp only [minorityZero, ones_indicator, decide_eq_true_eq]

theorem ones_not_card (ℓ : ℕ) (X : Fin ℓ → Bool) :
    (ones (fun i => !X i)).card + (ones X).card = ℓ := by
  have heq : ones (fun i => !X i) = (ones X)ᶜ := by
    ext i
    cases h : X i <;> simp [ones, h]
  rw [heq, Finset.card_compl]
  have hc := Finset.card_le_univ (ones X)
  simp only [Fintype.card_fin] at *
  omega

theorem fibre_hBlock {n ℓ : ℕ} (hℓ : Odd ℓ) (z : Fin n → Bool)
    (X : Fin n × Fin ℓ → Bool) (hX : InFiber (minorityZero ℓ) z X) (i : Fin n) :
    eval (toF2 X) (hBlock i) = toF2 z i := by
  have hXi := hX i
  have hcard : Finset.univ.filter (fun j => toF2 X (i, j) = 1) = ones (fun j => X (i, j)) := by
    ext j
    cases h : X (i, j) <;> simp [toF2, ones, h]
  rw [hBlock_eval, majOne_eval]
  change (if ℓ / 2 < (Finset.univ.filter (fun j => toF2 X (i, j) = 1)).card then 1 else 0) = toF2 z i
  rw [hcard]
  cases hz : z i
  · simp only [InFiber, hz, Bool.false_eq_true, ↓reduceIte, minorityZero, decide_eq_true_eq] at hXi
    rw [if_neg (by omega)]
    simp [toF2, hz]
  · simp only [InFiber, hz, ↓reduceIte, minorityZero, decide_eq_true_eq] at hXi
    have hc := ones_not_card ℓ (fun j => X (i, j))
    have hh : ℓ / 2 < (ones (fun j => X (i, j))).card := by
      rcases hℓ with ⟨k, hk⟩
      omega
    rw [if_pos hh]
    simp [toF2, hz]

theorem lnSupport_iff_light {n ℓ : ℕ} (A : Finset (Fin n × Fin ℓ)) :
    IsLnSupport (minorityZero ℓ) A ↔ A ∈ lightSets n ℓ := by
  simp only [IsLnSupport, minorityZero_indicator, lightSets, Finset.mem_filter, Finset.mem_univ, true_and]
  apply forall_congr'
  intro i
  change (tensorSection A i).card ≤ ℓ / 2 ↔ (blockPart A i).card ≤ ℓ / 2
  rw [section_card]

def globalIndexEquiv (n ℓ : ℕ) :
    SemAC02.FibreBasis.GlobalIndex (minorityZero ℓ) n ≃ GlobalLight n ℓ where
  toFun A := ⟨A.1, (lnSupport_iff_light A.1).mp A.2⟩
  invFun A := ⟨A.1, (lnSupport_iff_light A.1).mpr A.2⟩
  left_inv A := rfl
  right_inv A := rfl

theorem toF2_surjective {V : Type} : Function.Surjective (toF2 (V := V)) := by
  intro x
  refine ⟨fun i => decide (x i = 1), ?_⟩
  funext i
  rcases eq_zero_or_one (x i) with hi | hi <;> simp [toF2, hi]

theorem multilinear_ext_bool {V : Type} [Finite V] (p q : MvPolynomial V (ZMod 2))
    (hp : IsMultilinear p) (hq : IsMultilinear q)
    (he : ∀ X : V → Bool, eval (toF2 X) p = eval (toF2 X) q) : p = q := by
  apply multilinear_ext hp hq
  intro x
  obtain ⟨X, rfl⟩ := toF2_surjective x
  exact he X

end AC02Frege.MajorityFibreModel
end

section
-- Inlined Solutions.MajorityCoefficientFibres

open Module MvPolynomial AC02Frege SemAC02
open AC02Frege.BooleanAlgebra AC02Frege.MajorityTensorIndex AC02Frege.MajorityCoordinateBasis
open AC02Frege.MajorityExpansionCoordinates AC02Frege.MajorityCoefficientDegree
open AC02Frege.MajorityFibreModel

namespace AC02Frege.MajorityCoefficientFibres

theorem subst_on_fibre {n ℓ : ℕ} (hℓ : Odd ℓ) (z : Fin n → Bool)
    (X : Fin n × Fin ℓ → Bool) (hX : InFiber (minorityZero ℓ) z X)
    (q : MvPolynomial (Fin n) (ZMod 2)) :
    eval (toF2 X) (bind₁ (fun i => hBlock (ℓ := ℓ) i) q) = eval (toF2 z) q := by
  rw [eval_bind_majority]
  have heq : (fun i => eval (toF2 X) (hBlock (ℓ := ℓ) i)) = toF2 z := by
    funext i
    exact fibre_hBlock hℓ z X hX i
  rw [heq]

theorem coefficient_on_fibre {n ℓ : ℕ} (hℓ : Odd ℓ)
    (p : MvPolynomial (Fin n × Fin ℓ) (ZMod 2))
    (S : SemAC02.FibreBasis.GlobalIndex (minorityZero ℓ) n) (z : Fin n → Bool) :
    SemAC02.FibreCoordinates.coordinates (minorityZero ℓ) (minorityZero_antitone ℓ) p S z =
      eval (toF2 z) (coeffPoly p S.1) := by
  classical
  have hc : ∀ (z : Fin n → Bool) (X : Fin n × Fin ℓ → Bool), InFiber (minorityZero ℓ) z X →
      eval (toF2 X) p = ∑ S : SemAC02.FibreBasis.GlobalIndex (minorityZero ℓ) n,
        eval (toF2 z) (coeffPoly p S.1) * eval (toF2 X) (xMon S.1) := by
    intro z X hX
    have he := congrArg (eval (toF2 X)) (coeffPoly_expansion hℓ p).2.2
    change eval (toF2 X) (ML (∑ A ∈ lightSets n ℓ,
      xMon A * bind₁ (fun i => hBlock (ℓ := ℓ) i) (coeffPoly p A))) = eval (toF2 X) (ML p) at he
    rw [eval_ml, eval_ml, map_sum] at he
    simp only [map_mul, subst_on_fibre hℓ z X hX] at he
    have hsum : (∑ A ∈ lightSets n ℓ, eval (toF2 X) (xMon A) * eval (toF2 z) (coeffPoly p A)) =
        ∑ S : SemAC02.FibreBasis.GlobalIndex (minorityZero ℓ) n,
          eval (toF2 z) (coeffPoly p S.1) * eval (toF2 X) (xMon S.1) := by
      rw [← Finset.sum_coe_sort (lightSets n ℓ)]
      rw [← (globalIndexEquiv n ℓ).sum_comp
        (fun A : GlobalLight n ℓ => eval (toF2 X) (xMon A.1) * eval (toF2 z) (coeffPoly p A.1))]
      apply Finset.sum_congr rfl
      intro A _
      exact mul_comm _ _
    exact he.symm.trans hsum
  exact (SemAC02.FibreCoordinates.coordinates_unique (minorityZero ℓ) (minorityZero_antitone ℓ)
    p (fun S z => eval (toF2 z) (coeffPoly p S.1)) hc S z).symm

theorem coeffPoly_congr {n ℓ : ℕ} (hℓ : Odd ℓ)
    (p q : MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) (hpq : ML p = ML q) :
    coeffPoly p = coeffPoly q := by
  have hq := coeffPoly_expansion hℓ q
  have hq' : IsExpansion p (coeffPoly q) := ⟨hq.1, hq.2.1, hq.2.2.trans hpq.symm⟩
  exact (majority_expansion hℓ p).unique (coeffPoly_expansion hℓ p) hq'

theorem light_product_degree {n ℓ : ℕ} (hℓ : Odd ℓ)
    (B A : GlobalLight n ℓ) (v : MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) :
    (coeffPoly (xMon B.1 * v) A.1).totalDegree ≤ v.totalDegree := by
  let g := minorityZero ℓ
  let hg := minorityZero_antitone ℓ
  let S := (globalIndexEquiv n ℓ).symm A
  have hf : xMon B.1 ∈ lnSpan g n := Submodule.subset_span
    ⟨B.1, (lnSupport_iff_light B.1).mpr B.2, rfl⟩
  have hc := SemAC02.CoefficientControl.coefficient_degree g hg (xMon B.1) hf v S
  obtain ⟨r, hr, he⟩ := (SemAC02.CoordinateSpaces.mem_degreeSpace _).mp hc
  have heq : ML r = coeffPoly (xMon B.1 * v) A.1 := by
    apply multilinear_ext_bool _ _ (ml_multilinear _) ((coeffPoly_expansion hℓ _).1 A.1)
    intro z
    rw [eval_ml]
    exact (he z).trans (coefficient_on_fibre hℓ (xMon B.1 * v) S z)
  rw [← heq]
  exact (AC02Frege.BooleanFlip.ml_totalDegree_le r).trans hr

theorem light_product_blocks {n ℓ : ℕ} (hℓ : Odd ℓ)
    (B A : GlobalLight n ℓ) (v : MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) :
    (coeffPoly (xMon B.1 * v) A.1).totalDegree ≤ (v.vars.image Prod.fst).card := by
  classical
  let g := minorityZero ℓ
  let hg := minorityZero_antitone ℓ
  let S := (globalIndexEquiv n ℓ).symm A
  have hf : xMon B.1 ∈ lnSpan g n := Submodule.subset_span
    ⟨B.1, (lnSupport_iff_light B.1).mpr B.2, rfl⟩
  have hc := SemAC02.CoefficientControl.coefficient_locality g hg (xMon B.1) hf v
    (v.vars.image Prod.fst) (fun w hw => Finset.mem_image.mpr ⟨w, hw, rfl⟩) S
  obtain ⟨r, hr, he⟩ := SemAC02.BooleanLocality.represents_local_function (v.vars.image Prod.fst)
    (SemAC02.CoordinateSpaces.coordinateMap g hg S (xMon B.1 * v)) hc
  have heq : ML r = coeffPoly (xMon B.1 * v) A.1 := by
    apply multilinear_ext_bool _ _ (ml_multilinear _) ((coeffPoly_expansion hℓ _).1 A.1)
    intro z
    rw [eval_ml]
    exact (he z).trans (coefficient_on_fibre hℓ (xMon B.1 * v) S z)
  rw [← heq]
  exact (AC02Frege.BooleanFlip.ml_totalDegree_le r).trans hr

theorem light_product_function_bounds {n ℓ : ℕ} (hℓ : Odd ℓ)
    (B A : GlobalLight n ℓ) (v : MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) :
    (coeffPoly (xMon B.1 * v) A.1).totalDegree ≤ (ML v).totalDegree ∧
      (coeffPoly (xMon B.1 * v) A.1).totalDegree ≤ blocksOf v := by
  have he := congrFun (coeffPoly_congr hℓ (xMon B.1 * ML v) (xMon B.1 * v)
    (ml_mul_right _ _)) A.1
  rw [← he]
  exact ⟨light_product_degree hℓ B A (ML v), light_product_blocks hℓ B A (ML v)⟩

end AC02Frege.MajorityCoefficientFibres
end

section
-- Inlined Solutions.MajorityCoefficientAlgebra

open Module MvPolynomial AC02Frege SemAC02
open AC02Frege.BooleanAlgebra AC02Frege.MajorityTensorIndex AC02Frege.MajorityCoefficientDegree
open AC02Frege.MajorityFibreModel AC02Frege.MajorityCoefficientFibres

namespace AC02Frege.MajorityCoefficientAlgebra

theorem multilinear_add {V : Type} (p q : MvPolynomial V (ZMod 2))
    (hp : IsMultilinear p) (hq : IsMultilinear q) : IsMultilinear (p + q) :=
  (mem_restrictDegree V _ 1).mp ((restrictDegree V (ZMod 2) 1).add_mem
    ((mem_restrictDegree V _ 1).mpr hp) ((mem_restrictDegree V _ 1).mpr hq))

theorem multilinear_smul {V : Type} (a : ZMod 2) (p : MvPolynomial V (ZMod 2))
    (hp : IsMultilinear p) : IsMultilinear (a • p) :=
  (mem_restrictDegree V _ 1).mp ((restrictDegree V (ZMod 2) 1).smul_mem a
    ((mem_restrictDegree V _ 1).mpr hp))

theorem coefficient_characterization {n ℓ : ℕ} (hℓ : Odd ℓ)
    (p : MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) (A : GlobalLight n ℓ)
    (r : MvPolynomial (Fin n) (ZMod 2)) (hr : IsMultilinear r)
    (he : ∀ z : Fin n → Bool, SemAC02.FibreCoordinates.coordinates (minorityZero ℓ)
      (minorityZero_antitone ℓ) p ((globalIndexEquiv n ℓ).symm A) z = eval (toF2 z) r) :
    coeffPoly p A.1 = r := by
  apply multilinear_ext_bool _ _ ((coeffPoly_expansion hℓ p).1 A.1) hr
  intro z
  exact (coefficient_on_fibre hℓ p ((globalIndexEquiv n ℓ).symm A) z).symm.trans (he z)

noncomputable def coefficientMap {n ℓ : ℕ} (hℓ : Odd ℓ) (A : GlobalLight n ℓ) :
    MvPolynomial (Fin n × Fin ℓ) (ZMod 2) →ₗ[ZMod 2] MvPolynomial (Fin n) (ZMod 2) where
  toFun p := coeffPoly p A.1
  map_add' p q := by
    apply coefficient_characterization hℓ _ A _
      (multilinear_add _ _ ((coeffPoly_expansion hℓ p).1 A.1) ((coeffPoly_expansion hℓ q).1 A.1))
    intro z
    rw [SemAC02.FibreCoordinates.coordinates_add, map_add]
    exact congrArg₂ (· + ·)
      (coefficient_on_fibre hℓ p ((globalIndexEquiv n ℓ).symm A) z)
      (coefficient_on_fibre hℓ q ((globalIndexEquiv n ℓ).symm A) z)
  map_smul' a p := by
    change coeffPoly (a • p) A.1 = a • coeffPoly p A.1
    apply coefficient_characterization hℓ _ A _
      (multilinear_smul a _ ((coeffPoly_expansion hℓ p).1 A.1))
    intro z
    rw [SemAC02.FibreCoordinates.coordinates_smul, smul_eval]
    exact congrArg (fun x => a * x)
      (coefficient_on_fibre hℓ p ((globalIndexEquiv n ℓ).symm A) z)

theorem coefficientMap_mul_base {n ℓ : ℕ} (hℓ : Odd ℓ) (A : GlobalLight n ℓ)
    (q : MvPolynomial (Fin n) (ZMod 2)) (p : MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) :
    coefficientMap hℓ A (bind₁ (fun i => hBlock (ℓ := ℓ) i) q * p) =
      ML (q * coefficientMap hℓ A p) := by
  apply coefficient_characterization hℓ _ A _ (ml_multilinear _)
  intro z
  let S := (globalIndexEquiv n ℓ).symm A
  have he : (fun X : SemAC02.FibreBasis.Fibre (minorityZero ℓ) z =>
      eval (toF2 X.1) (bind₁ (fun i => hBlock (ℓ := ℓ) i) q * p)) =
      eval (toF2 z) q • (fun X : SemAC02.FibreBasis.Fibre (minorityZero ℓ) z => eval (toF2 X.1) p) := by
    funext X
    rw [map_mul, subst_on_fibre hℓ z X.1 X.2]
    rfl
  have hc : SemAC02.FibreCoordinates.coordinates (minorityZero ℓ) (minorityZero_antitone ℓ)
      (bind₁ (fun i => hBlock (ℓ := ℓ) i) q * p) S z =
      eval (toF2 z) q * SemAC02.FibreCoordinates.coordinates (minorityZero ℓ)
        (minorityZero_antitone ℓ) p S z := by
    unfold SemAC02.FibreCoordinates.coordinates
    rw [he, map_smul]
    rfl
  rw [hc, eval_ml, map_mul, coefficient_on_fibre hℓ p S z]
  rfl

theorem coefficientMap_product {n ℓ : ℕ} (hℓ : Odd ℓ) (A : GlobalLight n ℓ)
    (p v : MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) :
    coefficientMap hℓ A (p * v) = ∑ B ∈ lightSets n ℓ,
      ML (coeffPoly p B * coefficientMap hℓ A (xMon B * v)) := by
  classical
  let P := ∑ B ∈ lightSets n ℓ,
    xMon B * bind₁ (fun i => hBlock (ℓ := ℓ) i) (coeffPoly p B)
  have hp : ML P = ML p := (coeffPoly_expansion hℓ p).2.2
  have hmul : ML (P * v) = ML (p * v) := by
    calc
      ML (P * v) = ML (ML P * v) := (ml_mul_left P v).symm
      _ = ML (ML p * v) := by rw [hp]
      _ = ML (p * v) := ml_mul_left p v
  have hmap : coefficientMap hℓ A (P * v) = coefficientMap hℓ A (p * v) :=
    congrFun (coeffPoly_congr hℓ _ _ hmul) A.1
  rw [← hmap]
  change coefficientMap hℓ A ((∑ B ∈ lightSets n ℓ,
    xMon B * bind₁ (fun i => hBlock (ℓ := ℓ) i) (coeffPoly p B)) * v) = _
  rw [Finset.sum_mul, map_sum]
  apply Finset.sum_congr rfl
  intro B _
  have he : (xMon B * bind₁ (fun i => hBlock (ℓ := ℓ) i) (coeffPoly p B)) * v =
      bind₁ (fun i => hBlock (ℓ := ℓ) i) (coeffPoly p B) * (xMon B * v) := by ring
  rw [he, coefficientMap_mul_base]

end AC02Frege.MajorityCoefficientAlgebra
end

section
-- Inlined Solutions.BooleanDegreeSpaces

open MvPolynomial AC02Frege AC02Frege.BooleanBasis

namespace SemAC02.BooleanDegreeSpaces

theorem mem_Ble_iff {V : Type} (D : ℕ) (p : MvPolynomial V (ZMod 2)) :
    p ∈ Ble V D ↔ IsMultilinear p ∧ p.totalDegree ≤ D := by
  have he : Ble V D = monomialSpan (fun A : Finset V => A.card ≤ D) := by
    unfold Ble monomialSpan
    congr 1
    ext q
    constructor
    · rintro ⟨A,hA,rfl⟩; exact ⟨A,hA,rfl⟩
    · rintro ⟨A,hA,rfl⟩; exact ⟨A,hA,rfl⟩
  rw [he,mem_light_iff]

end SemAC02.BooleanDegreeSpaces
end

section
-- Inlined Solutions.MajorityLightSeparation

set_option maxHeartbeats 2000000

open MvPolynomial AC02Frege.BooleanAlgebra

namespace AC02Frege.MajorityLightSeparation

open MajorityLightCount MajorityTensorIndex MajorityCoefficientAlgebra

theorem light_le_Ble (n ℓ K : ℕ) : lightSpace n ℓ K ≤ SemAC02.Ble (Fin n × Fin ℓ) K := by
  apply Submodule.span_mono
  rintro p ⟨T,⟨hlight,hcard⟩,rfl⟩
  exact ⟨T,hcard,rfl⟩

theorem coefficient_constant {n ℓ K : ℕ} (hℓ : Odd ℓ)
    (p : MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) (hp : p ∈ lightSpace n ℓ K) :
    ∀ A : GlobalLight n ℓ, (coefficientMap hℓ A p).totalDegree ≤ 0 := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨T,⟨hlight,hcard⟩,rfl⟩ := hp
    intro A
    change (coeffPoly (xMon T) A.1).totalDegree ≤ 0
    simpa only [mul_one,totalDegree_one] using
      MajorityCoefficientFibres.light_product_degree hℓ ⟨T,hlight⟩ A (1 : MvPolynomial (Fin n × Fin ℓ) (ZMod 2))
  | zero => intro A; simp
  | add p q hp hq ihp ihq =>
    intro A
    rw [map_add]
    exact (totalDegree_add _ _).trans (max_le (ihp A) (ihq A))
  | smul a p hp ih =>
    intro A
    rw [map_smul]
    exact (totalDegree_smul_le a _).trans (ih A)

theorem light_chat_eq_zero {n ℓ K D : ℕ} (hℓ : Odd ℓ)
    (F : LiftSAParity.CNF (Fin n)) (hF : ¬PCDerivable F D 1)
    (p : MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) (hp : p ∈ lightSpace n ℓ K)
    (hchat : p ∈ CHat F ℓ D) : p = 0 := by
  classical
  have hml : IsMultilinear p :=
    ((SemAC02.BooleanDegreeSpaces.mem_Ble_iff K p).mp (light_le_Ble n ℓ K hp)).1
  have hall : ∀ A ∈ lightSets n ℓ, coeffPoly p A = 0 := by
    intro A hA
    have hdeg := coefficient_constant hℓ p hp ⟨A,hA⟩
    change (coeffPoly p A).totalDegree ≤ 0 at hdeg
    have hC := totalDegree_eq_zero_iff_eq_C.mp (Nat.eq_zero_of_le_zero hdeg)
    rcases MajorityFoundation.eq_zero_or_one (coeff 0 (coeffPoly p A)) with ha | ha
    · simpa only [ha,map_zero] using hC
    · have h1 : coeffPoly p A = 1 := by simpa only [ha,map_one] using hC
      have hc := (hchat A hA).2
      rw [h1] at hc
      exact False.elim (hF hc)
  have hexpand : expand (coeffPoly p) = p :=
    (MajorityCoefficientDegree.coeffPoly_expansion hℓ p).2.2.trans (ml_of_multilinear p hml)
  rw [← hexpand]
  unfold expand
  have hz : (∑ A ∈ lightSets n ℓ, xMon A*bind₁ (fun i => hBlock (ℓ:=ℓ) i) (coeffPoly p A)) = 0 := by
    apply Finset.sum_eq_zero
    intro A hA
    rw [hall A hA,map_zero,mul_zero]
  rw [hz,map_zero]

noncomputable def baseSpace {n : ℕ} (F : LiftSAParity.CNF (Fin n)) (D : ℕ) :
    Submodule (ZMod 2) (MvPolynomial (Fin n) (ZMod 2)) where
  carrier := CD F D
  zero_mem' := ⟨by simpa only [map_zero] using ml_multilinear (0 : MvPolynomial (Fin n) (ZMod 2)),Support.pc_zero F D⟩
  add_mem' hp hq := ⟨multilinear_add _ _ hp.1 hq.1,Support.pc_add F D hp.2 hq.2⟩
  smul_mem' a p hp := ⟨multilinear_smul a p hp.1,Support.pc_smul F D hp.2 a⟩

noncomputable def chatSpace {n ℓ : ℕ} (hℓ : Odd ℓ) (F : LiftSAParity.CNF (Fin n)) (D : ℕ) :
    Submodule (ZMod 2) (MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) :=
  ⨅ A : GlobalLight n ℓ, (baseSpace F D).comap (coefficientMap hℓ A)

theorem mem_chatSpace {n ℓ D : ℕ} (hℓ : Odd ℓ) (F : LiftSAParity.CNF (Fin n))
    (p : MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) : p ∈ chatSpace hℓ F D ↔ p ∈ CHat F ℓ D := by
  simp only [chatSpace,Submodule.mem_iInf,Submodule.mem_comap]
  constructor
  · intro h A hA
    exact h ⟨A,hA⟩
  · intro h A
    exact h A.1 A.2

end AC02Frege.MajorityLightSeparation
end

section
-- Inlined Solutions.BooleanDegreeBasis

open Module MvPolynomial AC02Frege AC02Frege.BooleanAlgebra

namespace SemAC02.BooleanDegreeBasis

abbrev DegreeIndex (V : Type) (K : ℕ) := {T : Finset V // T.card ≤ K}

theorem degree_span (V : Type) (K : ℕ) :
    Submodule.span (ZMod 2) (Set.range (fun T : DegreeIndex V K => xMon T.1)) = Ble V K := by
  unfold Ble
  congr 1
  ext p
  constructor
  · rintro ⟨T,rfl⟩; exact ⟨T.1,T.2,rfl⟩
  · rintro ⟨T,hT,rfl⟩; exact ⟨⟨T,hT⟩,rfl⟩

noncomputable def degreeBasis (V : Type) (K : ℕ) : Basis (DegreeIndex V K) (ZMod 2) (Ble V K) :=
  (Basis.span (xMon_linearIndependent.comp (fun T : DegreeIndex V K => T.1) Subtype.val_injective)).map
    (LinearEquiv.ofEq _ _ (degree_span V K))

instance finite_Ble (V : Type) [Fintype V] [DecidableEq V] (K : ℕ) : Module.Finite (ZMod 2) (Ble V K) :=
  Module.Finite.of_basis (degreeBasis V K)

theorem finrank_Ble (V : Type) [Fintype V] [DecidableEq V] (K : ℕ) :
    finrank (ZMod 2) (Ble V K) = Hn (Fintype.card V) K := by
  rw [Module.finrank_eq_card_basis (degreeBasis V K)]
  have he : Fintype.card (DegreeIndex V K) =
      (Finset.univ.filter (fun T : Finset V => T.card ≤ K)).card := Fintype.card_subtype _
  rw [he]
  exact MultiplierSupportCount.low_support_card V K

end SemAC02.BooleanDegreeBasis
end

section
-- Inlined Solutions.MajorityThreshold

set_option maxHeartbeats 2000000

open Module MvPolynomial

namespace AC02Frege.MajorityThreshold

open MajorityLightCount MajorityLightSeparation

/-- The threshold count (32), for every degree cutoff at most the number of lifted variables. -/
theorem threshold_lower {n ℓ K D : ℕ} (hℓ : Odd ℓ) (F : LiftSAParity.CNF (Fin n))
    (hF : ¬PCDerivable F D 1) (hK : K ≤ n*ℓ) :
    (monoCount (n*ℓ) K : ℝ)/2^n ≤ (hThresh F ℓ D K : ℝ) := by
  classical
  let V := Fin n × Fin ℓ
  let W := SemAC02.Ble V K
  let U := lightSpace n ℓ K
  let B := W ⊓ chatSpace hℓ F D
  have hUW : U ≤ W := light_le_Ble n ℓ K
  have hBW : B ≤ W := inf_le_left
  letI : Module.Finite (ZMod 2) B := Module.Finite.of_injective
    (Submodule.inclusion hBW) (Submodule.inclusion_injective hBW)
  have hdisj : Disjoint U B := by
    rw [Submodule.disjoint_def]
    intro p hp hB
    exact light_chat_eq_zero hℓ F hF p hp ((mem_chatSpace hℓ F p).mp hB.2)
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq U B
  have hinf : finrank (ZMod 2) ↥(U ⊓ B) = 0 := by rw [hdisj.eq_bot]; simp
  have hbound : finrank (ZMod 2) ↥(U ⊔ B) ≤ finrank (ZMod 2) W :=
    Submodule.finrank_mono (sup_le hUW hBW)
  have hW : finrank (ZMod 2) W = monoCount (n*ℓ) K := by
    calc
      _ = SemAC02.Hn (n*ℓ) K := by
        simpa only [W,V,Fintype.card_prod,Fintype.card_fin] using SemAC02.BooleanDegreeBasis.finrank_Ble V K
      _ = _ := by simp only [SemAC02.Hn,monoCount,min_eq_left hK]
  have hBset : Vdeg V K ∩ CHat F ℓ D = (B : Set (MvPolynomial V (ZMod 2))) := by
    ext p
    constructor
    · intro hp
      exact ⟨(SemAC02.BooleanDegreeSpaces.mem_Ble_iff K p).mpr hp.1,(mem_chatSpace hℓ F p).mpr hp.2⟩
    · intro hp
      exact ⟨(SemAC02.BooleanDegreeSpaces.mem_Ble_iff K p).mp hp.1,(mem_chatSpace hℓ F p).mp hp.2⟩
  have hBdim : dimSpan (Vdeg V K ∩ CHat F ℓ D) = finrank (ZMod 2) B := by
    unfold dimSpan
    rw [hBset,Submodule.span_eq]
  have hUthreshold : finrank (ZMod 2) U ≤ hThresh F ℓ D K := by
    unfold hThresh
    change finrank (ZMod 2) U ≤ monoCount (n*ℓ) K-dimSpan (Vdeg V K ∩ CHat F ℓ D)
    rw [hBdim]
    have hsum : finrank (ZMod 2) U+finrank (ZMod 2) B ≤ monoCount (n*ℓ) K := by
      rw [← hdim,hinf,add_zero]
      exact hbound.trans_eq hW
    exact Nat.le_sub_of_add_le hsum
  calc
    _ = (SemAC02.Hn (n*ℓ) K : ℝ)/2^n := by simp only [SemAC02.Hn,monoCount,min_eq_left hK]
    _ ≤ ((lightFamily n ℓ K).card : ℝ) := light_count_real n ℓ K
    _ = (finrank (ZMod 2) U : ℝ) := by rw [finrank_lightSpace]
    _ ≤ _ := by exact_mod_cast hUthreshold

end AC02Frege.MajorityThreshold
end

section
-- Inlined Solutions.SamplingJointProbabilities

set_option maxHeartbeats 2000000

namespace AC02Frege.SamplingJointProbabilities

theorem choose_power_compare (N j k : ℕ) (hj : j ≤ N) :
    j.choose k*N^k ≤ N.choose k*j^k := by
  induction k with
  | zero => simp
  | succ k ih =>
    by_cases hk : k+1 ≤ j
    · have hratio : (j-k)*N ≤ (N-k)*j := by
        rw [Nat.sub_mul,Nat.sub_mul,Nat.mul_comm N j]
        exact Nat.sub_le_sub_left (Nat.mul_le_mul_left k hj) _
      apply Nat.le_of_mul_le_mul_right (c:=k+1) ?_ (by omega)
      calc
        _ = (j.choose (k+1)*(k+1))*N^k*N := by rw [pow_succ]; ring
        _ = (j.choose k*(j-k))*N^k*N := by rw [Nat.choose_succ_right_eq]
        _ = (j.choose k*N^k)*((j-k)*N) := by ring
        _ ≤ (N.choose k*j^k)*((j-k)*N) := Nat.mul_le_mul_right _ ih
        _ ≤ (N.choose k*j^k)*((N-k)*j) := Nat.mul_le_mul_left _ hratio
        _ = (N.choose k*(N-k))*j^k*j := by ring
        _ = (N.choose (k+1)*(k+1))*j^k*j := by rw [Nat.choose_succ_right_eq]
        _ = (N.choose (k+1)*j^(k+1))*(k+1) := by rw [pow_succ]; ring
    · rw [Nat.choose_eq_zero_of_lt (by omega : j < k+1)]
      simp

theorem choose_ratio_le (N j k : ℕ) (hN : 1 ≤ N) (hj : j ≤ N) (hk : k ≤ N) :
    (j.choose k : ℝ)/(N.choose k : ℝ) ≤ ((j : ℝ)/(N : ℝ))^k := by
  have hNp : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hC : 0 < (N.choose k : ℝ) := by exact_mod_cast Nat.choose_pos hk
  rw [div_pow]
  apply (div_le_div_iff₀ hC (pow_pos hNp k)).mpr
  have h := choose_power_compare N j k hj
  have hh : (j.choose k : ℝ)*(N : ℝ)^k ≤ (N.choose k : ℝ)*(j : ℝ)^k := by exact_mod_cast h
  nlinarith

theorem joint_bound (N j : ℕ) (hN : 1 ≤ N) (hj : j ≤ N) (A : Finset (Fin N)) :
    ((((Finset.univ : Finset (Fin N)).powersetCard j).filter (A ⊆ ·)).card : ℝ)/
      (N.choose j : ℝ) ≤ ((j : ℝ)/(N : ℝ))^A.card := by
  classical
  have hAN : A.card ≤ N := by simpa only [Fintype.card_fin] using Finset.card_le_univ A
  by_cases hAj : A.card ≤ j
  · rw [Finset.card_filter_powersetCard_subset A Finset.univ j (Finset.subset_univ _) hAj,
      Finset.card_univ,Fintype.card_fin]
    have hCNj : 0 < (N.choose j : ℝ) := by exact_mod_cast Nat.choose_pos hj
    have hCNk : 0 < (N.choose A.card : ℝ) := by exact_mod_cast Nat.choose_pos hAN
    have he : ((N-A.card).choose (j-A.card) : ℝ)/(N.choose j : ℝ) =
        (j.choose A.card : ℝ)/(N.choose A.card : ℝ) := by
      apply (div_eq_div_iff hCNj.ne' hCNk.ne').mpr
      have h := Nat.choose_mul (n:=N) hAj
      have hh : (N.choose j : ℝ)*(j.choose A.card : ℝ) =
          (N.choose A.card : ℝ)*((N-A.card).choose (j-A.card) : ℝ) := by exact_mod_cast h
      nlinarith
    rw [he]
    exact choose_ratio_le N j A.card hN hj hAN
  · have he : ((Finset.univ : Finset (Fin N)).powersetCard j).filter (A ⊆ ·) = ∅ := by
      apply Finset.ext
      intro S
      constructor
      · intro hS
        exfalso
        obtain ⟨hSj,hAS⟩ := Finset.mem_filter.mp hS
        have hcard := (Finset.mem_powersetCard.mp hSj).2
        have hh := Finset.card_le_card hAS
        omega
      · simp
    rw [he]
    simp only [Finset.card_empty,Nat.cast_zero,zero_div]
    positivity

end AC02Frege.SamplingJointProbabilities
end

section
-- Inlined Solutions.SamplingMomentBound

set_option maxHeartbeats 2000000

namespace AC02Frege.SamplingMomentBound

open Classical

noncomputable def sample (N j : ℕ) : Finset (Finset (Fin N)) :=
  (Finset.univ : Finset (Fin N)).powersetCard j

noncomputable def moment (N j : ℕ) (I : Finset (Fin N)) (θ : ℝ) : ℝ :=
  (∑ S ∈ sample N j, Real.exp (θ*((S ∩ I).card : ℝ)))/(N.choose j : ℝ)

theorem exp_card_expansion {N : ℕ} (I S : Finset (Fin N)) (θ : ℝ) :
    Real.exp (θ*((S ∩ I).card : ℝ)) =
      ∑ A ∈ I.powerset, if A ⊆ S then (Real.exp θ-1)^A.card else 0 := by
  let t := Real.exp θ-1
  have hfilter : I.filter (fun i => i ∈ S) = S ∩ I := by ext i; simp [and_comm]
  have hp : (∏ i ∈ I, (1+if i ∈ S then t else 0)) = Real.exp (θ*((S ∩ I).card : ℝ)) := by
    calc
      _ = ∏ i ∈ I, if i ∈ S then Real.exp θ else 1 := by
        apply Finset.prod_congr rfl
        intro i hi
        by_cases h : i ∈ S <;> simp [h,t]
      _ = (Real.exp θ)^((S ∩ I).card) := by simp only [Finset.prod_ite,Finset.prod_const_one,mul_one,hfilter,Finset.prod_const]
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
  rw [← hp,Finset.prod_one_add]
  apply Finset.sum_congr rfl
  intro A hA
  by_cases hAS : A ⊆ S
  · rw [if_pos hAS]
    calc
      _ = ∏ _i ∈ A, t := Finset.prod_congr rfl (fun i hi => by simp [hAS hi])
      _ = _ := by simp [t]
  · rw [if_neg hAS]
    obtain ⟨i,hi,hni⟩ := Finset.not_subset.mp hAS
    exact Finset.prod_eq_zero hi (by simp [hni])

theorem moment_le (N j : ℕ) (hN : 1 ≤ N) (hj : j ≤ N) (I : Finset (Fin N))
    (θ : ℝ) (hθ : 0 ≤ θ) : moment N j I θ ≤ (1-(j : ℝ)/N+((j : ℝ)/N)*Real.exp θ)^I.card := by
  let p := (j : ℝ)/(N : ℝ)
  let t := Real.exp θ-1
  have ht : 0 ≤ t := by dsimp [t]; linarith [Real.one_le_exp hθ]
  have hinner (A : Finset (Fin N)) :
      (∑ S ∈ sample N j, if A ⊆ S then t^A.card else 0) =
        ((((sample N j).filter (A ⊆ ·)).card : ℝ)*t^A.card) := by
    rw [← Finset.sum_filter]
    simp
  have hsum : moment N j I θ =
      ∑ A ∈ I.powerset, t^A.card*((((sample N j).filter (A ⊆ ·)).card : ℝ)/(N.choose j : ℝ)) := by
    unfold moment
    simp_rw [exp_card_expansion]
    rw [Finset.sum_comm,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro A hA
    rw [hinner A]
    ring
  rw [hsum]
  calc
    _ ≤ ∑ A ∈ I.powerset, (t*p)^A.card := by
      apply Finset.sum_le_sum
      intro A hA
      have h := mul_le_mul_of_nonneg_left (SamplingJointProbabilities.joint_bound N j hN hj A)
        (pow_nonneg ht A.card)
      simpa only [mul_pow,sample,p] using h
    _ = (1+t*p)^I.card := by
      have h := Finset.prod_one_add (f:=fun _i : Fin N => t*p) I
      simpa only [Finset.prod_const] using h.symm
    _ = _ := by congr 1; dsimp [t,p]; ring

end AC02Frege.SamplingMomentBound
end

section
-- Inlined Solutions.BernoulliHoeffding

open MeasureTheory ProbabilityTheory

namespace AC02Frege.BernoulliHoeffding

theorem centered_mgf (p θ : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    p*Real.exp (θ*(1-p))+(1-p)*Real.exp (-θ*p) ≤ Real.exp (θ^2/8) := by
  let q : unitInterval := ⟨p,hp0,hp1⟩
  let μ := bernoulliMeasure true false q
  let X : Bool → ℝ := fun b => if b then 1 else 0
  have hm : AEMeasurable X μ := (measurable_of_countable X).aemeasurable
  have hb : ∀ᵐ b ∂μ, X b ∈ Set.Icc (0 : ℝ) 1 :=
    Filter.Eventually.of_forall (fun b => by cases b <;> simp [X])
  have hmean : ∫ b, X b ∂μ = p := by
    rw [integral_bernoulliMeasure]
    simp [X,q]
  have h := (hasSubgaussianMGF_of_mem_Icc hm hb).mgf_le θ
  rw [hmean] at h
  unfold mgf at h
  rw [integral_bernoulliMeasure] at h
  norm_num [X,q,smul_eq_mul] at h
  rw [show (1/4 : ℝ)*θ^2/2 = θ^2/8 by ring] at h
  simpa only [neg_mul] using h

theorem uncentered_mgf (p θ : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    1-p+p*Real.exp θ ≤ Real.exp (p*θ+θ^2/8) := by
  have h := mul_le_mul_of_nonneg_right (centered_mgf p θ hp0 hp1) (Real.exp_pos (p*θ)).le
  have he : (p*Real.exp (θ*(1-p))+(1-p)*Real.exp (-θ*p))*Real.exp (p*θ) = 1-p+p*Real.exp θ := by
    rw [add_mul,mul_assoc,mul_assoc,← Real.exp_add,← Real.exp_add]
    rw [show θ*(1-p)+p*θ = θ by ring,show -θ*p+p*θ = 0 by ring,Real.exp_zero,mul_one]
    ring
  rw [he,← Real.exp_add] at h
  simpa only [add_comm] using h

end AC02Frege.BernoulliHoeffding
end

section
-- Inlined Solutions.SamplingTail

set_option maxHeartbeats 2000000

namespace AC02Frege.SamplingTail

open Classical SamplingMomentBound

theorem sampling_tail (N j : ℕ) (hj : j ≤ N) (I : Finset (Fin N)) (hI : 1 ≤ I.card)
    (u : ℝ) (hu : 0 ≤ u) :
    ((((Finset.univ : Finset (Finset (Fin N))).filter (fun S => S.card = j ∧
        u ≤ ((S ∩ I).card : ℝ)-(I.card : ℝ)*((j : ℝ)/N))).card : ℕ) : ℝ)/
      (N.choose j : ℝ) ≤ Real.exp (-2*u^2/I.card) := by
  have hIN : I.card ≤ N := by simpa only [Fintype.card_fin] using Finset.card_le_univ I
  have hN : 1 ≤ N := hI.trans hIN
  have hNp : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hden : 0 < (N.choose j : ℝ) := by exact_mod_cast Nat.choose_pos hj
  let p := (j : ℝ)/(N : ℝ)
  let L := (I.card : ℝ)
  let θ := 4*u/L
  let E (S : Finset (Fin N)) := u ≤ ((S ∩ I).card : ℝ)-L*p
  have hL : 0 < L := by dsimp [L]; exact_mod_cast (show 0 < I.card by omega)
  have hθ : 0 ≤ θ := by dsimp [θ]; positivity
  have hp0 : 0 ≤ p := by dsimp [p]; positivity
  have hp1 : p ≤ 1 := (div_le_one hNp).mpr (by exact_mod_cast hj)
  have hmoment : moment N j I θ ≤ Real.exp (L*(p*θ+θ^2/8)) := by
    have hb := BernoulliHoeffding.uncentered_mgf p θ hp0 hp1
    have hb0 : 0 ≤ 1-p+p*Real.exp θ := by positivity
    have hpow := pow_le_pow_left₀ hb0 hb I.card
    calc
      _ ≤ (1-p+p*Real.exp θ)^I.card := SamplingMomentBound.moment_le N j hN hj I θ hθ
      _ ≤ (Real.exp (p*θ+θ^2/8))^I.card := hpow
      _ = _ := by rw [← Real.exp_nat_mul]
  have hline : (∑ S ∈ sample N j, if E S then (1 : ℝ) else 0) ≤
      Real.exp (-θ*(L*p+u))*(∑ S ∈ sample N j, Real.exp (θ*((S ∩ I).card : ℝ))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro S hS
    by_cases hE : E S
    · rw [if_pos hE,← Real.exp_add]
      apply Real.one_le_exp
      have hh : L*p+u ≤ ((S ∩ I).card : ℝ) := by dsimp [E] at hE; linarith
      have hmul := mul_le_mul_of_nonneg_left hh hθ
      linarith
    · rw [if_neg hE]
      positivity
  have hcount : (∑ S ∈ sample N j, if E S then (1 : ℝ) else 0) =
      (((sample N j).filter E).card : ℝ) := by rw [← Finset.sum_filter]; simp
  rw [hcount] at hline
  have hmarkov : (((sample N j).filter E).card : ℝ)/(N.choose j : ℝ) ≤
      Real.exp (-θ*(L*p+u))*moment N j I θ := by
    have h := div_le_div_of_nonneg_right hline hden.le
    simpa only [moment,mul_div_assoc] using h
  have htail : (((sample N j).filter E).card : ℝ)/(N.choose j : ℝ) ≤ Real.exp (-2*u^2/I.card) := by
    calc
      _ ≤ Real.exp (-θ*(L*p+u))*moment N j I θ := hmarkov
      _ ≤ Real.exp (-θ*(L*p+u))*Real.exp (L*(p*θ+θ^2/8)) :=
        mul_le_mul_of_nonneg_left hmoment (Real.exp_pos _).le
      _ = _ := by
        rw [← Real.exp_add]
        congr 1
        dsimp [θ,L]
        field_simp [ne_of_gt hL] <;> ring
  have he : (Finset.univ : Finset (Finset (Fin N))).filter (fun S => S.card = j ∧
      u ≤ ((S ∩ I).card : ℝ)-(I.card : ℝ)*((j : ℝ)/N)) = (sample N j).filter E := by
    ext S
    simp [sample,E,L,p,Finset.mem_powersetCard]
  rw [he]
  exact htail

end AC02Frege.SamplingTail
end

section
-- Inlined Theorems.Thm_AC02Frege_eq_49_sampling_tail
namespace AC02Frege

/-- Alekseev–Gryaznov–Pitassi–Robere–Shekhovtsov–Tzameret, *Progress on AC0[2]-Frege Lower Bounds*, manuscript (sha256 88d149fa…), App. C, (49), p.45 (tail bound for sampling without replacement): choose a uniform
`j`-subset of an `N`-element set; for a fixed set of `L ≥ 1` coordinates let `X` count how many
are selected, and put `p = j/N`. For every `u ≥ 0`, `Pr[X − Lp ≥ u] ≤ exp(−2u²/L)`.

**Formalization Note** The probability is the fraction of `j`-subsets `S` of `Fin N` with
`|S ∩ I| − |I| j/N ≥ u`, over `C(N, j)`; `0 ≤ j ≤ N`. -/
theorem eq_49_sampling_tail (N j : ℕ) (hj : j ≤ N) (I : Finset (Fin N)) (hI : 1 ≤ I.card)
    (u : ℝ) (hu : 0 ≤ u) :
    ((((Finset.univ : Finset (Finset (Fin N))).filter (fun S => S.card = j ∧
        u ≤ ((S ∩ I).card : ℝ) - (I.card : ℝ) * ((j : ℝ) / N))).card : ℕ) : ℝ)
        / (N.choose j : ℝ)
      ≤ Real.exp (-2 * u ^ 2 / I.card) := by
  exact SamplingTail.sampling_tail N j hj I hI u hu

end AC02Frege
end

section
-- Inlined Solutions.FiniteSamplingTail

set_option maxHeartbeats 1000000

namespace AC02Frege.FiniteSamplingTail

theorem sampling_tail {V : Type} [Fintype V] [DecidableEq V] (j : ℕ) (hj : j ≤ Fintype.card V)
    (I : Finset V) (hI : 1 ≤ I.card) (u : ℝ) (hu : 0 ≤ u) :
    ((((Finset.univ : Finset (Finset V)).filter (fun S => S.card = j ∧
      u ≤ ((S ∩ I).card : ℝ)-(I.card : ℝ)*((j : ℝ)/Fintype.card V))).card : ℕ) : ℝ)/
      ((Fintype.card V).choose j : ℝ) ≤ Real.exp (-2*u^2/I.card) := by
  classical
  let N := Fintype.card V
  let e := Fintype.equivFin V
  let I' := I.image e
  let P (S : Finset V) := S.card = j ∧ u ≤ ((S ∩ I).card : ℝ)-(I.card : ℝ)*((j : ℝ)/N)
  let Q (S : Finset (Fin N)) := S.card = j ∧ u ≤ ((S ∩ I').card : ℝ)-(I'.card : ℝ)*((j : ℝ)/N)
  have hcompat (S : Finset V) : P S ↔ Q (e.finsetCongr S) := by
    have hS : e.finsetCongr S = S.image e := by rw [Equiv.finsetCongr_apply,Finset.map_eq_image]; rfl
    rw [hS]
    dsimp [P,Q,I']
    rw [← Finset.image_inter S I e.injective,
      Finset.card_image_of_injective S e.injective,
      Finset.card_image_of_injective (S ∩ I) e.injective,
      Finset.card_image_of_injective I e.injective]
  have hcount : ((Finset.univ : Finset (Finset V)).filter P).card =
      ((Finset.univ : Finset (Finset (Fin N))).filter Q).card := by
    have h := Fintype.card_congr (e.finsetCongr.subtypeEquiv hcompat)
    simpa only [Fintype.card_subtype] using h
  have hI' : 1 ≤ I'.card := by simpa only [I',Finset.card_image_of_injective I e.injective] using hI
  have h := eq_49_sampling_tail N j hj I' hI' u hu
  change ((((Finset.univ : Finset (Finset V)).filter P).card : ℝ)/(N.choose j : ℝ)) ≤ _
  rw [hcount]
  simpa only [Q,I',Finset.card_image_of_injective I e.injective] using h

end AC02Frege.FiniteSamplingTail
end

section
-- Inlined Solutions.HeavyBlockTail

set_option maxHeartbeats 2000000

namespace AC02Frege.HeavyBlockTail

open Classical HeavyBlockCounting

theorem heavy_union_card {n ℓ : ℕ} (T : Finset (Fin n × Fin ℓ)) (J : Finset (Fin n))
    (hJ : J ⊆ heavyBlocks T) : J.card*ℓ ≤ 2*(T ∩ blockUnion J).card := by
  calc
    _ = ∑ _i ∈ J, ℓ := by simp
    _ ≤ ∑ i ∈ J, 2*(blockPart T i).card := by
      apply Finset.sum_le_sum
      intro i hi
      have hh := hJ hi
      simp only [heavyBlocks,Finset.mem_filter,Finset.mem_univ,true_and] at hh
      omega
    _ = 2*(∑ i ∈ J, (blockPart T i).card) := (Finset.mul_sum _ _ _).symm
    _ = _ := by rw [inter_union_card]

theorem fixed_heavy_tail {n ℓ j : ℕ} (hℓ : 1 ≤ ℓ) (hj : j ≤ n*ℓ)
    (J : Finset (Fin n)) (hJ : 1 ≤ J.card) (a : ℝ) (ha : 0 ≤ a)
    (harg : (j : ℝ) ≤ ((n*ℓ : ℕ) : ℝ)/2-a*n*Real.sqrt ℓ) :
    ((((Finset.univ : Finset (Finset (Fin n × Fin ℓ))).filter
      (fun T => T.card = j ∧ J ⊆ heavyBlocks T)).card : ℕ) : ℝ)/((n*ℓ).choose j : ℝ) ≤
      Real.exp (-2*(J.card : ℝ)*a^2) := by
  have hn : 1 ≤ n := hJ.trans (by simpa only [Fintype.card_fin] using Finset.card_le_univ J)
  have hnp : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hℓp : 0 < (ℓ : ℝ) := by exact_mod_cast (show 0 < ℓ by omega)
  have hqp : 0 < (J.card : ℝ) := by exact_mod_cast (show 0 < J.card by omega)
  let N := n*ℓ
  let I : Finset (Fin n × Fin ℓ) := blockUnion J
  let u := (J.card : ℝ)*a*Real.sqrt ℓ
  have hIc : I.card = J.card*ℓ := by simp [I,blockUnion]
  have hI : 1 ≤ I.card := by rw [hIc]; nlinarith
  have hNp : 0 < (N : ℝ) := by dsimp [N]; push_cast; positivity
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hmean : (I.card : ℝ)*((j : ℝ)/N) ≤ (I.card : ℝ)/2-u := by
    have hfrac := div_le_div_of_nonneg_right harg hNp.le
    have hm := mul_le_mul_of_nonneg_left hfrac (Nat.cast_nonneg I.card : (0 : ℝ) ≤ _)
    have he : (I.card : ℝ)*((((n*ℓ : ℕ) : ℝ)/2-a*n*Real.sqrt ℓ)/(N : ℝ)) = (I.card : ℝ)/2-u := by
      rw [hIc]
      dsimp [N,u]
      push_cast
      field_simp [hnp.ne',hℓp.ne'] <;> ring
    rw [he] at hm
    exact hm
  have hsub : (Finset.univ : Finset (Finset (Fin n × Fin ℓ))).filter (fun T => T.card = j ∧ J ⊆ heavyBlocks T) ⊆
      Finset.univ.filter (fun T => T.card = j ∧ u ≤ ((T ∩ I).card : ℝ)-(I.card : ℝ)*((j : ℝ)/N)) := by
    intro T hT
    obtain ⟨hTj,hTJ⟩ := (Finset.mem_filter.mp hT).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,hTj,?_⟩
    have hh := heavy_union_card T J hTJ
    have hh' : (J.card : ℝ)*ℓ ≤ 2*((T ∩ I).card : ℝ) := by exact_mod_cast hh
    have hc : (I.card : ℝ) = (J.card : ℝ)*ℓ := by exact_mod_cast hIc
    nlinarith
  have ht := FiniteSamplingTail.sampling_tail (V:=Fin n × Fin ℓ) j (by simpa using hj) I hI u hu
  simp only [Fintype.card_prod,Fintype.card_fin] at ht
  have he : -2*u^2/(I.card : ℝ) = -2*(J.card : ℝ)*a^2 := by
    rw [hIc]
    dsimp [u]
    push_cast
    simp only [mul_pow,Real.sq_sqrt (Nat.cast_nonneg ℓ)]
    field_simp [hqp.ne',hℓp.ne'] <;> ring
  rw [he] at ht
  have hden : 0 ≤ ((n*ℓ).choose j : ℝ) := Nat.cast_nonneg _
  exact (div_le_div_of_nonneg_right (by exact_mod_cast Finset.card_le_card hsub) hden).trans ht

end AC02Frege.HeavyBlockTail
end

section
-- Inlined Solutions.ExcludedHeavyFraction

set_option maxHeartbeats 2000000

namespace AC02Frege.ExcludedHeavyFraction

open Classical

theorem excluded_fraction (n ℓ Q j : ℕ) (hℓ : 1 ≤ ℓ) (hj : j ≤ n*ℓ)
    (a : ℝ) (ha : 0 ≤ a) (harg : (j : ℝ) ≤ ((n*ℓ : ℕ) : ℝ)/2-a*n*Real.sqrt ℓ) :
    ((((Finset.univ : Finset (Finset (Fin n × Fin ℓ))).filter
      (fun T => T.card = j ∧ Q < (heavyBlocks T).card)).card : ℕ) : ℝ)/((n*ℓ).choose j : ℝ) ≤
      (2 : ℝ)^n*Real.exp (-2*((Q+1 : ℕ) : ℝ)*a^2) := by
  let Js := (Finset.univ : Finset (Fin n)).powersetCard (Q+1)
  let Tail (J : Finset (Fin n)) := (Finset.univ : Finset (Finset (Fin n × Fin ℓ))).filter
    (fun T => T.card = j ∧ J ⊆ heavyBlocks T)
  let Bad := (Finset.univ : Finset (Finset (Fin n × Fin ℓ))).filter
    (fun T => T.card = j ∧ Q < (heavyBlocks T).card)
  have hsub : Bad ⊆ Js.biUnion Tail := by
    intro T hT
    obtain ⟨hTj,hTQ⟩ := (Finset.mem_filter.mp hT).2
    obtain ⟨J,hJ,hJcard⟩ := Finset.exists_subset_card_eq (by omega : Q+1 ≤ (heavyBlocks T).card)
    refine Finset.mem_biUnion.mpr ⟨J,?_,?_⟩
    · exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,hJcard⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hTj,hJ⟩
  have hcount : Bad.card ≤ ∑ J ∈ Js, (Tail J).card :=
    (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  calc
    _ ≤ ((∑ J ∈ Js, (Tail J).card : ℕ) : ℝ)/((n*ℓ).choose j : ℝ) :=
      div_le_div_of_nonneg_right (by exact_mod_cast hcount) (Nat.cast_nonneg _)
    _ = ∑ J ∈ Js, ((Tail J).card : ℝ)/((n*ℓ).choose j : ℝ) := by rw [Nat.cast_sum,Finset.sum_div]
    _ ≤ ∑ _J ∈ Js, Real.exp (-2*((Q+1 : ℕ) : ℝ)*a^2) := by
      apply Finset.sum_le_sum
      intro J hJ
      have hJcard := (Finset.mem_powersetCard.mp hJ).2
      simpa only [Tail,hJcard] using HeavyBlockTail.fixed_heavy_tail hℓ hj J (by omega) a ha harg
    _ = (Js.card : ℝ)*Real.exp (-2*((Q+1 : ℕ) : ℝ)*a^2) := by simp
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      have hcard : Js.card = n.choose (Q+1) := by simp [Js]
      rw [hcard]
      exact_mod_cast Nat.choose_le_two_pow n (Q+1)

theorem excluded_bound (n ℓ : ℕ) (hℓ : 1 ≤ ℓ) (c a : ℝ) (ha : 1 ≤ a)
    (hK : 0 ≤ ((n*ℓ : ℕ) : ℝ)/2-a*n*Real.sqrt ℓ) :
    epsExcl n ℓ ⌊c*n/16⌋₊ ⌊((n*ℓ : ℕ) : ℝ)/2-a*n*Real.sqrt ℓ⌋₊ ≤
      Real.exp (-(c*a^2/8-Real.log 2)*n) := by
  let Q := ⌊c*n/16⌋₊
  let K := ⌊((n*ℓ : ℕ) : ℝ)/2-a*n*Real.sqrt ℓ⌋₊
  have hargN : ((n*ℓ : ℕ) : ℝ)/2-a*n*Real.sqrt ℓ ≤ ((n*ℓ : ℕ) : ℝ) := by
    have hprod : 0 ≤ a*n*Real.sqrt ℓ := by positivity
    nlinarith [Nat.cast_nonneg (n*ℓ) (α:=ℝ)]
  have he : (2 : ℝ)^n*Real.exp (-2*((Q+1 : ℕ) : ℝ)*a^2) ≤
      Real.exp (-(c*a^2/8-Real.log 2)*n) := by
    have htwo : (2 : ℝ)^n = Real.exp ((n : ℝ)*Real.log 2) := by
      rw [Real.exp_nat_mul,Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    rw [htwo,← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hQ := Nat.lt_floor_add_one (c*n/16)
    change c*n/16 < (Q : ℝ)+1 at hQ
    have hmul := mul_le_mul_of_nonneg_right hQ.le (sq_nonneg a)
    push_cast
    nlinarith
  unfold epsExcl
  apply Finset.sup'_le
  intro j hj
  have hjK : j ≤ K := by have h := Finset.mem_range.mp hj; change j < K+1 at h; omega
  have hjarg : (j : ℝ) ≤ ((n*ℓ : ℕ) : ℝ)/2-a*n*Real.sqrt ℓ :=
    (Nat.cast_le.mpr hjK).trans (Nat.floor_le hK)
  have hjN : j ≤ n*ℓ := by exact_mod_cast hjarg.trans hargN
  exact (excluded_fraction n ℓ Q j hℓ hjN a (by linarith) hjarg).trans he

end AC02Frege.ExcludedHeavyFraction
end

section
-- Inlined Solutions.MajorityTwoCounts

set_option maxHeartbeats 2000000

namespace AC02Frege.MajorityTwoCounts

theorem two_counts {n ℓ : ℕ} (hℓ : Odd ℓ) (c a : ℝ) (hc0 : 0 < c) (hc1 : c < 1)
    (ha : 1 ≤ a) (F : LiftSAParity.CNF (Fin n)) (hF : ¬ PCDerivable F ⌊c*n⌋₊ 1)
    (hK : 0 ≤ ((n*ℓ : ℕ) : ℝ)/2-a*n*Real.sqrt ℓ) :
    let D := ⌊c*n⌋₊
    let Q := ⌊c*n/16⌋₊
    let K := ⌊((n*ℓ : ℕ) : ℝ)/2-a*n*Real.sqrt ℓ⌋₊
    (monoCount (n*ℓ) K : ℝ)/2^n ≤ (hThresh F ℓ D K : ℝ) ∧
    epsExcl n ℓ Q K ≤ Real.exp (-(c*a^2/8-Real.log 2)*n) ∧
    (2*Real.log 2+12 ≤ c*a^2/8 →
      epsExcl n ℓ Q K*(monoCount (n*ℓ) K : ℝ)/(hThresh F ℓ D K : ℝ) ≤ Real.exp (-12*n)) := by
  let D := ⌊c*n⌋₊
  let Q := ⌊c*n/16⌋₊
  let K := ⌊((n*ℓ : ℕ) : ℝ)/2-a*n*Real.sqrt ℓ⌋₊
  have hℓ1 : 1 ≤ ℓ := by obtain ⟨k,hk⟩ := hℓ; omega
  have hargN : ((n*ℓ : ℕ) : ℝ)/2-a*n*Real.sqrt ℓ ≤ ((n*ℓ : ℕ) : ℝ) := by
    have hprod : 0 ≤ a*n*Real.sqrt ℓ := by positivity
    nlinarith [Nat.cast_nonneg (n*ℓ) (α:=ℝ)]
  have hKN : K ≤ n*ℓ := by
    calc
      _ ≤ ⌊((n*ℓ : ℕ) : ℝ)⌋₊ := Nat.floor_mono hargN
      _ = _ := Nat.floor_natCast _
  have hthreshold := MajorityThreshold.threshold_lower hℓ F hF hKN
  have hexcluded := ExcludedHeavyFraction.excluded_bound n ℓ hℓ1 c a ha hK
  refine ⟨hthreshold,hexcluded,?_⟩
  intro hparam
  have hM : monoCount (n*ℓ) K = SemAC02.Hn (n*ℓ) K := by
    simp only [monoCount,SemAC02.Hn,min_eq_left hKN]
  have hMpos : 0 < (monoCount (n*ℓ) K : ℝ) := by
    rw [hM]
    exact_mod_cast SemAC02.BooleanDimension.Hn_pos (n*ℓ) K
  have hpow : (0 : ℝ) < 2^n := by positivity
  have hHpos : 0 < (hThresh F ℓ D K : ℝ) := (div_pos hMpos hpow).trans_le hthreshold
  have hratio : (monoCount (n*ℓ) K : ℝ)/(hThresh F ℓ D K : ℝ) ≤ 2^n := by
    apply (div_le_iff₀ hHpos).mpr
    have h := (div_le_iff₀ hpow).mp hthreshold
    nlinarith
  calc
    _ = epsExcl n ℓ Q K*((monoCount (n*ℓ) K : ℝ)/(hThresh F ℓ D K : ℝ)) := by ring
    _ ≤ Real.exp (-(c*a^2/8-Real.log 2)*n)*((monoCount (n*ℓ) K : ℝ)/(hThresh F ℓ D K : ℝ)) :=
      mul_le_mul_of_nonneg_right hexcluded (div_nonneg hMpos.le hHpos.le)
    _ ≤ Real.exp (-(c*a^2/8-Real.log 2)*n)*2^n := mul_le_mul_of_nonneg_left hratio (Real.exp_pos _).le
    _ ≤ _ := by
      have htwo : (2 : ℝ)^n = Real.exp ((n : ℝ)*Real.log 2) := by
        rw [Real.exp_nat_mul,Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      rw [htwo,← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have h := mul_le_mul_of_nonneg_right hparam (Nat.cast_nonneg n : (0 : ℝ) ≤ _)
      nlinarith

end AC02Frege.MajorityTwoCounts
end

open AC02Frege LiftSAParity

theorem solution {n ℓ : ℕ} (hℓ : Odd ℓ) (c a : ℝ) (hc0 : 0 < c) (hc1 : c < 1)
    (ha : 1 ≤ a) (F : CNF (Fin n)) (hF : ¬ PCDerivable F ⌊c * n⌋₊ 1)
    (hK : 0 ≤ ((n * ℓ : ℕ) : ℝ) / 2 - a * n * Real.sqrt ℓ) :
    let D := ⌊c * n⌋₊
    let Q := ⌊c * n / 16⌋₊
    let K := ⌊((n * ℓ : ℕ) : ℝ) / 2 - a * n * Real.sqrt ℓ⌋₊
    (monoCount (n * ℓ) K : ℝ) / 2 ^ n ≤ (hThresh F ℓ D K : ℝ) ∧
    epsExcl n ℓ Q K ≤ Real.exp (-(c * a ^ 2 / 8 - Real.log 2) * n) ∧
    (2 * Real.log 2 + 12 ≤ c * a ^ 2 / 8 →
      epsExcl n ℓ Q K * (monoCount (n * ℓ) K : ℝ) / (hThresh F ℓ D K : ℝ)
        ≤ Real.exp (-12 * n))  := by
  exact AC02Frege.MajorityTwoCounts.two_counts hℓ c a hc0 hc1 ha F hF hK
