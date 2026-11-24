-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IrreducibleOfIrreducibleMap
-- name    : Development_AbelianVarietyTheory_Definitions_Divisors_IrreducibleOfIrreducibleMap
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T12:53:14.940934+00:00
-- url     : https://prove2.me/theorems/e1433ef9-56c4-4dc6-b005-41c9a4c06b98
-- title:
--   Irreducible Of Irreducible Map
-- statement:
--   Definitions and structural lemmas for Irreducible Of Irreducible Map, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/IrreducibleOfIrreducibleMap.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_PointHeight
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_AevalEqZeroOfHomogeneousComponent
import Theorems.Thm_GlobalTheory_Chow_IsBlockHomogeneous_unique
import Theorems.Thm_GlobalTheory_Chow_exists_eq_C_mul_of_span_eq
import Theorems.Thm_GlobalTheory_Chow_isBlockHomogeneous_iff
import Theorems.Thm_GlobalTheory_quotientMapCSupSpanLinFormEquiv_mk
import Theorems.Thm_GlobalTheory_quotientSpanLinFormEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.quotientMapCSupSpanLinFormEquiv_mk
attribute [local simp] GlobalTheory.quotientSpanLinFormEquiv_mk


set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPolynomial
namespace GlobalTheory.ChowHt
attribute [local instance] MvPolynomial.gradedAlgebra
structure IsChowFormInt {k : Type} [Field k] {N : ℕ} (I : Ideal (MvPolynomial (Fin N) k))
    (e dl : ℕ) (f : MvPolynomial (Fin (e + 1) × Fin N) k) : Prop where

  homog : ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous (fun _ => dl) f

  irred : Irreducible f

  zero_iff : ∀ u : Fin (e + 1) × Fin N → AlgebraicClosure k, MvPolynomial.aeval u f = 0 ↔
    ∃ y : Fin N → AlgebraicClosure k, y ≠ 0 ∧ (∀ g ∈ I, MvPolynomial.aeval y g = 0) ∧
      ∀ i, ∑ j, u (i, j) * y j = 0
def IsChowFormCycle {k : Type} [Field k] {N : ℕ} (Z : Ideal (MvPolynomial (Fin N) k) →₀ ℕ)
    (e dl : ℕ) (f : MvPolynomial (Fin (e + 1) × Fin N) k) : Prop :=
  ∃ c : k, c ≠ 0 ∧ ∃ (d : Ideal (MvPolynomial (Fin N) k) → ℕ)
    (g : Ideal (MvPolynomial (Fin N) k) → MvPolynomial (Fin (e + 1) × Fin N) k),
    (∀ P ∈ Z.support, P.IsPrime ∧ P.IsHomogeneous (homogeneousSubmodule (Fin N) k) ∧
      IsChowFormInt P e (d P) (g P)) ∧
    dl = Z.sum (fun P m => m * d P) ∧ f = C c * Z.prod (fun P m => g P ^ m)
variable {k : Type} [Field k] {N : ℕ}
theorem isMultiHomogeneous_iff_block {B : ℕ} {a : Fin B → ℕ}
    {f : MvPolynomial (Fin B × Fin N) k} :
    ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous a f ↔ GlobalTheory.Chow.IsBlockHomogeneous f a :=
  GlobalTheory.Chow.isBlockHomogeneous_iff.symm
namespace IsChowFormInt
variable {I : Ideal (MvPolynomial (Fin N) k)} {e dl dl' : ℕ}
  {f f' : MvPolynomial (Fin (e + 1) × Fin N) k}
theorem ne_zero (h : IsChowFormInt I e dl f) : f ≠ 0 := h.irred.ne_zero
theorem C_mul (h : IsChowFormInt I e dl f) {c : k} (hc : c ≠ 0) :
    IsChowFormInt I e dl (C c * f) := by
  refine ⟨?_, (irreducible_isUnit_mul ((IsUnit.mk0 c hc).map C)).2 h.irred, fun u => ?_⟩
  · exact isMultiHomogeneous_iff_block.2
      (IsWeightedHomogeneous.C_mul (isMultiHomogeneous_iff_block.1 h.homog) c)
  · rw [map_mul, aeval_C, mul_eq_zero, map_eq_zero, ← h.zero_iff u]
    simp [hc]
theorem dvd_of_forall_aeval_eq_zero (h : IsChowFormInt I e dl f)
    {p : MvPolynomial (Fin (e + 1) × Fin N) k}
    (hp : ∀ u : Fin (e + 1) × Fin N → AlgebraicClosure k, aeval u f = 0 → aeval u p = 0) :
    f ∣ p := by
  haveI : (Ideal.span {f}).IsPrime := (Ideal.span_singleton_prime h.ne_zero).2 h.irred.prime
  rw [← Ideal.mem_span_singleton,
    ← IsPrime.vanishingIdeal_zeroLocus (K := AlgebraicClosure k) (Ideal.span {f})]
  exact fun u hu => hp u (hu f (Ideal.subset_span rfl))
theorem unique (h : IsChowFormInt I e dl f) (h' : IsChowFormInt I e dl' f') :
    dl = dl' ∧ ∃ c : k, c ≠ 0 ∧ f' = C c * f := by
  have h1 : f ∣ f' := h.dvd_of_forall_aeval_eq_zero fun u hu =>
    (h'.zero_iff u).2 ((h.zero_iff u).1 hu)
  have h2 : f' ∣ f := h'.dvd_of_forall_aeval_eq_zero fun u hu =>
    (h.zero_iff u).2 ((h'.zero_iff u).1 hu)
  obtain ⟨c, hc, hf⟩ := GlobalTheory.Chow.exists_eq_C_mul_of_span_eq
    (Ideal.span_singleton_eq_span_singleton.2 (associated_of_dvd_dvd h1 h2))
  refine ⟨?_, c, hc, hf⟩
  have h3 := (h.C_mul hc).homog
  rw [← hf] at h3
  exact congrFun (GlobalTheory.Chow.IsBlockHomogeneous.unique h'.ne_zero
    (isMultiHomogeneous_iff_block.1 h3) (isMultiHomogeneous_iff_block.1 h'.homog)) 0
theorem exists_point (h : IsChowFormInt I e dl f) :
    ∃ y : Fin N → AlgebraicClosure k, y ≠ 0 ∧ ∀ g ∈ I, MvPolynomial.aeval y g = 0 := by
  by_contra hc
  refine h.irred.not_isUnit (isUnit_of_dvd_one (h.dvd_of_forall_aeval_eq_zero fun u hu => ?_))
  obtain ⟨y, hy, hI, -⟩ := (h.zero_iff u).1 hu
  exact (hc ⟨y, hy, hI⟩).elim
theorem single (h : IsChowFormInt I e dl f) (hp : I.IsPrime)
    (hI : I.IsHomogeneous (homogeneousSubmodule (Fin N) k)) :
    IsChowFormCycle (Finsupp.single I 1) e dl f := by
  refine ⟨1, one_ne_zero, fun _ => dl, fun _ => f, fun P hP => ?_, ?_, ?_⟩
  · obtain rfl := Finset.mem_singleton.1 (Finsupp.support_single_subset hP)
    exact ⟨hp, hI, h⟩
  · rw [Finsupp.sum_single_index] <;> simp
  · rw [Finsupp.prod_single_index] <;> simp
end IsChowFormInt
theorem not_isChowFormInt_top {e dl : ℕ} (f : MvPolynomial (Fin (e + 1) × Fin N) k) :
    ¬ IsChowFormInt (⊤ : Ideal (MvPolynomial (Fin N) k)) e dl f := fun h => by
  obtain ⟨y, -, hy⟩ := h.exists_point
  simpa using hy 1 trivial
namespace IsChowFormCycle
variable {Z Z' : Ideal (MvPolynomial (Fin N) k) →₀ ℕ} {e dl dl' : ℕ}
  {f f' : MvPolynomial (Fin (e + 1) × Fin N) k}
theorem component (h : IsChowFormCycle Z e dl f) {P : Ideal (MvPolynomial (Fin N) k)}
    (hP : P ∈ Z.support) : P.IsPrime ∧ P.IsHomogeneous (homogeneousSubmodule (Fin N) k) ∧
      ∃ d g, IsChowFormInt P e d g := by
  obtain ⟨c, -, d, g, hg, -, -⟩ := h
  exact ⟨(hg P hP).1, (hg P hP).2.1, d P, g P, (hg P hP).2.2⟩
theorem C_mul (h : IsChowFormCycle Z e dl f) {a : k} (ha : a ≠ 0) :
    IsChowFormCycle Z e dl (C a * f) := by
  obtain ⟨c, hc, d, g, hg, hd, rfl⟩ := h
  exact ⟨a * c, mul_ne_zero ha hc, d, g, hg, hd, by rw [MvPolynomial.C_mul, mul_assoc]⟩
theorem eq_of_components (h : IsChowFormCycle Z e dl f)
    (d : Ideal (MvPolynomial (Fin N) k) → ℕ)
    (g : Ideal (MvPolynomial (Fin N) k) → MvPolynomial (Fin (e + 1) × Fin N) k)
    (hg : ∀ P ∈ Z.support, IsChowFormInt P e (d P) (g P)) :
    dl = Z.sum (fun P m => m * d P) ∧ ∃ c : k, c ≠ 0 ∧ f = C c * Z.prod (fun P m => g P ^ m) := by
  classical
  obtain ⟨c, hc, d₀, g₀, hg₀, rfl, rfl⟩ := h
  have hu := fun P hP => (hg P hP).unique (hg₀ P hP).2.2
  refine ⟨Finset.sum_congr rfl fun P hP => by simp only [(hu P hP).1], ?_⟩
  choose a ha hag using fun P hP => (hu P hP).2
  let a' : Ideal (MvPolynomial (Fin N) k) → k := fun P => if hP : P ∈ Z.support then a P hP else 1
  refine ⟨c * ∏ P ∈ Z.support, a' P ^ Z P, mul_ne_zero hc
    (Finset.prod_ne_zero_iff.2 fun P hP => pow_ne_zero _ ?_), ?_⟩
  · simp only [a', dif_pos hP]; exact ha P hP
  · rw [MvPolynomial.C_mul, mul_assoc, map_prod, Finsupp.prod, Finsupp.prod,
      ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun P hP => ?_
    simp only [a', dif_pos hP]
    rw [hag P hP, mul_pow, map_pow]
theorem unique (h : IsChowFormCycle Z e dl f) (h' : IsChowFormCycle Z e dl' f') :
    dl = dl' ∧ ∃ c : k, c ≠ 0 ∧ f' = C c * f := by
  obtain ⟨c, hc, d, g, hg, rfl, rfl⟩ := h
  obtain ⟨hd, c', hc', rfl⟩ := h'.eq_of_components d g fun P hP => (hg P hP).2.2
  refine ⟨hd.symm, c' * c⁻¹, mul_ne_zero hc' (inv_ne_zero hc), ?_⟩
  rw [← mul_assoc, ← MvPolynomial.C_mul, mul_assoc, inv_mul_cancel₀ hc, mul_one]
theorem add (h : IsChowFormCycle Z e dl f) (h' : IsChowFormCycle Z' e dl' f') :
    IsChowFormCycle (Z + Z') e (dl + dl') (f * f') := by
  classical
  have hex : ∀ P, ∃ d g, P ∈ Z.support ∪ Z'.support → (P.IsPrime ∧
      P.IsHomogeneous (homogeneousSubmodule (Fin N) k) ∧ IsChowFormInt P e d g) := by
    intro P
    by_cases hP : P ∈ Z.support ∪ Z'.support
    · rcases Finset.mem_union.1 hP with hP | hP
      · obtain ⟨h1, h2, d, g, h3⟩ := h.component hP
        exact ⟨d, g, fun _ => ⟨h1, h2, h3⟩⟩
      · obtain ⟨h1, h2, d, g, h3⟩ := h'.component hP
        exact ⟨d, g, fun _ => ⟨h1, h2, h3⟩⟩
    · exact ⟨0, 0, fun h => (hP h).elim⟩
  choose d g hg using hex
  obtain ⟨rfl, c, hc, rfl⟩ := h.eq_of_components d g fun P hP =>
    (hg P (Finset.mem_union_left _ hP)).2.2
  obtain ⟨rfl, c', hc', rfl⟩ := h'.eq_of_components d g fun P hP =>
    (hg P (Finset.mem_union_right _ hP)).2.2
  refine ⟨c * c', mul_ne_zero hc hc', d, g, fun P hP => hg P (Finsupp.support_add hP), ?_, ?_⟩
  · rw [Finsupp.sum_add_index' (by simp) (fun _ _ _ => add_mul _ _ _)]
  · rw [Finsupp.prod_add_index' (by simp) (fun _ _ _ => pow_add _ _ _), MvPolynomial.C_mul]
    ring
end IsChowFormCycle
theorem isChowFormCycle_single_iff {P : Ideal (MvPolynomial (Fin N) k)} {e dl : ℕ}
    {f : MvPolynomial (Fin (e + 1) × Fin N) k} :
    IsChowFormCycle (Finsupp.single P 1) e dl f ↔
      P.IsPrime ∧ P.IsHomogeneous (homogeneousSubmodule (Fin N) k) ∧ IsChowFormInt P e dl f := by
  refine ⟨fun h => ?_, fun h => h.2.2.single h.1 h.2.1⟩
  obtain ⟨h1, h2, d, g, h3⟩ := h.component (P := P) (by simp)
  obtain ⟨rfl, c, hc, rfl⟩ := (h3.single h1 h2).unique h
  exact ⟨h1, h2, h3.C_mul hc⟩
theorem irreducible_sq_add_sq :
    Irreducible (X 0 ^ 2 + X 1 ^ 2 : MvPolynomial (Fin 2) ℚ) := by
  rw [← MulEquiv.irreducible_iff (finSuccEquiv ℚ 1)]
  have h1 : finSuccEquiv ℚ 1 (X 0 ^ 2 + X 1 ^ 2 : MvPolynomial (Fin 2) ℚ) =
      Polynomial.X ^ 2 + Polynomial.C (X 0 ^ 2) := by
    have := finSuccEquiv_X_succ (R := ℚ) (n := 1) (j := 0)
    rw [map_add, map_pow, map_pow, finSuccEquiv_X_zero, map_pow, ← this]
    rfl
  have hm : (Polynomial.X ^ 2 + Polynomial.C (X 0 ^ 2 : MvPolynomial (Fin 1) ℚ)).Monic :=
    Polynomial.monic_X_pow_add_C _ two_ne_zero
  have hd : (Polynomial.X ^ 2 + Polynomial.C (X 0 ^ 2 : MvPolynomial (Fin 1) ℚ)).natDegree = 2 :=
    Polynomial.natDegree_X_pow_add_C
  rw [h1, hm.irreducible_iff_roots_eq_zero_of_degree_le_three (by omega) (by omega),
    Multiset.eq_zero_iff_forall_notMem]
  intro r hr
  have h2 := congrArg (MvPolynomial.eval fun _ => (1 : ℚ)) (Polynomial.isRoot_of_mem_roots hr).eq_zero
  simp at h2
  nlinarith [sq_nonneg (MvPolynomial.eval (fun _ => (1 : ℚ)) r)]
theorem isChowFormInt_sq_add_sq :
    IsChowFormInt (Ideal.span {(X 0 ^ 2 + X 1 ^ 2 : MvPolynomial (Fin 2) ℚ)}) 0 2
      (X (0, 0) ^ 2 + X (0, 1) ^ 2) := by
  refine ⟨?_, ?_, fun u => ?_⟩
  · rw [isMultiHomogeneous_iff_block]
    have hX : ∀ j : Fin 2, IsWeightedHomogeneous GlobalTheory.Chow.blockWeight
        (X (0, j) ^ 2 : MvPolynomial (Fin (0 + 1) × Fin 2) ℚ) (fun _ => 2) := by
      intro j
      convert (isWeightedHomogeneous_X ℚ GlobalTheory.Chow.blockWeight ((0 : Fin (0 + 1)), j)).pow 2 using 1
      funext b
      fin_cases b
      simp [GlobalTheory.Chow.blockWeight]
    exact (hX 0).add (hX 1)
  · have := (MulEquiv.irreducible_iff
      (renameEquiv ℚ (Equiv.uniqueProd (Fin 2) (Fin 1)).symm)).2 irreducible_sq_add_sq
    simpa using this
  · simp only [map_add, map_pow, aeval_X]
    constructor
    · intro h
      by_cases hu : u (0, 0) = 0
      · have h1 : u (0, 1) = 0 := by simpa [hu] using h
        obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (-1 : AlgebraicClosure ℚ) two_pos
        refine ⟨![1, z], by simp, fun g hg => ?_, fun i => ?_⟩
        · obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hg
          simp [hz]
        · fin_cases i
          simp [Fin.sum_univ_two, hu, h1]
      · refine ⟨![u (0, 1), -u (0, 0)], by simp [hu], fun g hg => ?_, fun i => ?_⟩
        · obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hg
          rw [add_comm] at h
          simp [h]
        · fin_cases i
          simp [Fin.sum_univ_two, mul_comm]
    · rintro ⟨y, hy, hI, hu⟩
      have h1 : y 0 ^ 2 + y 1 ^ 2 = 0 := by simpa using hI _ (Ideal.subset_span rfl)
      have h0 : y 0 ≠ 0 := by
        intro h0
        have : y 1 = 0 := by simpa [h0] using h1
        exact hy (funext fun j => by fin_cases j <;> simp [h0, this])
      have h2 := hu 0
      rw [Fin.sum_univ_two] at h2
      refine (mul_eq_zero.1 ?_).resolve_right (pow_ne_zero 2 h0)
      linear_combination u (0, 1) ^ 2 * h1 + (u (0, 0) * y 0 - u (0, 1) * y 1) * h2
example (f : MvPolynomial (Fin (0 + 1) × Fin 2) ℚ) :
    ¬ IsChowFormInt (Ideal.span {(X 0 ^ 2 + X 1 ^ 2 : MvPolynomial (Fin 2) ℚ)}) 0 1 f :=
  fun h => absurd (h.unique isChowFormInt_sq_add_sq).1 (by norm_num)
example (e dl : ℕ) (f : MvPolynomial (Fin (e + 1) × Fin N) k) :
    ¬ IsChowFormCycle (Finsupp.single (⊤ : Ideal (MvPolynomial (Fin N) k)) 1) e dl f :=
  fun h => not_isChowFormInt_top f (isChowFormCycle_single_iff.1 h).2.2
end GlobalTheory.ChowHt


