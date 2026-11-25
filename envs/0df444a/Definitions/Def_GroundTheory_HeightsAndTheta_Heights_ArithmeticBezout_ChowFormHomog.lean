-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ChowFormHomog
-- name    : GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ChowFormHomog
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T09:00:00.706442+00:00
-- url     : https://prove2.me/theorems/4abd5791-e2f8-542c-9811-50575d1a0fd8
-- title:
--   Chow Form Homog
-- statement:
--   Definitions and structural lemmas for Chow Form Homog, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/ChowFormHomog.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ChowDegree
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IsChowForm_degrees_eq_e2d80fd5d845
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_component_ne_zero_of_mem_31fa3e9616ec
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isChowForm_point_62847896aaea
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isMultiHomog_iff_4e11cc8773b5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isProjPrime_point_e4b734f59300
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isWeightedHomogeneous_of_mul_left_246006f8ee8f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_sum_weightSet_component_481e5721c867
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_weightSet_nonempty_9935efbea46e

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
theorem aeval_scale_of_isWeightedHomogeneous {σ R A : Type*} [CommSemiring R] [CommSemiring A]
    [Algebra R A] {w : σ → ℕ} {p : MvPolynomial σ R} {a : ℕ} (hp : IsWeightedHomogeneous w p a)
    (t : A) (u : σ → A) : aeval (fun j => t ^ w j * u j) p = t ^ a * aeval u p := by
  classical
  conv_lhs => rw [p.as_sum]
  conv_rhs => rw [p.as_sum]
  rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [aeval_monomial, aeval_monomial, Finsupp.prod, Finsupp.prod]
  simp only [mul_pow, Finset.prod_mul_distrib, ← pow_mul]
  rw [Finset.prod_pow_eq_pow_sum]
  have hw : ∑ j ∈ d.support, w j * d j = a := by
    rw [← hp (mem_support_iff.mp hd), Finsupp.weight_apply, Finsupp.sum]
    simp [smul_eq_mul, mul_comm]
  rw [hw]
  ring
variable {F : Type} [Field F] {n k : ℕ}
theorem scale_mem_incidence {I : Ideal (MvPolynomial (Fin n) F)}
    {u : Fin k × Fin n → AlgebraicClosure F} (hu : u ∈ incidence I k) (i : Fin k)
    (t : AlgebraicClosure F) : (fun ij => t ^ inGroup i ij * u ij) ∈ incidence I k := by
  obtain ⟨x, hx0, hxI, hux⟩ := hu
  refine ⟨x, hx0, hxI, fun i' => ?_⟩
  have hc : ∀ j : Fin n, t ^ inGroup i (i', j) * u (i', j) * x j =
      t ^ (if i' = i then 1 else 0) * (u (i', j) * x j) := fun j => by rw [mul_assoc]; rfl
  refine Eq.trans (Finset.sum_congr rfl fun j _ => hc j) ?_
  rw [← Finset.mul_sum, hux i', mul_zero]
theorem component_vanish_incidence {I : Ideal (MvPolynomial (Fin n) F)}
    {f : MvPolynomial (Fin k × Fin n) F} (hf : ∀ u ∈ incidence I k, aeval u f = 0) (i : Fin k)
    {a : ℕ} (ha : a ∈ weightSet (inGroup (n := n) i) f) :
    ∀ u ∈ incidence I k, aeval u (weightedHomogeneousComponent (inGroup (n := n) i) a f) = 0 := by
  classical
  intro u hu
  set w := inGroup (n := n) i
  set S := weightSet w f
  set q : Polynomial (AlgebraicClosure F) :=
    ∑ b ∈ S, Polynomial.C (aeval u (weightedHomogeneousComponent w b f)) * Polynomial.X ^ b with hq_def
  have hq : q = 0 := by
    apply Polynomial.funext
    intro t
    have h1 := hf _ (scale_mem_incidence hu i t)
    rw [← sum_weightSet_component (w := w) f, map_sum] at h1
    simp only [hq_def, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_zero]
    rw [← h1]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [aeval_scale_of_isWeightedHomogeneous (weightedHomogeneousComponent_isWeightedHomogeneous b f),
      mul_comm]
  have hc := congrArg (fun p => Polynomial.coeff p a) hq
  simp only [hq_def, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow,
    Polynomial.coeff_zero] at hc
  rw [Finset.sum_ite_eq, if_pos ha] at hc
  exact hc
theorem IsChowForm.exists_isWeightedHomogeneous_inGroup {I : Ideal (MvPolynomial (Fin n) F)}
    {f : MvPolynomial (Fin k × Fin n) F} (hf : IsChowForm I k f) (i : Fin k) :
    ∃ a, IsWeightedHomogeneous (inGroup (n := n) i) f a := by
  obtain ⟨a, ha⟩ := weightSet_nonempty (w := inGroup (n := n) i) hf.1
  have hvan : ∀ u ∈ incidence I k, aeval u f = 0 := (hf.2 f).mpr dvd_rfl
  obtain ⟨r, hr⟩ := (hf.2 _).mp (component_vanish_incidence hvan i ha)
  have hc := component_ne_zero_of_mem ha
  rw [hr] at hc
  refine isWeightedHomogeneous_of_mul_left (m := a) ?_ hf.1 (right_ne_zero_of_mul hc)
  rw [← hr]
  exact weightedHomogeneousComponent_isWeightedHomogeneous a f
theorem zero_mem_incidence {P : Ideal (MvPolynomial (Fin n) F)} (hP : IsProjPrime P) (k : ℕ) :
    (0 : Fin k × Fin n → AlgebraicClosure F) ∈ incidence P k := by
  obtain ⟨j, hj⟩ := hP.isRelevant
  have hex : ∃ x ∈ zeroLocus (AlgebraicClosure F) P, x ≠ 0 := by
    by_contra h
    push Not at h
    apply hj
    have hrad : X j ∈ vanishingIdeal F (zeroLocus (AlgebraicClosure F) P) := by
      rw [mem_vanishingIdeal_iff]
      intro x hx
      rw [h x hx]
      simp
    rwa [vanishingIdeal_zeroLocus_eq_radical, hP.isPrime.radical] at hrad
  obtain ⟨x, hx, hx0⟩ := hex
  exact ⟨x, hx0, fun g hg => mem_zeroLocus_iff.mp hx g hg, fun i => by simp⟩
theorem IsChowForm.exists_multiHomog {P : Ideal (MvPolynomial (Fin n) F)}
    {f : MvPolynomial (Fin k × Fin n) F} (hP : IsProjPrime P) (hf : IsChowForm P k f) :
    ∃ δ, 1 ≤ δ ∧ IsMultiHomog δ f := by
  rcases Nat.eq_zero_or_pos k with hk0 | hk
  · subst hk0
    exact ⟨1, le_rfl, fun d _ => funext fun i => i.elim0⟩
  choose a ha using fun i => hf.exists_isWeightedHomogeneous_inGroup i
  have hδ : IsMultiHomog (a ⟨0, hk⟩) f := (isMultiHomog_iff _ _).mpr fun i => by
    rw [hf.degrees_eq ha ⟨0, hk⟩ i]
    exact ha i
  refine ⟨a ⟨0, hk⟩, Nat.one_le_iff_ne_zero.mpr fun h0 => ?_, hδ⟩
  rw [h0] at hδ
  have hd0 : ∀ d ∈ f.support, d = 0 := by
    intro d hd
    have h := congrFun (hδ (mem_support_iff.mp hd))
    ext ij
    by_contra hne
    have h1 := h ij.1
    rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply] at h1
    have h2 := (Finset.sum_eq_zero_iff.mp h1) ij (Finsupp.mem_support_iff.mpr hne)
    simp [groupWeight] at h2
    exact hne h2
  have hC : f = C (coeff 0 f) := by
    ext d
    rw [coeff_C]
    split_ifs with hd
    · rw [hd]
    · by_contra hne
      exact hd (hd0 d (mem_support_iff.mpr hne)).symm
  have hz := (hf.2 f).mpr dvd_rfl 0 (zero_mem_incidence hP k)
  rw [hC, aeval_C, map_eq_zero_iff _ (algebraMap F (AlgebraicClosure F)).injective] at hz
  exact hf.1 (by rw [hC, hz, C_0])
example : ∃ δ, 1 ≤ δ ∧ IsMultiHomog δ (X (0, 0) : MvPolynomial (Fin 1 × Fin 1) ℚ) :=
  (isChowForm_point ℚ).exists_multiHomog (isProjPrime_point ℚ)
end
end GroundTheory.Heights₂.Heights


