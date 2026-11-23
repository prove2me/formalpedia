-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasFDerivAtWeightTwoDerivativeEisensteinTerm
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasFDerivAtWeightTwoDerivativeEisensteinTerm
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:20:02.093843+00:00
-- url     : https://prove2.me/theorems/09f0d947-48f4-4f96-843a-487fb36ad32b
-- title:
--   Has FDeriv At Weight Two Derivative Eisenstein Term
-- statement:
--   Definitions and structural lemmas for Has FDeriv At Weight Two Derivative Eisenstein Term, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasFDerivAtWeightTwoDerivativeEisensteinTerm.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DifferentiableRisingS
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasFDerivAtDeformedProductDerivativeTerm
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
import Theorems.Thm_GlobalTheory_WeightTwoSum_dz_apply
import Theorems.Thm_GlobalTheory_WeightTwoSum_dzbar_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub
attribute [local simp] GlobalTheory.WeightTwoSum.dz_apply
attribute [local simp] GlobalTheory.WeightTwoSum.dzbar_apply


set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.WeightTwoSum
open scoped ContDiff nonZeroDivisors
namespace GlobalTheory.WeightTwoSum
theorem norm_cpow_eq_mul_conj_cpow (u s : ℂ) :
    ((‖u‖ : ℝ) : ℂ) ^ (-2 * s) = (u * starRingEnd ℂ u) ^ (-s) := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  rw [sq, Complex.mul_cpow_ofReal_nonneg (norm_nonneg _) (norm_nonneg _)]
  rw [show -2 * s = ((2:ℕ):ℂ) * (-s) by push_cast; ring, Complex.cpow_nat_mul, sq]
theorem hasFDerivAt_factor_norm_cpow {I : Type} [Fintype I] (j : I) (a c K σ : ℂ) (n : ℕ) (z : I → ℂ)
    (hu : a + z j * c ≠ 0) :
    HasFDerivAt (𝕜 := ℝ) (fun w : I → ℂ => K * (a + w j * c)⁻¹ ^ n * ((‖a + w j * c‖ : ℝ) : ℂ) ^ (-2 * σ))
      ((K * (a + z j * c)⁻¹ ^ n * ((‖a + z j * c‖ : ℝ) : ℂ) ^ (-2 * σ) * (-((n : ℂ) + σ) * c / (a + z j * c))) • dz j +
       (K * (a + z j * c)⁻¹ ^ n * ((‖a + z j * c‖ : ℝ) : ℂ) ^ (-2 * σ) *
         (-σ * starRingEnd ℂ c / starRingEnd ℂ (a + z j * c))) • dzbar j) z := by
  simp_rw [norm_cpow_eq_mul_conj_cpow]
  set u := a + z j * c with hu_def
  have hU : HasFDerivAt (𝕜 := ℝ) (fun w : I → ℂ => a + w j * c) (c • dz j) z :=
    ((dz j).hasFDerivAt.mul_const c).const_add a
  have hC : HasFDerivAt (𝕜 := ℝ) (fun w : I → ℂ => starRingEnd ℂ (a + w j * c))
      ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (c • dz j)) z :=
    (Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt.comp z hU
  have hP := hU.mul hC
  have hcu : starRingEnd ℂ u ≠ 0 := (map_ne_zero _).2 hu
  have hne : u * starRingEnd ℂ u ≠ 0 := mul_ne_zero hu hcu
  have hslit : u * starRingEnd ℂ u ∈ Complex.slitPlane := by
    rw [Complex.mul_conj]
    exact Complex.ofReal_mem_slitPlane.2 (Complex.normSq_pos.2 hu)
  have hpow := ((hasDerivAt_id (u * starRingEnd ℂ u)).cpow_const (c := -σ) hslit).comp_hasFDerivAt z hP
  have hinv := (((hasDerivAt_id u).inv hu).pow n).comp_hasFDerivAt z hU
  have h := (hinv.const_mul K).mul hpow
  refine h.congr_fderiv ?_
  ext v
  clear h hinv hpow hP hC hU hslit
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    dz_apply, dzbar_apply, smul_eq_mul, ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply, map_mul,
    Function.comp_apply, id, Pi.inv_apply, Pi.pow_apply, Pi.mul_apply, ← hu_def]
  rw [Complex.cpow_sub _ _ hne, Complex.cpow_one]
  rcases n with _ | n
  · simp
    field_simp
    ring
  · simp only [Nat.add_sub_cancel, inv_pow]
    field_simp
    push_cast
    ring
theorem hasFDerivAt_eTerm : ∀ (E : Type) [Field E] [NumberField E] (I : Type) [Fintype I] [DecidableEq I]
    (φ : I → E →+* ℂ) (m : I → ℕ) (σ : ℂ) (x : E), x ≠ 0 → ∀ z ∈ polydisc I,
    HasFDerivAt (𝕜 := ℝ) (fun w : I → ℂ => eTerm φ m σ w x)
      (∑ j, (eTerm φ (m + Pi.single j 1) σ z x • dz j +
        (eTerm φ m σ z x * (-σ * φ j x / starRingEnd ℂ (defCoord φ z x j))) • dzbar j)) z := by
  intro E _ _ I _ _ φ m σ x hx z hz
  let C : ℕ → ℂ := fun n => (-1 : ℂ) ^ n * ∏ j ∈ Finset.range n, (2 + σ + j)
  let c : I → ℂ := fun i => starRingEnd ℂ (φ i x)
  let F : I → (I → ℂ) → ℂ := fun i w => C (m i) * c i ^ m i * (φ i x + w i * c i)⁻¹ ^ (2 + m i) *
    ((‖φ i x + w i * c i‖ : ℝ) : ℂ) ^ (-2 * σ)
  let α : I → ℂ := fun i => -(((2 + m i : ℕ) : ℂ) + σ) * c i / (φ i x + z i * c i)
  let β : I → ℂ := fun i => -σ * starRingEnd ℂ (c i) / starRingEnd ℂ (φ i x + z i * c i)
  have hF : ∀ i, HasFDerivAt (𝕜 := ℝ) (F i) ((F i z * α i) • dz i + (F i z * β i) • dzbar i) z := fun i =>
    hasFDerivAt_factor_norm_cpow i (φ i x) (c i) (C (m i) * c i ^ m i) σ (2 + m i) z
      (GlobalTheory.DeformedSum.defCoord_ne_zero φ z hz x hx i)
  have hprod := HasFDerivAt.finset_prod (u := Finset.univ) (g := F) (x := z) (fun i _ => hF i)
  have hfun : (fun w : I → ℂ => eTerm φ m σ w x) = fun w => ∏ i ∈ Finset.univ, F i w := rfl
  have hval : eTerm φ m σ z x = ∏ i ∈ Finset.univ, F i z := rfl
  rw [hfun]
  refine hprod.congr_fderiv ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  have key : ∀ (f g : I → ℂ), (∀ i, i ≠ j → g i = f i) →
      ∏ i, g i = (∏ i ∈ Finset.univ.erase j, f i) * g j := by
    intro f g h
    rw [← Finset.prod_erase_mul Finset.univ g (Finset.mem_univ j)]
    congr 1
    exact Finset.prod_congr rfl fun i hi => h i (Finset.ne_of_mem_erase hi)
  rw [smul_add, smul_smul, smul_smul]
  congr 1
  · congr 1
    unfold eTerm
    rw [key (fun i => F i z) _ ?_]
    · congr 1
      simp only [Pi.add_apply, Pi.single_eq_same, F, α, C, c, defCoord, Finset.prod_range_succ, pow_succ]
      push_cast
      ring
    · intro i hij
      simp only [Pi.add_apply, Pi.single_eq_of_ne hij, add_zero]
      rfl
  · congr 1
    rw [hval, ← Finset.prod_erase_mul Finset.univ (fun i => F i z) (Finset.mem_univ j)]
    simp only [β, c, defCoord, Complex.conj_conj]
    ring
end GlobalTheory.WeightTwoSum
example : ∀ (E : Type) [Field E] [NumberField E] (I : Type) [Fintype I] [DecidableEq I] (φ : I → E →+* ℂ) (m : I → ℕ) (σ : ℂ) (x : E), x ≠ 0 → ∀ z ∈ polydisc I, HasFDerivAt (𝕜 := ℝ) (fun w : I → ℂ => eTerm φ m σ w x) (∑ j, (eTerm φ (m + Pi.single j 1) σ z x • dz j + (eTerm φ m σ z x * (-σ * φ j x / starRingEnd ℂ (defCoord φ z x j))) • dzbar j)) z :=
  GlobalTheory.WeightTwoSum.hasFDerivAt_eTerm


