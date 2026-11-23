-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasFDerivAtDeformedProductDerivativeTerm
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasFDerivAtDeformedProductDerivativeTerm
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:06:18.595671+00:00
-- url     : https://prove2.me/theorems/ee61bd03-7dd9-4024-8b8f-cd2057750d15
-- title:
--   Has FDeriv At Deformed Product Derivative Term
-- statement:
--   Definitions and structural lemmas for Has FDeriv At Deformed Product Derivative Term, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasFDerivAtDeformedProductDerivativeTerm.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DTermOrigin
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub


set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.DeformedSum
namespace GlobalTheory.DeformedSum
theorem hasDerivAt_inv_pow_affine (c a b : ℂ) (n : ℕ) (u : ℂ) (hu : a + u * b ≠ 0) :
    HasDerivAt (fun t : ℂ => c * (a + t * b)⁻¹ ^ n)
      (c * (-(n : ℂ) * b * (a + u * b)⁻¹ ^ (n + 1))) u := by
  have h1 : HasDerivAt (fun t : ℂ => a + t * b) b u := by
    simpa using ((hasDerivAt_id u).mul_const b).const_add a
  have h2 : HasDerivAt (fun t : ℂ => c * (a + t * b)⁻¹ ^ n)
      (c * (n * (a + u * b)⁻¹ ^ (n - 1) * (-b / (a + u * b) ^ 2))) u :=
    ((h1.inv hu).pow n).const_mul c
  refine h2.congr_deriv ?_
  rcases n with _ | n
  · simp
  · rw [Nat.add_sub_cancel, div_eq_mul_inv, ← inv_pow]
    push_cast
    ring
theorem defCoord_ne_zero {E : Type} [Field E] [NumberField E] {I : Type} (φ : I → E →+* ℂ) (z : I → ℂ)
    (hz : z ∈ polydisc I) (x : E) (hx : x ≠ 0) (i : I) : defCoord φ z x i ≠ 0 := by
  intro h
  have hφ : φ i x ≠ 0 := (map_ne_zero (φ i)).mpr hx
  have hpos : 0 < ‖φ i x‖ := norm_pos_iff.mpr hφ
  have hz1 : ‖z i‖ < 1 := hz i
  unfold defCoord at h
  have heq : φ i x = -(z i * starRingEnd ℂ (φ i x)) := eq_neg_of_add_eq_zero_left h
  have hn : ‖φ i x‖ = ‖z i‖ * ‖φ i x‖ := by
    conv_lhs => rw [heq]
    rw [norm_neg, norm_mul, Complex.norm_conj]
  have hlt := mul_lt_of_lt_one_left hpos hz1
  linarith
theorem hasFDerivAt_dTerm : ∀ (E : Type) [Field E] [NumberField E] (I : Type) [Fintype I] [DecidableEq I] (φ : I → E →+* ℂ)
    (k : ℕ) (m : I → ℕ) (x : E), x ≠ 0 → ∀ z ∈ polydisc I,
    HasFDerivAt (fun w : I → ℂ => dTerm φ k m w x)
      (∑ j, dTerm φ k (m + Pi.single j 1) z x • (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : I => ℂ) j)) z := by
  intro E _ _ I _ _ φ k m x hx z hz
  set C : I → ℂ := fun i => ((-1 : ℂ) ^ m i * ∏ j ∈ Finset.range (m i), ((k : ℂ) + j)) *
    (starRingEnd ℂ (φ i x)) ^ m i with hC
  have hd : ∀ i, HasFDerivAt (fun w : I → ℂ => C i * (defCoord φ w x i)⁻¹ ^ (k + m i))
      ((C i * (-((k + m i : ℕ) : ℂ) * starRingEnd ℂ (φ i x) * (defCoord φ z x i)⁻¹ ^ (k + m i + 1))) •
        ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : I => ℂ) i) z := by
    intro i
    have h1 := hasDerivAt_inv_pow_affine (C i) (φ i x) (starRingEnd ℂ (φ i x)) (k + m i) (z i)
      (defCoord_ne_zero φ z hz x hx i)
    have h2 := h1.comp_hasFDerivAt z (hasFDerivAt_apply (𝕜 := ℂ) (F' := fun _ : I => ℂ) i z)
    exact h2
  have hprod := HasFDerivAt.finsetProd (u := Finset.univ) (fun i _ => hd i)
  have hfun : (fun w : I → ℂ => dTerm φ k m w x) =
      (fun w => ∏ i ∈ Finset.univ, C i * (defCoord φ w x i)⁻¹ ^ (k + m i)) := rfl
  rw [hfun]
  refine hprod.congr_fderiv ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_smul]
  congr 1
  symm
  unfold dTerm
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ j)]
  congr 1
  · refine Finset.prod_congr rfl fun i hi => ?_
    have hij : i ≠ j := Finset.ne_of_mem_erase hi
    simp [hC, hij]
  · simp only [hC, Pi.add_apply, Pi.single_eq_same, Finset.prod_range_succ]
    push_cast
    ring
end GlobalTheory.DeformedSum
example : ∀ (E : Type) [Field E] [NumberField E] (I : Type) [Fintype I] [DecidableEq I] (φ : I → E →+* ℂ) (k : ℕ) (m : I → ℕ) (x : E), x ≠ 0 → ∀ z ∈ polydisc I, HasFDerivAt (fun w : I → ℂ => dTerm φ k m w x) (∑ j, dTerm φ k (m + Pi.single j 1) z x • (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : I => ℂ) j)) z := GlobalTheory.DeformedSum.hasFDerivAt_dTerm


