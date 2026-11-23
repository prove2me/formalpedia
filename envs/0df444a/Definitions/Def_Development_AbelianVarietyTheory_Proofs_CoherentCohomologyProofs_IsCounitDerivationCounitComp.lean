-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsCounitDerivationCounitComp
-- name    : Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsCounitDerivationCounitComp
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:14:51.179119+00:00
-- url     : https://prove2.me/theorems/e1d74b77-9aa0-4c40-9038-2eed3d4eaa88
-- title:
--   Is Counit Derivation Counit Comp
-- statement:
--   Definitions and structural lemmas for Is Counit Derivation Counit Comp, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsCounitDerivationCounitComp.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
namespace GlobalTheory.LeftRightDerivations
variable {k : Type*} {H : Type*} [CommSemiring k] [CommSemiring H] [Bialgebra k H]
def IsCounitDerivation (φ : H →ₗ[k] k) : Prop :=
  ∀ a b : H, φ (a * b) =
    Coalgebra.counit (R := k) a * φ b + Coalgebra.counit (R := k) b * φ a
noncomputable def contrRight (φ : H →ₗ[k] k) : H ⊗[k] H →ₗ[k] H :=
  (TensorProduct.rid k H).toLinearMap ∘ₗ LinearMap.lTensor H φ
noncomputable def contrLeft (φ : H →ₗ[k] k) : H ⊗[k] H →ₗ[k] H :=
  (TensorProduct.lid k H).toLinearMap ∘ₗ LinearMap.rTensor H φ
@[simp] theorem contrRight_tmul (φ : H →ₗ[k] k) (a b : H) :
    contrRight φ (a ⊗ₜ[k] b) = φ b • a := by
  simp [contrRight]
@[simp] theorem contrLeft_tmul (φ : H →ₗ[k] k) (a b : H) :
    contrLeft φ (a ⊗ₜ[k] b) = φ a • b := by
  simp [contrLeft]
theorem contrRight_counit_comul (a : H) :
    contrRight (Coalgebra.counit (R := k)) (Coalgebra.comul (R := k) a) = a := by

  simp [contrRight, Coalgebra.lTensor_counit_comul]
theorem contrLeft_counit_comul (a : H) :
    contrLeft (Coalgebra.counit (R := k)) (Coalgebra.comul (R := k) a) = a := by
  simp [contrLeft, Coalgebra.rTensor_counit_comul]
theorem contrRight_mul {φ : H →ₗ[k] k} (hφ : IsCounitDerivation φ) (s t : H ⊗[k] H) :
    contrRight φ (s * t) =
      contrRight (Coalgebra.counit (R := k)) s * contrRight φ t +
        contrRight (Coalgebra.counit (R := k)) t * contrRight φ s := by

  induction s using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [add_mul, map_add, hx, hy]; ring
  | tmul a b =>
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [mul_add, map_add, hx, hy]; ring
    | tmul c d =>
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      simp only [contrRight_tmul, hφ b d, Algebra.smul_def, map_add, map_mul]
      ring
theorem contrLeft_mul {φ : H →ₗ[k] k} (hφ : IsCounitDerivation φ) (s t : H ⊗[k] H) :
    contrLeft φ (s * t) =
      contrLeft (Coalgebra.counit (R := k)) s * contrLeft φ t +
        contrLeft (Coalgebra.counit (R := k)) t * contrLeft φ s := by
  induction s using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [add_mul, map_add, hx, hy]; ring
  | tmul a b =>
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [mul_add, map_add, hx, hy]; ring
    | tmul c d =>
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      simp only [contrLeft_tmul, hφ a c, Algebra.smul_def, map_add, map_mul]
      ring
theorem contrRight_one (φ : H →ₗ[k] k) : contrRight φ 1 = φ 1 • (1 : H) := by
  rw [Algebra.TensorProduct.one_def, contrRight_tmul]
theorem contrLeft_one (φ : H →ₗ[k] k) : contrLeft φ 1 = φ 1 • (1 : H) := by
  rw [Algebra.TensorProduct.one_def, contrLeft_tmul]
section Ring
variable {k : Type*} {H : Type*} [CommRing k] [CommRing H] [Bialgebra k H]
theorem IsCounitDerivation.map_one {φ : H →ₗ[k] k} (hφ : IsCounitDerivation φ) : φ 1 = 0 := by

  have h := hφ 1 1
  rw [mul_one, Bialgebra.counit_one, one_mul] at h
  simpa using h
noncomputable def derivRight (φ : H →ₗ[k] k) (hφ : IsCounitDerivation φ) : Derivation k H H where
  toLinearMap := contrRight φ ∘ₗ Coalgebra.comul (R := k)
  map_one_eq_zero' := by
    rw [LinearMap.comp_apply, Bialgebra.comul_one, contrRight_one, hφ.map_one, zero_smul]
  leibniz' a b := by
    simp only [LinearMap.comp_apply, Bialgebra.comul_mul, contrRight_mul hφ,
      contrRight_counit_comul, smul_eq_mul]
noncomputable def derivLeft (φ : H →ₗ[k] k) (hφ : IsCounitDerivation φ) : Derivation k H H where
  toLinearMap := contrLeft φ ∘ₗ Coalgebra.comul (R := k)
  map_one_eq_zero' := by
    rw [LinearMap.comp_apply, Bialgebra.comul_one, contrLeft_one, hφ.map_one, zero_smul]
  leibniz' a b := by
    simp only [LinearMap.comp_apply, Bialgebra.comul_mul, contrLeft_mul hφ,
      contrLeft_counit_comul, smul_eq_mul]
end Ring
end GlobalTheory.LeftRightDerivations


