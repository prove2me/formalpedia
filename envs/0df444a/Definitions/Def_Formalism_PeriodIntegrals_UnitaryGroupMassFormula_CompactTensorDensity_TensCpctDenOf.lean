-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompactTensorDensity_TensCpctDenOf
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompactTensorDensity_TensCpctDenOf
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:14:37.703278+00:00
-- url     : https://prove2.me/theorems/2289e778-cbaa-4f0d-bf78-a7508b3fa986
-- title:
--   Tens Cpct Den Of
-- statement:
--   Definitions and structural lemmas for Tens Cpct Den Of, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CompactTensorDensity/TensCpctDenOf.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FinOrdAd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.TensCpctDenWork
open NumberField IsDedekindDomain TensorProduct
section Coord
variable {F E R : Type} [Field F] [CommRing E] [Algebra F E] [CommRing R] [Algebra F R]
def coordR (φ : E →ₗ[F] F) : E ⊗[F] R →ₗ[F] R :=
  TensorProduct.lid F R ∘ₗ φ.rTensor R
theorem coordR_tmul (φ : E →ₗ[F] F) (e : E) (x : R) : coordR φ (e ⊗ₜ[F] x) = φ e • x := by
  simp [coordR]
attribute [local instance] Algebra.TensorProduct.rightAlgebra
theorem coordR_smul (φ : E →ₗ[F] F) (a : R) (t : E ⊗[F] R) :
    coordR φ (a • t) = a * coordR φ t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul e x =>
    rw [Algebra.smul_def, Algebra.TensorProduct.right_algebraMap_apply,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, coordR_tmul, coordR_tmul, mul_smul_comm]
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, mul_add]
def coordL (φ : E →ₗ[F] F) : E ⊗[F] R →ₗ[R] R where
  toFun := coordR φ
  map_add' := map_add _
  map_smul' a t := by rw [RingHom.id_apply, smul_eq_mul]; exact coordR_smul φ a t
end Coord
end PI.TensCpctDenWork


