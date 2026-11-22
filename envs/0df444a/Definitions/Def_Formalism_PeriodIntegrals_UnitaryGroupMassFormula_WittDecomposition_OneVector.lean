-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WittDecomposition_OneVector
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WittDecomposition_OneVector
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T22:26:50.170213+00:00
-- url     : https://prove2.me/theorems/495bf989-ac94-492c-b905-86a363390267
-- title:
--   One Vector
-- statement:
--   Definitions and structural lemmas for One Vector, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WittDecomposition/OneVector.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WittDecomposition_Anisotropic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace PI.Witt
section
variable {K V : Type} [Field K] [StarRing K] [CharZero K] [AddCommGroup V] [Module K V]
  (B : V →ₗ⋆[K] V →ₗ[K] K)
def qrefl (v : V) (a : K) : V →ₗ[K] V :=
  LinearMap.id - (a⁻¹ • (B v)).smulRight v
lemma qrefl_apply (v : V) (a : K) (z : V) : qrefl B v a z = z - (a⁻¹ * B v z) • v := by
  simp [qrefl, LinearMap.smulRight_apply, smul_eq_mul]
lemma qrefl_qrefl (v : V) (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) (hv : B v v = a + b) (z : V) :
    qrefl B v a (qrefl B v b z) = z := by
  rw [qrefl_apply, qrefl_apply, map_sub, map_smul, smul_eq_mul, hv, sub_sub, ← add_smul]
  have h : b⁻¹ * B v z + a⁻¹ * (B v z - b⁻¹ * B v z * (a + b)) = 0 := by
    field_simp
    ring
  rw [h, zero_smul, sub_zero]
def qreflEquiv (v : V) (a : K) (ha : a ≠ 0) (hv : B v v = a + star a) : V ≃ₗ[K] V :=
  LinearEquiv.ofLinearMap (qrefl B v a) (qrefl B v (star a))
    (LinearMap.ext fun z => qrefl_qrefl B v a (star a) ha (by simpa using ha) hv z)
    (LinearMap.ext fun z => qrefl_qrefl B v (star a) a (by simpa using ha) ha
      (by rw [hv, add_comm]) z)
end
end PI.Witt


