-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JacobianTransvectionSplitting_DiagonalOneJacobian
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JacobianTransvectionSplitting_DiagonalOneJacobian
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:19:34.28312+00:00
-- url     : https://prove2.me/theorems/ccf9df5d-8466-4140-8b8c-a53c4fdd4c4b
-- title:
--   Diagonal One Jacobian
-- statement:
--   Definitions and structural lemmas for Diagonal One Jacobian, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/JacobianTransvectionSplitting/DiagonalOneJacobian.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JacobianTransvectionSplitting_DiscreteHaar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Function Topology
open scoped ENNReal NNReal Pointwise
namespace PI.NglqJacSplitW
section Diag
variable {F : Type} [Field F] [TopologicalSpace F] [IsTopologicalDivisionRing F]
  {ι : Type} [Fintype ι] [DecidableEq ι]
def scaleAt (i : ι) (a : F) (ha : a ≠ 0) : (ι → F) ≃ₜ+ (ι → F) where
  toFun x := update x i (a * x i)
  invFun x := update x i (a⁻¹ * x i)
  left_inv x := by
    ext j
    by_cases hj : j = i
    · subst hj
      simp [inv_mul_cancel_left₀ ha]
    · simp [update_of_ne hj]
  right_inv x := by
    ext j
    by_cases hj : j = i
    · subst hj
      simp [mul_inv_cancel_left₀ ha]
    · simp [update_of_ne hj]
  map_add' x y := by
    ext j
    by_cases hj : j = i
    · subst hj
      simp [mul_add]
    · simp [update_of_ne hj]
  continuous_toFun := continuous_id.update i (continuous_const.mul (continuous_apply i))
  continuous_invFun := continuous_id.update i (continuous_const.mul (continuous_apply i))
end Diag
end PI.NglqJacSplitW


