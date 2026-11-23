-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BesselDerivatives_ExpSup
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BesselDerivatives_ExpSup
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:29:54.57508+00:00
-- url     : https://prove2.me/theorems/43cee1d0-5680-4077-9255-827089c5c4b9
-- title:
--   Exp Sup
-- statement:
--   Definitions and structural lemmas for Exp Sup, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BesselDerivatives/ExpSup.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BesselDerivatives_ContDiffOnDirectionalDerivative
import Definitions.Def_Formalism_PeriodIntegrals_BesselDeriv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff Topology
open Matrix
noncomputable section
namespace PI.BesselDerivW
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
def mulRc (X : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
  LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ X)
def mulLc (X : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
  LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ X)
end PI.BesselDerivW


