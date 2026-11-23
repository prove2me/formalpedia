-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BesselDerivatives_LiftAOneZero
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BesselDerivatives_LiftAOneZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:24:40.626146+00:00
-- url     : https://prove2.me/theorems/dd5d7824-837f-4cbf-ae58-2b0c1e6c05e9
-- title:
--   Lift AOne Zero
-- statement:
--   Definitions and structural lemmas for Lift AOne Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BesselDerivatives/LiftAOneZero.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff Topology
noncomputable section
namespace PI.BesselDerivW
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]
def liftA (a : E →L[ℝ] E) : ℝ × E →L[ℝ] ℝ × E :=
  (ContinuousLinearMap.inr ℝ ℝ E).comp (a.comp (ContinuousLinearMap.snd ℝ ℝ E))
def rX (a : E →L[ℝ] E) (Φ : ℝ × E → V) (p : ℝ × E) : V := fderiv ℝ Φ p (liftA a p)
def dT (Φ : ℝ × E → V) (p : ℝ × E) : V := fderiv ℝ Φ p ((1 : ℝ), (0 : E))
variable {W : Set (ℝ × E)} {Φ : ℝ × E → V}
end PI.BesselDerivW


