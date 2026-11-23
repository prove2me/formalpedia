-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BesselDerivatives_ContDiffOnDirectionalDerivative
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BesselDerivatives_ContDiffOnDirectionalDerivative
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:27:22.995409+00:00
-- url     : https://prove2.me/theorems/c3fdb873-57c9-4fc4-b952-73edc6317daf
-- title:
--   Cont Diff On Directional Derivative
-- statement:
--   Definitions and structural lemmas for Cont Diff On Directional Derivative, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BesselDerivatives/ContDiffOnDirectionalDerivative.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BesselDerivatives_LiftAOneZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff Topology
open Filter
noncomputable section
namespace PI.BesselDerivW
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]
def r1 (a : E →L[ℝ] E) (G : E → V) (g : E) : V := fderiv ℝ G g (a g)
def r1W : List (E →L[ℝ] E) → (E → V) → E → V
  | [], G => G
  | a :: w, G => r1 a (r1W w G)
def r2W : List (E →L[ℝ] E) → (ℝ × E → V) → ℝ × E → V
  | [], Φ => Φ
  | a :: w, Φ => rX a (r2W w Φ)
end PI.BesselDerivW


