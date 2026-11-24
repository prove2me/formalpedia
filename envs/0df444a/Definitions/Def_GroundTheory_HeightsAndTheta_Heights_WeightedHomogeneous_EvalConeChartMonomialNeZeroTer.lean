-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_EvalConeChartMonomialNeZeroTer
-- name    : GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_EvalConeChartMonomialNeZeroTer
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:55:47.46016+00:00
-- url     : https://prove2.me/theorems/8788e016-d8bb-4150-9099-c73d9e9dc026
-- title:
--   Eval Cone Chart Monomial Ne Zero Ter
-- statement:
--   Definitions and structural lemmas for Eval Cone Chart Monomial Ne Zero Ter, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/EvalConeChartMonomialNeZeroTer.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
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
namespace ChartVanishing
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
def evalHom {F : Type*} [CommRing F] (z : Cone n F) : MvPolynomial (Coord n) ℤ →+* F :=
  eval₂Hom (Int.castRingHom F) fun v : Coord n ↦ z v.1 v.2
end ChartVanishing
end
end GroundTheory.Heights₂.Heights


