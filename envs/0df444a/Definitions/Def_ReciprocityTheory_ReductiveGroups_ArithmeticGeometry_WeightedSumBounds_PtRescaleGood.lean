-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PtRescaleGood
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PtRescaleGood
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:37:35.208912+00:00
-- url     : https://prove2.me/theorems/ca88fbf0-63a6-405e-8bfe-1ae5fb630d98
-- title:
--   Pt Rescale Good
-- statement:
--   Definitions and structural lemmas for Pt Rescale Good, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/PtRescaleGood.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PtSolveMapFixedIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.Sh
open MvPowerSeries ReciprocityTheory.PGsh
open Classical
noncomputable section
variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d : ℕ}
def ptAdd (G : LogFGL v d) {τ : Type*} (x y : Fin d → MvPowerSeries τ C) :
    Fin d → MvPowerSeries τ C :=
  fun a => subst (Sum.elim x y) (G.F a)
def ptSumL (G : LogFGL v d) {τ : Type*} :
    List (Fin d → MvPowerSeries τ C) → (Fin d → MvPowerSeries τ C)
  | [] => 0
  | x :: l => ptAdd G x (ptSumL G l)
end
end ReciprocityTheory.ChartRestriction.G.Sh


