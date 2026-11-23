-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PtBasisMapGood
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PtBasisMapGood
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:41:15.903321+00:00
-- url     : https://prove2.me/theorems/7c7d25fe-0814-4b83-b0ef-848e261fbdc5
-- title:
--   Pt Basis Map Good
-- statement:
--   Definitions and structural lemmas for Pt Basis Map Good, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/PtBasisMapGood.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PtRescaleGood
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
def ptOn (a : Fin d) (ga : Fin d → PowerSeries C) : Fin d → MvPowerSeries (Fin d) C :=
  fun b => PowerSeries.subst (X a : MvPowerSeries (Fin d) C) (ga b)
def ptBasisMap (G : LogFGL v d) (γ : Fin d → Fin d → PowerSeries C) :
    Fin d → MvPowerSeries (Fin d) C :=
  ptSumL G (List.ofFn fun a => ptOn a (γ a))
end
end ReciprocityTheory.ChartRestriction.G.Sh


