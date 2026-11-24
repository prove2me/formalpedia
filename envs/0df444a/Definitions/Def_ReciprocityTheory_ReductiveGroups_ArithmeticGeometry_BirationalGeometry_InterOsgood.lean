-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterOsgood
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterOsgood
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:58:06.131929+00:00
-- url     : https://prove2.me/theorems/06d9e24e-8c80-408d-abba-a809cf4ca161
-- title:
--   Inter Osgood
-- statement:
--   Definitions and structural lemmas for Inter Osgood, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterOsgood.lean

import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.Geo
def OsgoodStatement : Prop :=
  ∀ (e : ℕ) (U : Set (Fin e → ℂ)) (f : (Fin e → ℂ) → ℂ), IsOpen U → DifferentiableOn ℂ f U →
    AnalyticOnNhd ℂ f U
end ReciprocityTheory.ChartRestriction.G.Geo


