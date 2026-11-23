-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_GlobFnsDvrPf
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_GlobFnsDvrPf
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:44:57.783661+00:00
-- url     : https://prove2.me/theorems/80782225-9c67-4c91-8120-a0a685b0e749
-- title:
--   Glob Fns Dvr Pf
-- statement:
--   Definitions and structural lemmas for Glob Fns Dvr Pf, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/GlobFnsDvrPf.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_GlobalFunctionsDvrPowers
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_GlobalFunctionsDvrGeneric
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out
end ReciprocityTheory.ChartRestriction.G.Geo.Tor


