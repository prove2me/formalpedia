-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_RigidifiedOfChart
-- name    : Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_RigidifiedOfChart
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:58:23.613776+00:00
-- url     : https://prove2.me/theorems/606b9655-4b70-4ddd-92c7-08126e596c90
-- title:
--   Rigidified Of Chart
-- statement:
--   Definitions and structural lemmas for Rigidified Of Chart, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/RigidifiedOfChart.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory.ChartRig
variable {X Y : Scheme.{0}}
end GlobalTheory.ChartRig


