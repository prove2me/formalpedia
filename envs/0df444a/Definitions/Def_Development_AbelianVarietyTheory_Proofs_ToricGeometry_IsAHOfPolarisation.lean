-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsAHOfPolarisation
-- name    : Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsAHOfPolarisation
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:58:17.448595+00:00
-- url     : https://prove2.me/theorems/dc519e78-4ea7-4eb5-8827-e17a35d13025
-- title:
--   Is AHOf Polarisation
-- statement:
--   Definitions and structural lemmas for Is AHOf Polarisation, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/IsAHOfPolarisation.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
namespace GlobalTheory
def thetaZeroSec {X : Scheme.{0}} (L : LB X) : L.Sec where
  f _ := 0
  compat := by intros; simp
end GlobalTheory


