-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ScaledBaseChangeFibreSectionNonvanishingIff
-- name    : Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ScaledBaseChangeFibreSectionNonvanishingIff
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:31:21.367573+00:00
-- url     : https://prove2.me/theorems/4a0c48f5-d22e-427b-a165-56d2b21be615
-- title:
--   Scaled Base Change Fibre Section Nonvanishing Iff
-- statement:
--   Definitions and structural lemmas for Scaled Base Change Fibre Section Nonvanishing Iff, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ScaledBaseChangeFibreSectionNonvanishingIff.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
namespace GlobalTheory.Frames
end GlobalTheory.Frames


