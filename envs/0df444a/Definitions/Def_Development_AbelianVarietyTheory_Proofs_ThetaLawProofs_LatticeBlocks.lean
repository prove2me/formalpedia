-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_LatticeBlocks
-- name    : Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_LatticeBlocks
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T17:17:55.35389+00:00
-- url     : https://prove2.me/theorems/76a25dd5-ca5b-4b29-8721-517d42827801
-- title:
--   Lattice Blocks
-- statement:
--   Definitions and structural lemmas for Lattice Blocks, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/LatticeBlocks.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_KeyRuleOneOfKeyFormula
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ThetaCharBlockDiagonal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsHolomorphicUniformisationPowerThetaKeyDatuStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.KeyPow
end GlobalTheory.KeyPow
end


