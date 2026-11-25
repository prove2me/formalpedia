-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsAlgHomValuationSubring
-- name    : Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsAlgHomValuationSubring
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T14:18:49.536609+00:00
-- url     : https://prove2.me/theorems/d8595776-e095-4d8a-b5d8-612bab2ced58
-- title:
--   Exists Alg Hom Valuation Subring
-- statement:
--   Definitions and structural lemmas for Exists Alg Hom Valuation Subring, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsAlgHomValuationSubring.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_ColValMonomial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsCharactersDlogMinorsGe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_PowEqScaleAndExistsUniqueTorsion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_GermEvalOneStandardPointSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_UnitsZpowSurjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.TorsionCharacter
variable {O : Type} [CommRing O]
section Val
variable {F : Type} [Field F] (v : AddValuation F (WithTop ℚ))
end Val
end GlobalTheory.TorsionCharacter


