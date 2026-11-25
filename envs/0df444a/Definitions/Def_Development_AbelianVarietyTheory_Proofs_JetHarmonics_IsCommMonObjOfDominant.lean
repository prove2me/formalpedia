-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_IsCommMonObjOfDominant
-- name    : Development_AbelianVarietyTheory_Proofs_JetHarmonics_IsCommMonObjOfDominant
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T15:41:38.984824+00:00
-- url     : https://prove2.me/theorems/a2163bb7-249f-4553-b4b8-c5379ff9ac75
-- title:
--   Is Comm Mon Obj Of Dominant
-- statement:
--   Definitions and structural lemmas for Is Comm Mon Obj Of Dominant, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/IsCommMonObjOfDominant.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_NonemptyTorusExtensionOfIsGt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_QuasiCompactIffLocallyOfFinitePresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GrpObjOfDenseOpen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory.SplitExtComm
end GlobalTheory.SplitExtComm


