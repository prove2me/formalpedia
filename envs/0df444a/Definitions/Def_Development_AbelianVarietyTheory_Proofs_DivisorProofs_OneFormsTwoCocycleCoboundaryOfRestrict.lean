-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OneFormsTwoCocycleCoboundaryOfRestrict
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_OneFormsTwoCocycleCoboundaryOfRestrict
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T16:37:08.024876+00:00
-- url     : https://prove2.me/theorems/e767cf75-d5bd-4f90-bcc6-6751c1dca7fa
-- title:
--   One Forms Two Cocycle Coboundary Of Restrict
-- statement:
--   Definitions and structural lemmas for One Forms Two Cocycle Coboundary Of Restrict, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/OneFormsTwoCocycleCoboundaryOfRestrict.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ComparisonMemCechHodgeFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_VanishingH1InvertingMorphisms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsLocalizationOfData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsUnitMpOmjExtIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CechDR.FormExt
attribute [local instance] GlobalTheory.Cris.opModule GlobalTheory.Cris.isCentralScalar_kaehler GlobalTheory.Cris.isScalarTower_kaehler
end GlobalTheory.CechDR.FormExt


