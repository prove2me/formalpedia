-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HigherFormsOneCocycleCoboundaryOfRestrict
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_HigherFormsOneCocycleCoboundaryOfRestrict
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T16:37:16.347431+00:00
-- url     : https://prove2.me/theorems/c8891582-c387-4694-b20e-856e27f8abaf
-- title:
--   Higher Forms One Cocycle Coboundary Of Restrict
-- statement:
--   Definitions and structural lemmas for Higher Forms One Cocycle Coboundary Of Restrict, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HigherFormsOneCocycleCoboundaryOfRestrict.lean

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
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR
namespace GlobalTheory.CechDR.FormExtJ
attribute [local instance] opModJ isCentralScalarJ isScalarTowerJ
variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) (j : ℕ)
abbrev inrJ {T : C} (x : Om R (F.obj T) j) : (omjExt F j).obj T := TrivSqZeroExt.inr x
end GlobalTheory.CechDR.FormExtJ


