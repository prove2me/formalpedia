-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_JetSurvey_HtCharOfIsUnit
-- name    : Development_AbelianVarietyTheory_Counterexamples_JetSurvey_HtCharOfIsUnit
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T22:47:56.239094+00:00
-- url     : https://prove2.me/theorems/d77724d7-b5e0-43ed-8431-fb015653f786
-- title:
--   Ht Char Of Is Unit
-- statement:
--   Definitions and structural lemmas for Ht Char Of Is Unit, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/JetSurvey/HtCharOfIsUnit.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsUniqueIsAl
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv
namespace GlobalTheory.HodgeTateTest
open GlobalTheory.TangentPow GlobalTheory.GmPoints GlobalTheory.HodgeTateImage
variable {O : Type} [CommRing O]
noncomputable abbrev GmO (O : Type) [CommRing O] : Over (Spec (CommRingCat.of O)) :=
  Gm (Spec (CommRingCat.of O))
noncomputable def taut (p : ℕ) : Tv (GmO O) p where
  χ n := torsion.ι _ _
  isChar _ _ _ _ _ h := h
  compat _ _ _ _ h := h
noncomputable def dlogT (x : LieG (GmO O)) : O := (unitOf x.1 : DualNumber O).snd
end GlobalTheory.HodgeTateTest


