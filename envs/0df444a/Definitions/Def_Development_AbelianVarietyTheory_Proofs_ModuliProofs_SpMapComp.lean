-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SpMapComp
-- name    : Development_AbelianVarietyTheory_Proofs_ModuliProofs_SpMapComp
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T14:27:22.437413+00:00
-- url     : https://prove2.me/theorems/ac6c0145-905d-5677-8876-722a7ac33531
-- title:
--   Sp Map Comp
-- statement:
--   Definitions and structural lemmas for Sp Map Comp, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/SpMapComp.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_RangeSubsetOfGeom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsCoprimeZpow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_UnitOnInjectiveOfCommRing
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
namespace GlobalTheory.LevCover
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {S : Scheme.{0}}
def fnOn {L : Type} [CommRing L] {T : Scheme.{0}} (g : T ⟶ Sp L) : L →+* Γ(T, ⊤) :=
  g.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of L)).inv.hom
abbrev TateAt (D : Datum H) (t : SAB H S) {k : Type} [Field k] (x : Sp k ⟶ S) : Type :=
  TateIso D k (Over.mk x ⟶ t.G) (fun a g => g ≫ t.act.act a)
    (fun n g g' c => Out.WeilIs t.G t.PP.L n g g' (unitOn c))
end GlobalTheory.LevCover


