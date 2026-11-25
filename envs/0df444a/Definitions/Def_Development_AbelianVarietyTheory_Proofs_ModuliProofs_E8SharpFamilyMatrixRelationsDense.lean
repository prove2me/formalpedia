-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_E8SharpFamilyMatrixRelationsDense
-- name    : Development_AbelianVarietyTheory_Proofs_ModuliProofs_E8SharpFamilyMatrixRelationsDense
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T14:31:59.545261+00:00
-- url     : https://prove2.me/theorems/df5300d3-0502-4b41-a656-f57e9a1901ac
-- title:
--   E8 Sharp Family Matrix Relations Dense
-- statement:
--   Definitions and structural lemmas for E8 Sharp Family Matrix Relations Dense, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/E8SharpFamilyMatrixRelationsDense.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SharpRelations
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsReducedAlgebraOfSmoothOfIsNoetherianRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
noncomputable section
namespace GlobalTheory.SharpFamRel
section Group
variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S} {φ : G'.left ⟶ G.left}
  (h : IsGrpPullback G' G f φ)
section Points
variable {T : Over S} {T' : Over S'} (U : Over.mk (T'.hom ≫ f) ⟶ T)
end Points
def selfMap : Over.mk (G'.hom ≫ f) ⟶ G := Over.homMk φ h.1.w
end Group
def baseMap {S S' : Scheme.{0}} (f : S' ⟶ S) : Over.mk ((Out.baseOver S').hom ≫ f) ⟶ Out.baseOver S :=
  Over.homMk f ((Category.comp_id _).trans (Category.id_comp _).symm)
variable {o : Type} [CommRing o] {g k : ℕ} {J : Type} {b : TBase o k}
def NatEnd (F : ∀ {S : Scheme.{0}} {s : S ⟶ Sp o} (t : TObj g k J b s), t.A ⟶ t.A) : Prop :=
  ∀ {S S' : Scheme.{0}} {s : S ⟶ Sp o} {s' : S' ⟶ Sp o} (t' : TObj g k J b s') (t : TObj g k J b s) {f : S' ⟶ S}
    {φ : t'.A.left ⟶ t.A.left} (h : IsGrpPullback t'.A t.A f φ),
    (∀ j, (t'.act j).left ≫ φ = φ ≫ (t.act j).left) → pushPt h.1.w (F t') = selfMap h ≫ F t
def NatPt (F : ∀ {S : Scheme.{0}} {s : S ⟶ Sp o} (t : TObj g k J b s), Out.baseOver S ⟶ t.A) : Prop :=
  ∀ {S S' : Scheme.{0}} {s : S ⟶ Sp o} {s' : S' ⟶ Sp o} (t' : TObj g k J b s') (t : TObj g k J b s) {f : S' ⟶ S}
    {φ : t'.A.left ⟶ t.A.left} (h : IsGrpPullback t'.A t.A f φ),
    (∀ i, (t'.pt i).left ≫ φ = f ≫ (t.pt i).left) →
    (∀ j, (t'.act j).left ≫ φ = φ ≫ (t.act j).left) → pushPt h.1.w (F t') = baseMap f ≫ F t
variable {em : o →+* ℂ} {C : TObj g k J b (spMap em) → Prop} {S : Scheme.{0}} {s : S ⟶ Sp o}
end GlobalTheory.SharpFamRel
namespace GlobalTheory
open SharpFamRel
end GlobalTheory
end


