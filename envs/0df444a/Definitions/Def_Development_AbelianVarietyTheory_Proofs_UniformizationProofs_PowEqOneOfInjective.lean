-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PowEqOneOfInjective
-- name    : Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PowEqOneOfInjective
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T15:20:21.277838+00:00
-- url     : https://prove2.me/theorems/a88744eb-6af1-4930-b757-dc0c37b5bbc8
-- title:
--   Pow Eq One Of Injective
-- statement:
--   Definitions and structural lemmas for Pow Eq One Of Injective, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/PowEqOneOfInjective.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_ThetaMove
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExpansionBijectiveOverFields
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUniqueSecPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExpandsAtTransport
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PowEqOneOfPush
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ThetaGrpActsLinearly
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExpandsFOfIntegral
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_sval_of

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.ThetaSpecialise
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.H1 GlobalTheory.FieldBaseChange GlobalTheory.ThetaScalar
  GlobalTheory.ThetaBaseChange
section Pull
variable {X X' X'' Y Y' Y'' Y₁ Y₁' : Scheme.{0}} {L : LB X} {L' : LB X'} {L'' : LB X''} {Φ : X' ⟶ X} {Φ' : X'' ⟶ X'}
  {K : Type} [Fintype K] {ε : K → ℤ}
def IsPull {φ₁ : K → (Y₁ ⟶ X)} {φ : K → (Y ⟶ X)} (a : Y₁ ⟶ Y) (t : LB.Sec (LB.LinComb L φ₁ ε))
    (s : LB.Sec (LB.LinComb L φ ε)) : Prop :=
  (∀ κ, φ₁ κ = a ≫ φ κ) ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Y₁) (z : Z) (j : K → L.ι), (∀ κ, φ₁ κ (r z) ∈ L.U (j κ)) →
    gs r z (LB.wchart L φ₁ j) (t.f j) = gs (r ≫ a) z (LB.wchart L φ j) (s.f j)
variable {φ : K → (Y ⟶ X)} {φ₁ : K → (Y₁ ⟶ X)} {φ₂ : K → (Y₁' ⟶ X)} {a : Y₁ ⟶ Y} {b : Y₁' ⟶ Y₁}
  {s : LB.Sec (LB.LinComb L φ ε)} {t : LB.Sec (LB.LinComb L φ₁ ε)} {v : LB.Sec (LB.LinComb L φ₂ ε)}
theorem IsPull.sval (h : IsPull a t s) {Z : Scheme.{0}} (r : Z ⟶ Y₁) {z : Z} {J} (hJ : Good L z J) :
    sval t r z J = sval s (r ≫ a) z J := by
  unfold IsPull at h
  have hmem : ∀ k, φ₁ k (r z) ∈ L.U (J (r ≫ φ₁ k)) := fun k => by
    simpa only [Scheme.Hom.comp_apply] using hJ (r ≫ φ₁ k)
  rw [sval_of t r z J (fun k => J (r ≫ φ₁ k)) (fun _ => rfl), h.2 Z r z _ hmem]
  exact (sval_of s (r ≫ a) z J _ (fun k => by rw [h.1 k, Category.assoc])).symm
variable {w : LB.Iso L' (L.pull Φ)} {φ' : K → (Y' ⟶ X')} {s' : LB.Sec (LB.LinComb L' φ' ε)}
end Pull
section Side
variable {S₀ S₁ : Scheme.{0}} {G : Over S₀} [GrpObj G] {A : Over S₁} [GrpObj A]
  {f : S₁ ⟶ S₀} {φ : A.left ⟶ G.left} (hp : IsGrpPullback A G f φ) {S F : Type} [CommRing S] [CommRing F]
  {t : Spec (CommRingCat.of F) ⟶ S₁} {t₀ : Spec (CommRingCat.of S) ⟶ S₀} (g : S →+* F)
  (hτ : Spec.map (CommRingCat.ofHom g) ≫ t₀ = t ≫ f) {L₀ : LB G.left} {L₁ : LB A.left}
end Side
section Fam
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F]
end Fam
section Points
end Points
end GlobalTheory.ThetaSpecialise


