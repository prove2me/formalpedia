-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_LieAlgebraMaps
-- name    : Development_AbelianVarietyTheory_BlockTheory_DivisorBase_LieAlgebraMaps
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:54:00.271281+00:00
-- url     : https://prove2.me/theorems/3f7bf438-e873-45cc-b9aa-856fc3bf0345
-- title:
--   Lie Algebra Maps
-- statement:
--   Definitions and structural lemmas for Lie Algebra Maps, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/LieAlgebraMaps.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StAvDefs
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
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
namespace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps
section Lie
variable {R : Type} [CommRing R]
def lieAdd (G : Over (Spec (CommRingCat.of R))) [GrpObj G] (x y : LieG G) : LieG G :=
  ⟨x.1 * y.1, by
    rw [MonObj.comp_mul, x.2, y.2]
    exact mul_one (1 : specO R R ⟶ G)⟩
def lieMap {T G : Over (Spec (CommRingCat.of R))} [GrpObj T] [GrpObj G] (u : T ⟶ G) [IsMonHom u]
    (x : LieG T) : LieG G :=
  ⟨x.1 ≫ u, by rw [← Category.assoc, x.2, Category.assoc, IsMonHom.one_hom]⟩
def LieCongr (G : Over (Spec (CommRingCat.of R))) [GrpObj G] (I : Ideal R) (x y : LieG G) : Prop :=
  ∃ a ∈ I, ∃ z : LieG G, x = lieAdd G y (lieScale G a z)
def IsLieLinear {G H : Over (Spec (CommRingCat.of R))} [GrpObj G] [GrpObj H]
    (f : LieG G → LieG H) : Prop :=
  (∀ x y, f (lieAdd G x y) = lieAdd H (f x) (f y)) ∧
    ∀ (a : R) (x : LieG G), f (lieScale G a x) = lieScale H a (f x)
abbrev torus (R : Type) [CommRing R] (r : ℕ) : Over (Spec (CommRingCat.of R)) :=
  splitTorus (Spec (CommRingCat.of R)) (Fin r → ℤ)
def lieCoord {r : ℕ} (x : LieG (torus R r)) (i : Fin r) : R :=
  TrivSqZeroExt.snd (R := R) (M := R)
    ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).hom.hom
      (x.1.left.appTop.hom (charUnit (Spec (CommRingCat.of R)) (Fin r → ℤ) (Pi.single i 1)).val))
end Lie
abbrev baseChange (R A : Type) [CommRing R] [CommRing A] [Algebra R A] :
    Over (Spec (CommRingCat.of R)) ⥤ Over (Spec (CommRingCat.of A)) :=
  Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R A)))
def IsSaturatedTorus {R : Type} [CommRing R] [IsLocalRing R] {r : ℕ}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] (u : torus R r ⟶ G) [IsMonHom u] : Prop :=
  IsClosedImmersion ((baseChange R (IsLocalRing.ResidueField R)).map u).left ∧
    (∀ x y : LieG (torus R r),
      LieCongr G (IsLocalRing.maximalIdeal R) (lieMap u x) (lieMap u y) →
        LieCongr (torus R r) (IsLocalRing.maximalIdeal R) x y) ∧
    (Function.Bijective (lieCoord : LieG (torus R r) → Fin r → R) ∧
      (∀ x y : LieG (torus R r), lieCoord (lieAdd _ x y) = lieCoord x + lieCoord y) ∧
      ∀ (a : R) (x : LieG (torus R r)), lieCoord (lieScale _ a x) = a • lieCoord x) ∧
    ∃ ρ : LieG G → LieG (torus R r), IsLieLinear ρ ∧ ∀ x, ρ (lieMap u x) = x
def TorusSaturated : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type) [Field K] [Algebra R K] [IsFractionRing R K]
    (G : Over (Spec (CommRingCat.of R))) [GrpObj G], IsSemiAbelian G →
    ∀ (r : ℕ) (uK : (baseChange R K).obj (torus R r) ⟶ (baseChange R K).obj G),
      IsMonHom uK → IsClosedImmersion uK.left →
      ∃ (u : torus R r ⟶ G) (_ : IsMonHom u), (baseChange R K).map u = uK ∧
        (∀ u' : torus R r ⟶ G, IsMonHom u' → (baseChange R K).map u' = uK → u' = u) ∧
        IsSaturatedTorus u
example (R K : Type) [CommRing R] [Field K] [Algebra R K] (r : ℕ) :
    IsMonHom (𝟙 ((baseChange R K).obj (torus R r))) ∧
      IsClosedImmersion (𝟙 ((baseChange R K).obj (torus R r)) : _ ⟶ _).left :=
  ⟨inferInstance, by rw [Over.id_left]; infer_instance⟩
example (R : Type) [CommRing R] (r : ℕ) :
    ∃ ρ : LieG (torus R r) → LieG (torus R r), IsLieLinear ρ ∧ ∀ x, ρ (lieMap (𝟙 _) x) = x :=
  ⟨id, ⟨fun _ _ => rfl, fun _ _ => rfl⟩, fun x => Subtype.ext (Category.comp_id x.1)⟩
end GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps


