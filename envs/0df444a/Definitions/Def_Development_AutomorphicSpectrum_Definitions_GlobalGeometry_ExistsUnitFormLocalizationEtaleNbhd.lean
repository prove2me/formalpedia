-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_ExistsUnitFormLocalizationEtaleNbhd
-- name    : Development_AutomorphicSpectrum_Definitions_GlobalGeometry_ExistsUnitFormLocalizationEtaleNbhd
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:38:12.787017+00:00
-- url     : https://prove2.me/theorems/384e8775-1c5e-4824-b4a4-4b2af1af360b
-- title:
--   Exists Unit Form Localization Etale Nbhd
-- statement:
--   Definitions and structural lemmas for Exists Unit Form Localization Etale Nbhd, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/ExistsUnitFormLocalizationEtaleNbhd.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.BT
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
abbrev genPt (R : Type) [CommRing R] : Over (Spec (CommRingCat.of R)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))))
structure QFGroup (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] where

  G : Over (Spec (CommRingCat.of R))
  [grp : GrpObj G]
  [comm : IsCommMonObj G]
  flat : Flat G.hom
  quasiFinite : LocallyQuasiFinite G.hom
  separated : IsSeparated G.hom
  quasiCompact : QuasiCompact G.hom
  finPres : LocallyOfFinitePresentation G.hom

  pt : T →* (genPt R ⟶ G)
  pt_inj : ∀ s t (x y : Spec (CommRingCat.of (FractionRing R))), (pt s).left x = (pt t).left y → s = t
  pt_onto : ∀ g : G.left, (G.hom g).asIdeal = ⊥ → ∃ t x, (pt t).left x = g
  gen_reduced : IsReduced (pullback G.hom (genPt R).hom)
attribute [instance] QFGroup.grp QFGroup.comm
def valAt {B : Type} [CommRing B] {X : Scheme.{0}} (x : Spec (CommRingCat.of B) ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ U) (s : Γ(X, U)) : B :=
  (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom ((x.appLE U ⊤ h).hom s)
variable {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T]
def QFGroup.RegularAt (Γ : QFGroup R T) (f : T → FractionRing R) (g : Γ.G.left) : Prop :=
  ∃ U : Γ.G.left.Opens, g ∈ U ∧ ∃ s : Γ(Γ.G.left, U), ∀ (t : T) (h : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ U),
    valAt (Γ.pt t).left U h s = f t
def QFGroup.btSet (Γ : QFGroup R T) (U : Γ.G.left.Opens) : Set (T → R) :=
  {f | ∀ t, ∀ g ∈ U, Γ.RegularAt (fun h => algebraMap R (FractionRing R) (f (t * h))) g}
def QFGroup.btOrder (Γ : QFGroup R T) (U : Γ.G.left.Opens) : Subalgebra R (T → R) :=
  Algebra.adjoin R (Γ.btSet U)
structure QFGroup.IsFinOpenSub (Γ : QFGroup R T) (U : Γ.G.left.Opens) : Prop where
  finite : IsFinite (U.ι ≫ Γ.G.hom)
  one : ∀ x, (η[Γ.G]).left x ∈ U
  mul : ∀ (S : Over (Spec (CommRingCat.of R))) (x y : S ⟶ Γ.G), (∀ z, x.left z ∈ U) → (∀ z, y.left z ∈ U) →
    ∀ z, (x * y).left z ∈ U
  inv : ∀ (S : Over (Spec (CommRingCat.of R))) (x : S ⟶ Γ.G), (∀ z, x.left z ∈ U) → ∀ z, (x⁻¹).left z ∈ U
structure QFGroup.IsBaseChange {R' : Type} [CommRing R'] [IsDomain R'] (Γ' : QFGroup R' T) (Γ : QFGroup R T)
    (φ : R →+* R') (F : Γ'.G.left ⟶ Γ.G.left) : Prop where
  cart : IsPullback F Γ'.G.hom Γ.G.hom (Spec.map (CommRingCat.ofHom φ))
  mul : ∀ (S : Over (Spec (CommRingCat.of R'))) (x y : S ⟶ Γ'.G)
    (x₀ y₀ : Over.mk (S.hom ≫ Spec.map (CommRingCat.ofHom φ)) ⟶ Γ.G),
    x₀.left = x.left ≫ F → y₀.left = y.left ≫ F → (x₀ * y₀).left = (x * y).left ≫ F
  pts : ∃ (B : Type) (_ : CommRing B) (i : R →+* B) (j : B →+* FractionRing R) (j' : B →+* FractionRing R')
    (σ : T → (Spec (CommRingCat.of B) ⟶ Γ.G.left)),
    Function.Injective j ∧ j.comp i = algebraMap R _ ∧ j'.comp i = (algebraMap R' _).comp φ ∧
    (∀ t, σ t ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom i)) ∧
    (∀ t, Spec.map (CommRingCat.ofHom j) ≫ σ t = (Γ.pt t).left) ∧
    ∀ t, Spec.map (CommRingCat.ofHom j') ≫ σ t = (Γ'.pt t).left ≫ F
structure QFGroup.IsTorsionAlong (Γ : QFGroup R T) {S : Scheme.{0}} (G : Over S) [GrpObj G]
    (x : Spec (CommRingCat.of R) ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left) : Prop where
  isOver : i ≫ G.hom = Γ.G.hom ≫ x
  mul : ∀ (Y : Over (Spec (CommRingCat.of R))) (y z : Y ⟶ Γ.G) (y₀ z₀ : Over.mk (Y.hom ≫ x) ⟶ G),
    y₀.left = y.left ≫ i → z₀.left = z.left ≫ i → (y₀ * z₀).left = (y * z).left ≫ i
  inj : ∀ (Y : Over (Spec (CommRingCat.of R))) (y z : Y ⟶ Γ.G), y.left ≫ i = z.left ≫ i → y = z
  kernel : ∀ (Y : Over (Spec (CommRingCat.of R))) (g : Over.mk (Y.hom ≫ x) ⟶ G),
    g ^ N = 1 ↔ ∃ y : Y ⟶ Γ.G, y.left ≫ i = g.left
structure QFGroup.IsEmb (Γ : QFGroup R T) (A : Subalgebra R (T → R)) (j : Γ.G.left ⟶ Spec (CommRingCat.of A)) : Prop where
  isOver : j ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)) = Γ.G.hom
  pt : ∀ t, (Γ.pt t).left ≫ j = Spec.map (CommRingCat.ofHom
    ((algebraMap R (FractionRing R)).comp ((Pi.evalRingHom (fun _ : T => R) t).comp A.val.toRingHom)))
def QFGroup.TranslatesCover (Γ : QFGroup R T) (A : Subalgebra R (T → R)) (j : Γ.G.left ⟶ Spec (CommRingCat.of A))
    (U : Γ.G.left.Opens) : Prop :=
  ∀ P : PrimeSpectrum A, ∃ (t : T) (g : Γ.G.left), g ∈ U ∧
    ∀ (f f' : A), (∀ h, (f' : T → R) h = (f : T → R) (t * h)) → (f ∈ P.asIdeal ↔ f' ∈ (j g).asIdeal)
end GlobalTheory.CompanionTheory.Ar.BT


