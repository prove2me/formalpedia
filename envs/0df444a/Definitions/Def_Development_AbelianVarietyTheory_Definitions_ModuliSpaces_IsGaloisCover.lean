-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
-- name    : Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:05:11.68345+00:00
-- url     : https://prove2.me/theorems/bc1bdfdd-e090-4dc5-a3c2-b9d4a6f92af8
-- title:
--   Is Galois Cover
-- statement:
--   Definitions and structural lemmas for Is Galois Cover, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ModuliSpaces/IsGaloisCover.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
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
noncomputable section
namespace GlobalTheory.ZM
variable {o : Type} [CommRing o] {S S' : Scheme.{0}} {g : ℕ} {J : Type}
def DenseP {R : Type} [CommRing R] (P : Set (Ideal R)) : Prop := ∀ f : R, (∀ p ∈ P, p.IsPrime → f ∈ p) → f = 0
structure WFam (n : ℕ) {N' : ℕ} {b : TBase o (N' ^ 2)} (em : o →+* ℂ) (C : TObj g (N' ^ 2) J b (spMap em) → Prop)
    (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ : ℕ) where
  Y : MMPre n N' (thIdeal em C)
  U : Y.MM.Opens
  univ : TObj g (N' ^ 2) J b (U.ι ≫ Y.s)
  dense : Dense (fromSet em C univ)
  th : ∀ (R : Type) [CommRing R] (x : Sp R ⟶ U.toScheme) (v : Ix g (N' ^ 2) → R),
    univ.HasTh x v ↔ SecCoord Y.de Y.th (x ≫ U.ι) v
  obj : ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Y.MM) (t' : TObj g (N' ^ 2) J b (x ≫ Y.s))
    (v : Ix g (N' ^ 2) → K), t'.Shape Mat κ → t'.HasTh (𝟙 _) v → SecCoord Y.de Y.th x v →
    ∃ x' : Sp K ⟶ U.toScheme, x' ≫ U.ι = x ∧ TMap t' univ x'
def TObj.FibShape {k : ℕ} {b : TBase o k} {s : S ⟶ Sp o} (t : TObj g k J b s)
    (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ : ℕ) : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (t' : TObj g k J b (x ≫ s)), TMap t' t x → t'.Shape Mat κ
def dirMap {K : Type} [Field K] {n : ℕ} (lam : (Fin n → K) →ₗ[K] K) : TrivSqZeroExt K (Fin n → K) →+* DualNumber K :=
  (TrivSqZeroExt.map lam).toRingHom
structure IsGaloisCover {X Y : Scheme.{0}} (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (π : X ⟶ Y) : Prop where
  finite : Finite Ga
  one : ρ 1 = 𝟙 X
  mul : ∀ a c, ρ (a * c) = ρ a ≫ ρ c
  inv : ∀ a, ρ a ≫ π = π
  fin : IsFinite π
  etale : Etale π
  onto : Surjective π
  fibre : ∀ (K : Type) [Field K] [IsAlgClosed K] (y y' : Sp K ⟶ X), y ≫ π = y' ≫ π → ∃! a, y ≫ ρ a = y'
section PEL
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
def ObjUnder {l : Level H} {B : Type} [CommRing B] {bB : Base l B} {sB : S ⟶ Sp B} (ob : Obj D l bB sB) {k : ℕ}
    {b : TBase o k} {s : S ⟶ Sp o} (a : J → 𝓞 E) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La) (t : TObj g k J b s) : Prop :=
  ∃ φ : ob.t.G ≅ t.A, IsMonHom φ.hom ∧ LBIso ob.t.PP.L (t.L.pull φ.hom.left) ∧
    (∀ j, ob.t.act.act (a j) ≫ φ.hom = φ.hom ≫ t.act j) ∧
    ∀ i, (ob.etaA (bas (Pi.single i 1)) ≫ φ.hom).left = (t.pt i).left
def Lowers (l : Level H) {l₂ : Level H} {B : Type} [CommRing B] {b₂ : Base l₂ B} {s₂ : S ⟶ Sp B} (ob₂ : Obj D l₂ b₂ s₂)
    {G : Over S'} (eM eA : D.La → (𝟙_ (Over S') ⟶ G)) (y : S' ⟶ S) (φ : G.left ⟶ ob₂.t.G.left) : Prop :=
  (∀ a, (eM a).left ≫ φ = y ≫ (ob₂.eta a ^ (l₂.M / l.M)).left) ∧
    ∀ a, (eA a).left ≫ φ = y ≫ (ob₂.etaA a ^ (l₂.A / l.A)).left
structure LevelQuot (l : Level H) {l₂ : Level H} (Xo₂ : Moduli D l₂) where
  X : Scheme.{0}
  s : X ⟶ Sp (KA l)
  qproj : IsQProjOver s
  smooth : SmoothOfRelativeDimension D.dim s
  univ : Obj D l (baseKA l) s
  π : Xo₂.X ⟶ X
  jK : KA l →+* KA l₂
  jK_val : ∀ x, ((jK x : KA l₂) : ℂ) = ((x : KA l) : ℂ)
  overK : π ≫ s = Xo₂.s ≫ spMap jK
  fin : IsFinite π
  etale : Etale π
  onto : Surjective π
  m : SABMap Xo₂.univ.t univ.t π
  eta : ∀ a, (Xo₂.univ.eta a ^ (l₂.M / l.M)).left ≫ m.φ = π ≫ (univ.eta a).left
  etaA : ∀ a, (Xo₂.univ.etaA a ^ (l₂.A / l.A)).left ≫ m.φ = π ≫ (univ.etaA a).left
  fibre : ∀ (K : Type) [Field K] [IsAlgClosed K] (y y' : Sp K ⟶ Xo₂.X) (t : SAB H (Sp K))
    (mu : SABMap t Xo₂.univ.t y) (mu' : SABMap t Xo₂.univ.t y') (eM eA : D.La → (𝟙_ (Over (Sp K)) ⟶ t.G)),
    y ≫ Xo₂.s ≫ spMap jK = y' ≫ Xo₂.s ≫ spMap jK → Lowers l Xo₂.univ eM eA y mu.φ → Lowers l Xo₂.univ eM eA y' mu'.φ →
    y ≫ π = y' ≫ π
end PEL
end GlobalTheory.ZM
end


