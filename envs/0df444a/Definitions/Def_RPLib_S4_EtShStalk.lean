-- Prove2me | Definitions.Def_RPLib_S4_EtShStalk
-- name    : RPLib_S4_EtShStalk
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-15T07:12:19.441205+00:00
-- url     : https://prove2.me/theorems/ca40a10d-0175-4987-a88c-5a07d05e5324
-- title:
--   Etale sheaves of $\Lambda$-modules, geometric points and stalks
-- statement:
--   Throughout, $X$ is a scheme, $\Lambda$ a commutative ring and $\mathrm{Sh}(X_{\mathrm{et}}, \Lambda)$ the category of sheaves of $\Lambda$-modules on the small etale site of $X$. A geometric point is a morphism $\bar s : \mathrm{Spec}\,\Omega \to X$ with $\Omega$ separably closed; it is a point of the small etale site, and the stalk functor $F \mapsto F_{\bar s}$ is its fibre functor (a colimit of $F(U)$ over etale neighbourhoods $U \to X$ with a lift of $\bar s$). For every $x \in X$ the file fixes the geometric point $\bar x$ given by a separable closure of the residue field $\kappa(x)$, and proves that stalk functors are exact and that the family $(\bar x)_{x \in X}$ is conservative: a morphism of etale sheaves is an isomorphism, a sheaf is zero, and a sequence is exact if and only if this holds on every stalk $F_{\bar x}$.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (etale sheaves of $\Lambda$-modules on Mathlib's small etale site, geometric points, stalks and the Galois action on generic stalks). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   M. Artin, A. Grothendieck, J.-L. Verdier, Theorie des topos et cohomologie etale des schemas (SGA 4), Lecture Notes in Math. 269, 270, 305, Springer (1972-1973), Expose VIII; J. S. Milne, Etale Cohomology, Princeton University Press (1980), Chapter II, Section 2

import Mathlib

/-!
# S4-EtSheaves, part 1: etale sheaves of `Λ`-modules, geometric points and stalks

`EtSh Λ X` is the category of sheaves of `Λ`-modules on Mathlib's small etale site of `X`
(abelian, Grothendieck, with sheafification: `Mathlib/AlgebraicGeometry/Sites/AffineEtale.lean`).
A geometric point is a morphism `Spec Ω ⟶ X` with `Ω` separably closed; it is a point of the site
(`Scheme.pointSmallEtale`), and the stalk functor is its fibre functor. Stalks are exact and the
geometric points `geomPtAt x` (one over each `x : X`, `Ω` a separable closure of `κ(x)`) form a
conservative family, so isomorphisms, zero objects and exactness are detected on stalks.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtSheaves

universe u

/-- Sheaves of `Λ`-modules on the small etale site of `X`. -/
abbrev EtSh (Λ : Type u) [CommRing Λ] (X : Scheme.{u}) :=
  Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)

/-- A geometric point of `X`: a separably closed field `Ω` and a morphism `Spec Ω ⟶ X`. -/
structure GeomPt (X : Scheme.{u}) where
  Ω : Type u
  [fld : Field Ω]
  [sep : IsSepClosed Ω]
  pt : Spec (CommRingCat.of Ω) ⟶ X

attribute [instance] GeomPt.fld GeomPt.sep

namespace GeomPt

variable {X : Scheme.{u}} (s : GeomPt X)

/-- The point of `X` under the geometric point. -/
def center : X := s.pt default

/-- The point of the small etale site defined by `s`. -/
def point : (Scheme.smallEtaleTopology X).Point := Scheme.pointSmallEtale s.pt

variable (Λ : Type u) [CommRing Λ]

/-- The stalk functor `F ↦ F_s`. -/
def stalkF : EtSh Λ X ⥤ ModuleCat.{u} Λ := s.point.sheafFiber

instance : PreservesFiniteLimits (s.stalkF Λ) := by
  dsimp [stalkF]; infer_instance

instance : (s.stalkF Λ).IsLeftAdjoint := by
  dsimp [stalkF]; infer_instance

instance : PreservesColimits (s.stalkF Λ) := by
  dsimp [stalkF]; infer_instance

instance : PreservesFiniteColimits (s.stalkF Λ) := by
  dsimp [stalkF]; infer_instance

instance : (s.stalkF Λ).PreservesZeroMorphisms := by
  dsimp [stalkF]; infer_instance

end GeomPt

/-- The geometric point over `x` given by a separable closure of the residue field `κ(x)`. -/
def geomPtAt {X : Scheme.{u}} (x : X) : GeomPt X where
  Ω := SeparableClosure (X.residueField x)
  pt := (Scheme.SpecToEquivOfField (SeparableClosure (X.residueField x)) X).2
      ⟨x, CommRingCat.ofHom (algebraMap (X.residueField x) _)⟩

theorem center_geomPtAt {X : Scheme.{u}} (x : X) : (geomPtAt x).center = x := by
  simp only [GeomPt.center, geomPtAt, Scheme.SpecToEquivOfField]
  exact Scheme.fromSpecResidueField_apply x _

variable (Λ : Type u) [CommRing Λ] {X : Scheme.{u}}

/-- The stalk `F_x̄` at the geometric point `geomPtAt x`. -/
abbrev stalk (F : EtSh Λ X) (x : X) : ModuleCat.{u} Λ := ((geomPtAt x).stalkF Λ).obj F

/-- The points `geomPtAt x` form a conservative family. -/
theorem conservative (X : Scheme.{u}) :
    (ObjectProperty.ofObj (fun x : X => (geomPtAt x).point)).IsConservativeFamilyOfPoints :=
  Scheme.isConservativeFamilyOfPoints_pointSmallEtale' X

/-- A morphism of etale sheaves is an isomorphism iff it is so on all stalks. -/
theorem isIso_iff_stalk {F G : EtSh Λ X} (φ : F ⟶ G) :
    IsIso φ ↔ ∀ x : X, IsIso (((geomPtAt x).stalkF Λ).map φ) := by
  constructor
  · intro _ x; infer_instance
  · intro h
    have : ∀ i : (ObjectProperty.ofObj (fun x : X => (geomPtAt x).point)).FullSubcategory,
        IsIso ((i.obj.sheafFiber (A := ModuleCat.{u} Λ)).map φ) := by
      rintro ⟨Φ, hΦ⟩
      cases hΦ with
      | mk x => exact h x
    exact ((conservative X).jointlyReflectIsomorphisms (ModuleCat.{u} Λ)).isIso φ

/-- Morphisms of etale sheaves are determined by their stalks. -/
theorem hom_ext_stalk {F G : EtSh Λ X} {φ ψ : F ⟶ G}
    (h : ∀ x : X, ((geomPtAt x).stalkF Λ).map φ = ((geomPtAt x).stalkF Λ).map ψ) : φ = ψ := by
  refine ((conservative X).jointlyFaithful (ModuleCat.{u} Λ)).map_injective ?_
  rintro ⟨Φ, hΦ⟩
  cases hΦ with
  | mk x => exact h x

/-- A sheaf is zero iff all its stalks are zero. -/
theorem isZero_iff_stalk (F : EtSh Λ X) :
    IsZero F ↔ ∀ x : X, IsZero (stalk Λ F x) := by
  constructor
  · intro hF x; exact Functor.map_isZero _ hF
  · intro h
    rw [IsZero.iff_id_eq_zero]
    refine hom_ext_stalk Λ (fun x => ?_)
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero]
    exact (h x).eq_of_src _ _

/-- A short complex of etale sheaves is exact iff it is exact on all stalks. -/
theorem exact_iff_stalk (S : ShortComplex (EtSh Λ X)) :
    S.Exact ↔ ∀ x : X, (S.map ((geomPtAt x).stalkF Λ)).Exact := by
  constructor
  · intro hS x; exact hS.map _
  · intro h
    rw [S.exact_iff_isZero_homology, isZero_iff_stalk]
    intro x
    exact ((ShortComplex.exact_iff_isZero_homology _).1 (h x)).of_iso (S.mapHomologyIso _).symm

/-- Monomorphisms are detected on stalks. -/
theorem mono_iff_stalk {F G : EtSh Λ X} (φ : F ⟶ G) :
    Mono φ ↔ ∀ x : X, Mono (((geomPtAt x).stalkF Λ).map φ) := by
  constructor
  · intro _ x; infer_instance
  · intro h
    have : ∀ i : (ObjectProperty.ofObj (fun x : X => (geomPtAt x).point)).FullSubcategory,
        Mono ((i.obj.sheafFiber (A := ModuleCat.{u} Λ)).map φ) := by
      rintro ⟨Φ, hΦ⟩
      cases hΦ with
      | mk x => exact h x
    exact ((conservative X).jointlyReflectMonomorphisms (ModuleCat.{u} Λ)).mono φ

/-- Epimorphisms are detected on stalks. -/
theorem epi_iff_stalk {F G : EtSh Λ X} (φ : F ⟶ G) :
    Epi φ ↔ ∀ x : X, Epi (((geomPtAt x).stalkF Λ).map φ) := by
  constructor
  · intro _ x; infer_instance
  · intro h
    have : ∀ i : (ObjectProperty.ofObj (fun x : X => (geomPtAt x).point)).FullSubcategory,
        Epi ((i.obj.sheafFiber (A := ModuleCat.{u} Λ)).map φ) := by
      rintro ⟨Φ, hΦ⟩
      cases hΦ with
      | mk x => exact h x
    exact ((conservative X).jointlyReflectEpimorphisms (ModuleCat.{u} Λ)).epi φ

end RamanujanPetersson.EtSheaves


