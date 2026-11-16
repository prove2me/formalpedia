-- Prove2me | Definitions.Def_RPLib_S4_EtShGalAct
-- name    : RPLib_S4_EtShGalAct
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-15T07:14:43.833216+00:00
-- url     : https://prove2.me/theorems/6cbdc437-d978-406a-b82b-c15c74086b42
-- title:
--   The Galois action on stalks of etale sheaves
-- statement:
--   Throughout, $X$ is a scheme, $\Lambda$ a commutative ring and $\mathrm{Sh}(X_{\mathrm{et}}, \Lambda)$ the category of sheaves of $\Lambda$-modules on the small etale site of $X$. An automorphism $\tau$ of $\mathrm{Spec}\,\Omega$ over $X$ is an endomorphism of the geometric point $\bar s$ as a point of the site (it moves lifts $a \mapsto a \circ \tau$), so it acts on every stalk $F_{\bar s}$, contravariantly in $\tau$ and naturally in $F$. At the geometric point $\bar x$ attached to $x \in X$ (with $\Omega$ a separable closure of $\kappa(x)$) every $\sigma \in \mathrm{Gal}(\Omega/\kappa(x))$ gives $\mathrm{Spec}\,\sigma$ over $X$, and $\sigma \mapsto (\mathrm{Spec}\,\sigma)^*$ is a representation of $\mathrm{Gal}(\Omega/\kappa(x))$ on $F_{\bar x}$, natural in $F$.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (etale sheaves of $\Lambda$-modules on Mathlib's small etale site, geometric points, stalks and the Galois action on generic stalks). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   M. Artin, A. Grothendieck, J.-L. Verdier, Theorie des topos et cohomologie etale des schemas (SGA 4), Lecture Notes in Math. 269, 270, 305, Springer (1972-1973), Expose VIII, Section 2; J. S. Milne, Etale Cohomology, Princeton University Press (1980), Chapter II

import Mathlib
import Definitions.Def_RPLib_S4_EtShStalk

/-!
# S4-EtSheaves, part 23: the Galois action on stalks

An automorphism `τ` of `Spec Ω` over `X` is an endomorphism of the point `s` of the small etale site (lifts
`a ↦ τ ≫ a`), so it acts on the stalk functor (`stalkAut`, contravariantly in `τ`). At the geometric point
`geomPtAt x` (`Ω` a separable closure of `κ(x)`) every `σ ∈ Gal(Ω/κ(x))` gives `Spec σ` over `X`, and
`σ ↦ (Spec σ)^*` is a representation `galRep F x` of `Gal(Ω/κ(x))` on `F_x̄`, natural in `F`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtSheaves

universe u

namespace GeomPt

variable {X : Scheme.{u}} (s : GeomPt X)

/-- An automorphism `τ` of `Spec Ω` over `X` as an endomorphism of the point `s` (lifts `a ↦ τ ≫ a`). -/
def autHom (τ : Spec (CommRingCat.of s.Ω) ⟶ Spec (CommRingCat.of s.Ω)) (hτ : τ ≫ s.pt = s.pt) :
    s.point ⟶ s.point :=
  ⟨Functor.whiskerLeft (Scheme.Etale.forget X)
    (coyoneda.map (Over.homMk τ hτ : CategoryTheory.Over.mk s.pt ⟶ CategoryTheory.Over.mk s.pt).op)⟩

theorem autHom_id (h : 𝟙 (Spec (CommRingCat.of s.Ω)) ≫ s.pt = s.pt) : s.autHom (𝟙 _) h = 𝟙 _ := by
  apply GrothendieckTopology.Point.hom_ext
  ext U a
  change Over.homMk (𝟙 _) h ≫ a = a
  rw [← Category.id_comp a]
  congr 1

theorem autHom_comp {τ₁ τ₂ : Spec (CommRingCat.of s.Ω) ⟶ Spec (CommRingCat.of s.Ω)}
    (h₁ : τ₁ ≫ s.pt = s.pt) (h₂ : τ₂ ≫ s.pt = s.pt) (h : (τ₁ ≫ τ₂) ≫ s.pt = s.pt) :
    s.autHom (τ₁ ≫ τ₂) h = s.autHom τ₁ h₁ ≫ s.autHom τ₂ h₂ := by
  have key := Over.homMk_comp (U := CategoryTheory.Over.mk s.pt) (V := CategoryTheory.Over.mk s.pt)
    (W := CategoryTheory.Over.mk s.pt) τ₁ τ₂ h₁ h₂
  apply GrothendieckTopology.Point.hom_ext
  ext U a
  change Over.homMk (τ₁ ≫ τ₂) h ≫ a =
    (Over.homMk τ₁ h₁ : CategoryTheory.Over.mk s.pt ⟶ CategoryTheory.Over.mk s.pt) ≫
      (Over.homMk τ₂ h₂ : CategoryTheory.Over.mk s.pt ⟶ CategoryTheory.Over.mk s.pt) ≫ a
  rw [key]
  exact Category.assoc _ _ _

variable (Λ : Type u) [CommRing Λ]

/-- The action of `τ` on stalks. -/
def stalkAut (τ : Spec (CommRingCat.of s.Ω) ⟶ Spec (CommRingCat.of s.Ω)) (hτ : τ ≫ s.pt = s.pt) :
    s.stalkF Λ ⟶ s.stalkF Λ :=
  GrothendieckTopology.Point.Hom.sheafFiber (A := ModuleCat.{u} Λ) (s.autHom τ hτ)

theorem stalkAut_id {τ : Spec (CommRingCat.of s.Ω) ⟶ Spec (CommRingCat.of s.Ω)} (hτ : τ ≫ s.pt = s.pt)
    (e : τ = 𝟙 _) : s.stalkAut Λ τ hτ = 𝟙 _ := by
  subst e
  simp only [stalkAut, autHom_id]
  exact GrothendieckTopology.Point.Hom.sheafFiber_id _

theorem stalkAut_comp {τ₁ τ₂ τ : Spec (CommRingCat.of s.Ω) ⟶ Spec (CommRingCat.of s.Ω)}
    (h₁ : τ₁ ≫ s.pt = s.pt) (h₂ : τ₂ ≫ s.pt = s.pt) (hτ : τ ≫ s.pt = s.pt) (e : τ = τ₁ ≫ τ₂) :
    s.stalkAut Λ τ hτ = s.stalkAut Λ τ₂ h₂ ≫ s.stalkAut Λ τ₁ h₁ := by
  subst e
  simp only [stalkAut, autHom_comp s h₁ h₂]
  exact GrothendieckTopology.Point.Hom.sheafFiber_comp _ _

end GeomPt

variable {X : Scheme.{u}}

/-- The Galois group `Gal(Ω/κ(x))` of the geometric point `geomPtAt x`. -/
abbrev Gal (x : X) := SeparableClosure (X.residueField x) ≃ₐ[X.residueField x] SeparableClosure (X.residueField x)

/-- `σ ∈ Gal(Ω/κ(x))` as an automorphism of `Spec Ω`. -/
def galSpec (x : X) (σ : Gal x) :
    Spec (CommRingCat.of (SeparableClosure (X.residueField x))) ⟶
      Spec (CommRingCat.of (SeparableClosure (X.residueField x))) :=
  Spec.map (CommRingCat.ofHom (σ : SeparableClosure (X.residueField x) →+* SeparableClosure (X.residueField x)))

theorem galSpec_comp (x : X) (σ : Gal x) : galSpec x σ ≫ (geomPtAt x).pt = (geomPtAt x).pt := by
  change Spec.map (CommRingCat.ofHom (σ : SeparableClosure (X.residueField x) →+* SeparableClosure (X.residueField x))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) (SeparableClosure (X.residueField x)))) ≫
        X.fromSpecResidueField x =
    Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) (SeparableClosure (X.residueField x)))) ≫
      X.fromSpecResidueField x
  have e : (σ : SeparableClosure (X.residueField x) →+* SeparableClosure (X.residueField x)).comp
      (algebraMap (X.residueField x) (SeparableClosure (X.residueField x))) =
      algebraMap (X.residueField x) (SeparableClosure (X.residueField x)) := by
    ext a
    simp
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, e]

theorem galSpec_one (x : X) : galSpec x 1 = 𝟙 _ := by
  rw [galSpec, ← Spec.map_id]
  congr 1

theorem galSpec_mul (x : X) (σ ρ : Gal x) : galSpec x (σ * ρ) = galSpec x σ ≫ galSpec x ρ := by
  rw [galSpec, galSpec, galSpec, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

variable (Λ : Type u) [CommRing Λ]

/-- **The Galois representation on a stalk**: `Gal(Ω/κ(x))` acts on `F_x̄`. -/
def galRep (F : EtSh Λ X) (x : X) : Representation Λ (Gal x) (stalk Λ F x) where
  toFun σ := (((geomPtAt x).stalkAut Λ (galSpec x σ) (galSpec_comp x σ)).app F).hom
  map_one' := congrArg (fun t => (t.app F).hom)
    (GeomPt.stalkAut_id (geomPtAt x) Λ (galSpec_comp x 1) (galSpec_one x))
  map_mul' σ ρ := congrArg (fun t => (t.app F).hom)
    (GeomPt.stalkAut_comp (geomPtAt x) Λ (galSpec_comp x σ) (galSpec_comp x ρ) (galSpec_comp x (σ * ρ))
      (galSpec_mul x σ ρ))

theorem galRep_apply (F : EtSh Λ X) (x : X) (σ : Gal x) :
    galRep Λ F x σ = (((geomPtAt x).stalkAut Λ (galSpec x σ) (galSpec_comp x σ)).app F).hom := rfl

/-- **Stalk maps are Galois-equivariant.** -/
theorem galRep_natural {F G : EtSh Λ X} (φ : F ⟶ G) (x : X) (σ : Gal x) :
    (((geomPtAt x).stalkF Λ).map φ).hom ∘ₗ galRep Λ F x σ =
      galRep Λ G x σ ∘ₗ (((geomPtAt x).stalkF Λ).map φ).hom := by
  rw [galRep_apply, galRep_apply, ← ModuleCat.hom_comp, ← ModuleCat.hom_comp, NatTrans.naturality]

end RamanujanPetersson.EtSheaves


