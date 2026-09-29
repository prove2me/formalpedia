-- Prove2me | Definitions.Def_CerednikDrinfeld_QMLatticeAction
-- name    : CerednikDrinfeld_QMLatticeAction
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/3517a432-9816-5f78-93b3-e028ca0e6704
-- title:
--   Quaternionic lattice actions and a representability predicate
-- statement:
--   Throughout, $a,b\in\mathbb{Q}$ and $\Lambda$ is a $\mathbb{Z}$-submodule of the rational quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$; $f:A\to\operatorname{Spec} S$ is a scheme over a commutative ring $S$ equipped with a relative group law $L$, that is, a group structure on the set of $T$-points $\{P:T\to A\mid P\circ f=t\}$ for every $t:T\to\operatorname{Spec} S$, natural in $T$.
--
--   `LatticeAction Λ f L` is a structure packaging an action of $\Lambda$ on $(A,f,L)$: a family `act` of endomorphisms $A\to A$ indexed by $x\in\Lambda$, each commuting with $f$ (`act_over`); each inducing, by composition on $T$-points, a homomorphism for the group law $L$ (`act_hom`); with `act` at $1$ equal to $\mathbb{1}_A$ when $1\in\Lambda$; with the morphism attached to $xy$ equal to $\mathrm{act}(y)$ followed by $\mathrm{act}(x)$, for those $x,y$ with $xy\in\Lambda$; and with $\mathrm{act}(x+y)$ inducing on points the $L$-product of the maps induced by $\mathrm{act}(x)$ and $\mathrm{act}(y)$. Since $\Lambda$ is only an additive subgroup, the unit and multiplicativity clauses carry membership hypotheses as explicit arguments. These are exactly the six action fields of `FakeEllipticCurve`, and `ofFakeEllipticCurve` extracts them; an action is determined by its family `act`.
--
--   `IsGroupPullback φ L L' g`, for $\varphi:S\to S'$, a group law $L'$ on $f':A'\to\operatorname{Spec} S'$ and $g:A'\to A$, asserts that the square formed by $g,f',f,\operatorname{Spec}\varphi$ is cartesian and that $g$ carries $L'$-products of $S'$-points to $L$-products of their images.
--
--   `RepresentsLatticeActions Λ L E πE cl` is a predicate on a given classifying rule `cl`, which assigns to every $\varphi:R\to R'$, every named base-change model $(A',f',L',g)$ of $(A,f,L)$ along $\varphi$ in the above sense, and every $\Lambda$-action on it, a point $\operatorname{Spec} R'\to E$ over $\operatorname{Spec}\varphi$. Its three fields require: compatibility with a further base change $\psi:R'\to R''$ along a comparison morphism $h$ that is a group pullback, satisfies $h$ followed by $g$ equal to $g''$ and intertwines the two actions; surjectivity of `cl` onto the points of $E$ over $\operatorname{Spec}\varphi$, for each model; and injectivity of `cl` on actions on a fixed model. Thus `cl` is a bijection, model by model, between $\Lambda$-actions and $R'$-points of $E$; no existence of such $(E,\pi_E,cl)$ is asserted here.
--
--   **Relation to Mathlib.** Relative group laws, fake elliptic curves and the representability predicate are the project's own notions; the cartesian-square condition inside `IsGroupPullback` is Mathlib's `CategoryTheory.IsPullback`, and $\mathbb{H}[\mathbb{Q},a,b]$ with its $\mathbb{Z}$-submodules is Mathlib's quaternion algebra.
--
--   **Where it is used.** This vocabulary supports the moduli description of Shimura curves attached to an indefinite quaternion algebra over $\mathbb{Q}$ (`ShimuraCurveModel.ModuliWitness`), where points correspond to abelian surfaces with quaternionic multiplication by an order $\Lambda$ together with level structure. That description underlies the Čerednik–Drinfeld analysis of the Jacobian used in the level-lowering step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_CerednikDrinfeld_QMLatticeAction.lean

import Definitions.Def_CerednikDrinfeld_QMModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped Quaternion

namespace CerednikDrinfeld.QM

variable {a b : ℚ}

structure LatticeAction (Λ : Submodule ℤ ℍ[ℚ, a, b]) {S : Type u} [CommRing S] {A : Scheme.{u}}
    (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f) : Type u where

  act : ↥Λ → (A ⟶ A)

  act_over : ∀ x : ↥Λ, act x ≫ f = f

  act_hom : ∀ (x : ↥Λ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t f),
    pushPt (act x) (act_over x) (L.mul t P Q) = L.mul t (pushPt (act x) (act_over x) P) (pushPt (act x) (act_over x) Q)

  act_one : ∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, act ⟨1, h⟩ = 𝟙 A

  act_mul : ∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
    act ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = act y ≫ act x

  act_add : ∀ (x y : ↥Λ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t f),
    pushPt (act (x + y)) (act_over (x + y)) P = L.mul t (pushPt (act x) (act_over x) P) (pushPt (act y) (act_over y) P)

namespace LatticeAction

variable {Λ : Submodule ℤ ℍ[ℚ, a, b]}

@[ext] theorem ext {S : Type u} [CommRing S] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)} {L : RelativeGroupLaw S f}
    {X Y : LatticeAction Λ f L} (h : X.act = Y.act) : X = Y := by
  cases X; cases Y; cases h; rfl

def ofFakeEllipticCurve {N : ℕ} {S : Type u} [CommRing S] (E : FakeEllipticCurve Λ N S) : LatticeAction Λ E.f E.L where
  act := E.act
  act_over := E.act_over
  act_hom := E.act_hom
  act_one := E.act_one
  act_mul := E.act_mul
  act_add := E.act_add

@[simp] theorem ofFakeEllipticCurve_act {N : ℕ} {S : Type u} [CommRing S] (E : FakeEllipticCurve Λ N S) :
    (ofFakeEllipticCurve E).act = E.act := rfl

end LatticeAction

def IsGroupPullback {S S' : Type u} [CommRing S] [CommRing S'] (φ : S →+* S')
    {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)
    {A' : Scheme.{u}} {f' : A' ⟶ Spec (CommRingCat.of S')} (L' : RelativeGroupLaw S' f') (g : A' ⟶ A) : Prop :=
  ∃ hg : CategoryTheory.IsPullback g f' f (Spec.map (CommRingCat.ofHom φ)),
    ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t' f'),
      (L'.mul t' P Q).1 ≫ g =
        (L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ))
          ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1

structure RepresentsLatticeActions (Λ : Submodule ℤ ℍ[ℚ, a, b]) {R : Type u} [CommRing R]
    {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    (E : Scheme.{u}) (πE : E ⟶ Spec (CommRingCat.of R))
    (cl : ∀ (R' : Type u) [CommRing R'] (φ : R →+* R') {A' : Scheme.{u}} {f' : A' ⟶ Spec (CommRingCat.of R')}
      (L' : RelativeGroupLaw R' f') (g : A' ⟶ A), IsGroupPullback φ L L' g →
      LatticeAction Λ f' L' → SchemeHomOver (Spec.map (CommRingCat.ofHom φ)) πE) : Prop where

  cl_comp : ∀ (R' : Type u) [CommRing R'] (φ : R →+* R') {A' : Scheme.{u}} {f' : A' ⟶ Spec (CommRingCat.of R')}
      (L' : RelativeGroupLaw R' f') (g : A' ⟶ A) (hg : IsGroupPullback φ L L' g) (X' : LatticeAction Λ f' L')
      (R'' : Type u) [CommRing R''] (ψ : R' →+* R'') {A'' : Scheme.{u}} {f'' : A'' ⟶ Spec (CommRingCat.of R'')}
      (L'' : RelativeGroupLaw R'' f'') (g'' : A'' ⟶ A) (hg'' : IsGroupPullback (ψ.comp φ) L L'' g'')
      (X'' : LatticeAction Λ f'' L'') (h : A'' ⟶ A'),
      IsGroupPullback ψ L' L'' h → h ≫ g = g'' → (∀ x : ↥Λ, X''.act x ≫ h = h ≫ X'.act x) →
      (cl R'' (ψ.comp φ) L'' g'' hg'' X'').1 = Spec.map (CommRingCat.ofHom ψ) ≫ (cl R' φ L' g hg X').1

  cl_surjective : ∀ (R' : Type u) [CommRing R'] (φ : R →+* R') {A' : Scheme.{u}} {f' : A' ⟶ Spec (CommRingCat.of R')}
      (L' : RelativeGroupLaw R' f') (g : A' ⟶ A) (hg : IsGroupPullback φ L L' g)
      (s : SchemeHomOver (Spec.map (CommRingCat.ofHom φ)) πE), ∃ X' : LatticeAction Λ f' L', cl R' φ L' g hg X' = s

  cl_injective : ∀ (R' : Type u) [CommRing R'] (φ : R →+* R') {A' : Scheme.{u}} {f' : A' ⟶ Spec (CommRingCat.of R')}
      (L' : RelativeGroupLaw R' f') (g : A' ⟶ A) (hg : IsGroupPullback φ L L' g) (X₁ X₂ : LatticeAction Λ f' L'),
      cl R' φ L' g hg X₁ = cl R' φ L' g hg X₂ → X₁ = X₂

end CerednikDrinfeld.QM

end


