-- Prove2me | Definitions.Def_CerednikDrinfeld_QMStructureOnPolarised
-- name    : CerednikDrinfeld_QMStructureOnPolarised
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/b07c705a-ac61-588d-a17c-ce182a7e870c
-- title:
--   Quaternionic multiplication structures on polarised abelian surfaces
-- statement:
--   Fix rationals $a,b$, a $\mathbb Z$-submodule $\Lambda$ of the quaternion algebra $\mathbb H[\mathbb Q,a,b]$, a map $\star:\Lambda\to\Lambda$ and a family $\beta:\mathrm{Fin}\,4\to\Lambda$. For a commutative ring $S$ and $X$ a polarised abelian scheme of relative dimension $2$, fibre degree $d$ and level $m$ over $S$ (so $X$ carries $A\to\operatorname{Spec}S$, a relative group law $L$, four level-$m$ sections $X.P_i$ freely generating the geometric $m$-torsion, and an invertible, very ample module `pol` with $h^0=d$ on geometric fibres), the structure `QMStructure Λ star β X` consists of: a map $\mathrm{act}:\Lambda\to\operatorname{End}(A)$ whose values lie over $\operatorname{Spec}S$ and act on $T$-points as homomorphisms for $L$; multiplicativity $\mathrm{act}(xy)=\mathrm{act}(x)\circ\mathrm{act}(y)$ and $\mathrm{act}(1)=\mathrm{id}$, each stated under the hypothesis that the relevant element lies in $\Lambda$; additivity $\mathrm{act}(x+y)=\mathrm{act}(x)+\mathrm{act}(y)$ on points; and a trace condition: for every algebraically closed field $k$, every $sk:S\to k$, every finite-dimensional $k$-space $V$ parametrising the tangent vectors at the $k$-point bijectively, additively and $k$-homogeneously, and every $k$-linear $\Phi$ on $V$ inducing $\mathrm{act}(x)$, one has $\operatorname{tr}_k\Phi=n$ whenever $x+\bar x=n$ in $\mathbb H[\mathbb Q,a,b]$. In addition there is a section $P$ over $S$ with $\mathrm{act}(\beta_j)P=X.P_j$ for $j=0,\dots,3$, so that the level sections are $\Lambda$-translates of a single generator, and the property that for some $\mathcal L_E$ the predicate `IsCanonicalPolData` holds of $(X.f,X.L,\mathrm{act},\star,\mathcal L_E)$ — $\mathcal L_E$ invertible, symmetric, with kernel the $2$-torsion, faithfully flat-locally of the form $\mathcal L_0\otimes[-1]^*\mathcal L_0$ with trivial kernel, of positive $h^0$ on geometric fibres and Rosati-compatible with the action through $\star$ — while `pol` is Zariski-locally on the base isomorphic to $\mathcal L_E^{\otimes 3}$. Only $\mathrm{act}$ and $P$ are data; the remaining fields are propositions.
--
--   Three relations on such structures are defined. `IsPullback φ s s'`, for $\varphi:S\to S'$, asks for a morphism $g_A:A'\to A$ making a cartesian square over $\operatorname{Spec}\varphi$, compatible with the group laws and the level sections, with `pol` pulling back to `pol'`, intertwining the two $\Lambda$-actions and carrying $s'.P$ to $s.P$. `Iso s s'`, for two structures over the same $S$, asks for an isomorphism $e:A\cong A'$ over $S$ compatible with the group laws, matching level sections, with the polarisations corresponding after pullback Zariski-locally on the base, intertwining the actions and matching the generators. `Packages s u` compares a QM structure with a fake elliptic curve $u$ of level $1$ equipped with a full level-$m$ structure: it asks for an isomorphism of the underlying schemes over $S$ compatible with the group laws, intertwining $u$'s $\Lambda$-action with $\mathrm{act}$ and carrying $u$'s level generator to $P$; no condition on the polarisation or on $u$'s level morphism is imposed.
--
--   **Relation to Mathlib.** Mathlib has no notion of abelian scheme, polarisation, Rosati involution or quaternionic multiplication; these are the project's own, built on Mathlib's quaternion algebras $\mathbb H[\mathbb Q,a,b]$ with their star operation and on sheaves of modules on schemes with the monoidal structure set up in this development.
--
--   **Where it is used.** These structures express the moduli problem of polarised abelian surfaces with quaternionic multiplication and full level structure, in a shape matching the project's notion of a fine moduli space for polarised abelian schemes; `Packages` is the dictionary between such a structure and a fake elliptic curve with full level structure. They serve the construction of the Shimura curves entering the Čerednik–Drinfeld uniformisation used on the level-lowering side of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_CerednikDrinfeld_QMStructureOnPolarised.lean

import Definitions.Def_CerednikDrinfeld_QMCanonicalPol

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open scoped Quaternion
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation CerednikDrinfeld.QM

namespace AlgebraicGeometry.PolarisedAbelianScheme

variable {a b : ℚ}

structure QMStructure (Λ : Submodule ℤ ℍ[ℚ, a, b]) (star : ↥Λ → ↥Λ) (β : Fin (2 * 2) → ↥Λ)
    {d m : ℕ} {S : Type} [CommRing S] (X : PolarisedAbelianScheme 2 d m S) : Type 1 where

  act : ↥Λ → (X.A ⟶ X.A)

  act_over : ∀ x : ↥Λ, act x ≫ X.f = X.f

  act_hom : ∀ (x : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t X.f),
    pushPt (act x) (act_over x) (X.L.mul t P Q) = X.L.mul t (pushPt (act x) (act_over x) P) (pushPt (act x) (act_over x) Q)

  act_one : ∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, act ⟨1, h⟩ = 𝟙 X.A

  act_mul : ∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
    act ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = act y ≫ act x

  act_add : ∀ (x y : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t X.f),
    pushPt (act (x + y)) (act_over (x + y)) P =
      X.L.mul t (pushPt (act x) (act_over x) P) (pushPt (act y) (act_over y) P)

  act_trace : ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S →+* k)
    (V : Type) [AddCommGroup V] [Module k V] [Module.Finite k V] (τ : V → SchemeHomOver (tangentBase k sk) X.f),
    Function.Injective τ →
    (∀ P : SchemeHomOver (tangentBase k sk) X.f, P ∈ Set.range τ ↔ IsTangentVector X.L k sk P) →
    (∀ v w : V, τ (v + w) = X.L.mul (tangentBase k sk) (τ v) (τ w)) →
    (∀ (c : k) (v : V), (τ (c • v)).1 = tangentScale k c ≫ (τ v).1) →
    ∀ (x : ↥Λ) (Φ : V →ₗ[k] V), (∀ v : V, τ (Φ v) = pushPt (act x) (act_over x) (τ v)) →
    ∀ n : ℤ, (x : ℍ[ℚ, a, b]) + Star.star (x : ℍ[ℚ, a, b]) = ((n : ℚ) : ℍ[ℚ, a, b]) →
      LinearMap.trace k V Φ = (n : k)

  P : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) X.f

  level_match : ∀ j : Fin (2 * 2), pushPt (act (β j)) (act_over (β j)) P = X.P j

  pol_canonical : ∃ polE : X.A.Modules, CerednikDrinfeld.QM.IsCanonicalPolData X.f X.L act act_over star polE ∧
    LocIsoOnBase X.f X.pol (polE ⊗ polE ⊗ polE)

namespace QMStructure

variable {Λ : Submodule ℤ ℍ[ℚ, a, b]} {star : ↥Λ → ↥Λ} {β : Fin (2 * 2) → ↥Λ} {d m : ℕ}

def IsPullback {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S')
    {X : PolarisedAbelianScheme 2 d m S} {X' : PolarisedAbelianScheme 2 d m S'}
    (s : QMStructure Λ star β X) (s' : QMStructure Λ star β X') : Prop :=
  ∃ (gA : X'.A ⟶ X.A) (hg : CategoryTheory.IsPullback gA X'.f X.f (Spec.map (CommRingCat.ofHom φ))),
    (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S')) (x y : SchemeHomOver t' X'.f),
      (X'.L.mul t' x y).1 ≫ gA =
        (X.L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ))
          ⟨x.1 ≫ gA, by rw [Category.assoc, hg.w, ← Category.assoc, x.2]⟩
          ⟨y.1 ≫ gA, by rw [Category.assoc, hg.w, ← Category.assoc, y.2]⟩).1) ∧
    (∀ i, (X'.P i).1 ≫ gA = Spec.map (CommRingCat.ofHom φ) ≫ (X.P i).1) ∧
    Nonempty ((Scheme.Modules.pullback gA).obj X.pol ≅ X'.pol) ∧
    (∀ x : ↥Λ, s'.act x ≫ gA = gA ≫ s.act x) ∧
    s'.P.1 ≫ gA = Spec.map (CommRingCat.ofHom φ) ≫ s.P.1

def Iso {S : Type} [CommRing S] {X X' : PolarisedAbelianScheme 2 d m S}
    (s : QMStructure Λ star β X) (s' : QMStructure Λ star β X') : Prop :=
  ∃ (e : X.A ≅ X'.A) (he : e.hom ≫ X'.f = X.f),
    (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (x y : SchemeHomOver t X.f),
      (X.L.mul t x y).1 ≫ e.hom =
        (X'.L.mul t ⟨x.1 ≫ e.hom, by rw [Category.assoc, he]; exact x.2⟩
          ⟨y.1 ≫ e.hom, by rw [Category.assoc, he]; exact y.2⟩).1) ∧
    (∀ i, (X.P i).1 ≫ e.hom = (X'.P i).1) ∧
    (∀ p : ↥(Spec (CommRingCat.of S)), ∃ U : (Spec (CommRingCat.of S)).Opens, p ∈ U ∧
      Nonempty ((Scheme.Modules.pullback (X.f ⁻¹ᵁ U).ι).obj ((Scheme.Modules.pullback e.hom).obj X'.pol) ≅
        (Scheme.Modules.pullback (X.f ⁻¹ᵁ U).ι).obj X.pol)) ∧
    (∀ x : ↥Λ, s.act x ≫ e.hom = e.hom ≫ s'.act x) ∧
    s.P.1 ≫ e.hom = s'.P.1

def Packages {S : Type} [CommRing S] {X : PolarisedAbelianScheme 2 d m S}
    (s : QMStructure Λ star β X) (u : CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel Λ 1 m S) : Prop :=
  ∃ (e : u.1.A ≅ X.A) (he : e.hom ≫ X.f = u.1.f),
    (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (x y : SchemeHomOver t u.1.f),
      (u.1.L.mul t x y).1 ≫ e.hom =
        (X.L.mul t ⟨x.1 ≫ e.hom, by rw [Category.assoc, he]; exact x.2⟩
          ⟨y.1 ≫ e.hom, by rw [Category.assoc, he]; exact y.2⟩).1) ∧
    (∀ x : ↥Λ, u.1.act x ≫ e.hom = e.hom ≫ s.act x) ∧
    u.2.P.1 ≫ e.hom = s.P.1

end QMStructure

end AlgebraicGeometry.PolarisedAbelianScheme

end


