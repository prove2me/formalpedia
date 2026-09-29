-- Prove2me | Definitions.Def_CerednikDrinfeld_QMModuliProps
-- name    : CerednikDrinfeld_QMModuliProps
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/96ea2108-13a5-5694-b48e-dcbb48eec003
-- title:
--   Extra level structures, degeneracy and Atkin–Lehner relations
-- statement:
--   Over a commutative ring $S$, fix a $\mathbb Z$-submodule $\Lambda$ of a rational quaternion algebra $\mathbb H[\mathbb Q,a,b]$, a level $N$, and a `FakeEllipticCurve Λ N S` $E$, that is a relatively two-dimensional smooth proper scheme $A \to \operatorname{Spec} S$ with commutative relative group law $L$, a $\Lambda$-action by endomorphisms over $S$ satisfying a trace condition, and a level structure $\mathrm{lev} : C \hookrightarrow A$. The structure `ExtraLevel E ℓ` is a second such level datum on the same $A$: a closed immersion $\mathrm{levK} : K \to A$ whose points are closed under $L$-multiplication and inversion, contain the unit section, are killed by $\ell$-fold $L$-addition, are stable under every $\mathrm{act}\,x$ ($x \in \Lambda$), and meet the points factoring through $\mathrm{lev}$ only in the unit; $\mathrm{levK} \gg E.f$ is required finite, flat and locally of finite presentation of fibrewise rank $\ell^2$, and over every algebraically closed field $k$ with $\ell$ invertible the points factoring through $\mathrm{levK}$ form a group isomorphic to $(\mathbb Z/\ell)^2$. `WithExtraLevel Λ N ℓ S` is the sigma type of such pairs $u = (E,K)$, and `WithExtraLevel.Iso` asks for an isomorphism of the underlying schemes over $S$, compatible with the group laws, the $\Lambda$-actions, and both level structures in the sense that factorisation through $\mathrm{lev}$, respectively $\mathrm{levK}$, is preserved in both directions. Two degeneracy relations to level $N$ are defined: `IsLevelRestrict u d` is just `FakeEllipticCurve.Iso u.1 d`, and `IsLevelIsogeny ℓ u d` asks for morphisms $\varphi : A_u \to A_d$ and $\psi : A_d \to A_u$ over $S$, both additive and $\Lambda$-equivariant, with $\varphi \gg \psi$ and $\psi \gg \varphi$ equal to the action of $\ell$ whenever $\ell \in \Lambda$, with $\varphi$-kernel on points exactly the points factoring through $\mathrm{levK}$, and with $\varphi$ carrying $\mathrm{lev}$-points to $\mathrm{lev}$-points. `IsAtkinLehnerQuotient r E E'` has the same shape, with $\varphi\psi = \psi\varphi = [r]$ and with the kernel condition instead requiring that a point is killed by $\varphi$ exactly when it is killed by $\mathrm{act}\,m$ for every $m \in \Lambda$ with $m \, \overline m$ an integer multiple of $r$; `WithExtraLevel.IsAtkinLehnerQuotient` is the variant for pairs, with the extra clause that $\varphi$ carries $\mathrm{levK}$-points to $\mathrm{levK}$-points. Finally, two predicates on a moduli witness $w$ for a Shimura curve model $M$: `IsOriented` says that for every prime $\ell \mid N$ and every pair of places $P, Q$ of $M.\mathrm{Fbar}$, $Q$ lies in the support of $M.\mathrm{corrBar}\,\ell$ applied to $P$ if and only if there are $u$ with extra level $\ell$ and $d$ over $\overline{\mathbb Q}$ whose associated points are $w.\mathrm{pts}\,P$ and $w.\mathrm{pts}\,Q$ and with `IsLevelIsogeny ℓ u d`; `IsGoodReductionModel` says that $w.\pi X$ is smooth of relative dimension $1$ and that every base change of it along a point of the base with values in an algebraically closed field is integral.
--
--   **Relation to Mathlib.** Mathlib has no notion of fake elliptic curve, quaternionic level structure or Atkin–Lehner involution; these are the project's own predicates, built on Mathlib's scheme-morphism properties (`IsClosedImmersion`, `IsFinite`, `Flat`, `LocallyOfFinitePresentation`, `SmoothOfRelativeDimension`) and on the project's `RelativeGroupLaw`.
--
--   **Where it is used.** These relations give the moduli description of the Hecke correspondence at a prime dividing the level on a Shimura curve attached to an indefinite quaternion algebra, i.e. the $U_\ell$ operator as the composite of the forgetful and the quotient degeneracy maps, together with the Atkin–Lehner quotients at a ramified prime. They feed the Čerednik–Drinfeld description of the bad fibre used in the level-lowering step of the Frey–Serre–Ribet argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_CerednikDrinfeld_QMModuliProps.lean

import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Definitions.Def_CerednikDrinfeld_QMModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsDedekindDomain AlgebraicCurve
open scoped Quaternion TensorProduct NumberField

namespace CerednikDrinfeld.QM.FakeEllipticCurve

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type u} [CommRing S]

structure ExtraLevel (E : FakeEllipticCurve Λ N S) (ℓ : ℕ) : Type (u + 1) where

  K : Scheme.{u}

  levK : K ⟶ E.A

  levK_closed : IsClosedImmersion levK

  levK_sub : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E.f),
    FactorsThrough levK P → FactorsThrough levK Q → FactorsThrough levK (E.L.mul t P Q) ∧ FactorsThrough levK (E.L.inv t P)

  levK_one : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)), FactorsThrough levK (E.L.one t)

  levK_torsion : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f),
    FactorsThrough levK P → nsmulPt E.L t ℓ P = E.L.one t

  levK_stable : ∀ (x : ↥Λ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f),
    FactorsThrough levK P → FactorsThrough levK (pushPt (E.act x) (E.act_over x) P)

  levK_disjoint : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f),
    FactorsThrough levK P → FactorsThrough E.lev P → P = E.L.one t

  levK_finite : IsFinite (levK ≫ E.f)

  levK_flat : Flat (levK ≫ E.f)

  levK_finitePresentation : LocallyOfFinitePresentation (levK ≫ E.f)

  levK_rank : ∀ s : ↥(Spec (CommRingCat.of S)), (levK ≫ E.f).finrank s = ℓ ^ 2

  levK_fibre : ∀ (k : Type u) [Field k] [IsAlgClosed k] (sk : S →+* k), (ℓ : k) ≠ 0 →
    ∃ e : ZMod ℓ × ZMod ℓ ≃ {P : SchemeHomOver (geomPoint k sk) E.f // FactorsThrough levK P},
      ∀ x y : ZMod ℓ × ZMod ℓ, (e (x + y) : SchemeHomOver (geomPoint k sk) E.f) = E.L.mul (geomPoint k sk) (e x) (e y)

abbrev WithExtraLevel (Λ : Submodule ℤ ℍ[ℚ, a, b]) (N ℓ : ℕ) (S : Type u) [CommRing S] : Type (u + 1) :=
  Σ E : FakeEllipticCurve Λ N S, E.ExtraLevel ℓ

def WithExtraLevel.Iso {ℓ : ℕ} (u u' : WithExtraLevel Λ N ℓ S) : Prop :=
  ∃ (e : u.1.A ≅ u'.1.A) (he : e.hom ≫ u'.1.f = u.1.f),
    (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t u.1.f),
      mapPt e.hom he (u.1.L.mul t P Q) = u'.1.L.mul t (mapPt e.hom he P) (mapPt e.hom he Q)) ∧
    (∀ x : ↥Λ, u.1.act x ≫ e.hom = e.hom ≫ u'.1.act x) ∧
    (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t u.1.f),
      FactorsThrough u.1.lev P ↔ FactorsThrough u'.1.lev (mapPt e.hom he P)) ∧
    (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t u.1.f),
      FactorsThrough u.2.levK P ↔ FactorsThrough u'.2.levK (mapPt e.hom he P))

def IsLevelRestrict {ℓ : ℕ} (u : WithExtraLevel Λ N ℓ S) (d : FakeEllipticCurve Λ N S) : Prop :=
  FakeEllipticCurve.Iso u.1 d

def IsLevelIsogeny (ℓ : ℕ) (u : WithExtraLevel Λ N ℓ S) (d : FakeEllipticCurve Λ N S) : Prop :=
  ∃ (φ : u.1.A ⟶ d.A) (hφ : φ ≫ d.f = u.1.f) (ψ : d.A ⟶ u.1.A) (hψ : ψ ≫ u.1.f = d.f),
    (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t u.1.f),
      mapPt φ hφ (u.1.L.mul t P Q) = d.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q)) ∧
    (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t d.f),
      mapPt ψ hψ (d.L.mul t P Q) = u.1.L.mul t (mapPt ψ hψ P) (mapPt ψ hψ Q)) ∧
    (∀ x : ↥Λ, u.1.act x ≫ φ = φ ≫ d.act x) ∧ (∀ x : ↥Λ, d.act x ≫ ψ = ψ ≫ u.1.act x) ∧
    (∀ hℓ : ((ℓ : ℚ) : ℍ[ℚ, a, b]) ∈ Λ,
      φ ≫ ψ = u.1.act ⟨((ℓ : ℚ) : ℍ[ℚ, a, b]), hℓ⟩ ∧ ψ ≫ φ = d.act ⟨((ℓ : ℚ) : ℍ[ℚ, a, b]), hℓ⟩) ∧
    (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t u.1.f),
      mapPt φ hφ P = d.L.one t ↔ FactorsThrough u.2.levK P) ∧
    (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t u.1.f),
      FactorsThrough u.1.lev P → FactorsThrough d.lev (mapPt φ hφ P))

def IsAtkinLehnerQuotient (r : ℕ) (E E' : FakeEllipticCurve Λ N S) : Prop :=
  ∃ (φ : E.A ⟶ E'.A) (hφ : φ ≫ E'.f = E.f) (ψ : E'.A ⟶ E.A) (hψ : ψ ≫ E.f = E'.f),
    (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E.f),
      mapPt φ hφ (E.L.mul t P Q) = E'.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q)) ∧
    (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E'.f),
      mapPt ψ hψ (E'.L.mul t P Q) = E.L.mul t (mapPt ψ hψ P) (mapPt ψ hψ Q)) ∧
    (∀ x : ↥Λ, E.act x ≫ φ = φ ≫ E'.act x) ∧ (∀ x : ↥Λ, E'.act x ≫ ψ = ψ ≫ E.act x) ∧
    (∀ hr : ((r : ℚ) : ℍ[ℚ, a, b]) ∈ Λ,
      φ ≫ ψ = E.act ⟨((r : ℚ) : ℍ[ℚ, a, b]), hr⟩ ∧ ψ ≫ φ = E'.act ⟨((r : ℚ) : ℍ[ℚ, a, b]), hr⟩) ∧
    (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f),
      mapPt φ hφ P = E'.L.one t ↔
        ∀ (m : ↥Λ) (n : ℤ), (m : ℍ[ℚ, a, b]) * star (m : ℍ[ℚ, a, b]) = (((r : ℤ) * n : ℚ) : ℍ[ℚ, a, b]) →
          pushPt (E.act m) (E.act_over m) P = E.L.one t) ∧
    (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f),
      FactorsThrough E.lev P → FactorsThrough E'.lev (mapPt φ hφ P))

def WithExtraLevel.IsAtkinLehnerQuotient {ℓ : ℕ} (r : ℕ) (u u' : WithExtraLevel Λ N ℓ S) : Prop :=
  ∃ (φ : u.1.A ⟶ u'.1.A) (hφ : φ ≫ u'.1.f = u.1.f) (ψ : u'.1.A ⟶ u.1.A) (hψ : ψ ≫ u.1.f = u'.1.f),
    (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t u.1.f),
      mapPt φ hφ (u.1.L.mul t P Q) = u'.1.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q)) ∧
    (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t u'.1.f),
      mapPt ψ hψ (u'.1.L.mul t P Q) = u.1.L.mul t (mapPt ψ hψ P) (mapPt ψ hψ Q)) ∧
    (∀ x : ↥Λ, u.1.act x ≫ φ = φ ≫ u'.1.act x) ∧ (∀ x : ↥Λ, u'.1.act x ≫ ψ = ψ ≫ u.1.act x) ∧
    (∀ hr : ((r : ℚ) : ℍ[ℚ, a, b]) ∈ Λ,
      φ ≫ ψ = u.1.act ⟨((r : ℚ) : ℍ[ℚ, a, b]), hr⟩ ∧ ψ ≫ φ = u'.1.act ⟨((r : ℚ) : ℍ[ℚ, a, b]), hr⟩) ∧
    (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t u.1.f),
      mapPt φ hφ P = u'.1.L.one t ↔
        ∀ (m : ↥Λ) (n : ℤ), (m : ℍ[ℚ, a, b]) * star (m : ℍ[ℚ, a, b]) = (((r : ℤ) * n : ℚ) : ℍ[ℚ, a, b]) →
          pushPt (u.1.act m) (u.1.act_over m) P = u.1.L.one t) ∧
    (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t u.1.f),
      FactorsThrough u.1.lev P → FactorsThrough u'.1.lev (mapPt φ hφ P)) ∧
    (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t u.1.f),
      FactorsThrough u.2.levK P → FactorsThrough u'.2.levK (mapPt φ hφ P))

end CerednikDrinfeld.QM.FakeEllipticCurve

namespace CerednikDrinfeld

open CerednikDrinfeld.QM

variable {a b : ℚ}

def ShimuraCurveModel.ModuliWitness.IsOriented {R₀ : Submodule ℤ ℍ[ℚ, a, b]}
    {ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ}
    {𝒮 : ℕ → Set (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ}
    {M : ShimuraCurveModel R₀ ι 𝒮} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N q q' : ℕ}
    (w : M.ModuliWitness Λ N q q') : Prop :=
  ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∣ N → ∀ (P Q : Place (AlgebraicClosure ℚ) M.Fbar),
    Q ∈ (M.corrBar ℓ hℓ (Finsupp.single P 1)).support ↔
      ∃ (u : FakeEllipticCurve.WithExtraLevel Λ N ℓ (AlgebraicClosure ℚ)) (d : FakeEllipticCurve Λ N (AlgebraicClosure ℚ)),
        w.pt _ w.sbar u.1 = w.pts P ∧ w.pt _ w.sbar d = w.pts Q ∧ FakeEllipticCurve.IsLevelIsogeny ℓ u d

def ShimuraCurveModel.ModuliWitness.IsGoodReductionModel {R₀ : Submodule ℤ ℍ[ℚ, a, b]}
    {ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ}
    {𝒮 : ℕ → Set (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ}
    {M : ShimuraCurveModel R₀ ι 𝒮} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N q q' : ℕ}
    (w : M.ModuliWitness Λ N q q') : Prop :=
  SmoothOfRelativeDimension 1 w.πX ∧
  ∀ (k : Type) [Field k] [IsAlgClosed k]
    (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Localization.Away ((N * q * q' : ℕ) : ℤ)))),
    IsIntegral (CategoryTheory.Limits.pullback w.πX s)

end CerednikDrinfeld

end


