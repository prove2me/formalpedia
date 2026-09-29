-- Prove2me | Definitions.Def_CerednikDrinfeld_QMRigidificationLevel
-- name    : CerednikDrinfeld_QMRigidificationLevel
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/b1dc8623-6097-564f-8b33-1e2d115d1a02
-- title:
--   Normalised level transport for rigidified fake elliptic curves
-- statement:
--   The single declaration `IsNormLevelTransport` is a relation between a full level-$n$ structure on a fake elliptic curve $E$ over an $\mathcal O$-algebra $B$, equipped with a rigidification along a leg $\psi : O^{nr} \to B$, and a level-$n$ structure on the base curve $A_0$ over $O^{nr}/(\pi)$, normalised by a power of $r$.
--
--   The data are: a prime $r$; a commutative ring $\mathcal O$ with an element $\pi$; an $\mathcal O$-algebra $O^{nr}$ with an $\mathcal O$-algebra automorphism $\mathrm{Fr}$; a fake elliptic curve $A_0$ for the order $\Lambda$ and level $N$ over $O^{nr}/(\pi)$ together with formal coordinates $\theta_0$ of its structure morphism in dimension $2$; a ring homomorphism $\kappa : O^{nr}/(\pi) \to O^{nr}/\mathrm{pIdeal}\,r\,O^{nr}$; a two-variable series $\beta_0$ and a formal $\mathcal O_D$-module $\Phi$ over $O^{nr}/\mathrm{pIdeal}\,r\,O^{nr}$; a ring homomorphism $\iota$ from $\mathrm{Zp2}\,r$ to $O^{nr}$; a map $\mathrm{coord} : \Lambda \to \mathrm{Zp2}\,r \times \mathrm{Zp2}\,r$; a full level-$n$ structure $P_0$ on $A_0$; and, over a further $\mathcal O$-algebra $B$ with $\psi : O^{nr} \to B$, a fake elliptic curve $E$, a rigidification $\varrho$ of $E$ relative to $A_0$ along $\psi$, and a full level-$n$ structure $P_n$ on $E$.
--
--   The predicate asserts the existence of a morphism $Q : \operatorname{Spec}(B/(\pi)) \to \varrho.\mathtt{Ab}.A$ which is a section of the structure morphism of $\varrho.\mathtt{Ab}$ and which, composed with the comparison $\varrho.\mathtt{gA}$ to $A_0$, is the base change of $P_0$ along $\mathrm{Spec}$ of the induced map $O^{nr}/(\pi) \to B/(\pi)$; together with a formal $\mathcal O_D$-module $X$ over $B$, formal coordinates $\theta$ of $E$ exhibiting $E$ as a formal module for $X$ via $\mathrm{coord}$ (the predicate `IsFormalModuleVia`: $\theta$ are formal coordinates for the group law of $E$ with underlying law $X.F$, and the action of each $m \in \Lambda$ on points is computed, on nilpotent arguments, by the series attached to $\mathrm{coord}\,m$), an exponent $j$ with $j \le 1$, and a rigidified special formal module $t$ over $B$ for $\Phi$ with $t.X = X$, subject to three conditions. First, `IsRigTransport θ₀ κ β₀ ϱ θ j t`: there are a ring homomorphism $\kappa_B : B/(\pi) \to B/\mathrm{pIdeal}\,r\,B$ compatible with the reductions and with $\kappa$, and a series $\sigma$ over $B/(\pi)$, such that on every algebra $B''$ receiving compatible maps from $B$, $B/(\pi)$ and $O^{nr}/(\pi)$, the composite of a $\theta_0$-point of $\varrho.\mathtt{Ab}$ with argument in a nilpotent ideal with $\varrho.\varphi'$ and $\varrho.\mathtt{gb}$ is the $\theta$-point with argument $\sigma$ evaluated there, and $t.\rho$ is the reduction of $\sigma$ composed with the reduction of $\beta_0$ and with $X_i \mapsto X_i^{r^j}$. Secondly, $t$ is admissible for $\iota$ and the Frobenius-twisted leg $\psi \circ \mathrm{Fr}^{-j}$. Thirdly, the normalised level equation: the reduction modulo $\pi$ of the point $r^{t.n} \cdot P_n$ of $E$ equals $Q$ followed by $\varrho.\varphi'$ followed by $\varrho.\mathtt{gb}$. Thus the relation is a condition on chosen coordinates and a chosen rigidified model, with the multiplication by $r^{t.n}$ making the transported level insensitive to re-presenting the rigidification with shifted $r$-powers.
--
--   **Relation to Mathlib.** Fake elliptic curves, rigidifications and special formal $\mathcal O_D$-modules have no counterpart in Mathlib; all the notions combined here are the project's own, built on Mathlib's scheme theory and multivariate power series.
--
--   **Where it is used.** The relation fixes the level-structure half of the Čerednik–Drinfeld dictionary, matching full level-$n$ structures on a rigidified fake elliptic curve over an $\mathcal O$-algebra with those on the base curve in characteristic $\pi$ through the associated rigidified special formal module. It is used in the construction of the $r$-adic uniformisation of the Shimura curves with level structure that enter the modularity argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_CerednikDrinfeld_QMRigidificationLevel.lean

import Definitions.Def_CerednikDrinfeld_QMRigidification
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld.FormalOmega CerednikDrinfeld.SpecialFormal

namespace CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}

def IsNormLevelTransport {r : ℕ} [Fact r.Prime] {𝒪 : Type} [CommRing 𝒪] {π : 𝒪} {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr]
    (Fr : Onr ≃ₐ[𝒪] Onr)
    {A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π})}
    (θ₀ : RelativeGroupLaw.FormalCoordinates A₀.f 2)
    (κ : (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) →+* (Onr ⧸ pIdeal r Onr))
    (β₀ : Series (Onr ⧸ pIdeal r Onr))
    (Φ : FormalODModule r (Onr ⧸ pIdeal r Onr))
    (ι : Zp2 r →+* Onr)
    (coord : ↥Λ → Zp2 r × Zp2 r)
    {n : ℕ} (P₀ : A₀.FullLevel n)
    {B : Type} [CommRing B] [Algebra 𝒪 B] {ψ : Onr →ₐ[𝒪] B} {E : FakeEllipticCurve Λ N B}
    (ϱ : Rigidification r π A₀ ψ E) (Pn : E.FullLevel n) : Prop :=
  ∃ Q : Spec (CommRingCat.of (B ⧸ Ideal.span {algebraMap 𝒪 B π})) ⟶ ϱ.Ab.A, Q ≫ ϱ.Ab.f = 𝟙 _ ∧
    Q ≫ ϱ.gA = Spec.map (CommRingCat.ofHom (residueLeg π ψ)) ≫ (P₀.P).1 ∧
    ∃ (X : FormalODModule r B) (θ : RelativeGroupLaw.FormalCoordinates E.f 2) (_ : E.IsFormalModuleVia coord X θ)
      (j : ℕ) (t : Rigidified r Φ B), j ≤ 1 ∧ t.X = X ∧
      IsRigTransport θ₀ κ β₀ ϱ θ j t ∧
      t.IsAdmissible ι ((frobTwist Onr Fr (-(j : ℤ)) ψ : Onr →ₐ[𝒪] B) : Onr →+* B) ∧
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π}))) ≫ (nsmulPt E.L (𝟙 _) (r ^ t.n) Pn.P).1 =
        Q ≫ ϱ.φ' ≫ ϱ.gb

end CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification


