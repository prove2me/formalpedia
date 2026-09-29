-- Prove2me | Definitions.Def_CerednikDrinfeld_ThetaMer
-- name    : CerednikDrinfeld_ThetaMer
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/697d3c7c-767f-593b-8002-f6c216c27342
-- title:
--   Theta pairs and theta as a meromorphic function
-- statement:
--   The setting is a field $K_0$, a valued extension field $K$ of $K_0$ with value group $\Gamma_0$, a pseudo-uniformiser $\varpi$ for the pair (an element of $K_0$ whose image in $K$ has valuation strictly between $0$ and $1$, scaling all nonzero elements of $K_0$ into bounded powers of it), and a group homomorphism $\rho\colon G\to\mathrm{PGL}_2(K_0)$, acting on Drinfeld's half plane $\Omega=K\setminus\mathrm{im}(K_0\to K)$ by the projective Möbius action `pmoebius`. Recall that `holRing ϖ` is the subring of functions $\Omega\to K$ whose restriction to each affinoid $\varpi$-layer is a uniform limit of uniformly bounded, pole-free rational functions, and that `merField ϖ` is its fraction field.
--
--   The predicate `IsThetaPair ϖ ρ a b z₀ F H`, for points $a,b,z_0\in K$ and $F,H$ in `holRing ϖ`, asserts four things: $H$ is a non-zero-divisor of `holRing ϖ`; the zero set of $H$ on $\Omega$ is exactly the $\rho(G)$-orbit of $b$, in the sense that $H(z)=0$ if and only if $z=\rho(\gamma)\cdot b$ for some $\gamma\in G$; the zero set of $F$ is likewise exactly the $\rho(G)$-orbit of $a$; and for every $z\in\Omega$ outside the orbit of $b$, the quotient $F(z)/H(z)$ equals $\theta_\rho(a,b;z_0)(z)$, the infinite product over $\gamma\in G$ of the cross-ratios $\big((z-\rho(\gamma)a)(z_0-\rho(\gamma)b)\big)/\big((z-\rho(\gamma)b)(z_0-\rho(\gamma)a)\big)$.
--
--   Then `thetaMer ϖ ρ a b z₀` is the element of `merField ϖ` defined by cases: if a theta pair $(F,H)$ for the data exists, it is the fraction $F/H$ formed from a pair chosen from that existence statement; otherwise it is $0$. The two accompanying lemmas record exactly these two cases, `thetaMer_def_of_exists` in the presence of a pair and `thetaMer_of_not_exists` in its absence. Thus the definition is unconditional, with the value $0$ as a default, and any identity about the theta function requires the existence of a theta pair as an input.
--
--   **Relation to Mathlib.** Mathlib has no rigid-analytic geometry and no theta functions for Schottky-type groups; the ring of rigid-holomorphic functions, the half plane and the theta product are the project's own notions. The ambient fraction field is Mathlib's `FractionRing`, and the fraction is formed with `Localization.mk`; the infinite product in `theta` is Mathlib's multipliable product.
--
--   **Where it is used.** The element `thetaMer` is the analytic input to the Čerednik–Drinfeld description of the rigid-analytic uniformisation of Shimura curves: theta functions of the relevant discrete subgroup of $\mathrm{PGL}_2(K_0)$ produce meromorphic functions on the quotient, whose divisors and periods give the Mumford curve and its Jacobian. That uniformisation is used in the level-lowering part of the route to Fermat's Last Theorem.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_CerednikDrinfeld_ThetaMer.lean

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open scoped MatrixGroups
open Classical CerednikDrinfeld.Omega

namespace CerednikDrinfeld.Omega

variable {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K] [DecidableEq K]
variable {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

def IsThetaPair (ϖ : PseudoUniformizer K₀ K) {G : Type} [Group G] (ρ : G →* PGL(2, K₀)) (a b z₀ : K)
    (F H : ↥(holRing ϖ)) : Prop :=
  H ∈ nonZeroDivisors ↥(holRing ϖ) ∧
  (∀ z : ↥(upperHalfPlane K₀ K),
    (H : ↥(upperHalfPlane K₀ K) → K) z = 0 ↔ ∃ γ : G, pmoebius K₀ (ρ γ) b = (z : K)) ∧
  (∀ z : ↥(upperHalfPlane K₀ K),
    (F : ↥(upperHalfPlane K₀ K) → K) z = 0 ↔ ∃ γ : G, pmoebius K₀ (ρ γ) a = (z : K)) ∧
  (∀ z : ↥(upperHalfPlane K₀ K), (¬ ∃ γ : G, pmoebius K₀ (ρ γ) b = (z : K)) →
    (F : ↥(upperHalfPlane K₀ K) → K) z / (H : ↥(upperHalfPlane K₀ K) → K) z = theta ρ a b z₀ (z : K))

def thetaMer (ϖ : PseudoUniformizer K₀ K) {G : Type} [Group G] (ρ : G →* PGL(2, K₀)) (a b z₀ : K) : merField ϖ :=
  if h : ∃ F H : ↥(holRing ϖ), IsThetaPair ϖ ρ a b z₀ F H then
    Localization.mk h.choose ⟨h.choose_spec.choose, h.choose_spec.choose_spec.1⟩
  else 0

theorem thetaMer_def_of_exists (ϖ : PseudoUniformizer K₀ K) {G : Type} [Group G] (ρ : G →* PGL(2, K₀)) (a b z₀ : K)
    (h : ∃ F H : ↥(holRing ϖ), IsThetaPair ϖ ρ a b z₀ F H) :
    thetaMer ϖ ρ a b z₀ = Localization.mk h.choose ⟨h.choose_spec.choose, h.choose_spec.choose_spec.1⟩ :=
  dif_pos h

theorem thetaMer_of_not_exists (ϖ : PseudoUniformizer K₀ K) {G : Type} [Group G] (ρ : G →* PGL(2, K₀)) (a b z₀ : K)
    (h : ¬ ∃ F H : ↥(holRing ϖ), IsThetaPair ϖ ρ a b z₀ F H) : thetaMer ϖ ρ a b z₀ = 0 :=
  dif_neg h

end CerednikDrinfeld.Omega

end


