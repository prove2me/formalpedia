-- Prove2me | Definitions.Def_CoherentSDDP_Inner_Basic
-- name    : CoherentSDDP_Inner_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T20:10:22.821554+00:00
-- url     : https://prove2.me/theorems/484ecb0a-14c7-40bc-ae25-25afcd089c07
-- title:
--   §2, p. 3, and (10), p. 13 — coherent risk measures (cost convention), their extension to ℝ ∪ {+∞}, expectation, the dual form, epigraph convexity
-- statement:
--   This file fixes the vocabulary of one-step risk measures on a finite sample space $\Omega$, in the **cost convention** of Philpott, de Matos and Finardi: a random variable $Z:\Omega\to\mathbb R$ is a random cost, and larger is worse.
--
--   A function $\rho$ from random costs to $\mathbb R$ is a **coherent risk measure** if, for all $Z_1,Z_2:\Omega\to\mathbb R$,
--
--   1. *subadditivity:* $\rho(Z_1+Z_2)\le\rho(Z_1)+\rho(Z_2)$;
--   2. *monotonicity:* if $Z_1\le Z_2$ pointwise then $\rho(Z_1)\le\rho(Z_2)$;
--   3. *positive homogeneity:* $\rho(\lambda Z_1)=\lambda\rho(Z_1)$ for every real $\lambda>0$;
--   4. *translation equivariance:* $\rho(\mathbb I\lambda+Z_1)=\lambda+\rho(Z_1)$ for every real $\lambda$, where $\mathbb I\lambda$ is the constant random variable $\lambda$.
--
--   Each axiom is also available on its own, since the convexity property of the paper uses only the first and the third.
--
--   Costs in this paper may be $+\infty$ (an infeasible linear program, or a point outside the domain of an inner approximation). A risk measure $\rho$ on real costs is extended to $Z:\Omega\to\mathbb R\cup\{\pm\infty\}$ by
--   $$
--   \bar\rho(Z)=\begin{cases}\rho(Z) & \text{if } Z(\omega)<+\infty \text{ for every } \omega,\\ +\infty & \text{otherwise,}\end{cases}
--   $$
--   reflecting that every outcome has strictly positive probability, so an infinite cost in one outcome makes the risk infinite.
--
--   For probabilities $p:\Omega\to\mathbb R$ the file also defines the expectation $\mathbb E_p[Z]=\sum_\omega p(\omega)Z(\omega)$, the set
--   $$
--   \mathfrak B=\Big\{\zeta\in\mathbb R^\Omega:\ \sum_{\omega}p(\omega)\zeta(\omega)=1,\ \zeta\ge0\Big\},
--   $$
--   and, for $\mathfrak A\subseteq\mathbb R^\Omega$, the dual form (10), $\rho_{\mathfrak A}(Z)=\sup_{\zeta\in\mathfrak A}\sum_\omega p(\omega)\zeta(\omega)Z(\omega)$. Finally, an extended-real function $f$ on a real vector space is called convex when its epigraph $\{(x,r): f(x)\le r\}$, with $r$ real, is a convex set.
--
--   These are the objects in which every statement of the mission is phrased.
--
--   **Formalization Note** Random costs are functions `Ω → ℝ` and costs in $\mathbb R\cup\{\pm\infty\}$ are `EReal`-valued. The value $-\infty$ never arises for the costs of this paper; if a cost $Z(\omega)=-\infty$ were fed to $\bar\rho$ (all other values finite), Lean's `toReal` would read it as $0$, so statements that could meet $-\infty$ carry a hypothesis excluding it. The dual form is a real supremum over the subtype $\mathfrak A$; it has its intended meaning when $\mathfrak A$ is nonempty and the sums are bounded above, which holds for nonempty $\mathfrak A\subseteq\mathfrak B$ with $p>0$, the only situation in which it is used. The page writes the axioms for $\rho$ on "a space $\mathbb Z$ of random variables"; here that space is all of $\mathbb R^\Omega$, since $\Omega$ is finite.
-- source:
--   Philpott, de Matos & Finardi, On Solving Multistage Stochastic Programs with Coherent Risk Measures, authors' manuscript of 13 August 2012 (Operations Research, 2013), p. 3, §2 coherent risk measure axioms; p. 13, (10) and the set 𝔅

import Mathlib

namespace CoherentSDDP.Inner

/-- Subadditivity (p. 3): `ρ(Z₁ + Z₂) ≤ ρ(Z₁) + ρ(Z₂)`. -/
def RiskSubadditive {Ω : Type*} (ρ : (Ω → ℝ) → ℝ) : Prop :=
  ∀ Z₁ Z₂ : Ω → ℝ, ρ (Z₁ + Z₂) ≤ ρ Z₁ + ρ Z₂

/-- Monotonicity (p. 3, cost convention): if `Z₁ ≤ Z₂` pointwise then `ρ(Z₁) ≤ ρ(Z₂)`. -/
def RiskMonotone {Ω : Type*} (ρ : (Ω → ℝ) → ℝ) : Prop :=
  ∀ Z₁ Z₂ : Ω → ℝ, Z₁ ≤ Z₂ → ρ Z₁ ≤ ρ Z₂

/-- Positive homogeneity (p. 3): for `λ > 0`, `ρ(λZ) = λρ(Z)`. -/
def RiskPosHomogeneous {Ω : Type*} (ρ : (Ω → ℝ) → ℝ) : Prop :=
  ∀ (c : ℝ) (Z : Ω → ℝ), 0 < c → ρ (c • Z) = c * ρ Z

/-- Translation equivariance (p. 3): `ρ(𝕀λ + Z) = λ + ρ(Z)`, where `𝕀λ` is the constant `λ`. -/
def RiskTranslationEquivariant {Ω : Type*} (ρ : (Ω → ℝ) → ℝ) : Prop :=
  ∀ (c : ℝ) (Z : Ω → ℝ), ρ (fun ω => c + Z ω) = c + ρ Z

/-- A coherent risk measure in the cost convention (§2, p. 3): subadditive, monotone,
positively homogeneous and translation equivariant. -/
def IsCoherent {Ω : Type*} (ρ : (Ω → ℝ) → ℝ) : Prop :=
  RiskSubadditive ρ ∧ RiskMonotone ρ ∧ RiskPosHomogeneous ρ ∧ RiskTranslationEquivariant ρ

open Classical in
/-- The extension `ρ̄` of a real risk measure to costs in `ℝ ∪ {+∞}`: if some outcome has cost
`+∞` (every outcome has positive probability) the risk is `+∞`; otherwise `ρ` is applied to the
real-valued cost. The value `⊥` never occurs for the costs of this paper; on a `⊥` entry the
`toReal` below reads it as `0`. -/
noncomputable def riskE {Ω : Type*} (ρ : (Ω → ℝ) → ℝ) (Z : Ω → EReal) : EReal :=
  if ∀ ω, Z ω ≠ ⊤ then ((ρ (fun ω => (Z ω).toReal) : ℝ) : EReal) else ⊤

/-- Expectation `𝔼[Z] = Σ_ω p(ω) Z(ω)` on a finite sample space with probabilities `p`. -/
def expect {Ω : Type*} [Fintype Ω] (p : Ω → ℝ) (Z : Ω → ℝ) : ℝ :=
  ∑ ω, p ω * Z ω

/-- The set `𝔅 = {ζ : Σ_m p_m ζ_m = 1, ζ ≥ 0}` of §4, p. 13. -/
def dualSet {Ω : Type*} [Fintype Ω] (p : Ω → ℝ) : Set (Ω → ℝ) :=
  {ζ | ∑ ω, p ω * ζ ω = 1 ∧ 0 ≤ ζ}

/-- The dual form (10), p. 13: `ρ(Z) = sup_{ζ ∈ 𝔄} Σ_m p_m ζ_m Z(ω_m)`. This is a real
supremum; it is the intended value when `𝔄` is nonempty and the sums are bounded above, which
holds whenever `𝔄 ⊆ 𝔅` is nonempty and `p > 0`. -/
noncomputable def dualRisk {Ω : Type*} [Fintype Ω] (p : Ω → ℝ) (𝔄 : Set (Ω → ℝ))
    (Z : Ω → ℝ) : ℝ :=
  ⨆ ζ : 𝔄, ∑ ω, p ω * (ζ : Ω → ℝ) ω * Z ω

/-- Convexity of an extended-real function, as convexity of its (real) epigraph
`{(x, r) : f x ≤ r}`. -/
def EConvex {E : Type*} [AddCommGroup E] [Module ℝ E] (f : E → EReal) : Prop :=
  Convex ℝ {q : E × ℝ | f q.1 ≤ (q.2 : EReal)}

end CoherentSDDP.Inner


