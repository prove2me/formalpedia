-- Prove2me | Definitions.Def_StochArbitrage_Pricing_Model
-- name    : StochArbitrage_Pricing_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T00:22:25.308776+00:00
-- url     : https://prove2.me/theorems/f4d47196-fd07-46d3-ab33-ad07079e0810
-- title:
--   §2.1–§2.3, pp. 5–11 — payoffs on [a,b]^N, utility class U, benchmarks K, overlay polytope ∆, D(u,κ,δ,F), strict SAO set (2), SDF set M_(U,K), present value, polar cone ∆*
-- statement:
--   This file fixes the single-period market of §2.1 and the objects of §2.2–§2.3 on which every statement of the mission is built.
--
--   **Market.** There are $N$ base assets. Their payoff vector at the horizon is $x=(x_1,\dots,x_N)^\mathsf T\in\mathbb R^N$, with joint law $F$, a probability measure on $\mathbb R^N$. The payoffs are supported in a box: almost surely every coordinate lies in $[\mathrm{lo},\mathrm{hi}]$ with $-\infty<\mathrm{lo}<\mathrm{hi}<\infty$ (the paper's $\mathcal X=[a,b]$). The base assets have prices $p\in\mathbb R^N$.
--
--   **Standing assumptions.** A utility class $\mathcal U$ is a set of functions $u:\mathbb R\to\mathbb R$, each continuously differentiable, strictly increasing and strictly concave; $\mathcal U$ is convex and uniformly bounded on bounded sets (for every $r$ there is $B$ with $|u(y)|\le B$ for all $u\in\mathcal U$ and $|y|\le r$). The benchmark set $K\subseteq\mathbb R^N$ is closed and bounded, and every $\kappa\in K$ satisfies the budget restriction $p^\mathsf T\kappa=c$ with $c>0$. The overlay set is the polytope
--   $$\Delta=\{\delta\in\mathbb R^N : A\delta\le a\},$$
--   where $A$ is an $R\times N$ matrix and $a\in\mathbb R^R$; it is assumed bounded, and $a\ge 0$, i.e. the passive overlay $0_N$ is feasible.
--
--   **Objects.** The expected utility increment of the overlay $\delta$ over the benchmark $\kappa$ for the utility $u$ is
--   $$D(u,\kappa,\delta,F)=E_F[u(x^\mathsf T(\kappa+\delta))]-E_F[u(x^\mathsf T\kappa)].$$
--   The set of (strict) stochastic arbitrage opportunities, display (2), is
--   $$\Delta^\succ_{(\mathcal U,K,F)}=\{\delta\in\Delta : D(u,\kappa,\delta,F)>0\ \text{for all }(u,\kappa)\in\mathcal U\times K\}.$$
--   The candidate stochastic discount factors are the scaled marginal utilities
--   $$\mathcal M_{(\mathcal U,K)}=\{x\mapsto d\,u'(x^\mathsf T\kappa) : (u,\kappa)\in\mathcal U\times K,\ d>0\}.$$
--   A discount factor $m$ assigns the base assets the present-value vector $E_F[m(x)x]\in\mathbb R^N$. Finally, the polar cone of the overlay set is taken in the paper's form
--   $$\Delta^*=\{A^\mathsf T\sigma : \sigma\in\mathbb R^R,\ \sigma\ge 0,\ a^\mathsf T\sigma\le 0\}.$$
--
--   These definitions are shared by Theorem 2.3.1 and every supporting statement of the mission.
--
--   **Formalization Note.** Payoffs and portfolios are vectors `Fin N → ℝ`; $x^\mathsf T\kappa$ is the dot product. Expectations are Bochner integrals; the a.e. box support, continuity of $u$ and $u'$ and boundedness of the portfolios make every integrand used in the mission bounded, so no default value of the integral enters. $u'$ is `deriv u`, which is the true derivative because $u$ is $C^1$. The paper writes $a$ both for the lower end of $\mathcal X=[a,b]$ and for the right-hand side of $A\delta\le a$; Lean calls them `lo`, `hi` and `aVec`. "Uniformly bounded" is read on bounded sets, since no strictly increasing strictly concave function on $\mathbb R$ is bounded. The additional description of overlays by $p^\mathsf T\delta=0$ is not imposed separately: as in the paper, $\Delta$ is exactly the set $A\delta\le a$. The standing assumptions are bundled in `Market.Standing`.
-- source:
--   Arvanitis & Post, Ordering Arbitrage Portfolios and Finding Arbitrage Opportunities, AUEB Department of Economics Working Paper 04-2022 (March 2022; published as Generalized Stochastic Arbitrage Opportunities, Management Science 2024), pp. 5–11 (PDF 6–12), §2.1–§2.3, Definition 2.2.2, (2); M_(U,K) and ∆* p. 11 (PDF 12)

import Mathlib

namespace StochArbitrage.Pricing

open MeasureTheory Matrix

/-- Data of the single-period market in §2.1. -/
structure Market (N R : ℕ) where
  μ : Measure (Fin N → ℝ)
  lo : ℝ
  hi : ℝ
  p : Fin N → ℝ
  c : ℝ
  A : Matrix (Fin R) (Fin N) ℝ
  aVec : Fin R → ℝ

variable {N R : ℕ}

/-- The feasible overlay polytope Δ = {δ : Aδ ≤ a}. -/
def Market.overlaySet (M : Market N R) : Set (Fin N → ℝ) :=
  {δ | M.A *ᵥ δ ≤ M.aVec}

/-- Standing market, preference, benchmark, and overlay assumptions of §2.1. -/
def Market.Standing (M : Market N R) (U : Set (ℝ → ℝ))
    (K : Set (Fin N → ℝ)) : Prop :=
  IsProbabilityMeasure M.μ ∧ M.lo < M.hi ∧
  (∀ᵐ x ∂M.μ, ∀ i, x i ∈ Set.Icc M.lo M.hi) ∧
  (∀ u ∈ U, ContDiff ℝ 1 u ∧ StrictMono u ∧ StrictConcaveOn ℝ Set.univ u) ∧
  Convex ℝ U ∧
  (∀ r : ℝ, ∃ B : ℝ, ∀ u ∈ U, ∀ y : ℝ, |y| ≤ r → |u y| ≤ B) ∧
  IsClosed K ∧ Bornology.IsBounded K ∧ 0 < M.c ∧
  (∀ κ ∈ K, M.p ⬝ᵥ κ = M.c) ∧
  Bornology.IsBounded M.overlaySet ∧ 0 ≤ M.aVec

/-- Expected-utility increment D(u,κ,δ,F). -/
noncomputable def Market.D (M : Market N R) (u : ℝ → ℝ)
    (κ δ : Fin N → ℝ) : ℝ :=
  (∫ x, u (x ⬝ᵥ (κ + δ)) ∂M.μ) - ∫ x, u (x ⬝ᵥ κ) ∂M.μ

/-- The strict stochastic arbitrage opportunities, Definition 2.2.2 (2). -/
def Market.strictSAOSet (M : Market N R) (U : Set (ℝ → ℝ))
    (K : Set (Fin N → ℝ)) : Set (Fin N → ℝ) :=
  {δ | δ ∈ M.overlaySet ∧ ∀ u ∈ U, ∀ κ ∈ K, 0 < M.D u κ δ}

/-- The paper's marginal-utility stochastic discount factor set M_(U,K). -/
def sdfSet (U : Set (ℝ → ℝ)) (K : Set (Fin N → ℝ)) :
    Set ((Fin N → ℝ) → ℝ) :=
  {m | ∃ u ∈ U, ∃ κ ∈ K, ∃ d : ℝ, 0 < d ∧
    m = fun x => d * deriv u (x ⬝ᵥ κ)}

/-- Present values E_F[m(x)x]. -/
noncomputable def Market.presentValue (M : Market N R)
    (m : (Fin N → ℝ) → ℝ) : Fin N → ℝ :=
  fun i => ∫ x, m x * x i ∂M.μ

/-- The paper's matrix representation of Δ*. -/
def Market.polarCone (M : Market N R) : Set (Fin N → ℝ) :=
  {q | ∃ σ : Fin R → ℝ, 0 ≤ σ ∧ q = M.Aᵀ *ᵥ σ ∧ M.aVec ⬝ᵥ σ ≤ 0}

end StochArbitrage.Pricing


