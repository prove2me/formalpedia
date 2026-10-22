-- Prove2me | Definitions.Def_StrategyproofMinimax_Tree_cost
-- name    : StrategyproofMinimax_Tree_cost
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-01T21:51:28.195994+00:00
-- url     : https://prove2.me/theorems/23cbe3df-fded-4f8c-a9f2-c1ee4fbc769b
-- title:
--   Facility-location model on a metric network: cost, maximum cost, strategyproofness, optimal maximum cost
-- statement:
--   Let $G$ be a metric space (a network with the shortest-path distance $d$) carrying a σ-algebra. A set $N=\{1,\dots,n\}$ of agents reports a **location profile** $x=(x_1,\dots,x_n)\in G^n$, and a **randomized mechanism** $f:G^n\to\Delta(G)$ returns a probability distribution over the location of a facility.
--
--   The **cost** of an agent at $a$ under a distribution $P$ is the expected distance to the facility, and the **maximum cost** of $P$ with respect to $x$ is the expected distance to the farthest agent:
--   $$\operatorname{cost}(P,a)=\mathbb{E}_{y\sim P}[d(a,y)],\qquad \operatorname{mc}(P,x)=\mathbb{E}_{y\sim P}\Big[\max_{i\in N} d(x_i,y)\Big].$$
--   The mechanism $f$ is **strategyproof** (SP) if for every $x\in G^n$, every $i\in N$ and every $x_i'\in G$,
--   $$\operatorname{cost}(f(x),x_i)\le\operatorname{cost}(f(x_i',x_{-i}),x_i),$$
--   where $(x_i',x_{-i})$ is $x$ with its $i$-th entry replaced by $x_i'$. The **optimal maximum cost** of $x$ is that of the best deterministic facility location, $\mathrm{OPT}(x)=\min_{z\in G}\operatorname{mc}(\delta_z,x)$, where $\delta_z$ is the point mass at $z$.
--
--   These are the objects of Section 2 of the paper; every statement of this mission is about them, on the tree $G(m,k)$.
--
--   **Formalization Note.** Distributions are `ProbabilityMeasure G`; $\delta_z$ is `diracPM z`. The number of agents $n$ is fixed, as in the paper's $N=\{1,\dots,n\}$, and agents are indexed by `Fin n`. $\mathrm{OPT}$ is `optMc x`, the infimum over all $z\in G$ (on the compact tree used in this mission it is attained). The integrals are Bochner integrals; on the tree $G(m,k)$ of this mission the integrands are bounded and continuous, hence integrable against every probability measure.
-- source:
--   Alon, Feldman, Procaccia, Tennenholtz, Strategyproof Approximation of the Minimax on Networks, Math. Oper. Res. 35(3) (2010), p. 515, Section 2

import Mathlib

namespace StrategyproofMinimax.Tree

open MeasureTheory

variable {G : Type*} [PseudoMetricSpace G] [MeasurableSpace G]

/-- Cost of an agent located at `a` when the facility is drawn from the distribution `P`
(p. 515): `cost(P, a) = 𝔼_{y∼P}[d(a, y)]`. A deterministic facility at `z` is `diracPM z`. -/
noncomputable def cost (P : ProbabilityMeasure G) (a : G) : ℝ :=
  ∫ y, dist a y ∂(P : Measure G)

/-- Maximum cost of a facility distribution `P` with respect to the location profile
`x = ⟨x₁, …, xₙ⟩` (p. 515): `mc(P, x) = 𝔼_{y∼P}[mc(y, x)]` with `mc(y, x) = max_{i ∈ N} d(xᵢ, y)`. -/
noncomputable def mc {n : ℕ} (P : ProbabilityMeasure G) (x : Fin n → G) : ℝ :=
  ∫ y, (⨆ i, dist (x i) y) ∂(P : Measure G)

/-- A randomized mechanism `f : Gⁿ → Δ(G)` for the fixed agent set `N = {1, …, n}` is
strategyproof (p. 515): for every profile `x`, every agent `i` and every deviation `x'`,
`cost(f(x'ᵢ, x₋ᵢ), xᵢ) ≥ cost(f(x), xᵢ)`. The profile `(x'ᵢ, x₋ᵢ)` is `Function.update x i x'`. -/
def IsStrategyproof {n : ℕ} (f : (Fin n → G) → ProbabilityMeasure G) : Prop :=
  ∀ (x : Fin n → G) (i : Fin n) (x' : G),
    cost (f x) (x i) ≤ cost (f (Function.update x i x')) (x i)

/-- The deterministic facility location `z`, as the Dirac probability measure at `z`. -/
noncomputable def diracPM (z : G) : ProbabilityMeasure G :=
  ⟨Measure.dirac z, inferInstance⟩

/-- The optimal maximum cost of a deterministic facility location for the profile `x`:
`OPT(x) = min_{z ∈ G} mc(z, x)`, written as an infimum over all points `z ∈ G`. -/
noncomputable def optMc {n : ℕ} (x : Fin n → G) : ℝ :=
  ⨅ z : G, mc (diracPM z) x

end StrategyproofMinimax.Tree


