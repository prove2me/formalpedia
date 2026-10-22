-- Prove2me | Definitions.Def_StrategyproofMinimax_Circle_cost
-- name    : StrategyproofMinimax_Circle_cost
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-01T20:36:45.841768+00:00
-- url     : https://prove2.me/theorems/28cd90d9-e4d0-471d-9750-1d78858b3c51
-- title:
--   Facility-location model on the circle: cost, maximum cost, strategyproofness, approximation
-- statement:
--   Let $G$ be the circle of circumference one, realised as $\mathbb{R}/\mathbb{Z}$, with the arc-length (shortest-path) distance $d(a,b)\in[0,1/2]$. A set $N=\{1,\dots,n\}$ of agents reports a **location profile** $x=(x_1,\dots,x_n)\in G^n$, and a randomized mechanism returns a probability distribution $P$ over $G$ for the location of a facility.
--
--   The **cost** of an agent at $a$ is the expected distance to the facility, and the **maximum cost** of $P$ with respect to $x$ is the expected distance to the farthest agent:
--   $$\operatorname{cost}(P,a)=\mathbb{E}_{y\sim P}\,[d(a,y)],\qquad \operatorname{mc}(P,x)=\mathbb{E}_{y\sim P}\Big[\max_{i\in N} d(x_i,y)\Big].$$
--   A mechanism $f$ (one map $G^n\to\Delta(G)$ for each number $n$ of agents) is **strategyproof** if no agent can lower its cost by misreporting: for every $x\in G^n$, every $i\in N$ and every $x_i'\in G$,
--   $$\operatorname{cost}(f(x),x_i)\le\operatorname{cost}(f(x_i',x_{-i}),x_i),$$
--   where $(x_i',x_{-i})$ is $x$ with the $i$-th entry replaced by $x_i'$. It is a **$\rho$-approximation mechanism for the minimax** if for every profile
--   $$\operatorname{mc}(f(x),x)\le\rho\cdot\min_{z\in G}\operatorname{mc}(\delta_z,x),$$
--   the minimum being the optimal maximum cost of a deterministic facility location.
--
--   These are the objects of Section 2 of the paper, specialised to the circle; every statement of this mission is about them.
--
--   **Formalization Note.** The circle is `AddCircle (1 : ℝ)`, whose `dist a b = ‖a - b‖` is the arc-length distance. Distributions are `Measure (AddCircle 1)`; the mechanisms of this mission (`lrm`, `rc`, `mech31`) are explicit finite combinations of Dirac masses whose weights sum to one. The minimum over $z$ is written `⨅ z`; the function is continuous, nonnegative and $G$ is compact, so it is attained. The approximation is multiplicative because the optimum can be $0$. For $n=0$ the maximum over the empty set is $0$ by convention, and both properties hold trivially there.
-- source:
--   Alon, Feldman, Procaccia, Tennenholtz, Strategyproof Approximation of the Minimax on Networks, Math. Oper. Res. 35(3) (2010), p. 515, Section 2 (cost, SP, mc) and p. 519, Appendix A (circumference one)

import Mathlib

namespace StrategyproofMinimax.Circle

open MeasureTheory

/-- The circle `G` of circumference one (Appendix A normalizes the circumference to one) is
`AddCircle (1 : ℝ)`. Its distance `dist a b = ‖a - b‖` is the arc-length (shortest-path)
distance `d(a, b) ∈ [0, 1/2]`.

Cost of agent location `a` under a facility distribution `P` (p. 515):
`cost(P, a) = 𝔼_{y∼P}[d(a, y)]`. A deterministic facility at `y` is the Dirac mass at `y`. -/
noncomputable def cost (P : Measure (AddCircle (1 : ℝ))) (a : AddCircle (1 : ℝ)) : ℝ :=
  ∫ y, dist a y ∂P

/-- Maximum cost of a facility distribution `P` with respect to the location profile
`x = ⟨x₁, …, xₙ⟩` (p. 515): `mc(P, x) = 𝔼_{y∼P}[mc(y, x)]`, where
`mc(y, x) = max_{i ∈ N} d(xᵢ, y)`. -/
noncomputable def mc {n : ℕ} (P : Measure (AddCircle (1 : ℝ))) (x : Fin n → AddCircle (1 : ℝ)) :
    ℝ :=
  ∫ y, (⨆ i, dist (x i) y) ∂P

/-- A randomized mechanism `f` (one map `Gⁿ → Δ(G)` for every number `n` of agents) is
strategyproof (p. 515): for every profile `x`, agent `i` and deviation `x'`,
`cost(f(x'ᵢ, x₋ᵢ), xᵢ) ≥ cost(f(x), xᵢ)`. The deviated profile `(x'ᵢ, x₋ᵢ)` is
`Function.update x i x'`. -/
def IsStrategyproof
    (f : ∀ n : ℕ, (Fin n → AddCircle (1 : ℝ)) → Measure (AddCircle (1 : ℝ))) : Prop :=
  ∀ (n : ℕ) (x : Fin n → AddCircle (1 : ℝ)) (i : Fin n) (x' : AddCircle (1 : ℝ)),
    cost (f n x) (x i) ≤ cost (f n (Function.update x i x')) (x i)

/-- `f` is a `ρ`-approximation mechanism for the minimax: for every profile `x`,
`mc(f(x), x) ≤ ρ · OPT(x)`, where `OPT(x) = min_{z ∈ G} mc(z, x)` is the optimal maximum cost
of a deterministic facility location. Written multiplicatively, since `OPT(x)` can be `0`. -/
def IsApproximation (ρ : ℝ)
    (f : ∀ n : ℕ, (Fin n → AddCircle (1 : ℝ)) → Measure (AddCircle (1 : ℝ))) : Prop :=
  ∀ (n : ℕ) (x : Fin n → AddCircle (1 : ℝ)),
    mc (f n x) x ≤ ρ * ⨅ z : AddCircle (1 : ℝ), mc (Measure.dirac z) x

end StrategyproofMinimax.Circle


