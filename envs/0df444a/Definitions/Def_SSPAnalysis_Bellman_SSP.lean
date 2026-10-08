-- Prove2me | Definitions.Def_SSPAnalysis_Bellman_SSP
-- name    : SSPAnalysis_Bellman_SSP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T16:50:04.503616+00:00
-- url     : https://prove2.me/theorems/b07ac285-7422-4f6a-9d72-fb495d4c42f3
-- title:
--   Policy costs, properness, assumptions, X, weighted norm, and reachability
-- statement:
--   For a policy $\pi=(\mu_0,\mu_1,\ldots)$, multiply the transition matrices used before time $t$ and sum the expected stage costs through time $k$. The cost $x_i(\pi)$ is the limit inferior of these partial costs. The optimal cost is the infimum over every policy, and a policy is optimal when it attains that value at every state:
--
--   $$x_i(\pi)=\liminf_{k\to\infty}\sum_{t=0}^k [P(\mu_0)\cdots P(\mu_{t-1})c(\mu_t)]_i,\qquad x_i^*=\inf_\pi x_i(\pi).$$
--
--   A stationary selector is proper when the probability of being at state $1$ tends to one from each initial state. Assumption 1 makes state $1$ absorbing and cost-free, supplies a proper selector, and requires a partial-cost coordinate to tend to $+\infty$ under every improper selector. Assumption 2 makes control spaces compact metric spaces, costs lower semicontinuous, and transition probabilities continuous. Also defined are $X=\{x:x_1=0\}$, the positive-weight maximum norm, the matrix $E$ with first column one and all other entries zero, and positive-length probabilistic reachability.
--
--   These definitions preserve infinite improper-policy costs and give the exact setting of the target proposition.
--
--   **Formalization Note.** State $1$ is `0 : Fin n`. The empty transition product is the identity. Costs and optimal values are extended reals, so $+\infty$ and $-\infty$ are representable. The control set is its metric carrier, with compactness asserted on the whole carrier; no extra nonemptiness hypothesis is imposed because Assumption 1 supplies a selector.
-- source:
--   Bertsekas and Tsitsiklis, An Analysis of Stochastic Shortest Path Problems, Math. Oper. Res. 16(3) (1991), pp. 582–585, §2–§3, equations (2)–(4), Assumptions 1–2; p. 591, Appendix, reachability and E

import Mathlib
import Definitions.Def_SSPAnalysis_Bellman_Model

namespace SSPAnalysis.Bellman

open Matrix Filter Topology

namespace Model

variable {n : ℕ} {U : Fin n → Type*} (m : Model n U)

/-- The first `t` transition matrices of a policy, with empty product `1`. -/
def transProd (π : Policy U) : ℕ → Matrix (Fin n) (Fin n) ℝ
  | 0 => 1
  | t + 1 => transProd π t * m.P (π t)

/-- The partial cost through stage `k`, inclusive, in equation (2). -/
def partialCost (π : Policy U) (k : ℕ) : Fin n → ℝ :=
  ∑ t ∈ Finset.range (k + 1), m.transProd π t *ᵥ m.cvec (π t)

/-- Equation (2), the coordinatewise liminf of partial costs. -/
noncomputable def cost (π : Policy U) (i : Fin n) : EReal :=
  liminf (fun k : ℕ => ((m.partialCost π k i : ℝ) : EReal)) atTop

/-- Equation (3), infimum over all, including nonstationary, policies. -/
noncomputable def optCost (i : Fin n) : EReal :=
  ⨅ π : Policy U, m.cost π i

/-- Equation (4), optimality from every initial state. -/
def IsOptimal (π : Policy U) : Prop :=
  ∀ i, m.cost π i = m.optCost i

/-- Properness: eventual absorption at the paper's state 1. -/
def IsProper [NeZero n] (μ : Selector U) : Prop :=
  ∀ i, Tendsto (fun t : ℕ => (m.P μ ^ t) i 0) atTop (𝓝 1)

/-- Assumption 1, including the infinity of a coordinate's stationary
partial-cost sequence under every improper selector. -/
structure Assumption1 [NeZero n] : Prop where
  absorbing : ∀ u : U 0, m.p 0 u 0 = 1
  cost_free : ∀ u : U 0, m.c 0 u = 0
  exists_proper : ∃ μ : Selector U, m.IsProper μ
  improper_infinite : ∀ μ : Selector U, ¬ m.IsProper μ → ∃ i,
    Tendsto (fun k : ℕ => (∑ t ∈ Finset.range (k + 1),
      m.P μ ^ t *ᵥ m.cvec μ) i) atTop atTop

/-- Assumption 2: each control space is a compact metric space, costs are
lower semicontinuous, and transition coordinates are continuous. -/
structure Assumption2 [∀ i, MetricSpace (U i)] : Prop where
  compact : ∀ i, IsCompact (Set.univ : Set (U i))
  lsc : ∀ i, LowerSemicontinuous (m.c i)
  cont : ∀ i j, Continuous fun u : U i => m.p i u j

end Model

/-- The subspace with zero cost at the absorbing state. -/
def X (n : ℕ) [NeZero n] : Set (Fin n → ℝ) :=
  {x | x 0 = 0}

/-- The weighted maximum norm used in Proposition 1. -/
noncomputable def wNorm {n : ℕ} [NeZero n] (w x : Fin n → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun i => |x i| / w i

/-- The matrix whose first column is all ones and whose other entries vanish. -/
def E {n : ℕ} [NeZero n] : Matrix (Fin n) (Fin n) ℝ :=
  fun _ j => if j = 0 then 1 else 0

/-- Reachability by a positive-length path of positive probability. -/
def Reaches {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) : Prop :=
  ∃ t : ℕ, 0 < t ∧ 0 < (P ^ t) i j

end SSPAnalysis.Bellman


