-- Prove2me | Definitions.Def_BellmanIneq_Regret_BellmanInequalities
-- name    : BellmanIneq_Regret_BellmanInequalities
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T17:30:46.617712+00:00
-- url     : https://prove2.me/theorems/803ab494-81b8-4114-aa58-6edcac6e874c
-- title:
--   Bellman inequalities, maximum loss, and satisfying actions
-- statement:
--   For Offline's value $V$, a relaxed value $\phi(t,s)$ and Bellman loss $L_B(t,s)$ satisfy the **Bellman inequalities** when both are measurable with respect to $\mathcal G_t$, $\phi(0,s)=0$, the initial value satisfies $\mathbb E[V(T,s_0)\mid\mathcal G_T]\le\phi(T,s_0)$ almost surely, and for every decision period and state there is a feasible action $u$ such that
--
--   $$\phi(t,s)\le R(s,\xi^t,u)+\mathbb E[\phi(t-1,\mathcal T(s,\xi^t,u))\mid\mathcal G_t]+L_B(t,s).$$
--
--   An action is **satisfying** at a particular sample path when it meets this inequality. A real number $r$ is a **maximum-loss bound** when, for every time, state, and feasible action, the shortfall $\phi(t,s)-(R+\mathbb E[\phi(t-1,\mathcal T)\mid\mathcal G_t])$ is at most $r$ almost surely.
--
--   These predicates express the paper's Definitions 2, 4, and 5 using the same conditional continuation.
--
--   **Formalization Note** The maximum in Definition 2 is represented by a feasible-action witness; Definition 4 is represented by any almost-sure real upper bound. The relaxation and loss are pointwise bounded over the finite horizon so all conditional expectations are genuine. No nonnegativity condition is imposed on $L_B$ here.
-- source:
--   Vera, Banerjee, Gurvich, Online Allocation and Pricing: Constant Regret via Bellman Inequalities, arXiv:1906.06361v2, pp. 10–11, Definitions 2, 4, 5, equations (3)–(4)

import Definitions.Def_BellmanIneq_Regret_Problem

set_option autoImplicit false

namespace BellmanIneq.Regret

open MeasureTheory

/-- Vera, Banerjee, Gurvich, *Online Allocation and Pricing: Constant Regret via Bellman
Inequalities*, arXiv:1906.06361v2, p. 10, Definition 2.
Formalization Note: the relaxation and loss have pointwise finite bounds to prevent
junk conditional expectations. The maximum in (3) is a feasible-action witness.
The initial ordering keeps the paper's conditional expectation. -/
def BellmanInequalities {Ω S Ξ U : Type*} [mΩ : MeasurableSpace Ω] [mΞ : MeasurableSpace Ξ]
    (μ : Measure Ω) (P : Problem S Ξ U) (ξ : ℕ → Ω → Ξ) (T : ℕ)
    (Gextra : MeasurableSpace Ω) (K : ℝ) (ϕ LB : ℕ → S → Ω → ℝ)
    (s₀ : S) : Prop :=
  (∀ t ∈ Finset.Icc 0 T, ∀ s, StronglyMeasurable[augmented ξ T Gextra t] (ϕ t s)) ∧
  (∀ t ∈ Finset.Icc 0 T, ∀ s, StronglyMeasurable[augmented ξ T Gextra t] (LB t s)) ∧
  (∀ t ∈ Finset.Icc 0 T, ∀ s ω, |ϕ t s ω| ≤ K ∧ |LB t s ω| ≤ K) ∧
  (μ[@offlineValue Ω S Ξ U mΩ mΞ μ P ξ T Gextra T s₀ | augmented ξ T Gextra T] ≤ᵐ[μ] ϕ T s₀) ∧
  (∀ t ∈ Finset.Icc 1 T, ∀ s,
    ∀ᵐ ω ∂μ, ∃ u ∈ P.Feas s (ξ t ω),
      ϕ t s ω ≤ P.R s (ξ t ω) u + @cont Ω S Ξ U mΩ mΞ μ P ξ T Gextra ϕ t s u ω + LB t s ω) ∧
  (∀ s ω, ϕ 0 s ω = 0)

/-- Vera, Banerjee, Gurvich, *Online Allocation and Pricing: Constant Regret via Bellman Inequalities*, arXiv:1906.06361v2, p. 11, Definition 4.
Every feasible action's Bellman shortfall is at most `r` almost surely.
Formalization Note: `r` is a real upper bound for the printed maximum, avoiding
an ill-defined supremum over state, time and sample paths. -/
def MaxLossBound {Ω S Ξ U : Type*} [mΩ : MeasurableSpace Ω] [mΞ : MeasurableSpace Ξ]
    (μ : Measure Ω) (P : Problem S Ξ U) (ξ : ℕ → Ω → Ξ) (T : ℕ)
    (Gextra : MeasurableSpace Ω) (ϕ : ℕ → S → Ω → ℝ) (r : ℝ) : Prop :=
  ∀ t ∈ Finset.Icc 1 T, ∀ s u,
    ∀ᵐ ω ∂μ, u ∈ P.Feas s (ξ t ω) →
      ϕ t s ω - (P.R s (ξ t ω) u + @cont Ω S Ξ U mΩ mΞ μ P ξ T Gextra ϕ t s u ω) ≤ r

/-- Vera, Banerjee, Gurvich, *Online Allocation and Pricing: Constant Regret via Bellman Inequalities*, arXiv:1906.06361v2, p. 11, Definition 5,
equation (4). Whether an action meets the relaxed Bellman inequality on this path.
Formalization Note: this predicate uses the same `LB` as Definition 2 and the goal. -/
def Satisfying {Ω S Ξ U : Type*} [mΩ : MeasurableSpace Ω] [mΞ : MeasurableSpace Ξ]
    (μ : Measure Ω) (P : Problem S Ξ U) (ξ : ℕ → Ω → Ξ) (T : ℕ)
    (Gextra : MeasurableSpace Ω) (ϕ LB : ℕ → S → Ω → ℝ)
    (t : ℕ) (s : S) (u : U) (ω : Ω) : Prop :=
  ϕ t s ω ≤ P.R s (ξ t ω) u + @cont Ω S Ξ U mΩ mΞ μ P ξ T Gextra ϕ t s u ω + LB t s ω

end BellmanIneq.Regret


