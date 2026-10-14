-- Prove2me | Definitions.Def_RefMNLPricing_GainSeeking_Model
-- name    : RefMNLPricing_GainSeeking_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T08:32:08.120441+00:00
-- url     : https://prove2.me/theorems/23b7dc89-5382-4ef2-81a9-201fe296765a
-- title:
--   Definition 2, p. 8; (5)–(6), p. 9; Definition 4, p. 19 — types of reference effects, optimal value V⋆, optimal steady states
-- statement:
--   This file adds to the multi-product pricing model of Guo, Jiang and Shen (the revenue $\Pi$ and price box $\mathcal P^n=[0,p_H]^n$ of `RefMNLPricing.Myopic.Model`, the reference path and discounted revenue of `RefMNLPricing.Gap.Model`) the classification of reference effects, the optimal value function, and optimal steady states.
--
--   The products are $i\in N=\{1,\dots,n\}$, with price sensitivity $b_i$ and reference-price sensitivities $c_i^+$ (to gains) and $c_i^-$ (to losses).
--
--   1. **Types of reference effects** (Definition 2). Product $i$ is **loss-averse** if $c_i^+<c_i^-$, **loss-neutral** if $c_i^+=c_i^-$ and **gain-seeking** if $c_i^+>c_i^-$. The sets of such products are $N_l$, $N_n$ and $N_g$.
--   2. **Optimal value** ((5)–(6)). For a memory parameter $\alpha$ and a discount factor $\beta$,
--   $$V^\star(\mathbf r^0)=\sup_{(\mathbf p^t)_{t\ge0}\subseteq\mathcal P^n}\ \sum_{t=0}^\infty \beta^t\,\Pi(\mathbf p^t,\mathbf r^t),\qquad \mathbf r^{t+1}=\alpha\mathbf r^t+(1-\alpha)\mathbf p^t,$$
--   the supremum over all admissible price sequences.
--   3. **Optimal steady state** (Definition 4). A vector $\mathbf x\in\mathcal P^n$ is an optimal steady state when the constant price path $\mathbf p^t=\mathbf x$, started from reference price $\mathbf r^0=\mathbf x$, is optimal from $\mathbf x$. Along that path $\mathbf r^t=\mathbf x$ for every $t$, so it earns $\Pi(\mathbf x,\mathbf x)/(1-\beta)$, and the condition reads
--   $$V^\star(\mathbf x)\le\frac{\Pi(\mathbf x,\mathbf x)}{1-\beta}.$$
--
--   These objects carry the results of §4.2 on the long-run behaviour of the optimal policy: no optimal steady state when a product is gain-seeking (Theorem 4), the structure of optimal steady states without gain-seeking products (Theorem 5, Corollaries 3–4), existence when consumers are insensitive to promotions (Theorem 6), and the comparison with single-price policies (Theorem 7).
--
--   **Formalization Note** Products are indexed by `Fin n`, so the paper's product $i$ is index $i-1$. $V^\star$ is the supremum over all admissible price sequences rather than the maximum over stationary policies printed in (5); for this deterministic problem with continuous $\Pi$ on a compact box both give the value that satisfies the Bellman equation (6). It equals `RefMNLPricing.Gap.optValue`. The supremum is Lean's real `⨆`, which would be $0$ on an unbounded or empty family; every theorem assumes $0\le\beta<1$ and $p_H>0$, under which the family is nonempty and bounded. Definition 4 speaks of a fixed point of "the" optimal policy; optimal policies need not be unique, so the sequence form above is used: under (6) it holds exactly when some optimal stationary policy fixes $\mathbf x$. The standing assumptions $b>0$, $c^\pm\ge0$, $\alpha\in[0,1]$, $\beta\in[0,1)$, $p_H>0$ are hypotheses of the theorems, not built into the definitions.
-- source:
--   Guo, Jiang, Shen, Multi-Product Dynamic Pricing with Reference Effects Under Logit Demand, SSRN 4189049 (version of 2024-05-25), p. 8, Definition 2; p. 9, (5)–(6); p. 19, Definition 4

import Mathlib
import Definitions.Def_RefMNLPricing_Gap_Model
import Definitions.Def_RefMNLPricing_Myopic_Model

namespace RefMNLPricing.GainSeeking

/-! Model of Guo, Jiang, Shen, *Multi-Product Dynamic Pricing with Reference Effects Under Logit
Demand* (SSRN 4189049, version of 2024-05-25), §2, pp. 7–11.

Products are indexed by `Fin n` (the paper's product `i` is index `i - 1`). The parameters are
`a b cp cm : Fin n → ℝ` for the intrinsic utilities `a`, the price sensitivities `b`, and the
reference-price sensitivities `c⁺` (`cp`, gains) and `c⁻` (`cm`, losses). The paper's standing
assumptions `b > 0`, `c⁺, c⁻ ≥ 0`, `α ∈ [0, 1]`, `β ∈ [0, 1)`, `p_H > 0` are hypotheses of the
theorems, not part of these definitions. -/

variable {n : ℕ}

/-- Product `i` is loss-averse, `c_i⁺ < c_i⁻` (Definition 2, p. 8). -/
def IsLossAverse (cp cm : Fin n → ℝ) (i : Fin n) : Prop := cp i < cm i

/-- Product `i` is loss-neutral, `c_i⁺ = c_i⁻` (Definition 2, p. 8). -/
def IsLossNeutral (cp cm : Fin n → ℝ) (i : Fin n) : Prop := cp i = cm i

/-- Product `i` is gain-seeking, `c_i⁺ > c_i⁻` (Definition 2, p. 8); `N_g` is the set of these. -/
def IsGainSeeking (cp cm : Fin n → ℝ) (i : Fin n) : Prop := cm i < cp i

/-- The optimal value function `V⋆(r₀)` of (5)–(6), p. 9, taken as the supremum of the discounted
revenue over all admissible price sequences `p^t ∈ Pⁿ = [0, p_H]ⁿ`. -/
noncomputable def optValue (a b cp cm : Fin n → ℝ) (α β pH : ℝ) (r₀ : Fin n → ℝ) : ℝ :=
  ⨆ p : ℕ → Fin n → Set.Icc (0 : ℝ) pH, RefMNLPricing.Gap.disc a b cp cm α β (fun t i => (p t i : ℝ)) r₀

/-- An optimal steady state (Definition 4, p. 19), in sequence form: `x ∈ Pⁿ` and the constant
price path `p^t = x`, started from reference `x` (so `r^t = x` for all `t`), is optimal from `x`,
i.e. `V⋆(x) ≤ Π(x, x)/(1 − β)`. -/
def IsOptSteadyState (a b cp cm : Fin n → ℝ) (α β pH : ℝ) (x : Fin n → ℝ) : Prop :=
  RefMNLPricing.Myopic.InBox pH x ∧ optValue a b cp cm α β pH x ≤ RefMNLPricing.Myopic.revenue a b cp cm x x / (1 - β)

end RefMNLPricing.GainSeeking


