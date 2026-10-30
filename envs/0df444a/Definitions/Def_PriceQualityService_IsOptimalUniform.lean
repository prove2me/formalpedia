-- Prove2me | Definitions.Def_PriceQualityService_IsOptimalUniform
-- name    : PriceQualityService_IsOptimalUniform
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:38:40.099379+00:00
-- url     : https://prove2.me/theorems/d2d13c72-e94d-4576-9477-ecf3e284f048
-- title:
--   Optimal solution of the uniform-duration problem (7)
-- statement:
--   The products are $\mathcal N=\{1,\dots,N\}$. Product $i$ has quality sensitivity $\alpha_i$, service utility per unit time $s_i$, production-cost coefficient $c_i$ and service-cost coefficients $a_i,b_i$; the firm chooses its price $p_i$, quality $q_i$ and service duration $t_i$.
--
--   Problem (7) is the general model with the constraint that every product carries the same service duration $t\in[t_s,t_l]$:
--
--   $$
--   \max_{\mathbf p,\mathbf q,t}\ \Pi(\mathbf p,\mathbf q,(t,\dots,t);\mathcal N).
--   $$
--
--   Given a feasible quality set $Q$, a triple $(\mathbf p,\mathbf q,t)$ is an **optimal solution of (7)** if $\mathbf q\in Q$, $t\in[t_s,t_l]$, and
--
--   $$
--   \Pi(\mathbf p',\mathbf q',(t',\dots,t');\mathcal N)\le\Pi(\mathbf p,\mathbf q,(t,\dots,t);\mathcal N)\quad\text{for all }\mathbf p'\in\mathbb R^N,\ \mathbf q'\in Q,\ t'\in[t_s,t_l].
--   $$
--
--   This is the object Theorem 3 is about.
--
--   **Formalization Note** Optimality is "at least the profit of every feasible point" rather than equality with a supremum, so no default value of a supremum enters. Prices are unconstrained reals, as in the paper; the paper's quality set is the quality domain of pp. 8–9.
-- source:
--   Wang, Ke & Cui, Product Price, Quality and Service Decisions under Consumer Choice Models, accepted manuscript, SSRN 3766191 (MSOM 2020, doi:10.1287/msom.2020.0947), p. 15, eq. (7); profit (3), p. 9; durations [t_s, t_l], p. 7

import Mathlib
import Definitions.Def_PriceQualityService_profit

namespace PriceQualityService

/-- **Optimal solution of the uniform-duration problem (7).**
Wang, Ke & Cui, *Product Price, Quality and Service Decisions under Consumer Choice Models*,
accepted manuscript, SSRN 3766191 (MSOM 2020, doi:10.1287/msom.2020.0947), eq. (7), p. 15: "`max_{p,q,t} Π(p, q, t; 𝒩)`", the general model with the constraint
`t_i = t ∈ [t_s, t_l]` for every product `i`.

`IsOptimalUniform α s a b c Q ts tl p q t` says that `q ∈ Q`, `t ∈ [ts, tl]`, and the profit at
`(p, q, t, …, t)` is at least the profit at every `(p', q', t', …, t')` with `p' ∈ ℝ^N`,
`q' ∈ Q` and `t' ∈ [ts, tl]`.

**Formalization Note.** Optimality is "≥ the profit of every feasible point", not equality with
a supremum, so no junk value of `sSup` enters. Prices are unconstrained reals, as in the paper.
The quality set `Q` is a parameter; the paper's domain is `qualityDomain a b`. -/
def IsOptimalUniform {N : ℕ} (α s a b c : Fin N → ℝ) (Q : Set (Fin N → ℝ)) (ts tl : ℝ)
    (p q : Fin N → ℝ) (t : ℝ) : Prop :=
  q ∈ Q ∧ t ∈ Set.Icc ts tl ∧
    ∀ (p' q' : Fin N → ℝ) (t' : ℝ), q' ∈ Q → t' ∈ Set.Icc ts tl →
      profit α s a b c p' q' (fun _ => t') ≤ profit α s a b c p q (fun _ => t)

end PriceQualityService


