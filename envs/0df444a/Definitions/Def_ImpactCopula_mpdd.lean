-- Prove2me | Definitions.Def_ImpactCopula_mpdd
-- name    : ImpactCopula_mpdd
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:53:53.22646+00:00
-- url     : https://prove2.me/theorems/37ab36be-dfd7-4607-9b7c-c6b228c12fbc
-- title:
--   Modified partial Dini derivative $D_1C(u,v)$
-- statement:
--   The **modified partial Dini derivative** (MPDD) of a copula $C$ with respect to $u$ (Fang et al. 2020) is the function on $[0,1]\times\mathbb R$
--
--   $$
--   D_1C(u,v) = \begin{cases} \inf_{y>v} D_1^+C(u,y), & u \in [0,1),\ v \in [0,1),\\ \inf_{y>v} D_1^-C(1,y), & u = 1,\ v \in [0,1),\\ 0, & v < 0,\\ 1, & v \ge 1. \end{cases} \tag{A.30}
--   $$
--
--   For every copula it is a regular conditional distribution function of $C$ given $u$ (Remark 1), and it equals $\partial C/\partial u$ when $C$ has a density. It plays the role of $\mathbb P(V \le v \mid U = u)$.
--
--   **Formalization Note** Since $C$ lives on $[0,1]^2$, the infimum over $y > v$ is taken over $y \in (v, 1]$ (extending $C(u,y) = C(u,1)$ for $y > 1$ adds only values $1$, which do not change it). Values at $u \notin [0,1]$ are junk and unused.
-- source:
--   Lo–Wu–Zhang–Zhao, Optimal Impact Portfolios with General Dependence and Marginals, SSRN 4177277 (draft of February 25, 2024), Appendix A.3.1, Definition A.2, eq. (A.30), p.42 (PDF p.45)

import Mathlib
import Definitions.Def_ImpactCopula_diniRightUpper
import Definitions.Def_ImpactCopula_diniLeftUpper

namespace ImpactCopula

/-- The modified partial Dini derivative (MPDD) `D₁C` of a copula (Definition A.2, eq. (A.30)),
Lo–Wu–Zhang–Zhao, *Optimal Impact Portfolios with General Dependence and Marginals*, SSRN 4177277 (draft of February 25, 2024), p.42 (PDF p.45):
`D₁C(u, v) = inf_{y>v} D₁⁺C(u, y)` for `u ∈ [0, 1)`, `v ∈ [0, 1)`;
`inf_{y>v} D₁⁻C(1, y)` for `u = 1`, `v ∈ [0, 1)`; `0` for `v < 0`; `1` for `v ≥ 1`.

**Formalization Note.** The copula is defined on `[0, 1]²`, so `inf_{y>v}` ranges over
`y ∈ (v, 1]` (for the extension `C(u, y) = C(u, 1)`, `y > 1`, the values there are `1`, which
does not change the infimum). The paper defines `D₁C` on `[0, 1] × ℝ`; values at `u ∉ [0, 1]`
are junk (the `u < 1` branch also fires for `u < 0`, the other for `u > 1`) and no statement uses
them. -/
noncomputable def mpdd (C : ℝ → ℝ → ℝ) (u v : ℝ) : ℝ :=
  if v < 0 then 0
  else if 1 ≤ v then 1
  else if u < 1 then ⨅ y : Set.Ioc v 1, diniRightUpper C u y
  else ⨅ y : Set.Ioc v 1, diniLeftUpper C 1 y

end ImpactCopula


