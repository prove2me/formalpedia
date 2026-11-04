-- Prove2me | Definitions.Def_ImpactCopula_condInv
-- name    : ImpactCopula_condInv
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:54:49.517236+00:00
-- url     : https://prove2.me/theorems/26198eb9-bab7-4a95-974d-3d5f7aaf9c69
-- title:
--   The inverse $g_u(w)$ of $v \mapsto D_1C(u,v)$
-- statement:
--   For a copula $C$ and $u \in [0,1]$, let $g_u$ be the inverse function (Definition A.1) of the conditional distribution function $v \mapsto D_1C(u,v)$:
--
--   $$
--   g_u(w) = \inf\{v \in \mathbb R : D_1C(u,v) \ge w\} .
--   $$
--
--   This is the inverse Rosenblatt transform: if $V$ is uniform on $(0,1)$, then $g_u(V)$ has distribution function $D_1C(u,\cdot)$.
--
--   **Formalization Note** The infimum is a real `sInf`. For $w \in (0,1]$ it is the paper's value (the set contains $[1,\infty)$ and lies in $[0,\infty)$); for $w \le 0$ the paper's value is $-\infty$ and Lean's is $0$, which happens only on a null set and changes no law.
-- source:
--   Lo–Wu–Zhang–Zhao, Optimal Impact Portfolios with General Dependence and Marginals, SSRN 4177277 (draft of February 25, 2024), Theorem 2, eq. (15), p.12 (PDF p.15); Definition A.1, p.42 (PDF p.45)

import Mathlib
import Definitions.Def_ImpactCopula_mpdd

namespace ImpactCopula

/-- `g_u(w)`, the inverse function (Definition A.1, p.42, PDF p.45) of `v ↦ D₁C(u, v)`, as used in
Theorem 2, eq. (15), Lo–Wu–Zhang–Zhao, *Optimal Impact Portfolios with General Dependence and Marginals*, SSRN 4177277 (draft of February 25, 2024), p.12 (PDF p.15): `g_u(w) = inf {v : D₁C(u, v) ≥ w}`.

**Formalization Note.** Real-valued `sInf`: for `w ∈ (0, 1]` the set is nonempty (it contains
`[1, ∞)`) and bounded below by `0`, so the value is the paper's. For `w ≤ 0` the paper's value is
`−∞` and Lean's is `0`; this happens on a null set of `(u, w)` only and changes no law. -/
noncomputable def condInv (C : ℝ → ℝ → ℝ) (u w : ℝ) : ℝ :=
  sInf {v : ℝ | w ≤ mpdd C u v}

end ImpactCopula


