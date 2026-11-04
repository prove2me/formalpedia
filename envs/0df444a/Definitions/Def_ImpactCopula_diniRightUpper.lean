-- Prove2me | Definitions.Def_ImpactCopula_diniRightUpper
-- name    : ImpactCopula_diniRightUpper
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:53:03.526802+00:00
-- url     : https://prove2.me/theorems/d9952f98-4716-4f22-adc2-75ea27eae16f
-- title:
--   Partial right upper Dini derivative $D_1^+C(u,v)$
-- statement:
--   For a copula $C$, the **partial right upper Dini derivative** with respect to $u$ is
--
--   $$
--   D_1^+C(u,v) = \limsup_{h \to 0^+} \frac{C(u+h, v) - C(u, v)}{h} .
--   $$
--
--   It replaces $\partial C/\partial u$ when $C$ is not differentiable.
--
--   **Formalization Note** The limsup is the real `Filter.limsup` along $h \to 0^+$. For a copula, $u \in [0,1)$ and $v \in [0,1]$ the quotients lie in $[0,1]$ for $0 < h \le 1-u$, so it is the true limsup.
-- source:
--   Lo–Wu–Zhang–Zhao, Optimal Impact Portfolios with General Dependence and Marginals, SSRN 4177277 (draft of February 25, 2024), Appendix A.3.1, eq. (A.31), p.42 (PDF p.45)

import Mathlib

namespace ImpactCopula

/-- The partial right upper Dini derivative of `C` with respect to `u` (eq. (A.31)), Lo–Wu–Zhang–Zhao, *Optimal Impact Portfolios with General Dependence and Marginals*, SSRN 4177277 (draft of February 25, 2024),
p.42 (PDF p.45): `D₁⁺C(u, v) = limsup_{h→0+} (C(u + h, v) − C(u, v))/h`.

**Formalization Note.** The `limsup` is `Filter.limsup` in `ℝ` along `h → 0+`. For a copula and
`u ∈ [0, 1)`, `v ∈ [0, 1]` the difference quotients lie in `[0, 1]` once `0 < h ≤ 1 − u`, so the
real `limsup` is the true one. -/
noncomputable def diniRightUpper (C : ℝ → ℝ → ℝ) (u v : ℝ) : ℝ :=
  Filter.limsup (fun h : ℝ => (C (u + h) v - C u v) / h) (nhdsWithin 0 (Set.Ioi 0))

end ImpactCopula


