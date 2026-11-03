-- Prove2me | Definitions.Def_PLIAG_Phi
-- name    : PLIAG_Phi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:26:30.931367+00:00
-- url     : https://prove2.me/theorems/e417ee05-524f-499d-922a-3d68c4852cde
-- title:
--   Objective $\Phi=\sum_n f_n+h$ of problem (1.1)
-- statement:
--   The objective of problem (1.1) is
--
--   $$
--   \Phi(x):=F(x)+h(x),\qquad F(x):=\sum_{n=1}^{N}f_n(x),
--   $$
--
--   where the component functions $f_n$ and the regularizer $h$ take values in $(-\infty,+\infty]$.
--
--   **Formalization Note** Components are indexed by `Fin N`. All functions take values in `EReal`; under the paper's assumptions (each $f_n$ and $h$ proper) no summand is $-\infty$, so the `EReal` sum is the usual extended sum.
-- source:
--   Zhang, Dai, Guo, Peng, Proximal-Like Incremental Aggregated Gradient Method with Linear Convergence under Bregman Distance Growth Conditions, arXiv:1711.01136v3, (1.1), pp.1–2, and assumption B1, p.7

import Mathlib

namespace PLIAG

/-- **Objective of problem (1.1)** (Zhang–Dai–Guo–Peng, arXiv:1711.01136v3, (1.1), pp.1–2):
`Φ(x) := F(x) + h(x)` with `F(x) := Σ_{n=1}^N f_n(x)`.

**Formalization Note.** Components are indexed by `Fin N`. The `f_n` and `h` take values in
`EReal` (assumption B1, p.7, makes each `f_n` proper lsc convex with possibly infinite values).
Under the paper's assumptions no summand is `−∞`, so the `EReal` sum is the extended sum. -/
noncomputable def Phi {d N : ℕ} (f : Fin N → EuclideanSpace ℝ (Fin d) → EReal)
    (h : EuclideanSpace ℝ (Fin d) → EReal) (x : EuclideanSpace ℝ (Fin d)) : EReal :=
  (∑ n, f n x) + h x

end PLIAG


