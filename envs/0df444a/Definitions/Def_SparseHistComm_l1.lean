-- Prove2me | Definitions.Def_SparseHistComm_l1
-- name    : SparseHistComm_l1
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:36:49.274193+00:00
-- url     : https://prove2.me/theorems/17419151-7d64-4d7f-823e-3fd5c6d4a9b5
-- title:
--   $\ell_1$ distance $\|v - w\|_1$
-- statement:
--   For $v, w \in \mathbb R^d$, the **$\ell_1$ distance** is
--   $$
--   \|v - w\|_1 = \sum_{a=1}^d |v(a) - w(a)| .
--   $$
--   Accuracy of an estimate $\hat u$ of the histogram $u$ is measured by $\|\hat u - u\|_1$.
-- source:
--   Ye–Fan, Optimal Communication for Distributed Sparse Histogram Aggregation, arXiv:2611.04285 (held version, sha256 29df82a4…f27c6f), Definition 1, p.2, and throughout

import Mathlib

namespace SparseHistComm

/-- The `ℓ₁` distance `‖v − w‖₁ = ∑ₐ |v(a) − w(a)|` on `ℝ^d` (Ye–Fan, *Optimal Communication for Distributed Sparse Histogram Aggregation*, arXiv:2611.04285 (held version, sha256 29df82a4…f27c6f), Definition 1, p.2, and
throughout). -/
noncomputable def l1 {d : ℕ} (v w : Fin d → ℝ) : ℝ :=
  ∑ a, |v a - w a|

end SparseHistComm


