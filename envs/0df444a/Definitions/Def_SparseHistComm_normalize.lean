-- Prove2me | Definitions.Def_SparseHistComm_normalize
-- name    : SparseHistComm_normalize
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:37:30.475561+00:00
-- url     : https://prove2.me/theorems/16bb0979-95b2-4326-899d-65853905ec01
-- title:
--   Normalized decoder output $N(v)$
-- statement:
--   The **normalized output** of a decoder output $v \in \mathbb R^d$ is obtained by clipping each coordinate to $[0,1]$ and, if the clipped output has $\ell_1$ norm greater than $k + D$, replacing it by zero:
--   $$
--   N(v) = \begin{cases} 0 & \text{if } \|\mathrm{clip}(v)\|_1 > k + D,\\ \mathrm{clip}(v) & \text{otherwise.}\end{cases}
--   $$
--   Replacing a decoder by $N \circ \hat u$ changes no message, hence not the cost.
-- source:
--   Ye–Fan, Optimal Communication for Distributed Sparse Histogram Aggregation, arXiv:2611.04285 (held version, sha256 29df82a4…f27c6f), proof of Lemma 2, Appendix B-A, p.14

import Mathlib
import Definitions.Def_SparseHistComm_clip

namespace SparseHistComm

/-- The **normalized decoder output** (Ye–Fan, *Optimal Communication for Distributed Sparse Histogram Aggregation*, arXiv:2611.04285 (held version, sha256 29df82a4…f27c6f), proof of Lemma 2, p.14): clip each coordinate to
`[0, 1]`; "if the clipped output has ℓ1 norm greater than k + D, replace it by zero". -/
noncomputable def normalize {d : ℕ} (k : ℕ) (D : ℝ) (v : Fin d → ℝ) : Fin d → ℝ :=
  if (k : ℝ) + D < ∑ a, |clip v a| then 0 else clip v

end SparseHistComm


