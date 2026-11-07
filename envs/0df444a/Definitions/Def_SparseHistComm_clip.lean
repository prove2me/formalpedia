-- Prove2me | Definitions.Def_SparseHistComm_clip
-- name    : SparseHistComm_clip
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:36:51.511213+00:00
-- url     : https://prove2.me/theorems/ae82fb0d-c731-4acb-846f-cf5f4b0728f9
-- title:
--   Coordinatewise clipping to $[0,1]$
-- statement:
--   **Clipping** replaces each coordinate of a decoder output $v \in \mathbb R^d$ by its nearest point in $[0,1]$: $\mathrm{clip}(v)(a) = \max\{0, \min\{1, v(a)\}\}$.
-- source:
--   Ye–Fan, Optimal Communication for Distributed Sparse Histogram Aggregation, arXiv:2611.04285 (held version, sha256 29df82a4…f27c6f), proof of Lemma 2, Appendix B-A, p.14

import Mathlib

namespace SparseHistComm

/-- Coordinatewise clipping of a decoder output to `[0, 1]` (Ye–Fan, *Optimal Communication for Distributed Sparse Histogram Aggregation*, arXiv:2611.04285 (held version, sha256 29df82a4…f27c6f), proof of Lemma 2, p.14: "Clip
each output coordinate to [0, 1]"). -/
noncomputable def clip {d : ℕ} (v : Fin d → ℝ) : Fin d → ℝ :=
  fun a => max 0 (min 1 (v a))

end SparseHistComm


