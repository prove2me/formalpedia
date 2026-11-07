-- Prove2me | Definitions.Def_SparseHistComm_postList
-- name    : SparseHistComm_postList
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:39:29.890856+00:00
-- url     : https://prove2.me/theorems/2bfd7609-88a6-4b28-8105-f2b0424d8719
-- title:
--   Posterior list $I_i = \{a : P(X_i(a) = 1 \mid M_i, R) > \tau\}$
-- statement:
--   For a threshold $\tau$, the **posterior list** of user $i$ given $M_i = m$ and $R = r$ is
--   $$
--   I_i(m, r) = \{a : P(X_i(a) = 1 \mid M_i = m, R = r) > \tau\},
--   $$
--   the coordinates with sufficiently large local posterior probability. It is an analysis variable: neither the encoder nor the decoder computes it.
-- source:
--   Ye–Fan, Optimal Communication for Distributed Sparse Histogram Aggregation, arXiv:2611.04285 (held version, sha256 29df82a4…f27c6f), Eq. (16), p.8

import Mathlib
import Definitions.Def_SparseHistComm_post

namespace SparseHistComm

/-- The **posterior list** `Iᵢ = {a : P(Xᵢ(a) = 1 | Mᵢ, R) > τ}` of user `i` given its message
`Mᵢ = m` and `R = r` (Ye–Fan, *Optimal Communication for Distributed Sparse Histogram Aggregation*, arXiv:2611.04285 (held version, sha256 29df82a4…f27c6f), Eq. (16), p.8). -/
noncomputable def postList {n d : ℕ} (P : Protocol n d) (k : ℕ) (τ : ℝ) (i : Fin n) (r : P.Ω)
    (m : List Bool) : Finset (Fin d) :=
  (Finset.univ : Finset (Fin d)).filter (fun a => τ < post P k i r m a)

end SparseHistComm


