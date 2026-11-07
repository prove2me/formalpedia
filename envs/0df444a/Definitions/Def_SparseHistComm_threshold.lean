-- Prove2me | Definitions.Def_SparseHistComm_threshold
-- name    : SparseHistComm_threshold
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:36:48.511287+00:00
-- url     : https://prove2.me/theorems/4dbc9ba2-d174-4290-8bdb-8d73e6e26b54
-- title:
--   Required total level $t = nk - \lfloor nD \rfloor$
-- statement:
--   The **required total covering level** is the integer
--   $$
--   t = nk - \lfloor nD \rfloor ,
--   $$
--   where $\lfloor nD\rfloor$ is the floor of the real number $nD$ (not $n\lfloor D\rfloor$). An estimate that recovers at least $t$ active coordinates in total, counted over users, has distortion at most $D$.
-- source:
--   Ye–Fan, Optimal Communication for Distributed Sparse Histogram Aggregation, arXiv:2611.04285 (held version, sha256 29df82a4…f27c6f), Eq. (9), p.6; (12), p.7; (17), p.8

import Mathlib

namespace SparseHistComm

/-- The required total covering level `t = nk − ⌊nD⌋` (Ye–Fan, *Optimal Communication for Distributed Sparse Histogram Aggregation*, arXiv:2611.04285 (held version, sha256 29df82a4…f27c6f), Eq. (9), p.6, and (12), (16), (17)).

**Formalization Note** An integer; `⌊nD⌋` is `Int.floor` of the real number `n·D` (not `n⌊D⌋`). -/
noncomputable def threshold (n k : ℕ) (D : ℝ) : ℤ :=
  (n : ℤ) * k - ⌊(n : ℝ) * D⌋

end SparseHistComm


