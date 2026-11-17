-- Prove2me | Definitions.Def_SparseHistComm_Supplement_Algorithm1Output
-- name    : SparseHistComm_Supplement_Algorithm1Output
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T02:41:10.152665+00:00
-- url     : https://prove2.me/theorems/92b298b2-1fed-4bc1-948b-696e64c89ad3
-- title:
--   Output mixture of Algorithm 1
-- statement:
--   An output of Algorithm 1 consists of two probability laws on the covering levels $\{0,\ldots,k\}$, a public probability for choosing the first law, and the resulting expected total covering level $\widehat\Lambda_{n,k,D}(\delta)$.
--
--   The two laws represent the at-most-two public randomizations returned from the lower convex hull in the small-threshold branch; the large-threshold branch uses the prescribed binomial law and the all-zero erasure law.
--
--   **Formalization Note** Ties on the lower convex hull are deliberately left unresolved, as in the pseudocode. The companion predicate `algorithm1Returns` identifies exactly which records may be returned.
-- source:
--   Ye–Fan, Optimal Communication for Distributed Sparse Histogram Aggregation, arXiv:2611.04285 (held version, sha256 29df82a4…f27c6f), Algorithm 1 and Theorem 6, p.11

import Mathlib

namespace SparseHistComm

namespace Supplement

/-- The public mixture returned by Algorithm 1 (Ye–Fan, *Optimal Communication for Distributed
Sparse Histogram Aggregation*, arXiv:2611.04285 (held version, sha256 29df82a4…f27c6f),
Algorithm 1 and Theorem 6, p.11): two laws on covering levels `{0,…,k}`, a public mixing weight,
and the returned expected total covering level `Λ̂_{n,k,D}(δ)`.

**Formalization Note** The paper leaves tie-breaking on the lower convex hull unspecified. An output
therefore records either minimizing pair and its weight; `algorithm1Returns` below specifies exactly
which outputs the printed procedure may return. -/
structure Algorithm1Output (k : ℕ) where
  weight : ℝ
  first : stdSimplex ℝ (Fin (k + 1))
  second : stdSimplex ℝ (Fin (k + 1))
  hatLambda : ℝ

end Supplement

end SparseHistComm


