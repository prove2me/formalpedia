-- Prove2me | Definitions.Def_SparseHistComm_msgMass
-- name    : SparseHistComm_msgMass
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:37:23.6262+00:00
-- url     : https://prove2.me/theorems/8f05503a-0ed9-4b14-b01a-dd69450fa1b8
-- title:
--   Prior message probability $P(M_i = m \mid R = r)$
-- statement:
--   Under the uniform prior on $k$-subsets, the probability that user $i$ sends the string $m$ when $R = r$ is
--   $$
--   P(M_i = m \mid R = r) = \sum_{|x| = k} \pi(x)\, Q_{i,r}(m \mid x).
--   $$
--   A message has **conditional probability zero** when this vanishes.
-- source:
--   Ye–Fan, Optimal Communication for Distributed Sparse Histogram Aggregation, arXiv:2611.04285 (held version, sha256 29df82a4…f27c6f), Section IV, p.8; proof of Lemma 2, p.15

import Mathlib
import Definitions.Def_SparseHistComm_Protocol
import Definitions.Def_SparseHistComm_prior
open scoped ENNReal

namespace SparseHistComm

/-- The prior probability `P(Mᵢ = m | R = r) = ∑_{x, |x| = k} π(x) Q_{i,r}(m | x)` that user `i`
sends `m` when `R = r` and its input `Xᵢ` is drawn from the uniform prior on exactly-`k` supports
(Ye–Fan, *Optimal Communication for Distributed Sparse Histogram Aggregation*, arXiv:2611.04285 (held version, sha256 29df82a4…f27c6f), Section IV, p.8, and proof of Lemma 2, p.15: "messages of conditional probability
zero"). -/
noncomputable def msgMass {n d : ℕ} (P : Protocol n d) (k : ℕ) (i : Fin n) (r : P.Ω)
    (m : List Bool) : ℝ :=
  ∑ x ∈ (Finset.univ : Finset (Fin d)).powersetCard k, (prior d k).toReal * (P.enc i r x m).toReal

end SparseHistComm


