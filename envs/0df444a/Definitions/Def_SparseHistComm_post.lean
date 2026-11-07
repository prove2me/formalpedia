-- Prove2me | Definitions.Def_SparseHistComm_post
-- name    : SparseHistComm_post
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:38:25.400409+00:00
-- url     : https://prove2.me/theorems/33c66d1c-6669-4550-ba04-5ccd1203edeb
-- title:
--   Local posterior $P(X_i(a) = 1 \mid M_i = m, R = r)$
-- statement:
--   Under the uniform prior on $k$-subsets, the **local posterior** of coordinate $a$ for user $i$, given its message $M_i = m$ and $R = r$, is given by Bayes' rule:
--   $$
--   P(X_i(a) = 1 \mid M_i = m, R = r) = \frac{\sum_{|x| = k,\ a \in x} \pi(x)\, Q_{i,r}(m \mid x)}{P(M_i = m \mid R = r)} .
--   $$
--
--   **Formalization Note** For a message of conditional probability zero the quotient is $0/0 = 0$, so its posterior list is empty, as the paper allows ("lists for messages of conditional probability zero may be taken empty", p.15).
-- source:
--   Ye–Fan, Optimal Communication for Distributed Sparse Histogram Aggregation, arXiv:2611.04285 (held version, sha256 29df82a4…f27c6f), Eq. (16), p.8; proof of Lemma 2, p.15

import Mathlib
import Definitions.Def_SparseHistComm_msgMass
open scoped ENNReal

namespace SparseHistComm

/-- The **local posterior** `P(Xᵢ(a) = 1 | Mᵢ = m, R = r)` of coordinate `a` for user `i` under the
uniform prior on exactly-`k` supports (Ye–Fan, *Optimal Communication for Distributed Sparse Histogram Aggregation*, arXiv:2611.04285 (held version, sha256 29df82a4…f27c6f), Eq. (16), p.8), by Bayes' rule:
`(∑_{x ∋ a, |x| = k} π(x) Q_{i,r}(m | x)) / P(Mᵢ = m | R = r)`.

**Formalization Note** In `ℝ`; for a message of conditional probability zero the quotient is
`0/0 = 0`, so its posterior list (16) is empty ("lists for messages of conditional probability
zero may be taken empty", p.15). -/
noncomputable def post {n d : ℕ} (P : Protocol n d) (k : ℕ) (i : Fin n) (r : P.Ω)
    (m : List Bool) (a : Fin d) : ℝ :=
  (∑ x ∈ ((Finset.univ : Finset (Fin d)).powersetCard k).filter (fun x => a ∈ x),
      (prior d k).toReal * (P.enc i r x m).toReal) / msgMass P k i r m

end SparseHistComm


