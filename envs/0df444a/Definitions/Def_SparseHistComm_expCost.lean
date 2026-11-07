-- Prove2me | Definitions.Def_SparseHistComm_expCost
-- name    : SparseHistComm_expCost
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:37:28.324059+00:00
-- url     : https://prove2.me/theorems/5cdd1282-8028-4633-b319-1e54de2f3f7c
-- title:
--   Expected total message length $E[\sum_i |M_i|]$ on an input profile
-- statement:
--   For a protocol and an input profile $x$, the **expected total number of transmitted bits** is
--   $$
--   E\Big[\sum_{i=1}^n |M_i|\Big] = \int_\Omega \sum_{i=1}^n \sum_{m \in \{0,1\}^*} Q_{i,r}(m \mid x_i)\, |m| \, d\mu(r),
--   $$
--   over the protocol randomness. Message lengths may be random, as in variable-length compression; public randomness is free.
--
--   **Formalization Note** The value lies in $[0,\infty]$. The expectation of the sum is written as the sum of the users' marginal expectations given $R = r$, which equals the joint expectation.
-- source:
--   Ye–Fan, Optimal Communication for Distributed Sparse Histogram Aggregation, arXiv:2611.04285 (held version, sha256 29df82a4…f27c6f), Eq. (3), p.2

import Mathlib
import Definitions.Def_SparseHistComm_Protocol
open MeasureTheory
open scoped ENNReal

namespace SparseHistComm

/-- The **expected total message length** `E[∑ᵢ |Mᵢ|]` of a protocol on the input profile `x`
(Ye–Fan, *Optimal Communication for Distributed Sparse Histogram Aggregation*, arXiv:2611.04285 (held version, sha256 29df82a4…f27c6f), Eq. (3), p.2), over the protocol randomness:
`∫ ∑ᵢ ∑_{m} Q_{i,r}(m | xᵢ) · |m| dμ(r)`.

**Formalization Note** In `ℝ≥0∞` (the expectation may be infinite). The expectation of the sum
is written as the sum of the users' marginal expectations given `R = r`, which equals the joint
expectation because the other users' channels are probability mass functions. -/
noncomputable def expCost {n d : ℕ} (P : Protocol n d) (x : Fin n → Finset (Fin d)) : ℝ≥0∞ :=
  ∫⁻ r, ∑ i, ∑' m : List Bool, P.enc i r (x i) m * (m.length : ℝ≥0∞) ∂P.μ

end SparseHistComm


