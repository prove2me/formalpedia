-- Prove2me | Definitions.Def_SparseHistComm_succProb
-- name    : SparseHistComm_succProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:38:09.562544+00:00
-- url     : https://prove2.me/theorems/459d9d2a-f5cc-40f2-ab79-68a4f7d01afd
-- title:
--   Success probability $P(\|\hat u - u\|_1 \le D)$ on an input profile
-- statement:
--   For a protocol, a distortion level $D$ and an input profile $x = (x_1,\dots,x_n)$ with empirical histogram $u$, the **success probability** is
--   $$
--   P(\|\hat u - u\|_1 \le D) = \int_\Omega \sum_{m_1,\dots,m_n \in \{0,1\}^*} \prod_{i=1}^n Q_{i,r}(m_i \mid x_i)\, \mathbf 1\{\|\hat u(r, m) - u\|_1 \le D\} \, d\mu(r),
--   $$
--   the probability over the protocol randomness (public and private) that the estimate is within $\ell_1$ distance $D$ of the histogram.
--
--   **Formalization Note** A probability in $[0,\infty]$ (extended nonnegative reals), as a lower Lebesgue integral of a countable sum over message tuples.
-- source:
--   Ye–Fan, Optimal Communication for Distributed Sparse Histogram Aggregation, arXiv:2611.04285 (held version, sha256 29df82a4…f27c6f), Definition 1, (2), p.2

import Mathlib
import Definitions.Def_SparseHistComm_Protocol
import Definitions.Def_SparseHistComm_l1
import Definitions.Def_SparseHistComm_empHist
open MeasureTheory
open scoped ENNReal

namespace SparseHistComm

/-- The **success probability** `P(‖û − u‖₁ ≤ D)` of a protocol on the input profile `x`, over the
protocol randomness (Ye–Fan, *Optimal Communication for Distributed Sparse Histogram Aggregation*, arXiv:2611.04285 (held version, sha256 29df82a4…f27c6f), Definition 1, (2), p.2):
`∫ ∑_{m} ∏ᵢ Q_{i,r}(mᵢ | xᵢ) · 1{‖û(r, m) − u‖₁ ≤ D} dμ(r)`, where `u` is the empirical histogram
of `x`.

**Formalization Note** A probability in `ℝ≥0∞`, as a lower Lebesgue integral of a countable sum
over message tuples `m : Fin n → List Bool`. -/
noncomputable def succProb {n d : ℕ} (P : Protocol n d) (D : ℝ)
    (x : Fin n → Finset (Fin d)) : ℝ≥0∞ :=
  ∫⁻ r, ∑' m : Fin n → List Bool,
    (∏ i, P.enc i r (x i) (m i)) * (if l1 (P.dec r m) (empHist x) ≤ D then 1 else 0) ∂P.μ

end SparseHistComm


