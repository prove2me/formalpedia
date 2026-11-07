-- Prove2me | Definitions.Def_SparseHistComm_condExp
-- name    : SparseHistComm_condExp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:37:21.642037+00:00
-- url     : https://prove2.me/theorems/cdef6202-ef1b-412b-b116-391dc1194fbd
-- title:
--   Analysis expectation given $R = r$ under the uniform $k$-subset prior
-- statement:
--   In the analysis of Section IV, $X_1,\dots,X_n$ are independent and uniform over $k$-subsets and the messages are drawn from the protocol's channels. For a nonnegative function $g(X, M)$ of the inputs and the messages, the **conditional expectation given $R = r$** is
--   $$
--   E[g(X, M) \mid R = r] = \sum_{X_1,\dots,X_n} \sum_{m_1,\dots,m_n} \prod_{i=1}^n \pi(X_i)\, Q_{i,r}(m_i \mid X_i)\; g(X, m) .
--   $$
--
--   **Formalization Note** The value lies in $[0,\infty]$.
-- source:
--   Ye–Fan, Optimal Communication for Distributed Sparse Histogram Aggregation, arXiv:2611.04285 (held version, sha256 29df82a4…f27c6f), Section IV, p.8

import Mathlib
import Definitions.Def_SparseHistComm_Protocol
import Definitions.Def_SparseHistComm_prior
open scoped ENNReal

namespace SparseHistComm

/-- The **analysis expectation given `R = r`** of a nonnegative function `g(X, M)` of the inputs and
the messages, when `X₁, …, Xₙ` are independent and uniform over exactly-`k` supports and the
messages are drawn from the protocol's channels (Ye–Fan, *Optimal Communication for Distributed Sparse Histogram Aggregation*, arXiv:2611.04285 (held version, sha256 29df82a4…f27c6f), Section IV, p.8):
`∑_{X} ∑_{m} ∏ᵢ π(Xᵢ) Q_{i,r}(mᵢ | Xᵢ) · g(X, m)`.

**Formalization Note** In `ℝ≥0∞`; `X` ranges over `n`-tuples of `k`-subsets of `Fin d`. -/
noncomputable def condExp {n d : ℕ} (P : Protocol n d) (k : ℕ) (r : P.Ω)
    (g : (Fin n → Finset (Fin d)) → (Fin n → List Bool) → ℝ≥0∞) : ℝ≥0∞ :=
  ∑ X ∈ Fintype.piFinset (fun _ : Fin n => (Finset.univ : Finset (Fin d)).powersetCard k),
    ∑' m : Fin n → List Bool, (∏ i, prior d k * P.enc i r (X i) (m i)) * g X m

end SparseHistComm


