-- Prove2me | Definitions.Def_SparseHistComm_Supplement_Chet
-- name    : SparseHistComm_Supplement_Chet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T02:40:55.7472+00:00
-- url     : https://prove2.me/theorems/771a0602-948d-4bd2-8287-b6173cd6d0a4
-- title:
--   Heterogeneous communication complexity $C_{\mathrm{het}}(D,\delta)$
-- statement:
--   For $n$ users, $k$-sparse binary inputs in dimension $d$, distortion $D$, and failure probability $\delta$, the **heterogeneous communication complexity** is
--
--   $$
--   C_{\mathrm{het}}(D,\delta)
--     = \inf_{\Pi\text{ is }(D,\delta)\text{-accurate}}
--       \sup_{\|x_i\|_0\le k}
--       \mathbb E_\Pi\!\left[\sum_{i=1}^n |M_i|\right].
--   $$
--
--   The infimum ranges over every protocol in the paper's heterogeneous model: users may use different encoders, messages are arbitrary finite binary strings, and public and private randomness are allowed.
--
--   **Formalization Note** The value lies in $[0,\infty]$. This is exactly the published homogeneous complexity with only the common-encoder condition removed; no prefix-free or bounded-length condition is added.
-- source:
--   Ye–Fan, Optimal Communication for Distributed Sparse Histogram Aggregation, arXiv:2611.04285 (held version, sha256 29df82a4…f27c6f), Section I, p.3, and Theorem 2, p.9

import Mathlib
import Definitions.Def_SparseHistComm_worstCost
import Definitions.Def_SparseHistComm_IsAccurate

open scoped ENNReal

namespace SparseHistComm

namespace Supplement

/-- `C_het(D, δ)`, the infimum of the worst-case expected communication cost over all accurate
heterogeneous protocols (Ye–Fan, *Optimal Communication for Distributed Sparse Histogram
Aggregation*, arXiv:2611.04285 (held version, sha256 29df82a4…f27c6f), Section I, p.3,
and Theorem 2, p.9).

**Formalization Note** This differs from the published `SparseHistComm.Chom` only by omitting
`IsHomogeneous`: the infimum ranges over every published `Protocol n d`, with arbitrary public
randomness, per-user channels into `List Bool`, and measurable decoder. No prefix-free or bounded
message-length condition is imposed. -/
noncomputable def Chet (n k d : ℕ) (D δ : ℝ) : ℝ≥0∞ :=
  ⨅ (P : Protocol n d) (_ : IsAccurate P k D δ), worstCost P k

end Supplement

end SparseHistComm


