-- Prove2me | Definitions.Def_SparseHistComm_Chom
-- name    : SparseHistComm_Chom
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:40:22.035962+00:00
-- url     : https://prove2.me/theorems/34089c75-9416-4ca4-87db-7728f8d48931
-- title:
--   Homogeneous communication complexity $C_{\mathrm{hom}}(D,\delta)$
-- statement:
--   For $n$ users, sparsity $k$ and dimension $d$, the **homogeneous communication complexity** $C_{\mathrm{hom}}(D,\delta)$ is the infimum of the cost (3) over all $(D,\delta)$-accurate homogeneous protocols:
--   $$
--   C_{\mathrm{hom}}(D,\delta) = \inf\Big\{ \sup_{\|x_i\|_0 \le k} E\Big[\sum_{i=1}^n |M_i|\Big] \ :\ \text{the protocol is homogeneous and } (D,\delta)\text{-accurate} \Big\}.
--   $$
--   The paper suppresses $n, k, d$ in the notation.
--
--   **Formalization Note** An infimum in $[0,\infty]$ over every protocol (any public randomness space, any message channels into binary strings, any measurable decoder); it equals $\infty$ only if no accurate homogeneous protocol has finite cost.
-- source:
--   Ye–Fan, Optimal Communication for Distributed Sparse Histogram Aggregation, arXiv:2611.04285 (held version, sha256 29df82a4…f27c6f), Section I, p.3

import Mathlib
import Definitions.Def_SparseHistComm_worstCost
import Definitions.Def_SparseHistComm_IsAccurate
import Definitions.Def_SparseHistComm_IsHomogeneous
open scoped ENNReal

namespace SparseHistComm

/-- `C_hom(D, δ)`: the infimum of the cost (3) over `(D, δ)`-accurate homogeneous protocols, for
`n` users, `k`-sparse inputs and dimension `d` (Ye–Fan, *Optimal Communication for Distributed Sparse Histogram Aggregation*, arXiv:2611.04285 (held version, sha256 29df82a4…f27c6f), Section I, p.3: "Let Chom(D, δ) and
Chet(D, δ) be the infima of (3) over accurate homogeneous and heterogeneous protocols,
suppressing n, k, d").

**Formalization Note** An infimum in `ℝ≥0∞` over every protocol of `Protocol n d` (any public
randomness space `Ω : Type`, any message channels into `List Bool`, any measurable decoder); it is
`⊤` only if no accurate homogeneous protocol has finite cost. -/
noncomputable def Chom (n k d : ℕ) (D δ : ℝ) : ℝ≥0∞ :=
  ⨅ (P : Protocol n d) (_ : IsHomogeneous P) (_ : IsAccurate P k D δ), worstCost P k

end SparseHistComm


