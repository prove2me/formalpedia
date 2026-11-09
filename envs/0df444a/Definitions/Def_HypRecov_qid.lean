-- Prove2me | Definitions.Def_HypRecov_qid
-- name    : HypRecov_qid
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:35:46.136717+00:00
-- url     : https://prove2.me/theorems/f5e2dfc1-a4a8-4d47-a5d0-698cf68a8a03
-- title:
--   The identifiability order $q_{\mathrm{id}}=\min\{r,1+\lceil\log_2 k\rceil\}$
-- statement:
--   For integers $r$ and $k$ the **identifiability order** is
--   $$q_{\mathrm{id}}(r,k)=\min\{r,\ 1+\lceil\log_2 k\rceil\},$$
--   with logarithms to base two. It is the observation order of Theorems 1.1 and 6.4, and by Theorem 1.2 the least order at which the projection determines $\mathcal B_k(H)$ when $n\ge 2r$.
--
--   **Formalization Note** $\lceil\log_2 k\rceil$ is `Nat.clog 2 k`, which agrees with it for $k\ge 1$.
-- source:
--   Zhang, Chen, Shen, Hypergraph Recovery from Anonymous Projection Streams, STOC 2027 submission (manuscript sha256 719dcfff4dc2eba2d8c5a3c51679a08cfb11f076546dea963c6376a2b9da2c82), Theorem 1.1, p.2 (PDF p.3)

import Mathlib

namespace HypRecov

/-- **The identifiability order `q_id = min{r, 1 + ⌈log₂ k⌉}`.** Zhang, Chen, Shen, *Hypergraph
Recovery from Anonymous Projection Streams*, STOC 2027 submission (manuscript sha256 719dcfff…),
Theorem 1.1, p.2 (PDF p.3). "All logarithms in observation orders are to base two" (p.2).

**Formalization Note.** `Nat.clog 2 k` is `⌈log₂ k⌉` for `k ≥ 1`. -/
def qid (r k : ℕ) : ℕ := min r (1 + Nat.clog 2 k)

end HypRecov


