-- Prove2me | Definitions.Def_CachingML_PredMarker_cleanCount
-- name    : CachingML_PredMarker_cleanCount
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T15:56:04.66099+00:00
-- url     : https://prove2.me/theorems/78c09877-a00a-4b3f-80bd-645abf444001
-- title:
--   §3.2 — phases and the number $Q$ of clean elements
-- statement:
--   Fix a cache size $k \ge 1$ and a request sequence $\sigma$. Cut $\sigma$ into **phases**: the first phase starts with the first request, and a new phase starts at the request of an element that would be the $(k+1)$-th distinct element of the current phase, so that every phase contains at most $k$ distinct elements (exactly $k$, except possibly the last). An element is **clean** in phase $r$ if it is requested in phase $r$ but not in phase $r - 1$ (phase $0$ is empty, so every element of phase $1$ is clean); elements requested in both are **stale**. The number of clean elements is
--
--   $$Q(\sigma) = \sum_{r} \bigl|\{z : z \text{ is clean in phase } r\}\bigr|.$$
--
--   These are the phases of the Marker algorithm and of Predictive Marker: a phase ends when the cache is full, all its elements are marked, and a miss occurs. $Q$ is the quantity that Claim 1 compares with the offline optimum.
--
--   **Formalization Note** `cleanCountAux k prev cur τ` scans the sequence keeping the set `prev` of elements of the previous phase and the set `cur` of elements requested so far in the current phase; a request counts $1$ exactly when it is the first request of its element in the current phase and the element is not in `prev`.
-- source:
--   Lykouris, Vassilvitskii, Competitive Caching with Machine Learned Advice, arXiv:1802.05399v4, p. 12, §3.2 (phases of the Marker algorithm; clean and stale elements); phases as blocks of k distinct elements as on p. 18, §4.2

import Mathlib

namespace CachingML.PredMarker

/-- Auxiliary recursion for `cleanCount`. `prev` is the set of elements requested in the previous
phase, `cur` the set of elements requested so far in the current phase. A request of an element not in
`cur` when `cur` already holds `k` elements starts a new phase. A request counts `1` when it is the first
request of its element in the current phase and that element was not requested in the previous phase. -/
def cleanCountAux {α : Type*} [DecidableEq α] (k : ℕ) : Finset α → Finset α → List α → ℕ
  | _, _, [] => 0
  | prev, cur, z :: τ =>
    if z ∈ cur then cleanCountAux k prev cur τ
    else if cur.card < k then (if z ∈ prev then 0 else 1) + cleanCountAux k prev (insert z cur) τ
    else 1 + cleanCountAux k cur {z} τ

/-- The number `Q` of clean elements of the request sequence `σ` for cache size `k`
(Lykouris–Vassilvitskii, arXiv:1802.05399v4, §3.2, p. 12). The sequence is cut into phases: maximal
consecutive blocks with at most `k` distinct elements, a new phase starting at the request of the
`(k+1)`-th distinct element. An element is clean in phase `r` if it is requested in phase `r` but not in
phase `r − 1` (phase `0` is empty), and `Q = ∑_r (number of clean elements of phase r)`. -/
def cleanCount {α : Type*} [DecidableEq α] (k : ℕ) (σ : List α) : ℕ :=
  cleanCountAux k ∅ ∅ σ

end CachingML.PredMarker


