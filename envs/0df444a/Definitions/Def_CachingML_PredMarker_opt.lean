-- Prove2me | Definitions.Def_CachingML_PredMarker_opt
-- name    : CachingML_PredMarker_opt
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T15:52:32.417533+00:00
-- url     : https://prove2.me/theorems/cc5d88e9-58d8-4a92-8dd9-d920a90c722f
-- title:
--   §2.1 — the offline optimum $\mathrm{Opt}(\sigma)$ of caching from an empty cache
-- statement:
--   Fix a cache size $k \ge 1$. A cache holds at most $k$ elements and starts empty. Requests $z_1, \dots, z_n$ arrive in order; a request for an element in the cache is a **hit** and costs nothing, and a request for an element not in the cache is a **miss**: the element is loaded, and if the cache is full one element of the cache is evicted first. The offline optimum is
--
--   $$\mathrm{Opt}(\sigma) = \min_{\text{eviction schedules}} \#\{\text{misses on } \sigma\},$$
--
--   the minimum over all choices of evicted elements, made with full knowledge of $\sigma$.
--
--   This is the benchmark in the competitive ratio of every caching algorithm of the paper; Algorithm 1 starts from the same empty cache.
--
--   **Formalization Note** The minimum is computed by the recursion `optFrom k C τ`: a hit keeps the cache, a miss with fewer than $k$ cached elements loads without eviction, and a miss with a full cache takes the minimum over all evicted elements $e \in C$. Schedules that load only on a miss (demand paging) and do not evict while the cache has room lose no generality, since any schedule can be converted into one of this kind with no more misses. The last branch of the recursion is reached only when $k = 0$.
-- source:
--   Lykouris, Vassilvitskii, Competitive Caching with Machine Learned Advice, arXiv:1802.05399v4, pp. 5–6, §2.1 (competitive analysis; the caching problem)

import Mathlib

namespace CachingML.PredMarker

/-- `optFrom k C τ` is the least number of cache misses with which a cache of size `k`, holding the set
`C`, can serve the request sequence `τ`: a request in the cache is a hit (cost `0`); a request not in
the cache is a miss (cost `1`), and the element is loaded, without eviction if the cache holds fewer
than `k` elements and otherwise after evicting one element `e ∈ C` of the scheduler's choice (the
minimum is taken over all choices). The last branch (`C` empty and `C.card ≥ k`) only occurs for
`k = 0`. -/
def optFrom {α : Type*} [DecidableEq α] (k : ℕ) : Finset α → List α → ℕ
  | _, [] => 0
  | C, z :: τ =>
    if z ∈ C then optFrom k C τ
    else if C.card < k then 1 + optFrom k (insert z C) τ
    else if hC : C.Nonempty then 1 + C.inf' hC (fun e => optFrom k (insert z (C.erase e)) τ)
    else 1 + optFrom k (insert z C) τ

/-- The offline optimum `Opt(σ)` of the caching problem (Lykouris–Vassilvitskii, arXiv:1802.05399v4,
§2.1, pp. 5–6): the minimum number of cache misses of any (demand-paging) eviction schedule for a cache
of size `k` that starts empty and serves the request sequence `σ`. -/
def opt {α : Type*} [DecidableEq α] (k : ℕ) (σ : List α) : ℕ :=
  optFrom k ∅ σ

end CachingML.PredMarker


