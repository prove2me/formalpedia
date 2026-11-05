-- Prove2me | Definitions.Def_OmniThreshold_acceptedCount
-- name    : OmniThreshold_acceptedCount
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:34:01.611734+00:00
-- url     : https://prove2.me/theorems/bb685325-411b-452d-9d59-dd067ec92f7d
-- title:
--   Orders accepted at each location under a Global Threshold $S$
-- statement:
--   A **Global Threshold policy** $S\in\mathbb N$ accepts the first $S$ online orders, from all locations, and rejects all remaining orders. With order locations $X_0,X_1,\dots$ and $N$ orders in total, the number accepted at location $i$ is
--   $$
--   A_i^O(S)=\#\{k<\min(S,N):\ X_k=i\},
--   $$
--   so that $\sum_iA_i^O(S)=\min(S,N)$ and $A_i^O(S)\le\mathcal D_i^O$.
--
--   **Formalization Note** Arrivals are numbered from $0$, so "the first $S$ orders" are those with index $k<S$.
-- source:
--   Jia, Karp, Ravi & Tayur, Effective Online Order Acceptance Policies for Omni-Channel Fulfillment, SSRN 3932692, p.3

import Mathlib

namespace OmniThreshold

/-- The **orders accepted at each location under the Global Threshold policy `S`** (Jia, Karp,
Ravi & Tayur, *Effective Online Order Acceptance Policies for Omni-Channel Fulfillment*, SSRN
3932692, p.3: "A Global Threshold policy `S` accepts the first `S` online orders (from all
locations) and rejects all remaining orders"):
`A_i^O(ω) = #{k < min(S, N(ω)) : X_k(ω) = i}`.

Here `N ω` is the total number of online orders and `X k ω` the location of the `k`-th one.

**Formalization Note** Orders are numbered `k = 0, 1, …` (0-based) in order of arrival, so "the
first `S` orders" are those with `k < S`, of which only `k < N ω` exist. Hence
`∑_i A_i^O = min(S, N)`. -/
def acceptedCount {Ω : Type*} {n : ℕ} (X : ℕ → Ω → Fin n) (N : Ω → ℕ) (S : ℕ) (ω : Ω) :
    Fin n → ℕ :=
  fun i => ((Finset.range (min S (N ω))).filter (fun k => X k ω = i)).card

end OmniThreshold


