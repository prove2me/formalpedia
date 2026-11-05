-- Prove2me | Definitions.Def_OmniThreshold_onlineDemand
-- name    : OmniThreshold_onlineDemand
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:34:03.713379+00:00
-- url     : https://prove2.me/theorems/811fc724-c6c3-444c-aa95-db32ee136e99
-- title:
--   Online demand at each location, read off the order stream
-- statement:
--   Online orders arrive one at a time. $X_k\in[n]$ is the location of the $k$-th order ($k=0,1,2,\dots$), and $N$ is the total number of online orders. The **online demand** at location $i$ is
--   $$
--   \mathcal D_i^O=\#\{k<N:\ X_k=i\},
--   $$
--   so that $\sum_i\mathcal D_i^O=N$.
--
--   **Formalization Note** Arrivals are numbered from $0$. Only the first $N$ entries of the sequence $(X_k)$ are orders. Every quantity is a function of the outcome $\omega$.
-- source:
--   Jia, Karp, Ravi & Tayur, Effective Online Order Acceptance Policies for Omni-Channel Fulfillment, SSRN 3932692, §1.1, p.2

import Mathlib

namespace OmniThreshold

/-- The **online demand at each location** (Jia, Karp, Ravi & Tayur, *Effective Online Order
Acceptance Policies for Omni-Channel Fulfillment*, SSRN 3932692, §1.1, p.2: "At each location `i`,
there are two streams of demand, on-line (`D_i^O`) and physical (`D_i^P`)"), read off the stream of
online orders: `D_i^O(ω) = #{k < N(ω) : X_k(ω) = i}`.

Here `N ω` is the total number of online orders and `X k ω` the location of the `k`-th online
order.

**Formalization Note** Orders are numbered `k = 0, 1, …` (0-based) in their order of arrival; only
the first `N ω` entries of the sequence `X · ω` are orders. -/
def onlineDemand {Ω : Type*} {n : ℕ} (X : ℕ → Ω → Fin n) (N : Ω → ℕ) (ω : Ω) : Fin n → ℕ :=
  fun i => ((Finset.range (N ω)).filter (fun k => X k ω = i)).card

end OmniThreshold


