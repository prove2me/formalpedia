-- Prove2me | Definitions.Def_NSWBetter_bucket
-- name    : NSWBetter_bucket
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:51:26.185972+00:00
-- url     : https://prove2.me/theorems/85494f24-4250-4eb6-a876-09e55e915e1d
-- title:
--   Shmoys–Tardos bucket $b^t_g$ of agent $i$
-- statement:
--   The **buckets** of agent $i$ in the Shmoys–Tardos rounding (p.16). Order the goods by non-increasing value for $i$ and place them as consecutive intervals of lengths $x_{ig}$ on $[0,\sum_gx_{ig}]$; bucket $b^t$ ($t=0,1,\dots$) takes the part of each good lying in $[t,t+1]$:
--   $$b^t_g=\max\Bigl(0,\ \min(p_g+x_{ig},t+1)-\max(p_g,t)\Bigr),\qquad p_g=\sum_{g'\text{ before }g}x_{ig'}.$$
--   These are the unique buckets with properties (P1)–(P3); there are $k_i=\lceil\sum_gx_{ig}\rceil$ nonzero ones.
--
--   **Formalization Note** Bucket indices range over $0,\dots,m-1$; those $\ge k_i$ are zero.
-- source:
--   Viswanathan, A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations, arXiv:2607.13340 (held version, sha256 08811cb468c2df39231dca4222c5af94163587c7c83e205e50bbf0b91fc1deb3), Section 4, p.16, properties (P1)–(P3)

import Mathlib

namespace NSWBetter

open Classical in
/-- **The buckets of agent i (P1)–(P3).**
Viswanathan, *A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations*, arXiv:2607.13340 (held version, sha256 08811cb4…), Section 4, p.16: "We create ki buckets for agent i … b1 gets the highest valued fraction of goods (according to agent i) of size at most one. Then, of the remaining fractional bundle xi not in b1, b2 gets the highest valued fraction of goods of size at most 1, and so on"; "Formally, the bucketing is uniquely defined by the following properties [FL25]: (P1) … (P2) … (P3) …"

Lay out agent `i`'s goods in the order `r i` as consecutive intervals of lengths `x i g` on `[0, Σ_g x i g]`; bucket `t` (0-based) gets the part of good `g`'s interval inside `[t, t+1]`: `b^t_g = max(0, min(pre + x_ig, t+1) − max(pre, t))`, `pre` the total amount of the goods ranked before `g`.

**Formalization Note.** This is the unique bucketing satisfying (P1)–(P3) for the order `r i`. Buckets are indexed by `t : Fin m`; since `k_i = ⌈Σ_g x_ig⌉ ≤ m`, the buckets `t ≥ k_i` are the zero vector. -/
noncomputable def bucket {n m : ℕ} (r : Fin n → Fin m ≃ Fin m) (x : Fin n → Fin m → ℝ)
    (i : Fin n) (t : Fin m) (g : Fin m) : ℝ :=
  max 0 (min ((∑ g' ∈ Finset.univ.filter (fun g' => r i g' < r i g), x i g') + x i g)
      ((t : ℝ) + 1) - max (∑ g' ∈ Finset.univ.filter (fun g' => r i g' < r i g), x i g') (t : ℝ))

end NSWBetter


