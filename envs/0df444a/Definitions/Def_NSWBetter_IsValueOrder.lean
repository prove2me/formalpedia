-- Prove2me | Definitions.Def_NSWBetter_IsValueOrder
-- name    : NSWBetter_IsValueOrder
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:51:25.404464+00:00
-- url     : https://prove2.me/theorems/23a0527f-f9fa-4b68-9b89-6a99e95e0aad
-- title:
--   Ranking of goods by non-increasing value for each agent
-- statement:
--   For each agent $i$, a ranking $r_i$ of the goods (a bijection onto positions $0,\dots,m-1$) that lists them by non-increasing value $v_i$; goods of equal value may come in any order. This is the order "$v_i(g_1)\ge\dots\ge v_i(g_m)$" used to build the buckets of agent $i$.
-- source:
--   Viswanathan, A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations, arXiv:2607.13340 (held version, sha256 08811cb468c2df39231dca4222c5af94163587c7c83e205e50bbf0b91fc1deb3), Section 4, p.16 ("assume without loss of generality, vi(g1) ≥ vi(g2) ≥ · · · ≥ vi(gm)")

import Mathlib

namespace NSWBetter

/-- **Value orders.**
Viswanathan, *A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations*, arXiv:2607.13340 (held version, sha256 08811cb4…), Section 4, p.16: "Fix an agent i ∈ N and assume without loss of generality, vi(g1) ≥ vi(g2) ≥ · · · ≥ vi(gm)."

`r i g` is the rank (0-based position) of good `g` in agent `i`'s order; `IsValueOrder v r` says that a good of smaller rank is weakly more valuable to `i`. Ties may be ordered arbitrarily. -/
def IsValueOrder {n m : ℕ} (v : Fin n → Fin m → ℝ) (r : Fin n → Fin m ≃ Fin m) : Prop :=
  ∀ i g g', r i g < r i g' → v i g' ≤ v i g

end NSWBetter


