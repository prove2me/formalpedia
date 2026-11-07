-- Prove2me | Definitions.Def_NSWBetter_IsBucketMatching
-- name    : NSWBetter_IsBucketMatching
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:51:30.3412+00:00
-- url     : https://prove2.me/theorems/963ae9a5-b05b-42a1-92ed-bf3e4a35376c
-- title:
--   Integral matching between buckets and goods
-- statement:
--   An **integral matching** between the buckets $B$ and the goods $G$: a set of pairs (bucket $b^t$ of agent $i$, good $g$) in which every bucket and every good occurs at most once.
-- source:
--   Viswanathan, A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations, arXiv:2607.13340 (held version, sha256 08811cb468c2df39231dca4222c5af94163587c7c83e205e50bbf0b91fc1deb3), Section 4, p.16 (integral matching MG(x) between B and G)

import Mathlib

namespace NSWBetter

/-- **Integral matchings of the bucket graph.**
Viswanathan, *A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations*, arXiv:2607.13340 (held version, sha256 08811cb4…), Section 4, p.16: "we compute an integral matching MG(x) between B and G".

A matching is a finite set of triples `(i, t, g)` (bucket `t` of agent `i` matched to good `g`) in which every bucket and every good appears at most once. -/
def IsBucketMatching {n m : ℕ} (M : Finset (Fin n × Fin m × Fin m)) : Prop :=
  (∀ e ∈ M, ∀ e' ∈ M, e.1 = e'.1 → e.2.1 = e'.2.1 → e = e') ∧
  ∀ e ∈ M, ∀ e' ∈ M, e.2.2 = e'.2.2 → e = e'

end NSWBetter


