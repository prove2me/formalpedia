-- Prove2me | Definitions.Def_NSWBetter_IsFrac
-- name    : NSWBetter_IsFrac
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:49:16.475203+00:00
-- url     : https://prove2.me/theorems/0c915a44-d713-4105-b91d-29fbf1a00115
-- title:
--   Fractional allocation
-- statement:
--   A **fractional allocation** is an $n\times m$ matrix $x$ with $x_{ig}\in[0,1]$ for all $i,g$ and $\sum_{i\in N}x_{ig}\le1$ for every good $g$; $x_{ig}$ is the amount of good $g$ given to agent $i$.
-- source:
--   Viswanathan, A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations, arXiv:2607.13340 (held version, sha256 08811cb468c2df39231dca4222c5af94163587c7c83e205e50bbf0b91fc1deb3), Section 2, p.8 (fractional allocation)

import Mathlib

namespace NSWBetter

/-- **Fractional allocations.**
Viswanathan, *A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations*, arXiv:2607.13340 (held version, sha256 08811cb4…), Section 2, p.8: "A fractional allocation x is an n × m matrix … xig ∈ [0, 1] for each i ∈ N, g ∈ G, and Σ_(i∈N) xig ≤ 1 for each g ∈ G." -/
def IsFrac {n m : ℕ} (x : Fin n → Fin m → ℝ) : Prop :=
  (∀ i g, 0 ≤ x i g ∧ x i g ≤ 1) ∧ ∀ g, ∑ i, x i g ≤ 1

end NSWBetter


