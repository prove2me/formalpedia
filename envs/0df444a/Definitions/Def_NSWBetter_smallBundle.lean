-- Prove2me | Definitions.Def_NSWBetter_smallBundle
-- name    : NSWBetter_smallBundle
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:53:42.461351+00:00
-- url     : https://prove2.me/theorems/619262a7-4c51-4adb-89ac-b95338eba7e0
-- title:
--   Small part $v(S_i)$ of a round-robin bundle
-- statement:
--   $v(S_i)$, where $S_i$ is the set of small goods agent $i$ receives in the round robin allocation $W$ (Definition 3.7).
-- source:
--   Viswanathan, A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations, arXiv:2607.13340 (held version, sha256 08811cb468c2df39231dca4222c5af94163587c7c83e205e50bbf0b91fc1deb3), Definition 3.7, p.12 (Small Bundles of the Round Robin Allocation)

import Mathlib
import Definitions.Def_NSWBetter_sortDesc
import Definitions.Def_NSWBetter_largeCount

namespace NSWBetter

/-- **Small bundles (Definition 3.7).**
Viswanathan, *A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations*, arXiv:2607.13340 (held version, sha256 08811cb4…), Definition 3.7, p.12: "for each agent i, we use Si to denote the set of small goods that agent i receives in the round robin allocation W."

`smallBundle Δ s i = Σ_(k ≥ ℓ, k ≡ i mod Δ) v(g_(k+1))`: the value of the goods of `W_i` at sorted positions `≥ ℓ` (the small goods). -/
noncomputable def smallBundle (Δ : ℕ) (s : Multiset ℝ) (i : ℕ) : ℝ :=
  ∑ k ∈ (Finset.range (sortDesc s).length).filter (fun k => largeCount Δ s ≤ k ∧ k % Δ = i),
    (sortDesc s).getD k 0

end NSWBetter


