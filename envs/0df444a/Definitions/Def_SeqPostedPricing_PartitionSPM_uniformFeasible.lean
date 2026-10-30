-- Prove2me | Definitions.Def_SeqPostedPricing_PartitionSPM_uniformFeasible
-- name    : SeqPostedPricing_PartitionSPM_uniformFeasible
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:08:11.806466+00:00
-- url     : https://prove2.me/theorems/da9d9b64-b4bc-450d-9758-16c1d821f80b
-- title:
--   $k$-uniform matroid
-- statement:
--   A set $S$ of agents is feasible in the **$k$-uniform matroid** if $|S| \le k$. For $k = 1$ it is a single-item auction; for general $k$ a multi-unit auction with $k$ units.
-- source:
--   Chawla, Hartline, Malec, Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, §4.2, p. 7 (PDF p. 9)

import Mathlib

namespace SeqPostedPricing.PartitionSPM

/-- **`k`-uniform matroid** (Chawla, Hartline, Malec, Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, §4.2, p. 7 = PDF p. 9: "A matroid is k-uniform if all subsets of
size at most k are feasible"). A set of agents is feasible when it has at most `k` elements.

**Formalization Note** Any `k : ℕ`, including `0`. -/
def uniformFeasible {n : ℕ} (k : ℕ) (S : Finset (Fin n)) : Prop := S.card ≤ k

end SeqPostedPricing.PartitionSPM


