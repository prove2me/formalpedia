-- Prove2me | Definitions.Def_SeqPostedPricing_PartitionSPM_rank
-- name    : SeqPostedPricing_PartitionSPM_rank
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:08:28.832982+00:00
-- url     : https://prove2.me/theorems/16b174c1-48bc-45c2-9fd8-5d97b2d03194
-- title:
--   Rank of a set of agents
-- statement:
--   For a feasibility constraint $\mathcal J$ and a set $S$ of agents, the **rank** of $S$ is the size of the largest feasible subset of $S$:
--
--   $$
--   \mathrm{rank}(S) = \max_{S' \subseteq S,\ S' \in \mathcal J} |S'|.
--   $$
--
--   **Formalization Note** The paper writes $S' \subset S$; the largest feasible subset may be $S$ itself, so it is read as $\subseteq$. The value is $0$ when no subset is feasible.
-- source:
--   Chawla, Hartline, Malec, Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, §4, unnumbered, p. 6 (PDF p. 8)

import Mathlib

namespace SeqPostedPricing.PartitionSPM

open Classical in
/-- **Rank of a set of agents** (Chawla, Hartline, Malec, Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, §4, unnumbered, p. 6 = PDF p. 8: "let the rank of a subset S
of agents, rank(S), denote the size of the largest feasible subset in S, that is,
rank(S) = max_{S′⊂S,S′∈J} |S′|"). The largest size of a feasible subset of `S`.

**Formalization Note** "S′ ⊂ S" is read as `S′ ⊆ S` (the largest feasible subset may be `S`
itself). If no subset is feasible the value is `0`; for a downward-closed nonempty system `∅` is
feasible. -/
noncomputable def rank {n : ℕ} (Feas : Finset (Fin n) → Prop) (S : Finset (Fin n)) : ℕ :=
  (S.powerset.filter Feas).sup Finset.card

end SeqPostedPricing.PartitionSPM


