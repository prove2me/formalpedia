-- Prove2me | Definitions.Def_SeqPostedPricing_PartitionSPM_partitionFeasible
-- name    : SeqPostedPricing_PartitionSPM_partitionFeasible
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:07:56.481455+00:00
-- url     : https://prove2.me/theorems/d4773040-f247-4999-80da-ac990ea7f6ea
-- title:
--   Partition matroid
-- statement:
--   Let every agent $i$ belong to a block $\mathrm{blk}(i)$, and let every block $l$ have a capacity $\mathrm{cap}(l) \in \mathbb N$. A set $S$ of agents is feasible in the **partition matroid** if
--
--   $$
--   \big|\{i \in S : \mathrm{blk}(i) = l\}\big| \le \mathrm{cap}(l) \quad \text{for every block } l.
--   $$
--
--   This is the disjoint union of the uniform matroids of rank $\mathrm{cap}(l)$ on the blocks.
--
--   **Formalization Note** The blocks may be indexed by any type and capacities may be $0$.
-- source:
--   Chawla, Hartline, Malec, Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, §4.2, p. 7 (PDF p. 9)

import Mathlib

namespace SeqPostedPricing.PartitionSPM

open Classical in
/-- **Partition matroid** (Chawla, Hartline, Malec, Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, §4.2, p. 7 = PDF p. 9: "partition matroids, i.e. disjoint unions of
uniform matroids"; "A matroid is k-uniform if all subsets of size at most k are feasible"). Agent `i`
belongs to block `blk i`; a set `S` of agents is feasible when, for every block `l`, at most `cap l`
agents of `S` lie in `l`.

**Formalization Note** Any index type `ι` of blocks and any capacities (`0` allowed); blocks are the
fibres of `blk`, so they are disjoint and cover the agents. -/
def partitionFeasible {n : ℕ} {ι : Type*} (blk : Fin n → ι) (cap : ι → ℕ) (S : Finset (Fin n)) :
    Prop :=
  ∀ l : ι, (S.filter (fun i => blk i = l)).card ≤ cap l

end SeqPostedPricing.PartitionSPM


