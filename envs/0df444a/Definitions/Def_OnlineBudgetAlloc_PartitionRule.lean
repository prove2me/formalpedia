-- Prove2me | Definitions.Def_OnlineBudgetAlloc_PartitionRule
-- name    : OnlineBudgetAlloc_PartitionRule
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:30:44.476686+00:00
-- url     : https://prove2.me/theorems/c3848b92-65ed-4c92-a170-5e37ea0c8ff7
-- title:
--   Partition rule for the middle phase: groups $A_g \cup B_g$
-- statement:
--   At the start of the middle phase, the $M$ remaining advertisers are partitioned **arbitrarily** into $M/d$ groups of size $d$. Each group $g$ is split into two halves $A_g$ and $B_g$ of size $d/2$.
--
--   A **partition rule** produces this partition from the first-phase removal sequence. It lists the $i$-th member of $A_g$ and the $i$-th member of $B_g$, for every group $g$ and every $i < d/2$. The rule is **valid** if, for every first-phase removal sequence, it lists every advertiser not removed in the first phase exactly once.
--
--   Every theorem of the mission about $D_{N,d}$ holds for every valid partition rule, which is the paper's "arbitrarily partition".
--
--   **Formalization Note** The rule depends only on which advertisers were removed in the first phase, and in which order. It cannot depend on the algorithm's choices.
-- source:
--   Panigrahi, Zhang, The Competitive Ratio of Online Budgeted Allocation is Strictly Smaller than 1-1/e, arXiv:2610.41136 (held version, sha256 913d8f02…), §2, p.2 (Middle phase)

import Mathlib
import Definitions.Def_OnlineBudgetAlloc_Seed

namespace OnlineBudgetAlloc

/-- A **partition rule** for the middle phase of `D_{N,d}` (Panigrahi–Zhang, *The Competitive Ratio of Online Budgeted Allocation is Strictly Smaller than 1-1/e*, arXiv:2610.41136 (held version, sha256 913d8f02…), §2, p.2: "Arbitrarily
partition the remaining M advertisers into M/d groups of size d each, and further split each group
into two halves of size d/2 each. Order the groups arbitrarily and denote the subgroups Ai, Bi").
Given the first-phase removal sequence `r`, the advertiser `part r g true i` is the `i`-th member
of `A_g`, and `part r g false i` the `i`-th member of `B_g`. -/
abbrev PartitionRule (N d : ℕ) : Type :=
  (Fin (numFirst N) ↪ Fin N) → Fin (numGroups N d) → Bool → Fin (d / 2) → Fin N

/-- A partition rule is **valid** if, for every first-phase removal sequence `r`, it lists every
advertiser not removed in the first phase exactly once.

**Formalization Note** The paper's partition is arbitrary; the theorems of this mission hold for
every valid rule. The rule may depend on the first-phase removals (which advertisers remain), and
on nothing else. -/
def PartitionRule.IsValid {N d : ℕ} (part : PartitionRule N d) : Prop :=
  ∀ r : Fin (numFirst N) ↪ Fin N,
    Function.Injective (fun x : Fin (numGroups N d) × Bool × Fin (d / 2) => part r x.1 x.2.1 x.2.2) ∧
    ∀ j : Fin N, (∃ g h i, part r g h i = j) ↔ j ∉ Set.range r

end OnlineBudgetAlloc


