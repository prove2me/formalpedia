-- Prove2me | Definitions.Def_OnlineBudgetAlloc_inputD
-- name    : OnlineBudgetAlloc_inputD
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:31:33.225434+00:00
-- url     : https://prove2.me/theorems/305ffef5-0ae1-4518-8614-f6103ed7eceb
-- title:
--   The input of $D_{N,d}$ built from a seed
-- statement:
--   Fix a seed and a partition rule. All $N$ advertisers have budget $1$. Removed advertisers bid $0$ on all later items.
--
--   1. **First phase** ($N/3$ rounds). Each round has one item, on which every remaining advertiser bids $\tfrac34$. After the item is assigned, the next advertiser in the seed's first-phase order is removed.
--   2. **Middle phase** ($M/d$ rounds, $M = 2N/3$). Round $g$ has three items. On item 1, all $d$ advertisers of group $g$ bid $1$. On item 2, they all bid $\tfrac12$. On item 3, the $d/2$ advertisers of $A_g$ (if the coin of group $g$ says so) or of $B_g$ bid $\tfrac12$. All other advertisers bid $0$. After all $3M/d$ middle items, the seed's chosen advertiser of each $A_g$ and of each $B_g$ is removed.
--   3. **Final phase** ($R = M(1-2/d)$ rounds). Each round has one item, on which every remaining advertiser bids $1$. After final item $u$, the surviving advertiser of rank $u$ is removed.
--
--   The module also defines the **remaining set** just before each item (`alive`) and its size $s_t$ (`numAlive`), the number of remaining advertisers just before item $t$ is assigned (§3.2, p.4).
--
--   **Formalization Note** The first-phase removal sequence is `Seed.removed1`. The predicates `firstSurvivor`, `midRemoved`, `finalSurvivor` and the rank `finalRank` describe who is still present.
-- source:
--   Panigrahi, Zhang, The Competitive Ratio of Online Budgeted Allocation is Strictly Smaller than 1-1/e, arXiv:2610.41136 (held version, sha256 913d8f02…), §2, pp.2–3; s_t: §3.2, p.4

import Mathlib
import Definitions.Def_OnlineBudgetAlloc_Instance
import Definitions.Def_OnlineBudgetAlloc_Seed
import Definitions.Def_OnlineBudgetAlloc_PartitionRule

namespace OnlineBudgetAlloc

/-- The first-phase removal sequence of a seed: after first-phase item `k`, advertiser
`s.ord1 k` is removed. -/
def Seed.removed1 {N d : ℕ} (s : Seed N d) : Fin (numFirst N) ↪ Fin N :=
  ⟨fun k => s.ord1 (Fin.castLE (Nat.div_le_self N 3) k),
    s.ord1.injective.comp (Fin.castLE_injective _)⟩

/-- Advertiser `j` survives the first phase. -/
def Seed.firstSurvivor {N d : ℕ} (s : Seed N d) (j : Fin N) : Prop :=
  numFirst N ≤ (s.ord1.symm j).val

/-- Advertiser `j` is removed at the end of the middle phase: it is the advertiser at position
`remA g` of `A_g`, or at position `remB g` of `B_g`, for some group `g`. -/
def midRemoved {N d : ℕ} (part : PartitionRule N d) (s : Seed N d) (j : Fin N) : Prop :=
  ∃ g, part s.removed1 g true (s.remA g) = j ∨ part s.removed1 g false (s.remB g) = j

/-- Advertiser `j` survives the first and the middle phase. -/
def finalSurvivor {N d : ℕ} (part : PartitionRule N d) (s : Seed N d) (j : Fin N) : Prop :=
  s.firstSurvivor j ∧ ¬ midRemoved part s j

open Classical in
/-- The rank of a final-phase survivor `j`: the number of final-phase survivors with a smaller
`ord3`-value. The survivor of rank `u` is removed right after final-phase item `u`. -/
noncomputable def finalRank {N d : ℕ} (part : PartitionRule N d) (s : Seed N d) (j : Fin N) : ℕ :=
  (Finset.univ.filter fun j' => finalSurvivor part s j' ∧ s.ord3 j' < s.ord3 j).card

/-- Advertiser `j` is in the **remaining set** just before item `t` of `D_{N,d}` arrives
(Panigrahi–Zhang, *The Competitive Ratio of Online Budgeted Allocation is Strictly Smaller than 1-1/e*, arXiv:2610.41136 (held version, sha256 913d8f02…), §2, pp.2–3). First phase (`t < N/3`): `j` is not among `ord1 0, …, ord1 (t−1)`. Middle
phase: `j` survived the first phase (the middle removals happen only after all `3M/d` middle items).
Final phase (item `u = t − N/3 − 3M/d`): `j` survived the middle phase and is not among the
survivors of rank `< u`. -/
def alive {N d : ℕ} (part : PartitionRule N d) (s : Seed N d) (t : Fin (numItems N d))
    (j : Fin N) : Prop :=
  if t.val < numFirst N then t.val ≤ (s.ord1.symm j).val
  else if t.val < numFirst N + 3 * numGroups N d then s.firstSurvivor j
  else finalSurvivor part s j ∧ t.val - (numFirst N + 3 * numGroups N d) ≤ finalRank part s j

open Classical in
/-- `s_t`: the number of remaining advertisers just before item `t` is assigned
(Panigrahi–Zhang, *The Competitive Ratio of Online Budgeted Allocation is Strictly Smaller than 1-1/e*, arXiv:2610.41136 (held version, sha256 913d8f02…), §3.2, p.4). -/
noncomputable def numAlive {N d : ℕ} (part : PartitionRule N d) (s : Seed N d)
    (t : Fin (numItems N d)) : ℕ :=
  (Finset.univ.filter fun j => alive part s t j).card

open Classical in
/-- The input of `D_{N,d}` built from the seed `s` and the partition rule `part`
(Panigrahi–Zhang, *The Competitive Ratio of Online Budgeted Allocation is Strictly Smaller than 1-1/e*, arXiv:2610.41136 (held version, sha256 913d8f02…), §2, pp.2–3). Every advertiser has budget `1`.

* First phase, item `t < N/3`: every remaining advertiser bids `3/4`.
* Middle phase, round `g` (items `N/3 + 3g + c`): item 1 (`c = 0`) — all `d` advertisers of group
  `g` bid `1`; item 2 (`c = 1`) — they all bid `1/2`; item 3 (`c = 2`) — the `d/2` advertisers of
  `A_g` (if `coin g`) or of `B_g` (otherwise) bid `1/2`. All other advertisers bid `0`.
* Final phase: every remaining advertiser bids `1`.

Removed advertisers bid `0` on all later items. -/
noncomputable def inputD {N d : ℕ} (part : PartitionRule N d) (s : Seed N d) :
    Instance N (numItems N d) where
  B := fun _ => 1
  b := fun t j =>
    if t.val < numFirst N then (if alive part s t j then 3 / 4 else 0)
    else if t.val < numFirst N + 3 * numGroups N d then
      (if hg : (t.val - numFirst N) / 3 < numGroups N d then
        (if (t.val - numFirst N) % 3 = 0 then
          (if ∃ h i, part s.removed1 ⟨_, hg⟩ h i = j then 1 else 0)
        else if (t.val - numFirst N) % 3 = 1 then
          (if ∃ h i, part s.removed1 ⟨_, hg⟩ h i = j then 1 / 2 else 0)
        else
          (if ∃ i, part s.removed1 ⟨_, hg⟩ (s.coin ⟨_, hg⟩) i = j then 1 / 2 else 0))
      else 0)
    else (if alive part s t j then 1 else 0)

end OnlineBudgetAlloc


