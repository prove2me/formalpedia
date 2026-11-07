-- Prove2me | Definitions.Def_OnlineBudgetAlloc_Seed
-- name    : OnlineBudgetAlloc_Seed
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:29:39.113913+00:00
-- url     : https://prove2.me/theorems/d529d330-f8a3-460f-b2e9-36ae75fd5696
-- title:
--   Seed of the random input $D_{N,d}$ and its phase sizes
-- statement:
--   The random input $D_{N,d}$ of §2 has three phases: a first phase of $N/3$ rounds, a middle phase of $M/d$ rounds with three items each ($M = 2N/3$), and a final phase of $R = M(1 - 2/d)$ rounds. It has $N/3 + 3M/d + R$ items in total.
--
--   All its randomness is a **seed** with five components:
--   1. a permutation giving the order in which the first phase removes advertisers;
--   2. for each middle-phase group $g$, a fair coin choosing whether $A_g$ or $B_g$ bids on the group's item 3;
--   3. for each group, the position of the advertiser removed from $A_g$;
--   4. for each group, the position of the advertiser removed from $B_g$;
--   5. a permutation that ranks the advertisers surviving the middle phase; the final phase removes them in this order.
--
--   $D_{N,d}$ is the input built from a uniformly random seed. Under the uniform law, each removal is uniform over the current remaining set (or over the current half), the coins are fair and independent, and none of this depends on the algorithm.
--
--   **Formalization Note** The module also defines the phase sizes `numFirst` $= N/3$, `numM` $= 2N/3$, `numGroups` $= M/d$, `numR` $= M - 2M/d$ and `numItems`, all with natural-number division, and the item indices `firstItem`, `midItem g c` (item $c+1$ of round $g$) and `finalItem`. Every theorem that uses them assumes the divisibility conditions of §2.
-- source:
--   Panigrahi, Zhang, The Competitive Ratio of Online Budgeted Allocation is Strictly Smaller than 1-1/e, arXiv:2610.41136 (held version, sha256 913d8f02…), §2, pp.2–3

import Mathlib

namespace OnlineBudgetAlloc

/-- The number `N/3` of rounds of the first phase of `D_{N,d}` (Panigrahi–Zhang, *The Competitive Ratio of Online Budgeted Allocation is Strictly Smaller than 1-1/e*, arXiv:2610.41136 (held version, sha256 913d8f02…), §2, p.2). -/
def numFirst (N : ℕ) : ℕ := N / 3

/-- The number `M := 2N/3` of advertisers remaining after the first phase (Panigrahi–Zhang, *The Competitive Ratio of Online Budgeted Allocation is Strictly Smaller than 1-1/e*, arXiv:2610.41136 (held version, sha256 913d8f02…), §2, p.2). -/
def numM (N : ℕ) : ℕ := 2 * N / 3

/-- The number `M/d` of groups (and of rounds) of the middle phase (Panigrahi–Zhang, *The Competitive Ratio of Online Budgeted Allocation is Strictly Smaller than 1-1/e*, arXiv:2610.41136 (held version, sha256 913d8f02…), §2, p.2). -/
def numGroups (N d : ℕ) : ℕ := 2 * N / 3 / d

/-- The number `R := M(1 − 2/d) = M − 2M/d` of advertisers remaining after the middle phase, which
is the number of rounds of the final phase (Panigrahi–Zhang, *The Competitive Ratio of Online Budgeted Allocation is Strictly Smaller than 1-1/e*, arXiv:2610.41136 (held version, sha256 913d8f02…), §2, p.3). -/
def numR (N d : ℕ) : ℕ := 2 * N / 3 - 2 * (2 * N / 3 / d)

/-- The number of items of `D_{N,d}`: `N/3` (first phase) `+ 3M/d` (middle phase) `+ R` (final
phase) (Panigrahi–Zhang, *The Competitive Ratio of Online Budgeted Allocation is Strictly Smaller than 1-1/e*, arXiv:2610.41136 (held version, sha256 913d8f02…), §2, pp.2–3). -/
def numItems (N d : ℕ) : ℕ := numFirst N + 3 * numGroups N d + numR N d

/-- The random seed of the input distribution `D_{N,d}` (Panigrahi–Zhang, *The Competitive Ratio of Online Budgeted Allocation is Strictly Smaller than 1-1/e*, arXiv:2610.41136 (held version, sha256 913d8f02…), §2, pp.2–3). `D_{N,d}` is the
law of the input built from a uniformly random seed.

* `ord1` — the first-phase removal order: after first-phase item `k`, advertiser `ord1 k` is
  removed.
* `coin g` — which half of group `g` bids on its item 3 (`true`: `A_g`, `false`: `B_g`).
* `remA g`, `remB g` — the position, inside the halves `A_g` and `B_g`, of the advertiser removed
  from that half at the end of the middle phase.
* `ord3` — ranks the advertisers surviving the middle phase: the final-phase item `u` is followed
  by the removal of the survivor of rank `u` (the one with the `u`-th smallest `ord3`-value).

**Formalization Note** Under the uniform law on `Seed N d`, each removal is uniform over the
current remaining set (respectively, the current half), the coins are fair and independent, and
all of it is independent of the algorithm: this is exactly the paper's law. -/
structure Seed (N d : ℕ) where
  /-- First-phase removal order. -/
  ord1 : Equiv.Perm (Fin N)
  /-- The half of each middle-phase group that bids on item 3 (`true` = `A_g`). -/
  coin : Fin (numGroups N d) → Bool
  /-- Which advertiser of `A_g` is removed in the middle phase. -/
  remA : Fin (numGroups N d) → Fin (d / 2)
  /-- Which advertiser of `B_g` is removed in the middle phase. -/
  remB : Fin (numGroups N d) → Fin (d / 2)
  /-- Final-phase removal ranks. -/
  ord3 : Equiv.Perm (Fin N)

/-- `Seed N d` is finite: it is in bijection with the product of its five fields. -/
instance Seed.instFintype (N d : ℕ) : Fintype (Seed N d) :=
  Fintype.ofEquiv
    (Equiv.Perm (Fin N) × (Fin (numGroups N d) → Bool) × (Fin (numGroups N d) → Fin (d / 2)) ×
      (Fin (numGroups N d) → Fin (d / 2)) × Equiv.Perm (Fin N))
    { toFun := fun x => ⟨x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2⟩
      invFun := fun s => (s.ord1, s.coin, s.remA, s.remB, s.ord3)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- The `k`-th item of the first phase (`k < N/3`), as an item of `D_{N,d}`. -/
def firstItem {N : ℕ} (d : ℕ) (k : Fin (numFirst N)) : Fin (numItems N d) :=
  ⟨k.val, by have := k.isLt; unfold numItems; omega⟩

/-- Item `c + 1` (`c = 0, 1, 2`) of round `g` of the middle phase, i.e. item
`N/3 + 3g + c` of `D_{N,d}`. -/
def midItem {N d : ℕ} (g : Fin (numGroups N d)) (c : Fin 3) : Fin (numItems N d) :=
  ⟨numFirst N + 3 * g.val + c.val, by have := g.isLt; have := c.isLt; unfold numItems; omega⟩

/-- The `u`-th item of the final phase (`u < R`), i.e. item `N/3 + 3M/d + u` of `D_{N,d}`. -/
def finalItem {N d : ℕ} (u : Fin (numR N d)) : Fin (numItems N d) :=
  ⟨numFirst N + 3 * numGroups N d + u.val, by have := u.isLt; unfold numItems; omega⟩

end OnlineBudgetAlloc


