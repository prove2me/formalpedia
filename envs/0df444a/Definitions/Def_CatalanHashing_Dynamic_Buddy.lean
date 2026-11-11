-- Prove2me | Definitions.Def_CatalanHashing_Dynamic_Buddy
-- name    : CatalanHashing_Dynamic_Buddy
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T05:05:32.414791+00:00
-- url     : https://prove2.me/theorems/c14bc554-0065-47b2-9774-3d7f48e2a506
-- title:
--   The buddy allocator over strided subarrays B_{k,a} of the backup table
-- statement:
--   The backup table $B$ has $m_B=2^K$ cells. For $0\le k\le K$ and $0\le a<2^k$, the **subarray** $B_{k,a}$ consists of the cells $a,\ a+2^k,\ a+2\cdot2^k,\dots$; it has depth $k$ and density $2^{-k}$, and $B_{k',a'}\subseteq B_{j,a}$ iff $j\le k'$ and $a'\equiv a\pmod{2^j}$.
--
--   **Allocation** of a subarray of density $2^{-k}$ ($k\le K$): let $j\le k$ be the largest depth at which some free subarray exists, and let $Q$ be any free subarray at depth $j$. Allocate any depth-$k$ subarray inside $Q$; the rest of $Q$, one subarray at each depth $j+1,\dots,k$ (the sibling of each ancestor of the allocated subarray below $Q$), stays free. Initially $B=B_{0,0}$ is free and nothing is allocated; subarrays are never freed. A state is **reachable** if some sequence of successful allocations, with any admissible choices, leads to it from the initial state. The **allocated density** of a state is $\sum_{B_{k,a}\ \mathrm{allocated}}2^{-k}$.
--
--   **Formalization Note.** A subarray is the pair $(k,a)$; a state is the list of free and the list of allocated subarrays. `AllocStep K s k s'` holds for every admissible choice of $Q$ and of the allocated subarray.
-- source:
--   Conway, Komlós, Kuszmaul, Catalan Hashing: Efficient Linear Probing for Variable-Length Items, arXiv:2611.05235 (copy sha256 e2048176…), p. 21, Section 6.3 (Allocating Subarrays)

import Mathlib

/-!
# The buddy allocator over strided subarrays (Section 6.3)

Conway, Komlós, Kuszmaul, *Catalan Hashing: Efficient Linear Probing for Variable-Length Items*,
arXiv:2611.05235 (copy sha256 e2048176…), p. 21, Section 6.3 ("Allocating Subarrays").

The backup table `B` has `m_B = 2^K` cells. For `0 ≤ k ≤ K` and `0 ≤ a < 2^k` the subarray
`B_{k,a}` consists of the cells `a, a + 2^k, a + 2·2^k, …`; its depth is `k` and its density
`2^{-k}`. A subarray is written as the pair `(k, a)`. `B_{k',a'}` lies inside `B_{j,a}` iff
`j ≤ k'` and `a' ≡ a (mod 2^j)`.

To allocate a subarray of density `2^{-k}`: let `j ≤ k` be the largest depth at which some free
subarray exists and let `Q` be any free subarray at depth `j`; allocate any depth-`k` subarray
`B_{k,a'}` inside `Q`; the rest of `Q`, one subarray at each depth `j + 1, …, k` (the sibling at
depth `d + 1` of the depth-`(d + 1)` ancestor of `B_{k,a'}`), remains free. The choices of `Q`
and of `a'` are arbitrary (`AllocStep` allows every choice). Subarrays are never freed.
Initially the whole of `B` (`B_{0,0}`) is free.
-/

namespace CatalanHashing.Dynamic

/-- The subarray `B_{k,a}`, as the pair `(k, a)`. -/
abbrev Subarray : Type := ℕ × ℕ

/-- `B_{s}` lies inside `B_{q}`. -/
def Subarray.Inside (s q : Subarray) : Prop :=
  q.1 ≤ s.1 ∧ s.2 % 2 ^ q.1 = q.2

/-- The other child of the depth-`d` subarray containing the depth-`(d + 1)` subarray with
offset `r < 2^(d+1)`. -/
def siblingOffset (d r : ℕ) : ℕ :=
  if r < 2 ^ d then r + 2 ^ d else r - 2 ^ d

/-- What remains free of a depth-`j` subarray after allocating `B_{k,a'}` inside it: one
subarray at each depth `j + 1, …, k`. -/
def remainderSubarrays (j k a' : ℕ) : List Subarray :=
  (List.range (k - j)).map (fun i => (j + i + 1, siblingOffset (j + i) (a' % 2 ^ (j + i + 1))))

/-- The allocator state: the free subarrays and the allocated ones. -/
structure BuddyState where
  /-- The free subarrays. -/
  free : List Subarray
  /-- The allocated subarrays. -/
  allocated : List Subarray

/-- Initially `B_{0,0}` (all of `B`) is free and nothing is allocated. -/
def BuddyState.init : BuddyState :=
  ⟨[(0, 0)], []⟩

/-- The total density `Σ 2^{-k}` of the allocated subarrays. -/
noncomputable def BuddyState.allocatedDensity (s : BuddyState) : ℝ :=
  (s.allocated.map (fun q => (1 / 2 : ℝ) ^ q.1)).sum

/-- One successful allocation of density `2^{-k}` (`k ≤ K`, where `m_B = 2^K`), with any
admissible choice of `Q` and of the allocated subarray. -/
def AllocStep (K : ℕ) (s : BuddyState) (k : ℕ) (s' : BuddyState) : Prop :=
  k ≤ K ∧
  ∃ q ∈ s.free, q.1 ≤ k ∧ (∀ q' ∈ s.free, q'.1 ≤ k → q'.1 ≤ q.1) ∧
    ∃ a', a' < 2 ^ k ∧ Subarray.Inside (k, a') q ∧
      s' = ⟨s.free.erase q ++ remainderSubarrays q.1 k a', (k, a') :: s.allocated⟩

/-- The states reachable from the initial state by successful allocations. -/
def BuddyReachable (K : ℕ) (s : BuddyState) : Prop :=
  Relation.ReflTransGen (fun s s' => ∃ k, AllocStep K s k s') BuddyState.init s

end CatalanHashing.Dynamic


