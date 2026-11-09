-- Prove2me | Definitions.Def_DSICCompComp_IsFeasibleAlloc
-- name    : DSICCompComp_IsFeasibleAlloc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T13:29:02.538645+00:00
-- url     : https://prove2.me/theorems/3156a990-7a93-4d5d-9492-83268d44c2dd
-- title:
--   Feasible allocations of the affine maximizer
-- statement:
--   Fix $\ell \le m$ items sold by the affine maximizer and $r \le n$ **reserve** bidders $1,\dots,r$. A deterministic allocation $S = (S_1,\dots,S_n)$, where $S_i$ is the set of items given to bidder $i$, is **feasible** if
--   $$
--   \bigcup_i S_i \subseteq [\ell], \qquad S_i \cap S_h = \varnothing \ \ (i \ne h), \qquad |S_i| \le 2 \ \ (i \in [n]\setminus[r]).
--   $$
--   So the affine maximizer allocates only the first $\ell$ items, never gives an item to two bidders, and gives at most two items to each non-reserve bidder (reserve bidders may receive more).
--
--   **Formalization Note** Indices are 0-based: the items $[\ell]$ are $j < \ell$ and the reserve bidders $[r]$ are $i < r$.
-- source:
--   Ryu–Weinberg–Xue, The DSIC Competition Complexity of Additive Buyers over Independent Items, STOC 2027 submission (manuscript of Nov. 3, 2026, sha256 bf61bfdb…), §3.3, p.11 (pdf p.12)

import Mathlib

namespace DSICCompComp

/-- The allocation constraints of the affine maximizer of §3.3 (Ryu–Weinberg–Xue, *The DSIC
Competition Complexity of Additive Buyers over Independent Items*, STOC 2027 submission,
manuscript of Nov. 3, 2026, sha256 bf61bfdb…, §3.3, p.11 (pdf p.12)): a deterministic allocation
`S = (S_1, …, S_n)` (`S_i` the set of items given to bidder `i`) is feasible if
`∪_i S_i ⊆ [ℓ]`, `S_i ∩ S_h = ∅` for all `i ≠ h`, and `|S_i| ≤ 2` for every non-reserve bidder
`i ∈ [n] ∖ [r]`.

**Formalization Note** 0-based indices: the paper's items `[ℓ] = {1, …, ℓ}` are the items
`j : Fin m` with `j < ℓ`, and the paper's reserve bidders `[r]` are the bidders `i : Fin n` with
`i < r`. -/
def IsFeasibleAlloc {n m : ℕ} (ℓ r : ℕ) (S : Fin n → Finset (Fin m)) : Prop :=
  (∀ i, ∀ j ∈ S i, j.val < ℓ) ∧ (∀ i h, i ≠ h → Disjoint (S i) (S h)) ∧
    ∀ i : Fin n, r ≤ i.val → (S i).card ≤ 2

instance {n m : ℕ} (ℓ r : ℕ) : DecidablePred (IsFeasibleAlloc (n := n) (m := m) ℓ r) :=
  fun _ => by unfold IsFeasibleAlloc; infer_instance

end DSICCompComp


