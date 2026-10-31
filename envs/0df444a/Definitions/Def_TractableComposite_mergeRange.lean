-- Prove2me | Definitions.Def_TractableComposite_mergeRange
-- name    : TractableComposite_mergeRange
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:52:11.996225+00:00
-- url     : https://prove2.me/theorems/f324198c-ffa1-4035-aa5a-bcdd9c8f7b28
-- title:
--   Divide-and-conquer merge of the rows of $\bar z$
-- statement:
--   Sorts the coordinates $\bar z_{ij}$, $j\ge1$, of rows $lo,\dots,lo+len-1$: a single row gives the list $(i,1),\dots,(i,n)$, built by a ticked loop; otherwise the lower and upper halves are sorted recursively and merged with the lower rows on the left. Ties therefore go to the smaller $i$ and, within a row, $j$ increases, so equal values of one row stay adjacent (Algorithm 1, lines 5–6). The recursion has depth $\lceil\log_2 len\rceil$, which gives the $O(dn\log d)$ cost of the sort.
-- source:
--   He & Tawarmalani, Tractable relaxations of composite functions (manuscript, sha256 8c6bca18…), Algorithm 1, lines 3–7, p.12, and Corollary 1's proof, p.13

import Mathlib
import Definitions.Def_LNTopology_Hermetization_tick
import Definitions.Def_TractableComposite_mergeTwo

namespace TractableComposite

/-- **Divide-and-conquer merge of the lists of rows `lo, …, lo+len−1`**, Algorithm 1, lines 3–7, p.12, and
Corollary 1's proof, p.13 ("d-way merge sort (see 5.4.1 in [19])"). He & Tawarmalani, *Tractable relaxations of composite functions* (manuscript, sha256 8c6bca18…), pp.12–13.

`mergeRange z lo len` returns, for one row `i = lo` (when `len = 1`, `lo < d`), the list
`[(i,1), …, (i,n)]` built by a ticked loop (the coordinate `z̄ᵢ₀ = 1` is left out: "z̄ᵢ₀ are sorted before z̄ᵢⱼ
for j ≠ 0", line 5); for `len ≥ 2` it merges the lower half `lo, …, lo+⌊len/2⌋−1` and the upper half with
`mergeTwo`, the lower rows on the left. Ties are therefore broken toward the smaller `i` and, within a
row, the order of `j` is kept, which realizes lines 5–6 (reading R4). The recursion depth is
`⌈log₂ len⌉`.

**Cost model** (reading R3; the published discipline of `LNTopology.Hermetization.tick`): every real
arithmetic operation (`radd`, `rsub`, `rmul`, `rdiv`), every real comparison (`rle`, `req`) and every
query of `φ` (`phiAt`) costs one tick; every iteration of every loop and every recursive call ticks at
least once, and the unticked work inside one iteration is a bounded number of reads and updates of
array-like state (`Fin d → Fin (n+1) → ℝ`, `Fin d → Fin (n+1)`, `Fin d → Fin (n+1) → Bool`, the head of
a list, index arithmetic on `ℕ`/`Fin`); the only decisions on real data are the ticked primitives; the
program never reads the counter. The running time of a run started at `0` is the final counter. -/
noncomputable def mergeRange {d n : ℕ} (z : Fin d → Fin (n + 1) → ℝ) (lo len : ℕ) :
    StateM ℕ (List (Fin d × Fin (n + 1))) :=
  if hlen : len ≤ 1 then do
    LNTopology.Hermetization.tick 1
    if h : lo < d ∧ len = 1 then
      let mut acc : List (Fin d × Fin (n + 1)) := []
      for jj in List.range n do
        LNTopology.Hermetization.tick 1
        acc := (⟨lo, h.1⟩, ⟨n - jj, by omega⟩) :: acc
      return acc
    else
      return []
  else do
    let l ← mergeRange z lo (len / 2)
    let r ← mergeRange z (lo + len / 2) (len - len / 2)
    mergeTwo z l r
termination_by len

end TractableComposite


