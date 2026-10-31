-- Prove2me | Definitions.Def_TractableComposite_mergeTwo
-- name    : TractableComposite_mergeTwo
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:51:12.296474+00:00
-- url     : https://prove2.me/theorems/a836c767-9e7b-4ddc-9207-8dc55b62f49b
-- title:
--   Ticked stable merge of two sorted lists
-- statement:
--   Merges two lists of index pairs $(i,j)$, each in non-increasing order of $\bar z_{ij}$, with one ticked comparison per output element. On a tie the head of the left list is output first; this realizes the tie rule of Algorithm 1 (lines 5–6).
-- source:
--   He & Tawarmalani, Tractable relaxations of composite functions (manuscript, sha256 8c6bca18…), Corollary 1's proof, p.13 ("d-way merge sort")

import Mathlib
import Definitions.Def_LNTopology_Hermetization_tick
import Definitions.Def_LNTopology_Hermetization_rle

namespace TractableComposite

/-- **Ticked stable merge of two lists of coordinates of z̄**, Corollary 1's proof, p.13 ("d sorted lists, each
of size n, can be merged in O(dn log d) time using the d-way merge sort algorithm"). He & Tawarmalani, *Tractable relaxations of composite functions* (manuscript, sha256 8c6bca18…), p.13.

Each list holds pairs `(i, j)` standing for `z̄ᵢⱼ`, in non-increasing order of `z̄ᵢⱼ`. Each call compares the
two heads with one ticked comparison and outputs the head of the **left** list unless the right head is
strictly larger; so on ties the left list goes first (the tie rule of Algorithm 1, lines 5–6, reading
R4). An empty side costs one tick and returns the other list.

**Cost model** (reading R3; the published discipline of `LNTopology.Hermetization.tick`): every real
arithmetic operation (`radd`, `rsub`, `rmul`, `rdiv`), every real comparison (`rle`, `req`) and every
query of `φ` (`phiAt`) costs one tick; every iteration of every loop and every recursive call ticks at
least once, and the unticked work inside one iteration is a bounded number of reads and updates of
array-like state (`Fin d → Fin (n+1) → ℝ`, `Fin d → Fin (n+1)`, `Fin d → Fin (n+1) → Bool`, the head of
a list, index arithmetic on `ℕ`/`Fin`); the only decisions on real data are the ticked primitives; the
program never reads the counter. The running time of a run started at `0` is the final counter. -/
noncomputable def mergeTwo {d n : ℕ} (z : Fin d → Fin (n + 1) → ℝ) :
    List (Fin d × Fin (n + 1)) → List (Fin d × Fin (n + 1)) → StateM ℕ (List (Fin d × Fin (n + 1)))
  | [], ys => do
    LNTopology.Hermetization.tick 1
    pure ys
  | x :: xs, [] => do
    LNTopology.Hermetization.tick 1
    pure (x :: xs)
  | x :: xs, y :: ys => do
    let takeLeft ← LNTopology.Hermetization.rle (z y.1 y.2) (z x.1 x.2)
    if takeLeft then
      let r ← mergeTwo z xs (y :: ys)
      pure (x :: r)
    else
      let r ← mergeTwo z (x :: xs) ys
      pure (y :: r)
termination_by xs ys => xs.length + ys.length

end TractableComposite


