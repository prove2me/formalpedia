-- Prove2me | Definitions.Def_DynSort_rebuild
-- name    : DynSort_rebuild
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:33:53.010946+00:00
-- url     : https://prove2.me/theorems/01d8fac0-921c-42c7-8244-5a0d8969b57b
-- title:
--   The ReBuild operation, and the counters of an execution
-- statement:
--   **ReBuild** reconstructs a level-$L$ section $D$. A level-$1$ section is sorted. For $L=i+1\ge2$: if the block sizes of $D$ satisfy the Block Sizes invariant they are kept; otherwise $D$ becomes a single block if $|D|\le11\cdot2^i$, and three blocks otherwise, with a middle block of exactly $2^i$ cells, a last block of
--   $$\max\Bigl\{8\cdot2^i,\ \Bigl\lceil\tfrac{|D|-2^i}{2}\Bigr\rceil\Bigr\}$$
--   cells and a first block of the remaining cells. The stored elements are sorted and distributed in increasing order among the original sections, the transfer section is made empty, the hole (if any) is treated as the largest element so that it occupies the last cell, and ReBuild recurses into every original section down to level $1$.
--
--   The same module defines the counters of an execution of the DST and A-DST operations: the element movements excluding ReBuild, the recourse of ReBuild (the number of stored elements whose cell changed), the number of SwapHole calls, and a log of the ReBuild recourse and SwapHole count after every SwapHole call.
--
--   **Formalization Note** When a kept three-block division had a nonempty transfer section, its middle original section is created anew, since it now receives all $2^i$ cells of the middle block. A variant puts the hole first instead of last: the convention of p.25 for the component that receives a hole.
-- source:
--   Azar, Bhore, Dey, Panigrahi, Vardi, Zhang, Online and Fully-Dynamic Sorting, STOC 2027 submission (manuscript sha256 da7f0d5ef6191ccaa6c70faec62234592c6d108cd2357bda3e5b6dac010acf6c), §4.4, p.14 (PDF p.16); hole-first convention, §5.2, p.25 (PDF p.27)

import Mathlib
import Definitions.Def_DynSort_Sec

namespace DynSort

/-! # The ReBuild operation, and the state and counters of the DST operations

Y. Azar, S. Bhore, D. Dey, D. Panigrahi, O. Vardi, I. Zhang, *Online and Fully-Dynamic Sorting*,
STOC 2027 submission (manuscript sha256 da7f0d5e…), §4.4, p.14 (PDF p.16); hole-first convention,
§5.2, p.25 (PDF p.27).

ReBuild, verbatim (p.14): "For a level-1 DST, we simply sort its stored elements. For a
level-(i + 1) DST D, where i ≥ 1, we first consider the sizes of its constituent blocks. If they
satisfy the Block Sizes invariant, we preserve the number and sizes of these blocks, but not
necessarily their contents. Otherwise, we choose a new block division as follows: if |D| ≤ 11·2^i,
we create a single block. Otherwise, we create three blocks, where the middle contains exactly 2^i
cells, the last contains max{8·2^i, ⌈(|D| − 2^i)/2⌉} cells, and the first contains the remaining
cells. In either case, we sort all the elements of D and distribute them among the original
sections of the blocks in increasing order, according to the designated block sizes. The transfer
section of the middle block, if present, is made empty. If D contains a hole, we treat it as the
largest element, so that it occupies the last cell of D. As before, the hole counts toward block
sizes. We then apply ReBuild recursively to each original section, rebuilding its constituent DST
all the way down to level 1. This recursion is performed regardless of whether the block division
was changed."

**Formalization Note.**
* `fill L s cells` lays the sorted cell list `cells` into a level-`L` section, keeping the block
  sizes of the old section `s` when they are valid for these cells (`none`: a newly created
  section). When a kept three-block division had a nonempty transfer section, its middle original
  section is created anew, since it receives all `2^{L−1}` cells of the middle block.
* `rebuildSec L holeFirst S` sorts the stored elements of `S`, puts the hole last (first when
  `holeFirst`, the convention of p.25 for the component receiving a hole), and calls `fill`. It
  also returns the number of stored elements whose absolute cell changed: the recourse of this
  ReBuild.
* `Ctr` holds the counters of an execution: `moves` (element movements excluding ReBuild, as in
  Claims 15–21), `rebuildMoves` (ReBuild recourse), `swaps` (SwapHole calls) and `swapLog`, the
  pair `(rebuildMoves, swaps)` recorded after every SwapHole call. `St` is a root with counters.
-/

variable {α : Type}

/-- Counters of an execution of the DST / A-DST operations. -/
structure Ctr where
  moves : ℕ := 0
  rebuildMoves : ℕ := 0
  swaps : ℕ := 0
  swapLog : List (ℕ × ℕ) := []
  deriving Repr

/-- A root section together with the counters. -/
structure St (α : Type) where
  root : Sec α
  ctr : Ctr := {}

/-- The Block Sizes invariant at the top of a level-`L` section (its blocks have level `L − 1`). -/
def blockSizesOk (L : ℕ) : Sec α → Bool
  | .leaf _ => true
  | .single O => decide (O.size ≤ 12 * 2 ^ (L - 1))
  | .three O1 T2 O2 O3 =>
      let q := 2 ^ (L - 1)
      decide (T2.size + O2.size = q ∧ q ≤ O1.size ∧ O1.size < 12 * q ∧
        7 * q ≤ O3.size ∧ O3.size < 12 * q)

/-- Lay the cells `cells` (sorted, hole placed) into a level-`L` section, keeping the valid block
division of the old section `s` (p.14). -/
def fill : ℕ → Option (Sec α) → List (Option α) → Sec α
  | 0, _, cells => .leaf cells
  | 1, _, cells => .leaf cells
  | L + 2, s, cells =>
    let q := 2 ^ (L + 1)
    let D := cells.length
    let fresh : Unit → Sec α := fun _ =>
      if D ≤ 11 * q then .single (fill (L + 1) none cells)
      else
        let Lb := max (8 * q) ((D - q + 1) / 2)
        let F := D - q - Lb
        .three (fill (L + 1) none (cells.take F)) (fill (L + 1) none [])
          (fill (L + 1) none ((cells.drop F).take q)) (fill (L + 1) none (cells.drop (F + q)))
    match s with
    | some (.single O) =>
      if O.size = D ∧ D ≤ 12 * q then .single (fill (L + 1) (some O) cells) else fresh ()
    | some (.three O1 T2 O2 O3) =>
      if (Sec.three O1 T2 O2 O3).size = D ∧ blockSizesOk (L + 2) (.three O1 T2 O2 O3) = true then
        let F := O1.size
        .three (fill (L + 1) (some O1) (cells.take F)) (fill (L + 1) none [])
          (fill (L + 1) (if T2.size = 0 then some O2 else none) ((cells.drop F).take q))
          (fill (L + 1) (some O3) (cells.drop (F + q)))
      else fresh ()
    | _ => fresh ()

/-- **ReBuild** of a level-`L` section (p.14): the rebuilt section and its recourse. -/
def rebuildSec [LinearOrder α] (L : ℕ) (holeFirst : Bool) (S : Sec α) : Sec α × ℕ :=
  let st := S.stored.mergeSort (fun a b => decide (a ≤ b))
  let nh := S.holes
  let cells : List (Option α) :=
    if holeFirst then List.replicate nh none ++ st.map some
    else st.map some ++ List.replicate nh none
  (fill L (some S) cells,
    ((S.flat.zip cells).filter (fun p => p.1.isSome && decide (p.1 ≠ p.2))).length)

/-- ReBuild of the level-`L` section at address `a` of the root, adding its recourse to
`rebuildMoves`. -/
def rebuildAt [LinearOrder α] (L : ℕ) (holeFirst : Bool) (a : List ℕ) (st : St α) : St α :=
  match st.root.get a with
  | none => st
  | some S =>
    let r := rebuildSec L holeFirst S
    { root := st.root.modify (fun _ => r.1) a,
      ctr := { st.ctr with rebuildMoves := st.ctr.rebuildMoves + r.2 } }

end DynSort


