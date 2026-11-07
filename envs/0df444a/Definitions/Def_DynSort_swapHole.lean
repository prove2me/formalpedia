-- Prove2me | Definitions.Def_DynSort_swapHole
-- name    : DynSort_swapHole
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:34:40.104568+00:00
-- url     : https://prove2.me/theorems/aed24c18-e2dd-4ab4-83fe-47afb2aa5c13
-- title:
--   The SwapHole operation, its repair step, and SwapHole between components
-- statement:
--   **SwapHole $(D,D')$** transfers a hole between adjacent sections without moving any element. In the right-to-left form used inside a DST, $D=O_2$ holds the hole in its first cell and $D'=T_2$ is its left neighbour: the cell leaves the chain of first original sections of $D$ and becomes the last cell of the chain of last original sections of $D'$.
--
--   The **repair step** then examines the affected sections (the two chains) and their ancestors, from highest level to lowest. A section requires repair if a Block Sizes invariant fails at its top or it has three blocks and its middle original section stores no element. The highest-level section requiring repair is rebuilt, or its parent when it is the last original section of a three-block parent; this repeats until no examined section requires repair.
--
--   Between two adjacent components of an A-DST, the hole leaves the end of the left component and becomes the first cell of the right one; each component is repaired independently, and in the receiving component the hole is treated as the smallest element.
--
--   **Formalization Note** Sections are tracked by address. Among several highest-level sections requiring repair, the first in the order root, then down each chain, is taken; a rebuilt section satisfies the invariants and never requires repair again, so the loop runs at most once per examined section. Every call adds one to the SwapHole count and is recorded in the log.
-- source:
--   Azar, Bhore, Dey, Panigrahi, Vardi, Zhang, Online and Fully-Dynamic Sorting, STOC 2027 submission (manuscript sha256 da7f0d5ef6191ccaa6c70faec62234592c6d108cd2357bda3e5b6dac010acf6c), §4.4, p.15 (PDF p.17); §5.2, pp.24–25 (PDF pp.26–27)

import Mathlib
import Definitions.Def_DynSort_rebuild

namespace DynSort

/-! # The SwapHole operation and its repair step

Y. Azar, S. Bhore, D. Dey, D. Panigrahi, O. Vardi, I. Zhang, *Online and Fully-Dynamic Sorting*,
STOC 2027 submission (manuscript sha256 da7f0d5e…), §4.4, p.15 (PDF p.17); between components,
§5.2, pp.24–25 (PDF pp.26–27).

Verbatim (p.15): "1. Let D and D′ denote the DSTs supplying and receiving the hole, respectively.
Suppose D is immediately to the left of D′, and its last cell h contains the hole. We remove h from
D and make it the first cell of D′. This is done recursively along the chains of last original
sections of D and first original sections of D′, down to level 1. A transfer in the opposite
direction is symmetric. 2. After transferring the hole, we examine the affected sections and their
ancestors, from highest level to lowest. A section requires repair if a Block Size invariant is
violated or if it has three blocks and its middle original section becomes empty. Let S be the
highest-level section requiring repair. We apply ReBuild to S, unless S is the last original
section of a three-block parent P, in which case we rebuild P instead. […] We repeat until all
affected sections satisfy the structural invariants."

Between components (p.25): "When rebuilding a section in D′ containing the hole, we treat the hole
as the smallest element, leaving it in the first cell rather than the last."

**Formalization Note.**
* `swapHole d aD aD' st` is SwapHole (D, D′) from right to left inside a level-`d` root: `D` at
  address `aD` holds the hole in its first cell, which leaves the chain of first original sections
  of `D` and becomes the last cell of the chain of last original sections of `D′` at `aD'`, its
  left neighbour. All uses in §4.5 are of this form, (O₂, T₂) of a three-block section.
* The affected sections are these two chains; with their ancestors they are examined in the order
  root first, then down each chain (`D`'s first). The repair step rebuilds the highest-level
  section requiring repair (the first of them in that order), or its parent when it is the last
  original section (index 3) of a three-block parent, and repeats while one requires repair.
  Sections are tracked by address; a rebuilt section satisfies the invariants, so it never requires
  repair again. The loop runs at most once per examined section, plus one final check.
* Every call adds one to `swaps` and appends `(rebuildMoves, swaps)` to `swapLog`.
* If the first cell of `D` is not the hole, nothing happens.
-/

variable {α : Type}

namespace Sec

/-- Addresses of the chain of first original sections, from the section at `a` down to level 1. -/
def chainFirstAddrs : Sec α → List ℕ → List (List ℕ)
  | .leaf _, a => [a]
  | .single O, a => a :: O.chainFirstAddrs (a ++ [0])
  | .three O1 _ _ _, a => a :: O1.chainFirstAddrs (a ++ [0])

/-- Addresses of the chain of last original sections, from the section at `a` down to level 1. -/
def chainLastAddrs : Sec α → List ℕ → List (List ℕ)
  | .leaf _, a => [a]
  | .single O, a => a :: O.chainLastAddrs (a ++ [0])
  | .three _ _ _ O3, a => a :: O3.chainLastAddrs (a ++ [3])

/-- The first cell of the level-1 section at the end of the chain of first original sections. -/
def firstChainHead : Sec α → Option (Option α)
  | .leaf c => c.head?
  | .single O => O.firstChainHead
  | .three O1 _ _ _ => O1.firstChainHead

/-- The last cell of the level-1 section at the end of the chain of last original sections. -/
def lastChainLast : Sec α → Option (Option α)
  | .leaf c => c.getLast?
  | .single O => O.lastChainLast
  | .three _ _ _ O3 => O3.lastChainLast

/-- Remove the first cell along the chain of first original sections. -/
def popFirstChain : Sec α → Sec α
  | .leaf c => .leaf c.tail
  | .single O => .single O.popFirstChain
  | .three O1 T2 O2 O3 => .three O1.popFirstChain T2 O2 O3

/-- Remove the last cell along the chain of last original sections. -/
def popLastChain : Sec α → Sec α
  | .leaf c => .leaf c.dropLast
  | .single O => .single O.popLastChain
  | .three O1 T2 O2 O3 => .three O1 T2 O2 O3.popLastChain

/-- Add a first cell along the chain of first original sections. -/
def pushFirstChain (x : Option α) : Sec α → Sec α
  | .leaf c => .leaf (x :: c)
  | .single O => .single (O.pushFirstChain x)
  | .three O1 T2 O2 O3 => .three (O1.pushFirstChain x) T2 O2 O3

/-- Add a last cell along the chain of last original sections. -/
def pushLastChain (x : Option α) : Sec α → Sec α
  | .leaf c => .leaf (c ++ [x])
  | .single O => .single (O.pushLastChain x)
  | .three O1 T2 O2 O3 => .three O1 T2 O2 (O3.pushLastChain x)

end Sec

/-- A level-`L` section requires repair (p.15): a Block Size invariant fails at its top, or it has
three blocks and its middle original section stores no element. -/
def requiresRepair (L : ℕ) : Sec α → Bool
  | .leaf _ => false
  | .single O => !blockSizesOk L (.single O)
  | .three O1 T2 O2 O3 => !blockSizesOk L (.three O1 T2 O2 O3) || O2.stored.isEmpty

/-- The addresses of a section and its ancestors, root first. -/
def prefixes (a : List ℕ) : List (List ℕ) := (List.range (a.length + 1)).map a.take

/-- Remove repetitions, keeping first occurrences. -/
def orderedUnion (l : List (List ℕ)) : List (List ℕ) :=
  l.foldl (fun acc x => if x ∈ acc then acc else acc ++ [x]) []

/-- One repair step in a level-`d` root (p.15, step 2): rebuild the highest-level examined section
requiring repair, or its parent if it is the last original section of a three-block parent. -/
def repairStep [LinearOrder α] (d : ℕ) (holeFirst : Bool) (seen : List (List ℕ)) (st : St α) :
    Option (St α) :=
  let bad := seen.filter (fun p =>
    match st.root.get p with
    | some S => requiresRepair (d - p.length) S
    | none => false)
  match bad with
  | [] => none
  | b :: bs =>
    let p := bs.foldl (fun best x => if x.length < best.length then x else best) b
    let tgt := if p.getLast? = some 3 then p.dropLast else p
    let hs := holeFirst && (match st.root.get tgt with
      | some S => decide (S.holes ≠ 0)
      | none => false)
    some (rebuildAt (d - tgt.length) hs tgt st)

/-- Repeat the repair step until no examined section requires repair (at most `fuel` steps). -/
def repair [LinearOrder α] (d : ℕ) (holeFirst : Bool) (seen : List (List ℕ)) :
    ℕ → St α → St α
  | 0, st => st
  | k + 1, st =>
    match repairStep d holeFirst seen st with
    | none => st
    | some st' => repair d holeFirst seen k st'

/-- Record a SwapHole call in the counters. -/
def Ctr.logSwap (c : Ctr) : Ctr := { c with swapLog := c.swapLog ++ [(c.rebuildMoves, c.swaps)] }

/-- **SwapHole (D, D′) from right to left** (p.15) in a level-`d` root: the hole in the first cell
of the section `D` at `aD` becomes the last cell of its left neighbour `D′` at `aD'`, followed by
the repair step. -/
def swapHole [LinearOrder α] (d : ℕ) (aD aD' : List ℕ) (st : St α) : St α :=
  match st.root.get aD, st.root.get aD' with
  | some D, some D' =>
    if D.firstChainHead = some none then
      let r := (st.root.modify Sec.popFirstChain aD).modify (Sec.pushLastChain none) aD'
      let seen := orderedUnion
        ((D.chainFirstAddrs aD ++ D'.chainLastAddrs aD').flatMap prefixes)
      let st1 := repair d false seen (seen.length + 1)
        { root := r, ctr := { st.ctr with swaps := st.ctr.swaps + 1 } }
      { st1 with ctr := st1.ctr.logSwap }
    else st
  | _, _ => st

/-- **SwapHole between adjacent A-DST components** (§5.2, pp.24–25): the level-`kD` component `D`
ends with the hole, which becomes the first cell of the level-`kD'` component `D′` to its right;
each component is repaired independently, the hole counted as the smallest element in `D′`. -/
def swapHoleComp [LinearOrder α] (kD kD' : ℕ) (D D' : Sec α) (c : Ctr) :
    Sec α × Sec α × Ctr :=
  if D.lastChainLast = some none then
    let seenD := orderedUnion ((D.chainLastAddrs []).flatMap prefixes)
    let st1 := repair kD false seenD (seenD.length + 1)
      { root := D.popLastChain, ctr := { c with swaps := c.swaps + 1 } }
    let seenD' := orderedUnion ((D'.chainFirstAddrs []).flatMap prefixes)
    let st2 := repair kD' true seenD' (seenD'.length + 1)
      { root := D'.pushFirstChain none, ctr := st1.ctr }
    (st1.root, st2.root, st2.ctr.logSwap)
  else (D, D', c)

end DynSort


