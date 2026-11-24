-- Prove2me | Definitions.Def_KernelRamsey_Mask
-- name    : KernelRamsey_Mask
-- status  : Definition
-- author  : @@bwdaugherty
-- created : 2026-11-24T16:26:36.2886+00:00
-- url     : https://prove2.me/theorems/705f06df-0a5e-4c17-880e-2003cc49ef12
-- title:
--   Bit-mask encoding of graphs and a fuel-bounded clique search
-- statement:
--   A graph on vertices $0,\dots,n-1$ is encoded by a list of $n$ natural numbers: bit $j$ of entry $i$ is set when $j$ is a neighbour of $i$. This module defines the row lookup, the mask of the lowest $n$ bits, the structurally recursive clique search `noClique` (fuel, clique size, candidate mask), the clique predicate on rows, the simple graph given by symmetric rows, and the rows of the complement graph.
-- source:
--   B. W. Daugherty, G. Ward and S. Ryan, Kernel-Evaluated Ramsey Bounds in Lean 4, version 1.0.0, 2026, doi:10.5281/zenodo.24505785.

import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Tactic

namespace KernelRamsey

/-- Entry `i` of the list, or `0` outside the list. -/
def row (rows : List Nat) (i : Nat) : Nat := rows.getD i 0

/-- The bit mask with the lowest `n` bits set. -/
def fullMask (n : Nat) : Nat := 2 ^ n - 1

/-- Search for a `k`-clique among the candidates `cand`; `true` certifies that there is none. -/
def noClique (rows : List Nat) : Nat → Nat → Nat → Bool
  | 0, k, cand => match k with
      | 0 => false
      | _ + 1 => cand == 0
  | f + 1, k, cand => match k with
      | 0 => false
      | k' + 1 =>
          if cand == 0 then true
          else
            let p := Nat.log2 cand
            noClique rows f k' ((cand ^^^ 2 ^ p) &&& row rows p) &&
              noClique rows f (k' + 1) (cand ^^^ 2 ^ p)

/-- A finite set of vertices is a clique of the mask graph when every ordered pair of distinct
members is joined by a set bit. -/
def IsMaskClique {n : Nat} (rows : List Nat) (S : Finset (Fin n)) : Prop :=
  ∀ i ∈ S, ∀ j ∈ S, i ≠ j → (row rows i.val).testBit j.val = true

/-- The graph given by the mask rows, with edges `i ~ j` when `i ≠ j` and bit `j` of row `i` is
set. It is a simple graph when the rows are symmetric. -/
def maskGraph (n : Nat) (rows : List Nat)
    (hsymm : ∀ i j : Fin n, (row rows i.val).testBit j.val = (row rows j.val).testBit i.val) :
    SimpleGraph (Fin n) where
  Adj i j := i ≠ j ∧ (row rows i.val).testBit j.val = true
  symm := ⟨fun i j ⟨h, hb⟩ => ⟨h.symm, by rw [← hsymm i j]; exact hb⟩⟩
  loopless := ⟨fun i ⟨h, _⟩ => h rfl⟩

/-- Rows of the complement graph: bit `j` of row `i` is set when `j ≠ i` and `j` is not a
neighbour of `i`. -/
def complementRows (n : Nat) (rows : List Nat) : List Nat :=
  (List.range n).map fun i => (fullMask n ^^^ row rows i) &&& (fullMask n ^^^ 2 ^ i)

end KernelRamsey


