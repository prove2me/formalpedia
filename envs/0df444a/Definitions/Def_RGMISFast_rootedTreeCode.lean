-- Prove2me | Definitions.Def_RGMISFast_rootedTreeCode
-- name    : RGMISFast_rootedTreeCode
-- status  : Definition
-- author  : @srikkanthr
-- created : 2026-11-15T22:26:04.786208+00:00
-- url     : https://prove2.me/theorems/5868ec2e-573a-465d-9afa-82a1b81286c4
-- title:
--   Depth-first decoder for rooted connected-set tree codes
-- statement:
--   A rooted tree code consists of a binary word of length $2j$ and $j$ neighbour indices in $\{0,\ldots,\Delta-1\}$. The decoder starts at the root with a stack and the singleton visited set. A descent bit consumes a neighbour index, follows that entry in the current vertex's fixed adjacency-list order, and adds the new vertex to the stack and visited set. A return bit removes the current stack entry. The output is the visited vertex set.
--
--   The decoder is total: a missing neighbour skips that descent, and a descent with an empty stack or no remaining label terminates. Completeness for connected sets is a separate theorem, not part of the definition.
--
--   **Formalization note.** This implements the paper's ordered rooted spanning-tree encoding by its depth-first descent/return word. Counting all binary words over-approximates the Catalan family of valid shapes. The adjacency-list order is the fixed order supplied by `Finset.toList`; no linear order on vertices is assumed.
-- source:
--   Dalirrooyfard, Makarychev, Mitrović, Ramachandran, Randomized Greedy MIS Is Fast at Every Node, Appendix A, proof of Lemma A.2, printed p.29 (PDF p.31), manuscript sha256 e93cdfecc03618969d5f2ecf8171c6f84c528edcc473b2f864299e555f823664.

import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.OfFn
set_option autoImplicit false
namespace RGMISFast

/-- Execute a depth-first traversal code. `true` descends to the next labelled
neighbour; `false` returns to the parent on the stack. Invalid descents terminate
or skip the step as specified below. No validity claim about arbitrary codes is made. -/
noncomputable def rootedTreeCodeRun {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℕ) :
    List Bool → List (Fin Δ) → List V → Finset V → Finset V := by
  classical
  exact fun bits labels stack seen =>
    match bits with
    | [] => seen
    | false :: rest => rootedTreeCodeRun G Δ rest labels stack.tail seen
    | true :: rest =>
      match labels, stack with
      | label :: remaining, v :: parents =>
        match (G.neighborFinset v).toList[label.val]? with
        | none => rootedTreeCodeRun G Δ rest remaining (v :: parents) seen
        | some w => rootedTreeCodeRun G Δ rest remaining (w :: v :: parents) (insert w seen)
      | _, _ => seen
termination_by bits => bits.length

/-- The set decoded from `2j` descent/return bits and `j` neighbour labels.
The root is initially visited; adjacency lists use the fixed `Finset.toList` order.
This is the depth-first binary-word encoding of the ordered rooted tree in the
proof of Lemma A.2 (Appendix A, printed p.29). -/
noncomputable def rootedTreeCode {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℕ) (u : V) (j : ℕ)
    (shape : Fin (2*j) → Bool) (labels : Fin j → Fin Δ) : Finset V := by
  classical
  exact rootedTreeCodeRun G Δ (List.ofFn shape) (List.ofFn labels) [u] {u}

end RGMISFast


