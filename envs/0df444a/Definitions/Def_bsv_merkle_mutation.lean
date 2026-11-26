-- Prove2me | Definitions.Def_bsv_merkle_mutation
-- name    : bsv_merkle_mutation
-- status  : Definition
-- author  : @GregoryJWard
-- created : 2026-11-26T14:28:31.629835+00:00
-- url     : https://prove2.me/theorems/8290571d-5fe7-5e78-ad6b-d97d927f8930
-- title:
--   Duplicate-subtree flag of the pending-hash Merkle computation
-- statement:
--   The flag raised when, while adding a leaf, the computation combines a pending hash with an equal carried hash (the pattern of CVE-2012-2459; nothing is proved about that attack beyond naming the pattern), and the tree property it is compared with.
--
--   1. `insertMut` records whether, while a hash is carried up through the occupied slots, some pending hash equals the hash being carried.
--   2. `mutatedCS` is the disjunction of these comparisons over the insertion of all leaves. The final sweep compares nothing.
--   3. `eqPair` says that some complete adjacent pair (positions $0,1$; $2,3$; and so on) of a list has equal entries.
--   4. `mutatedTree` is `eqPair` on the list, or recursively on the list of its combined complete pairs. Thus only pairs of complete subtrees are examined.
--
--   **Formalization Note** This is a Lean model written for reasoning; nothing is claimed about any particular program.
-- source:
--   Gregory J. Ward, Bryan W. Daugherty, Shawn M. Ryan, BSV Lean proofs (Apache-2.0). https://github.com/codenlighten/bsv-lean-proofs

import Definitions.Def_bsv_merkle_counter
/-!
Authors: Gregory J. Ward, Bryan W. Daugherty, Shawn M. Ryan.
Source: https://github.com/codenlighten/bsv-lean-proofs (41c4bfd), Apache-2.0.
-/

namespace Bsv.Merkle

section

variable {α : Type} [DecidableEq α] (H : α → α → α)

/-- The comparisons made while one leaf is carried up: `inner[level] == hash`
at each occupied level it passes. -/
def insertMut (h : α) : List (Option α) → Bool
  | [] => false
  | none :: _ => false
  | some x :: s => x == h || insertMut (H x h) s

/-- The flag after adding the leaves of `l` to slots `s`. -/
def mutCounter : List α → List (Option α) → Bool
  | [], _ => false
  | a :: t, s => insertMut H a s || mutCounter t (insert H a s)

/-- The flag after all leaves have been added to empty slots. -/
def mutatedCS (l : List α) : Bool := mutCounter H l []

/-- Some complete pair of this level has two equal nodes. -/
def eqPair : List α → Bool
  | a :: b :: t => a == b || eqPair t
  | _ => false

/-- The tree-level meaning. `pairs` keeps exactly the nodes of the next level
that are roots of complete subtrees, so the recursion visits, at every level,
the pairs of complete subtrees and no others. -/
def mutatedTree : List α → Bool
  | a :: b :: t => eqPair (a :: b :: t) || mutatedTree (pairs H (a :: b :: t))
  | _ => false
termination_by l => l.length
decreasing_by simp only [length_pairs, List.length_cons]; omega

end

end Bsv.Merkle


