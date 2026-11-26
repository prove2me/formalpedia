-- Prove2me | Definitions.Def_bsv_merkle_tree
-- name    : bsv_merkle_tree
-- status  : Definition
-- author  : @GregoryJWard
-- created : 2026-11-26T11:40:03.316976+00:00
-- url     : https://prove2.me/theorems/2641619b-6225-464f-9f6c-1beea1bcc6cf
-- title:
--   Merkle tree levels, branches and branch folding
-- statement:
--   Binary Merkle trees over a list of nodes of an arbitrary type, with a combining function $H$ about which nothing is assumed.
--
--   1. `level`: adjacent pairs $a, b$ become $H(a, b)$; an unpaired last node $a$ becomes $H(a, a)$.
--   2. `root`: `none` for the empty list, `some a` for the one-element list $[a]$, and otherwise the root of the next level.
--   3. `sib`: the entry at position $i \oplus 1$ (exclusive or) of a level, or `none` if that position is past the end.
--   4. `branch`: empty for a list of at most one element; otherwise the sibling of position $i$, followed by the branch of position $\lfloor i/2 \rfloor$ in the next level.
--   5. `fold`: starting from a value $h$ at position $i$, each branch entry replaces $h$ by $H(h, h)$ if the entry is `none`, by $H(x, h)$ if it is $x$ and $i$ is odd, and by $H(h, x)$ if it is $x$ and $i$ is even; then $i$ is replaced by $\lfloor i/2 \rfloor$.
--
--   This is a model written for reasoning; it is not a transcription of any particular implementation.
-- source:
--   Gregory J. Ward, Bryan W. Daugherty, Shawn M. Ryan, BSV Lean proofs (Apache-2.0). https://github.com/codenlighten/bsv-lean-proofs/blob/41c4bfdc5ce4dd9bfbf0e21c77e6586d041261de/BsvLeanProofs/Merkle.lean

/-!
Authors: Gregory J. Ward, Bryan W. Daugherty, Shawn M. Ryan.
Source: https://github.com/codenlighten/bsv-lean-proofs (41c4bfd), Apache-2.0.
-/

namespace Bsv.Merkle

variable {α : Type} (H : α → α → α)

/-- One level up. -/
def level : List α → List α
  | [] => []
  | [a] => [H a a]
  | a :: b :: t => H a b :: level t

theorem length_level : ∀ l : List α, (level H l).length = (l.length + 1) / 2
  | [] => by simp [level]
  | [_] => by simp [level]
  | _ :: _ :: t => by
    simp only [level, List.length_cons, length_level t]
    omega

/-- The root; `none` only for the empty list. -/
def root : List α → Option α
  | [] => none
  | [a] => some a
  | a :: b :: t => root (level H (a :: b :: t))
termination_by l => l.length
decreasing_by simp only [length_level, List.length_cons]; omega

/-- The entry at position `i ^^^ 1`, or `none` if that is past the end (in
particular when `i` is the unpaired last node, which is combined with
itself). -/
def sib (l : List α) (i : Nat) : Option α := l[i ^^^ 1]?

/-- The branch of the leaf at position `i`. -/
def branch : List α → Nat → List (Option α)
  | [], _ => []
  | [_], _ => []
  | a :: b :: t, i => sib (a :: b :: t) i :: branch (level H (a :: b :: t)) (i / 2)
termination_by l => l.length
decreasing_by simp only [length_level, List.length_cons]; omega

/-- One verifier step. -/
def step (h : α) (s : Option α) (i : Nat) : α :=
  match s with
  | none => H h h
  | some x => if i % 2 = 1 then H x h else H h x

/-- Recompute a root from a leaf, its branch and its position. -/
def fold : α → List (Option α) → Nat → α
  | h, [], _ => h
  | h, s :: br, i => fold (step H h s i) br (i / 2)

end Bsv.Merkle


