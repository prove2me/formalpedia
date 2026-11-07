-- Prove2me | Definitions.Def_DynBrooks_MatchingWalk
-- name    : DynBrooks_MatchingWalk
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T04:05:18.430392+00:00
-- url     : https://prove2.me/theorems/25891b64-82e6-455b-987f-a974918da6db
-- title:
--   §6.2 — matchings, the random walk to a free right vertex, loop erasure
-- statement:
--   A bipartite graph has finite sets $L$ (left) and $R$ (right) and, for each left vertex $x$, the set of right vertices incident to it. A **matching** assigns to some right vertices a left vertex incident to it, with no left vertex used twice. A right vertex is **free** if it is unmatched.
--
--   **The walk** (p.67): "Keep the matching fixed during the walk. From the current left vertex, select an incident right vertex uniformly. If it is free, stop. Otherwise, move to its matched left vertex and repeat." The definition gives $P[\tau>s]$, the probability that the first $s$ selections from a given start are all matched right vertices, by the exact law of the walk; the sequences of selections of a walk that stops; **loop erasure** of such a sequence (a selection already on the stack removes everything above it); and **augmenting paths** (alternating, through distinct right vertices, from the root to a free right vertex).
--
--   **Formalization Note** Parallel hyperedges keep separate right vertices (p.66), so a set of incident right vertices per left vertex loses nothing.
-- source:
--   Mishra, Mukherjee, Fully Dynamic Brooks Coloring (STOC 2027 submission, preprint, sha256 6542a9f18a48e0b539c2aadee984a641d38a01a551fd32d5fa4d4c5164e32d7b), §6.2, pp.66–67 (PDF 68–69)

import Mathlib

namespace DynBrooks

/-! # The random walk of Lemma 6.1

Mishra, Mukherjee, *Fully Dynamic Brooks Coloring* (STOC 2027 submission, sha256 6542a9f1…), §6.2,
p.67 (PDF 69): "Keep the matching fixed during the walk. From the current left vertex, select an
incident right vertex uniformly. If it is free, stop. Otherwise, move to its matched left vertex and
repeat." "To obtain an augmenting path, erase loops from the stopped walk."

**Formalization Note.** A bipartite graph is `adj : L → Finset R` (right vertices incident to a left
vertex); parallel hyperedges are separate right vertices (p.66), so this form loses nothing. A matching
is `mate : R → Option L`, injective on matched right vertices, with `y ∈ adj x` whenever
`mate y = some x`. -/

variable {L R : Type} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]

/-- `mate` is a matching of the bipartite graph `adj`. -/
def IsMatching (adj : L → Finset R) (mate : R → Option L) : Prop :=
  (∀ y x, mate y = some x → y ∈ adj x) ∧ ∀ y y' x, mate y = some x → mate y' = some x → y = y'

/-- `P[τ > s]` from left vertex `x`: the probability that the first `s` selections are all matched
right vertices. -/
noncomputable def survive (adj : L → Finset R) (mate : R → Option L) : ℕ → L → ℝ
  | 0, _ => 1
  | s + 1, x =>
      ((adj x).card : ℝ)⁻¹ *
        ∑ y ∈ adj x,
          match mate y with
          | none => 0
          | some x' => survive adj mate s x'

/-- `ys` is the sequence of right vertices selected by a walk from `x` that stops: every selection is
incident to the current left vertex, every selection but the last is matched (and the walk moves to
its mate), and the last is free. -/
def IsStoppedWalk (adj : L → Finset R) (mate : R → Option L) : L → List R → Prop
  | _, [] => False
  | x, [y] => y ∈ adj x ∧ mate y = none
  | x, y :: y' :: ys =>
      y ∈ adj x ∧ ∃ x', mate y = some x' ∧ IsStoppedWalk adj mate x' (y' :: ys)

/-- Loop erasure with a stack (most recent first): a selection already on the stack removes everything
above it; a new one is pushed. A repeated left vertex is reached through its unique matched right
vertex, so testing right vertices is testing left vertices. -/
def eraseLoops (ys : List R) : List R :=
  ys.foldl (fun st y => if y ∈ st then st.dropWhile (· ≠ y) else y :: st) []

/-- `ys` (in visit order) is an augmenting path from `x`: it alternates between non-matching edges
and matching edges through distinct right vertices and ends at a free right vertex. -/
def IsAugmentingPath (adj : L → Finset R) (mate : R → Option L) (x : L) (ys : List R) : Prop :=
  ys.Nodup ∧ IsStoppedWalk adj mate x ys

end DynBrooks


