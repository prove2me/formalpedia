-- Prove2me | Definitions.Def_MultiAccessLogspace_Halting_Rulers
-- name    : MultiAccessLogspace_Halting_Rulers
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:58:35.793003+00:00
-- url     : https://prove2.me/theorems/e3728389-bc2a-4f65-a256-efb8a4facf50
-- title:
--   Definitions 3.2, 3.6 — hyporulers and hyperrulers
-- statement:
--   Fix natural numbers $d,b$ with $b\ge1$. A **hyporuler** at depth zero is the empty list. At depth $d+1$ it is a nonempty list of at most $b$ depth-$d$ hyporuler blocks joined by single separators $d+1$.
--
--   Definition 3.2 states: “Let d ≥ 0 and b ≥ 1. A (d, b)-hyporuler is a sequence of the form h⃗ = (h⃗^(1), d, h⃗^(2), d, . . . , d, h⃗^(t)), (1) where t ≤ b and each h⃗^(i) is a (d − 1, b)-hyporuler. In the base case, when d = 0, the empty sequence is the unique (0, b)-hyporuler.”
--
--   A **hyperruler** at depth zero is any finite list of zeros. At depth $d+1$, it has exactly $b$ depth-$d$ hyperruler blocks separated by $d+1$, followed directly by a tail whose entries are in $\{0,\ldots,d+1\}$.
--
--   Definition 3.6 states: “Let d ≥ 0 and b ≥ 1. A (d, b)-hyperruler is a sequence of the form h⃗ = (h⃗^(1), d, h⃗^(2), d, . . . , d, h⃗^(b), z⃗), where each h⃗^(i) is a (d − 1, b)-hyperruler and z⃗ is an arbitrary sequence of elements of {0, 1, . . . , d}. In the base case, when d = 0, a (0, b)-hyperruler is an arbitrary-length sequence of zeroes.”
--
--   For a list $h_1,\ldots,h_N$, define $i_j$ as the last index at most $j$ with $h_{i_j}>h_j$, or zero when there is no such index. The characterization predicate is
--   $$
--   \forall j\in\{1,\ldots,N\},\quad \#\{k:i_j<k\le j,\ h_k=h_j\}\le b-1.
--   $$
--   A list with values in $\mathbb N\cup\{\infty\}$ is a hyporuler only when all entries are finite and its underlying natural list is a hyporuler. These predicates support the two generation bounds and the finite-length bound; no probabilistic theorem is assumed in their definitions.
-- source:
--   William M. Hoza, STOC 2027 submission #92 (October 2026), Definition 3.2 and Lemma 3.3; Definition 3.6 on PDF p. 8, PDF p. 7 (printed p. 6); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/92.pdf; PDF SHA-256 92de35889559d87b5a77d83317b9c7b2c8924912fbd5c712f2af3c005c8998d8

import Mathlib

/-!
Hoza, STOC 2027 submission #92: hyporulers (Definition 3.2, PDF p. 7) and hyperrulers
(Definition 3.6, PDF p. 8).
-/

namespace MultiAccessLogspace.Halting

/-- `h` is a `(d, b)`-hyporuler (Definition 3.2). The empty sequence is the unique
`(0, b)`-hyporuler. A `(d + 1, b)`-hyporuler has the form
`(h⁽¹⁾, d + 1, h⁽²⁾, d + 1, …, d + 1, h⁽ᵗ⁾)` with `1 ≤ t ≤ b` and each block a
`(d, b)`-hyporuler. (`t = 0` would add nothing: `t = 1` with an empty block is the same sequence.)
-/
def IsHyporuler (b : ℕ) : ℕ → List ℕ → Prop
  | 0, h => h = []
  | d + 1, h =>
    ∃ blocks : List (List ℕ),
      blocks ≠ [] ∧ blocks.length ≤ b ∧
      (∀ B ∈ blocks, IsHyporuler b d B) ∧
      h = List.intercalate [d + 1] blocks

/-- `h` is a `(d, b)`-hyperruler (Definition 3.6). A `(0, b)`-hyperruler is any sequence of zeros.
A `(d + 1, b)`-hyperruler has the form `(h⁽¹⁾, d + 1, …, d + 1, h⁽ᵇ⁾, z)` with exactly `b` blocks,
each a `(d, b)`-hyperruler, followed directly by an arbitrary sequence `z` of elements of
`{0, …, d + 1}`. -/
def IsHyperruler (b : ℕ) : ℕ → List ℕ → Prop
  | 0, h => ∀ a ∈ h, a = 0
  | d + 1, h =>
    ∃ (blocks : List (List ℕ)) (z : List ℕ),
      blocks.length = b ∧
      (∀ B ∈ blocks, IsHyperruler b d B) ∧
      (∀ a ∈ z, a ≤ d + 1) ∧
      h = List.intercalate [d + 1] blocks ++ z

/-- The entry `h_k` of `h = (h_1, …, h_N)`, indexed from `1` as in the source. It is only used
for `1 ≤ k ≤ N`. -/
def entry (h : List ℕ) (k : ℕ) : ℕ := h.getD (k - 1) 0

/-- The largest `i ∈ [j]` with `h_i > h_j`, or `0` if no such `i` exists. -/
def lastGreater (h : List ℕ) (j : ℕ) : ℕ :=
  ((Finset.Icc 1 j).filter fun i => entry h j < entry h i).sup id

/-- Condition 2 of Lemma 3.3: for every `j ∈ [N]`, with `i = lastGreater h j`, the value `h_j`
appears at most `b - 1` times among `h_{i+1}, …, h_j`. -/
def HyporulerCondition (b : ℕ) (h : List ℕ) : Prop :=
  ∀ j ∈ Finset.Icc 1 h.length,
    ((Finset.Icc (lastGreater h j + 1) j).filter fun k => entry h k = entry h j).card ≤ b - 1

/-- A sequence with values in `ℕ ∪ {∞}` is a `(d, b)`-hyporuler when no entry is `∞` and the
underlying sequence of naturals is one. -/
def IsHyporulerENat (b d : ℕ) (h : List ℕ∞) : Prop :=
  ∃ l : List ℕ, h = l.map (fun a : ℕ => (a : ℕ∞)) ∧ IsHyporuler b d l

end MultiAccessLogspace.Halting


