-- Prove2me | Definitions.Def_GT_multizeta
-- name    : GT_multizeta
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-13T21:09:39.456604+00:00
-- url     : https://prove2.me/theorems/ba2637f6-8d86-45b5-8fd3-22520a407c37
-- title:
--   Multiple zeta values, stuffle and shuffle products
-- statement:
--   This file defines **multiple zeta values** and the two products that relate them.
--
--   For a word $n_1 \cdots n_k$ of positive integers with $n_1 \ge 2$,
--
--   $$\zeta(n_1,\dots,n_k) = \sum_{j_1 > j_2 > \cdots > j_k \ge 1} \frac{1}{j_1^{n_1} j_2^{n_2}\cdots j_k^{n_k}}, \qquad \zeta(\,) = 1 .$$
--
--   The definition is by an iterated sum: an auxiliary function computes the tail sum over $m > j_2 > \cdots > j_k \ge 1$ for a bound $m$, and the outer sum ranges over $j_1 \ge 1$. A word is **admissible** when all its letters are at least $1$ and its first letter (if any) is at least $2$; exactly then does the series converge.
--
--   The **stuffle** (quasi-shuffle) product is defined recursively on words of positive integers by
--
--   $$n w \ \text{⧢}\ n' w' = n\,(w \ \text{⧢}\ n' w') + n'\,(n w \ \text{⧢}\ w') + (n+n')\,(w \ \text{⧢}\ w'),$$
--
--   and the **shuffle** product recursively on binary words in the letters $0, 1$ by
--
--   $$\alpha w * \alpha' w' = \alpha\,(w * \alpha' w') + \alpha'\,(\alpha w * w') .$$
--
--   Both products are recorded as multisets of words, which is exactly the multiplicity information needed for the corresponding relations among multiple zeta values. The passage between the two alphabets is the standard encoding $n_1 \cdots n_k \mapsto 0^{n_1-1}1 \cdots 0^{n_k-1}1$ and its inverse, which cuts a binary word into blocks ending in $1$; the zeta value of a binary word is the zeta value of the word of block lengths.
--
--   **Formalization Note.** Multiple zeta values are real numbers defined through Mathlib's `tsum`, which returns $0$ for a non-summable family; for non-admissible words the definition therefore returns a junk value, and every statement about these numbers carries an admissibility hypothesis. Binary words use `false` for the letter $0$ and `true` for the letter $1$. A binary word that does not end in $1$ has its trailing zeros discarded by the decoding map.
-- source:
--   Thomas Willwacher, The Grothendieck-Teichmüller Group, ETH Zürich lecture notes (in progress), 27 February 2014, Section 6.1, p. 53 (definition of multiple zeta values, stuffle product, Proposition 6.1, shuffle product, Proposition 6.2, Euler's identity zeta(2,1) = zeta(3))

import Mathlib

/-!
# Multiple zeta values, the stuffle product and the shuffle product

Willwacher, *The Grothendieck-Teichmüller Group* (ETH lecture notes, 27 Feb 2014),
Section 6.1, p. 53.
-/

namespace GrothendieckTeichmuller

noncomputable section

/-- Auxiliary tail sum: `mzvTail [n₂, …, n_k] m` is the sum of `∏ⱼ jⱼ^{-nⱼ}` over
`m > j₂ > ⋯ > j_k ≥ 1`. -/
def mzvTail : List ℕ → ℕ → ℝ
  | [], _ => 1
  | k :: ns, m => ∑' j : ℕ, if 1 ≤ j ∧ j < m then ((j : ℝ) ^ k)⁻¹ * mzvTail ns j else 0

/-- The multiple zeta value
`ζ(n₁, …, n_k) = ∑_{j₁ > j₂ > ⋯ > j_k ≥ 1} 1 / (j₁^{n₁} ⋯ j_k^{n_k})`,
with `ζ() = 1` for the empty word. For non-admissible words the defining series diverges and
this definition returns the junk value `0` coming from Mathlib's convention for `tsum`. -/
def mzv : List ℕ → ℝ
  | [] => 1
  | k :: ns => ∑' j : ℕ, if 1 ≤ j then ((j : ℝ) ^ k)⁻¹ * mzvTail ns j else 0

/-- A word `n₁ ⋯ n_k` of positive integers is admissible if it is empty or `n₁ ≥ 2`; all its
letters are required to be at least `1`. Exactly for admissible words the series defining
`ζ(n₁, …, n_k)` converges. -/
def IsAdmissible (u : List ℕ) : Prop :=
  (∀ k ∈ u, 1 ≤ k) ∧ ∀ k ∈ u.head?, 2 ≤ k

/-- The stuffle (quasi-shuffle) product of two words of positive integers, as a multiset of
words:
`n w ⧢ n' w' = n (w ⧢ n' w') + n' (n w ⧢ w') + (n + n') (w ⧢ w')`. -/
def stuffle : List ℕ → List ℕ → Multiset (List ℕ)
  | [], w => {w}
  | w, [] => {w}
  | a :: v, b :: w =>
      (stuffle v (b :: w)).map (fun z => a :: z) +
        (stuffle (a :: v) w).map (fun z => b :: z) +
        (stuffle v w).map (fun z => (a + b) :: z)
  termination_by v w => v.length + w.length

/-- The shuffle product of two binary words (letters `false = 0`, `true = 1`), as a multiset of
words: `α w ∗ α' w' = α (w ∗ α' w') + α' (α w ∗ w')`. -/
def shuffleBin : List Bool → List Bool → Multiset (List Bool)
  | [], w => {w}
  | w, [] => {w}
  | a :: v, b :: w =>
      (shuffleBin v (b :: w)).map (fun z => a :: z) +
        (shuffleBin (a :: v) w).map (fun z => b :: z)
  termination_by v w => v.length + w.length

/-- The binary encoding of a word of positive integers:
`n₁ ⋯ n_k ↦ 0^{n₁-1} 1 ⋯ 0^{n_k-1} 1`. -/
def compToBin : List ℕ → List Bool
  | [] => []
  | k :: ns => List.replicate (k - 1) false ++ true :: compToBin ns

/-- The inverse encoding: a binary word is cut into blocks each ending with `1`, and each block
`0^{m-1} 1` contributes the letter `m`. Trailing `0`s (i.e. words not ending in `1`) are
discarded. -/
def binToComp : List Bool → List ℕ
  | [] => []
  | true :: w => 1 :: binToComp w
  | false :: w =>
      match binToComp w with
      | [] => []
      | k :: ns => (k + 1) :: ns

/-- The multiple zeta value attached to a binary word, `ζ(0^{n₁-1} 1 ⋯ 0^{n_k-1} 1)
= ζ(n₁, …, n_k)`. -/
def mzvBin (w : List Bool) : ℝ := mzv (binToComp w)

end

end GrothendieckTeichmuller


