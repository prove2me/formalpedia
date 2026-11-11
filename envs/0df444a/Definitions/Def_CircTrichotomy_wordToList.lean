-- Prove2me | Definitions.Def_CircTrichotomy_wordToList
-- name    : CircTrichotomy_wordToList
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:57:48.194736+00:00
-- url     : https://prove2.me/theorems/dcd5d9ab-2b9e-4b68-98a3-205fb1e3f305
-- title:
--   Non-empty words: the free semigroup $\Sigma^+$, letters and letter replacement
-- statement:
--   The free semigroup $\Sigma^+$ consists of the non-empty finite words over $\Sigma$, with concatenation. A word $x=x_0x_1\cdots x_{|x|-1}$ has positions starting at $0$; $(x)_i=x_i$ is its letter at position $i$, and
--   $$x[i\leftarrow a]=x_0\cdots x_{i-1}\,a\,x_{i+1}\cdots x_{|x|-1}$$
--   is the word obtained by replacing the letter at position $i$ by $a$.
--
--   These operations are used in the identities of $\mathbf X$, the exchange principle and the lower-bound witness.
--
--   **Formalization Note** Stamps are morphisms from Mathlib's `FreeSemigroup α`; `wordToList` converts a non-empty word to a list (languages are sets of lists), and turns products into concatenation.
-- source:
--   Göller, Manuel, A Circuit Complexity Trichotomy For Regular Languages, arXiv:2611.03615 (version of November 3, 2026, sha256 5bef1791…), §A.1, p.16 and p.7

import Mathlib

set_option autoImplicit false

namespace CircTrichotomy

/-- The non-empty word `x ∈ α⁺` (an element of the free semigroup `FreeSemigroup α`) as a list
`x₀ x₁ … x_{|x|−1}` (Göller, Manuel, *A Circuit Complexity Trichotomy For Regular Languages*,
arXiv:2611.03615 (version of November 3, 2026, sha256 5bef1791…), §A.1, p.16: Σ⁺ is the set of
non-empty finite words, positions start at 0).

**Formalization Note** Stamps are semigroup morphisms from `FreeSemigroup α` (= α⁺ with
concatenation); languages are sets of lists. `wordToList` is the bridge. -/
def wordToList {α : Type} (x : FreeSemigroup α) : List α := x.head :: x.tail

/-- `wordToList` turns the product of the free semigroup into concatenation. -/
theorem wordToList_mul {α : Type} (x y : FreeSemigroup α) :
    wordToList (x * y) = wordToList x ++ wordToList y := by
  simp [wordToList]

/-- The list has the word's length. -/
theorem length_wordToList {α : Type} (x : FreeSemigroup α) :
    (wordToList x).length = x.length := rfl

/-- The letter `(x)ᵢ` at position `i` of a non-empty word (p.7: "(w)ᵢ = wᵢ"); for `i ≥ |x|` the
value is the first letter (never used out of range). -/
def letterAt {α : Type} (x : FreeSemigroup α) (i : ℕ) : α := (wordToList x).getD i x.head

/-- The word `x[i ← a]` obtained from `x` by replacing the letter at position `i` by `a`
(p.7: "w[i ← a] = w₀ … w_{i−1} a w_{i+1} … w_{n−1}"); for `i ≥ |x|` it is `x`. -/
def setAt {α : Type} (x : FreeSemigroup α) (i : ℕ) (a : α) : FreeSemigroup α :=
  match i with
  | 0 => ⟨a, x.tail⟩
  | i + 1 => ⟨x.head, x.tail.set i a⟩

end CircTrichotomy


