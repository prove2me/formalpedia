-- Prove2me | Definitions.Def_MatSemiBurnside_IsProdRepr
-- name    : MatSemiBurnside_IsProdRepr
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:37:24.79166+00:00
-- url     : https://prove2.me/theorems/7d4ddb9d-160d-409c-8a18-57889f7fc3d2
-- title:
--   Words over $X$ representing a class, and the diameter bound of $\langle X\rangle/\sim$
-- statement:
--   Let $X\subseteq\mathrm{Mat}_d(\mathbb Q)$ be finite and $\sim$ a congruence on $\langle X\rangle$.
--
--   1. A **word** $a_1\cdots a_k$ over $X$ ($k\ge1$, $a_i\in X$) **represents** a class $q$ of $\langle X\rangle/\sim$ when the product $a_1\cdots a_k\in\langle X\rangle$ lies in $q$.
--   2. The **length** of a class is the least $k\ge1$ such that the class is represented by a word of length $k$. The **diameter** of $\langle X\rangle/\sim$ is the least $n\in\mathbb N$ such that every class has length at most $n$ (infinite if there is none).
--   3. The diameter is at most $n$ exactly when every $a\in\langle X\rangle$ satisfies $a\sim a_1\cdots a_k$ for some $a_1,\dots,a_k\in X$ with $1\le k\le n$.
--
--   These notions measure how long a product of generators must be to reach every class of the quotient.
--
--   **Formalization Note** A word is a nonempty `List` of matrices in $X$ and its product is `List.prod` in the matrix monoid. `DiameterLE X c n` is item 3.
-- source:
--   Guttenberg, Lhote, Shirmohammadi, Worrell, Burnside Problems for Matrix Semigroup Quotients with Applications to Border Complexity, STOC 2027 submission (held version, sha256 1bc61d4e…), §2, p.6

import Mathlib
set_option autoImplicit false

namespace MatSemiBurnside

/-- **A word over X representing a congruence class.** Guttenberg, Lhote, Shirmohammadi, Worrell, *Burnside Problems for Matrix Semigroup Quotients
with Applications to Border Complexity*, STOC 2027 submission (held version, sha256 1bc61d4e…), §2, p.6: "the class of a has length
equal to the least positive integer k such that a ∼ a1 · · · ak with ai ∈ X."

`IsProdRepr X c l q` says that `l = [a₁, …, a_k]` is a nonempty list of elements of X whose
product a₁ ⋯ a_k (an element of ⟨X⟩) lies in the class `q` of ⟨X⟩/∼.

**Formalization Note.** The product is `List.prod` in the matrix monoid; for a nonempty list of
elements of X it is the nonempty product a₁ ⋯ a_k and lies in ⟨X⟩ = `Subsemigroup.closure X`,
whose membership proof is carried as an existential. -/
def IsProdRepr {d : ℕ} (X : Finset (Matrix (Fin d) (Fin d) ℚ))
    (c : Con (Subsemigroup.closure (X : Set (Matrix (Fin d) (Fin d) ℚ))))
    (l : List (Matrix (Fin d) (Fin d) ℚ)) (q : c.Quotient) : Prop :=
  l ≠ [] ∧ (∀ x ∈ l, x ∈ X) ∧
    ∃ h : l.prod ∈ Subsemigroup.closure (X : Set (Matrix (Fin d) (Fin d) ℚ)),
      ((⟨l.prod, h⟩ : Subsemigroup.closure (X : Set (Matrix (Fin d) (Fin d) ℚ))) : c.Quotient) = q

/-- **Diameter of ⟨X⟩/∼ at most n.** Guttenberg, Lhote, Shirmohammadi, Worrell, *Burnside Problems for Matrix Semigroup Quotients
with Applications to Border Complexity*, STOC 2027 submission (held version, sha256 1bc61d4e…), §2, p.6: "The diameter of ⟨X⟩/∼ with respect to X/∼ is
the least n ∈ N such that every class has length at most n, and is infinite if no such n exists."

`DiameterLE X c n` says every class has length at most n: every a ∈ ⟨X⟩ is congruent to a
product a₁ ⋯ a_k of k elements of X with 1 ≤ k ≤ n. The diameter is at most n exactly when
`DiameterLE X c n` holds. -/
def DiameterLE {d : ℕ} (X : Finset (Matrix (Fin d) (Fin d) ℚ))
    (c : Con (Subsemigroup.closure (X : Set (Matrix (Fin d) (Fin d) ℚ)))) (n : ℕ) : Prop :=
  ∀ a : Subsemigroup.closure (X : Set (Matrix (Fin d) (Fin d) ℚ)),
    ∃ l : List (Matrix (Fin d) (Fin d) ℚ), l.length ≤ n ∧ IsProdRepr X c l (a : c.Quotient)

end MatSemiBurnside


