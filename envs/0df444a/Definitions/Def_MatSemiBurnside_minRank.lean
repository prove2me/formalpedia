-- Prove2me | Definitions.Def_MatSemiBurnside_minRank
-- name    : MatSemiBurnside_minRank
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:37:35.064625+00:00
-- url     : https://prove2.me/theorems/f748f1d4-86d9-4581-8952-a69a392cd218
-- title:
--   Minimum rank $\rho(c)$ of a congruence class
-- statement:
--   Let $X\subseteq\mathrm{Mat}_d(\mathbb Q)$ be finite and $\sim$ a congruence on $\langle X\rangle$. For a class $c$ of $\langle X\rangle/\sim$,
--   $$\rho(c) := \min\{\operatorname{rank}(a) : a\in c\}.$$
--
--   Congruent matrices can have different ranks; the proof of Theorem 1 counts classes by decreasing induction on $\rho$.
--
--   **Formalization Note** Written as the infimum of a set of natural numbers; every class contains an element, so the set is nonempty and the infimum is attained.
-- source:
--   Guttenberg, Lhote, Shirmohammadi, Worrell, Burnside Problems for Matrix Semigroup Quotients with Applications to Border Complexity, STOC 2027 submission (held version, sha256 1bc61d4e…), Appendix B, p.30

import Mathlib
set_option autoImplicit false

namespace MatSemiBurnside

/-- **Minimum rank of a congruence class.** Guttenberg, Lhote, Shirmohammadi, Worrell, *Burnside Problems for Matrix Semigroup Quotients
with Applications to Border Complexity*, STOC 2027 submission (held version, sha256 1bc61d4e…), Appendix B, p.30: "for each equivalence class c,
define ρ(c) := min{rank(a) : a ∈ c}."

`minRank c q` is the least rank of a matrix in the class `q` of ⟨X⟩/∼.

**Formalization Note.** Written as `sInf` of a set of naturals. Every class of a quotient
contains an element, so the set is nonempty and `sInf` is its minimum. -/
noncomputable def minRank {d : ℕ} {X : Finset (Matrix (Fin d) (Fin d) ℚ)}
    (c : Con (Subsemigroup.closure (X : Set (Matrix (Fin d) (Fin d) ℚ)))) (q : c.Quotient) : ℕ :=
  sInf {k : ℕ | ∃ a : Subsemigroup.closure (X : Set (Matrix (Fin d) (Fin d) ℚ)),
    (a : c.Quotient) = q ∧ (a : Matrix (Fin d) (Fin d) ℚ).rank = k}

end MatSemiBurnside


