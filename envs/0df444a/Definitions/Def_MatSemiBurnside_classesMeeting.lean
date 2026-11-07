-- Prove2me | Definitions.Def_MatSemiBurnside_classesMeeting
-- name    : MatSemiBurnside_classesMeeting
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:39:09.874299+00:00
-- url     : https://prove2.me/theorems/258c1a01-2d68-4e21-8063-3947dc7f2248
-- title:
--   Classes of $\langle X\rangle/\sim$ met by a set, and the uniform bound on stable subsemigroups
-- statement:
--   Let $X\subseteq\mathrm{Mat}_d(\mathbb Q)$ be finite, let $\langle X\rangle$ be the semigroup of all nonempty products of matrices from $X$, and let $\sim$ be a **congruence** on $\langle X\rangle$: an equivalence relation with $a_1\sim b_1$, $a_2\sim b_2\Rightarrow a_1a_2\sim b_1b_2$.
--
--   1. For a set $S$ of matrices, the classes of $\langle X\rangle/\sim$ **met** by $S$ are the classes containing an element of $S$. For a subsemigroup $S\le\langle X\rangle$, their number is the size $|S/\sim|$ of the quotient of $S$ by the restriction of $\sim$; it may be infinite.
--   2. For a natural number $N$, the **uniform bound $N$ on stable subsemigroups** holds when
--   $$|S/\sim|\le N\quad\text{for every stable subsemigroup } S\le\langle X\rangle.$$
--
--   The uniform bound is the hypothesis of Theorem 1 and the standing assumption of its proof.
--
--   **Formalization Note** $\langle X\rangle$ is `Subsemigroup.closure X` and $\sim$ is a `Con` on it. $|S/\sim|$ is the `Set.encard` of the set of classes met, a value in $\mathbb N\cup\{\infty\}$, so a stable subsemigroup meeting infinitely many classes violates every bound. $S$ ranges over all subsemigroups of $\mathrm{Mat}_d(\mathbb Q)$ contained in $\langle X\rangle$ that are stable sets: empty, infinite and non-finitely-generated ones included.
-- source:
--   Guttenberg, Lhote, Shirmohammadi, Worrell, Burnside Problems for Matrix Semigroup Quotients with Applications to Border Complexity, STOC 2027 submission (held version, sha256 1bc61d4e…), §2, p.6; Theorem 1, p.3

import Mathlib
import Definitions.Def_MatSemiBurnside_IsStableSet
set_option autoImplicit false

namespace MatSemiBurnside

/-- **Classes of ⟨X⟩/∼ met by a set S.** Guttenberg, Lhote, Shirmohammadi, Worrell, *Burnside Problems for Matrix Semigroup Quotients
with Applications to Border Complexity*, STOC 2027 submission (held version, sha256 1bc61d4e…), §2, p.6: "For a subsemigroup S ≤ ⟨X⟩, we write
S/∼ for the quotient by the restriction of ∼ to S; its size counts the classes of ⟨X⟩/∼ that
meet S."

Here ⟨X⟩ is `Subsemigroup.closure X` (all nonempty products of elements of X), `c` is a
congruence on ⟨X⟩ and `classesMeeting c S` is the set of classes `q` of ⟨X⟩/∼ containing an
element of `S`. Its `Set.encard` is |S/∼|.

**Formalization Note.** |S/∼| is `(classesMeeting c S).encard`, a value in ℕ ∪ {∞}; an infinite
S/∼ has size ∞, never 0. -/
def classesMeeting {d : ℕ} {X : Finset (Matrix (Fin d) (Fin d) ℚ)}
    (c : Con (Subsemigroup.closure (X : Set (Matrix (Fin d) (Fin d) ℚ))))
    (S : Set (Matrix (Fin d) (Fin d) ℚ)) : Set c.Quotient :=
  {q | ∃ a : Subsemigroup.closure (X : Set (Matrix (Fin d) (Fin d) ℚ)),
    (a : Matrix (Fin d) (Fin d) ℚ) ∈ S ∧ (a : c.Quotient) = q}

/-- **Uniform bound N on stable subsemigroups.** Guttenberg, Lhote, Shirmohammadi, Worrell, *Burnside Problems for Matrix Semigroup Quotients
with Applications to Border Complexity*, STOC 2027 submission (held version, sha256 1bc61d4e…), Theorem 1, p.3: "|S/∼| ≤ N for every stable
subsemigroup S ≤ ⟨X⟩" (the hypothesis of Theorem 1, and the standing assumption of Appendix B,
p.29).

**Formalization Note.** S ranges over all subsemigroups of the matrix semigroup Mat_d(ℚ)
contained in ⟨X⟩ (empty, infinite and non-finitely-generated ones included) that are stable sets.
|S/∼| is a `Set.encard`, so an S meeting infinitely many classes violates the bound. -/
def UniformStableBound {d : ℕ} (X : Finset (Matrix (Fin d) (Fin d) ℚ))
    (c : Con (Subsemigroup.closure (X : Set (Matrix (Fin d) (Fin d) ℚ)))) (N : ℕ) : Prop :=
  ∀ S : Subsemigroup (Matrix (Fin d) (Fin d) ℚ),
    S ≤ Subsemigroup.closure (X : Set (Matrix (Fin d) (Fin d) ℚ)) →
    IsStableSet (S : Set (Matrix (Fin d) (Fin d) ℚ)) →
    (classesMeeting c (S : Set (Matrix (Fin d) (Fin d) ℚ))).encard ≤ (N : ℕ∞)

end MatSemiBurnside


