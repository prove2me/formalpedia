-- Prove2me | Definitions.Def_MatSemiBurnside_IsStableSet
-- name    : MatSemiBurnside_IsStableSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:38:02.069704+00:00
-- url     : https://prove2.me/theorems/75f0388c-99c1-467c-a833-31965c16308d
-- title:
--   Rank-stable matrices, rank-stable sets and stable sets
-- statement:
--   Let $d$ be a positive integer and let kernels and images be those of the row action $x\mapsto xa$.
--
--   1. A matrix $a\in\mathrm{Mat}_d(\mathbb Q)$ is **rank-stable** if $\operatorname{rank}(a)=\operatorname{rank}(a^2)$.
--   2. A set $S\subseteq\mathrm{Mat}_d(\mathbb Q)$ is **rank-stable** if $\operatorname{rank}(a)=\operatorname{rank}(b)=\operatorname{rank}(ab)$ for all $a,b\in S$ (including $a=b$).
--   3. A rank-stable set is **stable** if all its elements have the same kernel and the same image.
--
--   For example, the nilpotent matrix $A=\begin{pmatrix}0&1\\0&0\end{pmatrix}$ is not rank-stable, so $\{A\}$ is not stable, while the matrices $A_x=\begin{pmatrix}1&x\\0&0\end{pmatrix}$, $A_y$ with $x\ne y$ form a rank-stable set that is not stable (different images). Any set of invertible matrices is stable.
--
--   Stable subsemigroups are the "group-like" pieces of a matrix semigroup on which Theorem 1 places its uniform bound.
--
--   **Formalization Note** The empty set is stable (vacuously).
-- source:
--   Guttenberg, Lhote, Shirmohammadi, Worrell, Burnside Problems for Matrix Semigroup Quotients with Applications to Border Complexity, STOC 2027 submission (held version, sha256 1bc61d4e…), §2, p.6 (and Example 1, p.6)

import Mathlib
import Definitions.Def_MatSemiBurnside_rowKer
set_option autoImplicit false

namespace MatSemiBurnside

/-- **Rank-stable matrix.** Guttenberg, Lhote, Shirmohammadi, Worrell, *Burnside Problems for Matrix Semigroup Quotients
with Applications to Border Complexity*, STOC 2027 submission (held version, sha256 1bc61d4e…), §2, p.6: "We call a rank-stable if rank(a) = rank(a²)." -/
def IsRankStable {d : ℕ} (a : Matrix (Fin d) (Fin d) ℚ) : Prop :=
  a.rank = (a ^ 2).rank

/-- **Rank-stable set.** Guttenberg, Lhote, Shirmohammadi, Worrell, *Burnside Problems for Matrix Semigroup Quotients
with Applications to Border Complexity*, STOC 2027 submission (held version, sha256 1bc61d4e…), §2, p.6: "A set X ⊆ Matd(F) is called rank-stable if
rank(a) = rank(b) = rank(ab) for all a, b ∈ X." The condition is required for all pairs,
including `a = b`. -/
def IsRankStableSet {d : ℕ} (S : Set (Matrix (Fin d) (Fin d) ℚ)) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, a.rank = b.rank ∧ b.rank = (a * b).rank

/-- **Stable set.** Guttenberg, Lhote, Shirmohammadi, Worrell, *Burnside Problems for Matrix Semigroup Quotients
with Applications to Border Complexity*, STOC 2027 submission (held version, sha256 1bc61d4e…), §2, p.6: "A rank-stable set is called stable if all its elements have
the same kernel and the same image."

**Formalization Note.** Kernels and images are those of the row action `x ↦ xa`
(`rowKer`, `rowIm`). The empty set is stable (vacuously). -/
def IsStableSet {d : ℕ} (S : Set (Matrix (Fin d) (Fin d) ℚ)) : Prop :=
  IsRankStableSet S ∧ ∀ a ∈ S, ∀ b ∈ S, rowKer a = rowKer b ∧ rowIm a = rowIm b

end MatSemiBurnside


