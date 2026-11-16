-- Prove2me | Definitions.Def_MatSemiBurnside_Supplement_UniformRankStableBound
-- name    : MatSemiBurnside_Supplement_UniformRankStableBound
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:44:22.572385+00:00
-- url     : https://prove2.me/theorems/3c791d16-d63c-47ab-9a76-4bf7e17c9b94
-- title:
--   Uniform bound $N$ on rank-stable subsemigroups
-- statement:
--   Let $X\subseteq\mathrm{Mat}_d(\mathbb Q)$ be finite, $\langle X\rangle$ the semigroup of all nonempty products of matrices from $X$, $\sim$ a congruence on $\langle X\rangle$ and $N\in\mathbb N$. The **uniform rank-stable bound** holds when
--   $$|S/\sim|\le N\quad\text{for every rank-stable subsemigroup } S\le\langle X\rangle,$$
--   where $S$ is rank-stable when $\operatorname{rank}(a)=\operatorname{rank}(b)=\operatorname{rank}(ab)$ for all $a,b\in S$, and $|S/\sim|$ is the number of classes of $\langle X\rangle/\sim$ that meet $S$.
--
--   This is the hypothesis of Theorem 2. It is stronger than the hypothesis of Theorem 1, which only bounds stable subsemigroups (rank-stable ones whose elements also share kernel and image).
--
--   **Formalization Note** $S$ ranges over all subsemigroups of $\mathrm{Mat}_d(\mathbb Q)$ contained in $\langle X\rangle$, empty and infinite ones included; $|S/\sim|$ is a `Set.encard` of the base definition `classesMeeting`, so infinitely many classes violate the bound.
-- source:
--   Guttenberg, Lhote, Shirmohammadi, Worrell, Burnside Problems for Matrix Semigroup Quotients with Applications to Border Complexity, STOC 2027 submission (held version, sha256 1bc61d4e…), Theorem 2, p.4 (rank-stable sets defined §2, p.6)

import Mathlib
import Definitions.Def_MatSemiBurnside_classesMeeting
set_option autoImplicit false

namespace MatSemiBurnside.Supplement

open MatSemiBurnside

/-- **Uniform bound N on rank-stable subsemigroups.** Guttenberg, Lhote, Shirmohammadi, Worrell, *Burnside Problems for Matrix Semigroup Quotients
with Applications to Border Complexity*, STOC 2027 submission (held version, sha256 1bc61d4e…), Theorem 2, p.4 (restated p.10, p.35):
"|S/∼| ≤ N for every rank-stable subsemigroup S ≤ ⟨X⟩" (the hypothesis of Theorem 2, and the standing
assumption of Appendix D, p.33).

**Formalization Note.** The analogue of the base `UniformStableBound` with `IsRankStableSet` (rank(a) = rank(b) =
rank(ab) for all a, b ∈ S, a = b included; p.6) in place of `IsStableSet`. S ranges over all subsemigroups of
Mat_d(ℚ) contained in ⟨X⟩ (empty, infinite and non-finitely-generated ones included). |S/∼| is the
`Set.encard` of the classes of ⟨X⟩/∼ that meet S (base `classesMeeting`), so an S meeting infinitely many
classes violates the bound. -/
def UniformRankStableBound {d : ℕ} (X : Finset (Matrix (Fin d) (Fin d) ℚ))
    (c : Con (Subsemigroup.closure (X : Set (Matrix (Fin d) (Fin d) ℚ)))) (N : ℕ) : Prop :=
  ∀ S : Subsemigroup (Matrix (Fin d) (Fin d) ℚ),
    S ≤ Subsemigroup.closure (X : Set (Matrix (Fin d) (Fin d) ℚ)) →
    IsRankStableSet (S : Set (Matrix (Fin d) (Fin d) ℚ)) →
    (classesMeeting c (S : Set (Matrix (Fin d) (Fin d) ℚ))).encard ≤ (N : ℕ∞)

end MatSemiBurnside.Supplement


