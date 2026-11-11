-- Prove2me | Definitions.Def_CellProbeTree_Matching_Mate
-- name    : CellProbeTree_Matching_Mate
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T18:34:40.10533+00:00
-- url     : https://prove2.me/theorems/46018fa7-3bc8-4872-a842-8cf574d5ffce
-- title:
--   Matching brackets: excess, findclose and findopen
-- statement:
--   Let $x = x_1 \cdots x_N$ be a word over the brackets `(` (an **opening**, Mathlib's `DyckStep.U`) and `)` (a **closing**, `DyckStep.D`). The **excess** of its length-$k$ prefix is
--   $$\mathrm{excess}_x(k) = \#\{\ell \le k : x_\ell = (\} - \#\{\ell \le k : x_\ell = )\}.$$
--   An opening at position $q$ is **matched** by the closing at position $c > q$ when $c$ is the first position after $q$ at which the excess returns to its value just before $q$:
--   $$\mathrm{excess}_x(c) = \mathrm{excess}_x(q-1), \qquad \mathrm{excess}_x(k) > \mathrm{excess}_x(q-1) \text{ for } q \le k < c .$$
--   Then $\mathrm{findclose}_x(q) = c$ and $\mathrm{findopen}_x(c) = q$. The **mate** of a position is its matching position: $\mathrm{findclose}$ at an opening, $\mathrm{findopen}$ at a closing. For example, the pairs of `(()())` are $(1,6)$, $(2,3)$, $(4,5)$. In a Dyck word every position has exactly one mate, and a position is an opening exactly when its mate lies to its right.
--
--   **Formalization Note.** `IsMatchPair x i j` and `Mate x i j` use 0-based positions $0,\dots,N-1$ (paper position $q$ is Lean position $q-1$); `IsOpenMate x q c` is the paper's 1-based $\mathrm{findclose}_x(q) = c$. Mates are relations, not functions, so there is no junk value at a position without a mate.
-- source:
--   Liang, Liu, Nearly Tight Cell-Probe Lower Bounds for Querying on Tree via Talagrand Inequality, STOC 2027 submission (manuscript sha256 0e5a8eb2…), p. 3 §1.2 (Dyck words), p. 4 Theorem 1.2 and p. 17 §4.1 (findclose, findopen)

import Mathlib

/-!
# Matching brackets in a word over `(` and `)`

Liang, Liu, *Nearly Tight Cell-Probe Lower Bounds for Querying on Tree via Talagrand Inequality*,
STOC 2027 submission, §1.2 (p. 3) and §4.1 (p. 17): `findclose` and `findopen`.

Words are lists of Mathlib's `DyckStep` (`U` = opening `(`, `D` = closing `)`).

**Formalization Note.** Positions in `IsMatchPair` and `Mate` are 0-based (`0, …, N-1`);
`IsOpenMate` is the paper's 1-based `findclose`.
-/

namespace CellProbeTree.Matching

/-- The excess of the length-`k` prefix of `x`: openings minus closings among its first `k`
letters (all of `x` when `k ≥ x.length`). -/
def excess (x : List DyckStep) (k : ℕ) : ℤ :=
  ((x.take k).count DyckStep.U : ℤ) - ((x.take k).count DyckStep.D : ℤ)

/-- 0-based positions: the opening at position `i` of `x` is matched by the closing at position
`j`, i.e. `j` is the first position after `i` at which the excess returns to its value just
before `i`. -/
def IsMatchPair (x : List DyckStep) (i j : ℕ) : Prop :=
  i < j ∧ j < x.length ∧ excess x (j + 1) = excess x i ∧
    ∀ k : ℕ, i < k → k ≤ j → excess x i < excess x k

/-- 0-based positions: `j` is the mate of `i` in `x`, i.e. `j = findclose(i)` when `i` is an
opening and `j = findopen(i)` when `i` is a closing. -/
def Mate (x : List DyckStep) (i j : ℕ) : Prop :=
  IsMatchPair x i j ∨ IsMatchPair x j i

/-- 1-based positions, as in the paper: `findclose_x(q) = c`. -/
def IsOpenMate (x : List DyckStep) (q c : ℕ) : Prop :=
  1 ≤ q ∧ IsMatchPair x (q - 1) (c - 1)

end CellProbeTree.Matching


