-- Prove2me | Definitions.Def_BiconvexProg_BranchBound_Box
-- name    : BiconvexProg_BranchBound_Box
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T17:51:37.593976+00:00
-- url     : https://prove2.me/theorems/20dc9482-d009-4867-9684-933977a8a3af
-- title:
--   Boxes $\{(x,y): l \le x \le L,\ m \le y \le M\}$ in $\mathbb{R}^n \times \mathbb{R}^n$ and the four-way split rule of Figure 1
-- statement:
--   A **box** in $\mathbb{R}^n \times \mathbb{R}^n$ is given by four bound vectors $l, L, m, M \in \mathbb{R}^n$ and is the set
--
--   $$\Omega = \{(x, y) : l \le x \le L,\ m \le y \le M\}$$
--
--   (coordinatewise inequalities). Its $i$-th **coordinate rectangle** is $\Omega_i = \{(x_i, y_i) : l_i \le x_i \le L_i,\ m_i \le y_i \le M_i\} \subseteq \mathbb{R}^2$. A box $\Omega'$ is a **sub-box** of $\Omega$ when $l \le l'$, $L' \le L$, $m \le m'$ and $M' \le M$.
--
--   **Splitting** a box at index $I$ and at a point $(a, b)$ replaces its $I$-th rectangle by four subrectangles and keeps every other rectangle. The children are numbered counterclockwise from the lower-left subrectangle, as in Figure 1 of the paper:
--
--   1. $(l_I, L_I, m_I, M_I) \mapsto (l_I, a, m_I, b)$;
--   2. $(l_I, L_I, m_I, M_I) \mapsto (a, L_I, m_I, b)$;
--   3. $(l_I, L_I, m_I, M_I) \mapsto (a, L_I, b, M_I)$;
--   4. $(l_I, L_I, m_I, M_I) \mapsto (l_I, a, b, M_I)$.
--
--   These are the nodes of the branch-and-bound tree of Al-Khayyal and Falk. At every stage the selected node is split in this way at the solution of its subproblem.
--
--   **Formalization Note** Degenerate boxes ($l_i = L_i$ or $m_i = M_i$) are allowed, as in the paper. The four children are indexed by `Fin 4`, with $0,1,2,3$ standing for the paper's superscripts $21, 22, 23, 24$, and `split` returns them as a multiset. Nothing in the definition requires $(a,b)$ to lie in the rectangle; in the algorithm it always does.
-- source:
--   Al-Khayyal, Falk, Jointly Constrained Biconvex Programming, Math. Oper. Res. 8(2), 1983, pp. 274, 276–278, Problem 𝒫 (c), the sets Ω^{kj}, and the split rule of Figure 1 (p. 278)

import Mathlib

namespace BiconvexProg.BranchBound

/-- A box `{(x, y) : l ≤ x ≤ L, m ≤ y ≤ M}` in `ℝⁿ × ℝⁿ`, given by its four bound vectors
(Al-Khayyal–Falk 1983, pp. 274, 276). Degenerate boxes (`l i = L i` or `m i = M i`) are allowed. -/
structure Box (n : ℕ) where
  /-- lower bounds on `x` -/
  l : Fin n → ℝ
  /-- upper bounds on `x` -/
  L : Fin n → ℝ
  /-- lower bounds on `y` -/
  m : Fin n → ℝ
  /-- upper bounds on `y` -/
  M : Fin n → ℝ

namespace Box

variable {n : ℕ}

/-- The point set `{(x, y) : l ≤ x ≤ L, m ≤ y ≤ M}` of a box (coordinatewise order). -/
def toSet (B : Box n) : Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
  Set.Icc B.l B.L ×ˢ Set.Icc B.m B.M

/-- The `i`-th coordinate rectangle `Ω_i = {(x_i, y_i) : l_i ≤ x_i ≤ L_i, m_i ≤ y_i ≤ M_i}`. -/
def rect (B : Box n) (i : Fin n) : Set (ℝ × ℝ) :=
  Set.Icc (B.l i) (B.L i) ×ˢ Set.Icc (B.m i) (B.M i)

/-- `B'` is a sub-box of `B`: `l ≤ l'`, `L' ≤ L`, `m ≤ m'`, `M' ≤ M` coordinatewise. -/
def IsSubBox (B' B : Box n) : Prop :=
  B.l ≤ B'.l ∧ B'.L ≤ B.L ∧ B.m ≤ B'.m ∧ B'.M ≤ B.M

/-- The four children of `B` obtained by splitting its `I`-th rectangle at the point `(a, b)`
(p. 278, Figure 1), numbered counterclockwise from the lower-left subrectangle
(`0, 1, 2, 3` stand for the paper's `21, 22, 23, 24`):
* child 0: `(l_I, L_I, m_I, M_I) := (l_I, a, m_I, b)`;
* child 1: `(a, L_I, m_I, b)`;
* child 2: `(a, L_I, b, M_I)`;
* child 3: `(l_I, a, b, M_I)`;
and all rectangles `i ≠ I` are kept. -/
def child (B : Box n) (I : Fin n) (a b : ℝ) : Fin 4 → Box n :=
  ![⟨B.l, Function.update B.L I a, B.m, Function.update B.M I b⟩,
    ⟨Function.update B.l I a, B.L, B.m, Function.update B.M I b⟩,
    ⟨Function.update B.l I a, B.L, Function.update B.m I b, B.M⟩,
    ⟨B.l, Function.update B.L I a, Function.update B.m I b, B.M⟩]

/-- The multiset of the four children of `B` split at index `I` and point `(a, b)`. -/
def split (B : Box n) (I : Fin n) (a b : ℝ) : Multiset (Box n) :=
  {B.child I a b 0, B.child I a b 1, B.child I a b 2, B.child I a b 3}

end Box

end BiconvexProg.BranchBound


