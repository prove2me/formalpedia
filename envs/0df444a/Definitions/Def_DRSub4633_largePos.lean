-- Prove2me | Definitions.Def_DRSub4633_largePos
-- name    : DRSub4633_largePos
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T23:59:18.924103+00:00
-- url     : https://prove2.me/theorems/f4ce0ddb-d43f-431a-9a2a-dc5aac889815
-- title:
--   The label of a large coordinate in the large order
-- statement:
--   Fix the state $x$. The large coordinates $L=\{j: x_j>s\}$, together with one dummy coordinate of state $1$ and weight $q=1$, are labelled $1,\dots,m$ in nonincreasing order of $q$, ties broken by original index, with the dummy coordinate placed first (label $1$) even in a tie.
--
--   For an original large coordinate $j$, its label is
--   $$2+\#\{k\in L:\ q_k>q_j,\ \text{or}\ q_k=q_j\ \text{and}\ k<j\}.$$
--
--   **Formalization Note** Only the original coordinates of $\mathbb R^n$ are represented; the dummy large coordinate of p.10 enters only through its label $1$ and its weight $q_1=1$.
-- source:
--   Aggarwal–Du, 0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular Maximization, arXiv:2610.21072, Section 4.1, p.10

import Mathlib
import Definitions.Def_DRSub4633_sPar
import Definitions.Def_DRSub4633_qLarge

namespace DRSub4633

/-- **Position of a large coordinate in the large order.** Aggarwal–Du, *0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular
Maximization*, arXiv:2610.21072, Section 4.1, p.10: "The
coordinates in `L` are relabeled as `1, . . . , m` in nonincreasing order of `qᵢ`, with ties broken
by their original indices", where `L` includes one dummy coordinate with state `1` and `q = 1`
which "is placed first, including in a tie".

For a large coordinate `j` (`x_j > s`), `largePos x j` is its label in `{2, …, m}`: two plus the
number of large coordinates `k` that precede it, i.e. with `q_k > q_j`, or `q_k = q_j` and `k < j`.

**Formalization Note.** Label `1` is the dummy coordinate (it precedes every original large
coordinate). The dummy is not a coordinate of `ℝⁿ`: its own field component is zero, and every
point at which `F` is evaluated ignores it (p.10), so only its label and its weight `q₁ = 1` enter
the formulas (see `qAt`). Coordinates are `Fin n`, compared by their order. For a small coordinate
the value is not used. -/
noncomputable def largePos {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) (j : Fin n) : ℕ :=
  2 + (Finset.univ.filter (fun k : Fin n =>
    sPar < x k ∧ (qLarge x j < qLarge x k ∨ (qLarge x k = qLarge x j ∧ k < j)))).card

end DRSub4633


