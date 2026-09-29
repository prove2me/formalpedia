-- Prove2me | Definitions.Def_ClassicalSchurValues
-- name    : ClassicalSchurValues
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-09-26T21:18:38.527992+00:00
-- url     : https://prove2.me/theorems/8b37964d-f96c-4b67-a020-15d6ade2a514
-- title:
--   The sequence $W$, three sumfree classes covering $\hat W$, and four sumfree sets covering $\mathbb{Z}_7 \times \mathbb{Z}_7 \setminus \{0\}$
-- statement:
--   This bundle records the explicit finite objects of the note from which the lower bounds $L(4) \ge 16$ and $L(5) \ge 49$ are obtained.
--
--   1. The sequence $W$ (Lean `seqW`) of length $15$ and sum $31$, displayed below (note, §2).
--   2. Three finite sets of positive integers (Lean `classesW`, indexed by $0, 1, 2$; note, Lemma 2): $C_0 = \{1, 3, 8, 12, 18, 22, 28\}$, $C_1 = \{2, 6, 7, 10, 11, 25, 26, 29, 30\}$ and $C_2 = \{9, 13, 16, 17, 19, 20, 21, 27, 31\}$.
--   3. Four subsets $D_0, D_1, D_2, D_3$ of $\mathbb{Z}_7 \times \mathbb{Z}_7$ (Lean `partitionZ7Z7`, indexed by $0, 1, 2, 3$; called $C_0, \dots, C_3$ in Theorem 5 of the note), each with $12$ elements, listed in the table.
--
--   | set | elements $(a, b) \in \mathbb{Z}_7 \times \mathbb{Z}_7$ |
--   |---|---|
--   | $D_0$ | (0,2) (0,5) (1,4) (2,3) (2,4) (3,2) (3,3) (4,4) (4,5) (5,3) (5,4) (6,3) |
--   | $D_1$ | (1,1) (1,3) (1,5) (1,6) (3,0) (3,5) (4,0) (4,2) (6,1) (6,2) (6,4) (6,6) |
--   | $D_2$ | (0,3) (0,4) (1,0) (1,2) (2,1) (2,6) (3,4) (4,3) (5,1) (5,6) (6,0) (6,5) |
--   | $D_3$ | (0,1) (0,6) (2,0) (2,2) (2,5) (3,1) (3,6) (4,1) (4,6) (5,0) (5,2) (5,5) |
--
--   The sequence $W$ and, by Lemma 1 of the note, its set of block sums are
--
--   $$
--   W = (1, 1, 1, 6, 1, 1, 1, 7, 1, 1, 1, 6, 1, 1, 1), \qquad \hat W = [1, 3] \cup [6, 13] \cup [16, 22] \cup [25, 31],
--   $$
--
--   where $[a, b] = \{a, a+1, \dots, b\}$; so $\hat W$ has $25$ elements. In the note, $C_0, C_1, C_2$ are sumfree and partition $\hat W$ (Lemma 2), so $\operatorname{sdeg}(\hat W) \le 3$; and $D_0, \dots, D_3$ are sumfree in $\mathbb{Z}_7 \times \mathbb{Z}_7$ and partition its $48$ nonzero elements (Theorem 5).
--
--   The sequence $W$ with the classes $C_0, C_1, C_2$ is the witness for $L(4) \ge 16$. The four sets $D_i$, through the lift of the Lift bundle, give $L(5) \ge 49$.
--
--   **Formalization Note** The classes are Lean `Finset`s indexed by `Fin 3` and `Fin 4`. The bundle contains only the data. The facts that the mission uses (the sumfree property of $C_0, C_1, C_2$ and their cover of $\hat W$, the bound $4L$ on the sum of the first $L$ entries of $W$ for $L \le 15$, and the sumfree property of the $D_i$ in the group and their cover of the nonzero elements) are proved inside the proofs of the theorems that use them. The disjointness of the classes, which the note also states, is not needed there.
-- source:
--   A. McKenna, "The Schur degree of block sums: L(4) = 16 and L(5) ≥ 49", Zenodo (2026), https://doi.org/10.5281/zenodo.22987189, §3 (the sequence W; Lemma 3.1; Lemma 3.2: the classes C₀, C₁, C₂) and §5, proof of Theorem 1.2 (the four sets that partition ℤ₇ × ℤ₇ ∖ {0}). Lean source: https://github.com/mysticflounder/schur-degree-block-sums/blob/v1.0.1/lean/ClassicalSchur/Values.lean#L27-L33 and https://github.com/mysticflounder/schur-degree-block-sums/blob/v1.0.1/lean/ClassicalSchur/Values.lean#L84-L94 (release v1.0.1, doi:10.5281/zenodo.22987688).

-- Generated from lean/ClassicalSchur/Values.lean by skeleton
-- subtraction: every declaration except the def-material below is deleted,
-- and project imports are rewritten to their platform Definitions bundles.
import Mathlib

namespace ClassicalSchur



/-- The sequence `W` of the note: length 15, sum 31. -/
def seqW : List ℕ := [1, 1, 1, 6, 1, 1, 1, 7, 1, 1, 1, 6, 1, 1, 1]

/-- The classes `C₀, C₁, C₂` of Lemma 2 of the note. -/
def classesW : Fin 3 → Finset ℕ :=
  ![{1, 3, 8, 12, 18, 22, 28}, {2, 6, 7, 10, 11, 25, 26, 29, 30},
    {9, 13, 16, 17, 19, 20, 21, 27, 31}]

/-- The four sets of Theorem 5 of the note: a partition of the nonzero
elements of `ℤ₇ × ℤ₇` into sets that are sumfree in the group. -/
def partitionZ7Z7 : Fin 4 → Finset (ZMod 7 × ZMod 7) :=
  ![{(0, 2), (0, 5), (1, 4), (2, 3), (2, 4), (3, 2), (3, 3), (4, 4), (4, 5), (5, 3), (5, 4),
      (6, 3)},
    {(1, 1), (1, 3), (1, 5), (1, 6), (3, 0), (3, 5), (4, 0), (4, 2), (6, 1), (6, 2), (6, 4),
      (6, 6)},
    {(0, 3), (0, 4), (1, 0), (1, 2), (2, 1), (2, 6), (3, 4), (4, 3), (5, 1), (5, 6), (6, 0),
      (6, 5)},
    {(0, 1), (0, 6), (2, 0), (2, 2), (2, 5), (3, 1), (3, 6), (4, 1), (4, 6), (5, 0), (5, 2),
      (5, 5)}]

end ClassicalSchur


