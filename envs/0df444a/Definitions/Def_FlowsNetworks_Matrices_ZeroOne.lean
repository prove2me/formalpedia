-- Prove2me | Definitions.Def_FlowsNetworks_Matrices_ZeroOne
-- name    : FlowsNetworks_Matrices_ZeroOne
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:37:17.311009+00:00
-- url     : https://prove2.me/theorems/7dc158bd-5ef7-4fa0-84cb-7adbd2722120
-- title:
--   (0, 1)-matrices, the conjugate sequence $a^*_j$ and the diagonally restricted conjugate sequence $a^{**}_k$
-- statement:
--   Following Chapter II, §12 of Ford and Fulkerson's *Flows in Networks*, this file defines the objects of the existence theorems for $(0, 1)$-matrices.
--
--   1. An $m \times n$ **$(0, 1)$-matrix** is an $m \times n$ matrix $A = (a_{ij})$ whose entries are the integers $0$ and $1$.
--   2. For nonnegative integers $a_1, \dots, a_m$, the **conjugate sequence** is
--   $$a^*_j = |\{\, i \mid a_i \ge j \,\}|, \qquad j = 1, \dots, n,$$
--   the number of dots in column $j$ when $a_i$ is drawn as a row of $a_i$ dots pushed to the left.
--   3. For nonnegative integers $a_1, \dots, a_n$, draw an $n \times n$ array and, in row $i$, place $a_i$ dots in the leftmost columns *other than the diagonal column $i$* (all $n - 1$ off-diagonal columns if $a_i \ge n - 1$). Thus row $i$ has a dot in column $j \ne i$ exactly when fewer than $a_i$ off-diagonal columns of row $i$ lie to the left of column $j$, that is, when $j \le a_i$ for $j < i$ and when $j - 1 \le a_i$ for $j > i$. The **diagonally restricted conjugate sequence** $(a^{**}_k)$ counts the dots in column $k$:
--   $$a^{**}_k = |\{\, i \mid i < k,\ a_i \ge k - 1 \,\}| + |\{\, i \mid i > k,\ a_i \ge k \,\}|, \qquad k = 1, \dots, n.$$
--   For example, $a = (4, 3, 3, 2, 2, 1)$ gives $a^{**} = (5, 4, 2, 3, 1, 0)$, which is not monotone.
--
--   The conjugate sequence is the right-hand side of the Gale–Ryser condition (Theorem 12.1); the diagonally restricted conjugate is the right-hand side of the zero-trace condition (Theorem 12.4).
--
--   **Formalization Note** A $(0, 1)$-matrix is a `Matrix (Fin m) (Fin n) ℕ` with every entry at most $1$ (`IsZeroOne`). Rows and columns are indexed from $0$: the book's index $j$ is `j + 1`. `conj a j` is $a^*_{j+1}$, defined for column indices `j : Fin n` only; the integers $a_i$ may exceed $n$. `diagDot a i j` is the dot pattern of item 3, and `diagConj a k` is the number of rows with a dot in column `k`, i.e. $a^{**}_{k+1}$. Both are computed directly from the integers $a_i$, never from the existence of a matrix.
-- source:
--   Ford & Fulkerson, Flows in Networks, RAND Report R-375-PR (1962), Chapter II, p. 76 (§12, (0, 1)-matrices), pp. 78–80 (the conjugate sequence, a*_j = |{i | a_i ≥ j}|), pp. 88–89 (the diagonally restricted conjugate sequence and its figure), p. 90 (a**_k = |I_k| + |J_k|)

import Mathlib

namespace FlowsNetworks.Matrices

/-- An `m × n` (0, 1)-matrix (Ford–Fulkerson, *Flows in Networks*, Chapter II, §12, p. 76): every
entry of `A`, a matrix of natural numbers, is `0` or `1`. Row `i` is `Fin m`-indexed and column `j`
is `Fin n`-indexed; the book's row `i` and column `j` are `i + 1` and `j + 1`. -/
def IsZeroOne {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℕ) : Prop :=
  ∀ i j, A i j ≤ 1

/-- The conjugate sequence (Chapter II, p. 79–80): for nonnegative integers `a_1, …, a_m` and a
column `j` (the book's `j + 1`, so `j + 1 ∈ {1, …, n}`),
`a*_{j+1} = |{i | a_i ≥ j + 1}|`, the number of rows whose integer is at least the column index. -/
def conj {m n : ℕ} (a : Fin m → ℕ) (j : Fin n) : ℕ :=
  (Finset.univ.filter (fun i : Fin m => j.val + 1 ≤ a i)).card

/-- The dot pattern of the diagonally restricted conjugate (Chapter II, pp. 88–89): in an `n × n`
array, row `i` places its `a_i` dots in the leftmost columns other than the diagonal column `i`
(in all `n − 1` off-diagonal columns when `a_i ≥ n − 1`). Row `i` has a dot in column `j` iff
`j ≠ i` and fewer than `a_i` off-diagonal columns of row `i` lie strictly left of column `j`;
that number is `j` (0-based) when `j < i` and `j − 1` when `j > i`. -/
def diagDot {n : ℕ} (a : Fin n → ℕ) (i j : Fin n) : Prop :=
  i ≠ j ∧ (if i < j then j.val - 1 else j.val) < a i

instance {n : ℕ} (a : Fin n → ℕ) (i j : Fin n) : Decidable (diagDot a i j) := by
  unfold diagDot; infer_instance

/-- The diagonally restricted conjugate sequence `(a**_k)` (Chapter II, pp. 88–90): `a**_k` is the
number of dots in column `k` of the pattern `diagDot a`. Equivalently (p. 90),
`a**_k = |{i | i < k, a_i ≥ k − 1}| + |{i | i > k, a_i ≥ k}|` in the book's 1-based indices. -/
def diagConj {n : ℕ} (a : Fin n → ℕ) (k : Fin n) : ℕ :=
  (Finset.univ.filter (fun i : Fin n => diagDot a i k)).card

end FlowsNetworks.Matrices


