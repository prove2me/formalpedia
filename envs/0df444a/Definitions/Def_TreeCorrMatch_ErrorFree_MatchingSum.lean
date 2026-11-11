-- Prove2me | Definitions.Def_TreeCorrMatch_ErrorFree_MatchingSum
-- name    : TreeCorrMatch_ErrorFree_MatchingSum
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T16:24:01.84708+00:00
-- url     : https://prove2.me/theorems/8c7fa28c-5462-4660-92b0-2b9d96d5a122
-- title:
--   The matching sums $S_q(Z)$ and the augmented matrices $A_q(Z)$
-- statement:
--   Let $c,\tilde c\ge0$ and let $Z=(Z_{ij})$ be a real $c\times\tilde c$ matrix. For an integer $q\ge0$ the **matching sum** (11) is
--
--   $$S_q(Z)=\frac1{q!}\sum_{\sigma\in\mathrm{Inj}([1:q],[1:c])}\ \sum_{\tilde\sigma\in\mathrm{Inj}([1:q],[1:\tilde c])}\ \prod_{a=1}^{q}Z_{\sigma(a),\tilde\sigma(a)},$$
--
--   where $\mathrm{Inj}(A,B)$ is the set of injections from $A$ to $B$; for $q=0$ it equals $1$, the paper's convention $S_0(Z)=1$.
--
--   For $q\in[0:\min\{c,\tilde c\}]$ the **augmented matrix** (13) is the $(c+\tilde c-q)\times(c+\tilde c-q)$ block matrix
--
--   $$A_q(Z)=\begin{bmatrix} Z & \mathbf 1_{c\times(c-q)}\\ \mathbf 1_{(\tilde c-q)\times\tilde c} & \mathbf 0_{(\tilde c-q)\times(c-q)}\end{bmatrix},$$
--
--   with $\mathbf 1$ and $\mathbf 0$ all-ones and all-zeros blocks of the indicated sizes. The permanent $\mathrm{per}(A)=\sum_{\sigma}\prod_i A_{i,\sigma(i)}$ is Mathlib's `Matrix.permanent` (equal to $1$ for the $0\times0$ matrix).
--
--   These are the quantities through which the likelihood-ratio recursion is expressed as permanents of nonnegative matrices.
--
--   **Formalization Note** Indices are $0$-based (`Fin c`), injections are embeddings `Fin q ↪ Fin c`. In `augMatrix` the first $c$ rows are the rows of $Z$ and the first $\tilde c$ columns are its columns.
-- source:
--   Cheng, Wang, Ying, Near-Quadratic Error-Free Graph Matching above Otter's Threshold via Approximate Local Tree Correlation Testing, arXiv:2611.02281 (held copy, sha256 0dfdbedd…), p. 9, eq. (11), and p. 10, eq. (13) (PDF pp. 11–12)

import Mathlib

/-!
The matching sums `S_q(Z)` and the augmented matrices `A_q(Z)`.

Cheng, Wang, Ying, arXiv:2611.02281 (held copy, sha256 0dfdbedd…), §4.1, eq. (11), p. 9, and
eq. (13), p. 10. The permanent is Mathlib's `Matrix.permanent`.
-/

namespace TreeCorrMatch.ErrorFree

/-- The matching sum (11):
`S_q(Z) = (1/q!) ∑_{σ ∈ Inj([1:q],[1:c]), σ̃ ∈ Inj([1:q],[1:c̃])} ∏_{a=1}^q Z_{σ(a), σ̃(a)}`
for a `c × c̃` matrix `Z`; for `q = 0` it equals `1`, the paper's convention `S_0(Z) = 1`. -/
noncomputable def matchingSum {c c' : ℕ} (Z : Matrix (Fin c) (Fin c') ℝ) (q : ℕ) : ℝ :=
  (1 / (q.factorial : ℝ)) * ∑ σ : Fin q ↪ Fin c, ∑ σ' : Fin q ↪ Fin c', ∏ a, Z (σ a) (σ' a)

/-- The augmented matrix (13), of size `c + c̃ - q`:
`A_q(Z) = [[Z, 1_{c×(c-q)}], [1_{(c̃-q)×c̃}, 0_{(c̃-q)×(c-q)}]]`.
Rows `0, …, c-1` are the rows of `Z`; columns `0, …, c̃-1` are the columns of `Z`. -/
def augMatrix {c c' : ℕ} (Z : Matrix (Fin c) (Fin c') ℝ) (q : ℕ) :
    Matrix (Fin (c + c' - q)) (Fin (c + c' - q)) ℝ :=
  fun i j =>
    if hi : i.val < c then
      (if hj : j.val < c' then Z ⟨i.val, hi⟩ ⟨j.val, hj⟩ else 1)
    else
      (if j.val < c' then 1 else 0)

end TreeCorrMatch.ErrorFree


