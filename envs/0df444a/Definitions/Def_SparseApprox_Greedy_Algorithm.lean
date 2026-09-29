-- Prove2me | Definitions.Def_SparseApprox_Greedy_Algorithm
-- name    : SparseApprox_Greedy_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T15:20:06.447423+00:00
-- url     : https://prove2.me/theorems/0ddfd57f-76fa-4b38-8d9f-91ff5d00dde3
-- title:
--   Algorithm Greedy: state after r selection steps, and runs of the selection phase
-- statement:
--   This file encodes the subset selection phase of Algorithm Greedy (Natarajan 1995, p. 229) on input $A\in\mathbb R^{m\times n}$, $b\in\mathbb R^m$, $\varepsilon>0$.
--
--   The **state** at the start of iteration $r$ consists of the columns $a^{(r)}_1,\dots,a^{(r)}_n$ of $A^{(r)}$, the vector $b^{(r)}$ and the set $\tau$ of indices chosen so far. Initially $A^{(0)}=\mathbf A$ ($A$ with normalized columns), $b^{(0)}=b$ and $\tau=\emptyset$. If index $k$ is chosen at iteration $r$, then
--   $$b^{(r+1)}=b^{(r)}-\big(a_k^{(r)T}b^{(r)}\big)a_k^{(r)},\qquad \tau\leftarrow\tau\cup\{k\},$$
--   and for every $j$ outside the new $\tau$
--   $$a_j^{(r+1)}=\frac{a_j^{(r)}-\big(a_k^{(r)T}a_j^{(r)}\big)a_k^{(r)}}{\big\|a_j^{(r)}-\big(a_k^{(r)T}a_j^{(r)}\big)a_k^{(r)}\big\|_2},$$
--   while the columns with index in the new $\tau$ are left as they are. Given the sequence of choices $k_0,k_1,\dots$, the state at every iteration is determined by this recursion.
--
--   A sequence of choices is a **run of $t$ iterations** if, for every $r<t$:
--   1. the while-condition holds: $\|b^{(r)}\|_2>\varepsilon$;
--   2. $k_r\notin\tau$;
--   3. the exit "no solution exists" is not taken: $a_{k_r}^{(r)T}b^{(r)}\neq 0$;
--   4. $k_r$ is a greedy choice: $|a_{k_r}^{(r)T}b^{(r)}|\ge|a_j^{(r)T}b^{(r)}|$ for every $j\notin\tau$.
--
--   The number of vectors selected by such a run is $t$. Ties in the greedy choice are resolved arbitrarily: every tie-breaking gives a run.
--
--   **Formalization Note** The choices are a sequence `k : ℕ → Fin n`, and `IsGreedyRun A b ε k t` constrains only its first $t$ entries. The paper's exit test is $A^{(r)T}b^{(r)}=0$ over all columns; the columns with index in $\tau$ are orthogonal to $b^{(r)}$, so the test is equivalent to testing the maximizing column. A column that projects to $0$ stays $0$ (the convention $0/\|0\|_2=0$), has correlation $0$, and is never chosen.
-- source:
--   Natarajan, Sparse Approximate Solutions to Linear Systems, SIAM J. Comput. 24 (1995), p. 229, Algorithm Greedy (selection phase)

import Mathlib
import Definitions.Def_SparseApprox_Greedy_Basic

open scoped InnerProductSpace

namespace SparseApprox.Greedy

/-- The state of Algorithm Greedy at the start of an iteration: the columns `a_j⁽ʳ⁾` of `A⁽ʳ⁾`,
the vector `b⁽ʳ⁾`, and the set `τ` of indices chosen so far. -/
structure State (m n : ℕ) where
  col : Fin n → EuclideanSpace ℝ (Fin m)
  res : EuclideanSpace ℝ (Fin m)
  chosen : Finset (Fin n)

/-- The initial state: `A⁽⁰⁾ = A` (bold: columns normalized), `b⁽⁰⁾ = b`, `τ = ∅`. -/
noncomputable def initState {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : EuclideanSpace ℝ (Fin m)) : State m n :=
  ⟨fun j => normalizeVec (colE A j), b, ∅⟩

/-- One iteration of the selection phase with chosen index `k`, `a = a_k⁽ʳ⁾`:
`b⁽ʳ⁺¹⁾ = b⁽ʳ⁾ − (aᵀb⁽ʳ⁾) a`, `τ ← τ ∪ {k}`, and for `j` outside the new `τ`,
`a_j⁽ʳ⁺¹⁾ = normalize(a_j⁽ʳ⁾ − (aᵀa_j⁽ʳ⁾) a)`; columns with index in the new `τ` are left
unchanged, as in the pseudo-code. -/
noncomputable def greedyStep {m n : ℕ} (s : State m n) (k : Fin n) : State m n :=
  { col := fun j =>
      if j ∈ insert k s.chosen then s.col j
      else normalizeVec (s.col j - ⟪s.col k, s.col j⟫_ℝ • s.col k)
    res := s.res - ⟪s.col k, s.res⟫_ℝ • s.col k
    chosen := insert k s.chosen }

/-- The state at the start of iteration `r` when the indices chosen at iterations
`0, 1, …` are `k 0, k 1, …`. -/
noncomputable def greedyState {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : EuclideanSpace ℝ (Fin m)) (k : ℕ → Fin n) : ℕ → State m n
  | 0 => initState A b
  | r + 1 => greedyStep (greedyState A b k r) (k r)

/-- The choices `k 0, …, k (t-1)` are a run of `t` iterations of the selection phase of
Algorithm Greedy on input `A, b, ε`: at every iteration `r < t`, with state `s`,
the while-condition `‖b⁽ʳ⁾‖₂ > ε` holds, the "no solution exists" exit is not taken
(`a_k⁽ʳ⁾ᵀb⁽ʳ⁾ ≠ 0`), `k r ∉ τ`, and `|a_k⁽ʳ⁾ᵀb⁽ʳ⁾|` is maximum over `j ∉ τ`. -/
def IsGreedyRun {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin m))
    (ε : ℝ) (k : ℕ → Fin n) (t : ℕ) : Prop :=
  ∀ r < t,
    ε < ‖(greedyState A b k r).res‖ ∧
    k r ∉ (greedyState A b k r).chosen ∧
    ⟪(greedyState A b k r).col (k r), (greedyState A b k r).res⟫_ℝ ≠ 0 ∧
    ∀ j ∉ (greedyState A b k r).chosen,
      |⟪(greedyState A b k r).col j, (greedyState A b k r).res⟫_ℝ| ≤
        |⟪(greedyState A b k r).col (k r), (greedyState A b k r).res⟫_ℝ|

end SparseApprox.Greedy


