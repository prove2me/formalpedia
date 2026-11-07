-- Prove2me | Definitions.Def_PackingLPAccel_PackingLP
-- name    : PackingLPAccel_PackingLP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:40:19.950617+00:00
-- url     : https://prove2.me/theorems/aaa4de77-74ff-44a7-b4ec-9b6411115b12
-- title:
--   The packing LP (1): feasibility, $\mathrm{OPT}$, normalization, and the goal's layout
-- statement:
--   For a matrix $A\in\mathbb R^{m\times n}_{\ge0}$, the packing linear program is
--
--   $$\max_{x\ge0,\ Ax\le\mathbf 1}\ \langle\mathbf 1,x\rangle,$$
--
--   with optimal value $\mathrm{OPT}$. The module also defines the column norm $\|A_{:,j}\|_\infty$, the quantity $\|Ax\|_\infty$ for nonnegative data, and the normalization $\min_j\|A_{:,j}\|_\infty=1$ that the paper assumes without loss of generality.
--
--   The input of the goal's program holds $m,n,N=\mathrm{nnz}(A)$, the positions of the nonzero entries, $\epsilon$ and their values. The output is $\hat x_j=M(1+N+j)$.
--
--   **Formalization Note** $\mathrm{OPT}$ is a real supremum. Its set is nonempty, and it is bounded above exactly when no column of $A$ is empty, which every theorem assumes; for $A=0$ the program is unbounded.
-- source:
--   Chen, Chen, Graur, Sidford, Accelerated Parallel Algorithms for Packing Linear Programming, STOC 2027 submission (manuscript sha256 1dac7711…), display (1), p.1 (pdf 2); normalization, p.10 (pdf 11)

import Mathlib
import Definitions.Def_PackingLPAccel_Layout

namespace PackingLPAccel

/-!
# The packing linear program (1) and the goal's input layout

Chen, Chen, Graur, Sidford, *Accelerated Parallel Algorithms for Packing Linear Programming*,
STOC 2027 submission (manuscript sha256 1dac7711…), display (1), p.1.

**Formalization Note.** `packingOpt A` is a real `sSup`. Its set is nonempty and it is bounded above
exactly when no column of `A` is empty, which every theorem assumes (for `A = 0` the program is
unbounded). `colNorm A j` is `∥A_{:,j}∥_∞`, written with a real `⨆` over the finite set of rows, so it
is `0` when `m = 0`. Goal layout: `I 0 = m`, `I 1 = n`, `I 2 = N`, then the `N` positions at
`I (3 + 2t)`, `I (4 + 2t)`; `M 0 = ε`, `M (1 + t)` the `t`-th value; output `x̂_j = M (1 + N + j)`.
-/

variable {m n : ℕ}

/-- `x ≥ 0` and `Ax ≤ 1`, the feasible set of (1). -/
def Feasible (A : Matrix (Fin m) (Fin n) ℝ) (x : Fin n → ℝ) : Prop :=
  (∀ j, 0 ≤ x j) ∧ ∀ i, ∑ j, A i j * x j ≤ 1

/-- `OPT := max_{x ≥ 0, Ax ≤ 1} ⟨1, x⟩`. -/
noncomputable def packingOpt (A : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  sSup {v | ∃ x, Feasible A x ∧ v = ∑ j, x j}

/-- `∥A_{:,j}∥_∞`. -/
noncomputable def colNorm (A : Matrix (Fin m) (Fin n) ℝ) (j : Fin n) : ℝ := ⨆ i, |A i j|

/-- `∥Ax∥_∞` for a nonnegative matrix and vector: the largest row sum. -/
noncomputable def rowMax (A : Matrix (Fin m) (Fin n) ℝ) (x : Fin n → ℝ) : ℝ :=
  ⨆ i, ∑ j, A i j * x j

/-- The normalization `min_j ∥A_{:,j}∥_∞ = 1` of p.10. -/
def IsNormalized (A : Matrix (Fin m) (Fin n) ℝ) : Prop :=
  (∀ j, 1 ≤ colNorm A j) ∧ ∃ j, colNorm A j = 1

/-- The integer list of the goal's input. -/
def goalInts {N : ℕ} (m n : ℕ) (e : Fin N → Fin m × Fin n) : List ℤ :=
  [(m : ℤ), (n : ℤ), (N : ℤ)] ++ sparseIdx e

/-- The goal's initial state: `A` in sparse form and `ε`. -/
noncomputable def goalInit {N : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (ε : ℝ)
    (e : Fin N → Fin m × Fin n) : State :=
  initState (ε :: sparseVals A e) (goalInts m n e)

/-- The goal's output vector: `x̂_j = M (1 + N + j)`. -/
def goalOutput {n : ℕ} (N : ℕ) (s : State) : Fin n → ℝ :=
  fun j => s.M (1 + (N : ℤ) + ((j : ℕ) : ℤ))

end PackingLPAccel


