-- Prove2me | Definitions.Def_PDASNewton_NormCone_Setting
-- name    : PDASNewton_NormCone_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T03:09:20.083206+00:00
-- url     : https://prove2.me/theorems/eb1ede50-6d5d-4e2f-8f17-dd0fea871fc6
-- title:
--   §2–§3, pp. 4–9 — problem (3.1), the primal-dual active set step, runs, active sets, blocks A_𝓘 and A_𝓘𝓐, ‖B₊‖₁, M-matrix
-- statement:
--   This module fixes the finite-dimensional setting of Hintermüller, Ito and Kunisch used in Theorem 3.3. Throughout, $n \ge 0$, $A \in \mathbb{R}^{n\times n}$, $f, \psi \in \mathbb{R}^n$ and $c \in \mathbb{R}$; vectors are ordered componentwise. The paper writes $A$ for the matrix and calligraphic $\mathcal{A}$, $\mathcal{I}$ for the active and inactive index sets; in Lean the matrix is `A` and an index set is a finite set `S`, standing for $\mathcal{I}$, with complement $\mathcal{A}$.
--
--   1. **Problem (3.1)** (p. 6). A pair $(y,\lambda) \in \mathbb{R}^n\times\mathbb{R}^n$ solves (3.1) if
--   $$Ay + \lambda = f, \qquad \lambda - \max(0, \lambda + c(y-\psi)) = 0,$$
--   the maximum taken componentwise.
--
--   2. **Active set** (step (ii), p. 4). For an iterate $(y,\lambda)$,
--   $$\mathcal{A} = \{ i : \lambda_i + c(y-\psi)_i > 0 \}, \qquad \mathcal{I} = \{ i : \lambda_i + c(y-\psi)_i \le 0 \},$$
--   the inactive set being the complement of the active set.
--
--   3. **One step** (step (iii), p. 4). $(y',\lambda')$ follows $(y,\lambda)$ if
--   $$Ay' + \lambda' = f, \qquad y'_i = \psi_i \ (i \in \mathcal{A}), \qquad \lambda'_i = 0 \ (i \in \mathcal{I}),$$
--   where $\mathcal{A}, \mathcal{I}$ are the sets of $(y,\lambda)$.
--
--   4. **Run.** Sequences $(y^k, \lambda^k)_{k\ge 0}$ with arbitrary initial data $(y^0,\lambda^0)$ such that every $(y^{k+1},\lambda^{k+1})$ follows $(y^k,\lambda^k)$. The stopping option of step (iv) is not modelled: a run is infinite.
--
--   5. **Blocks** (p. 5). For an index set $\mathcal{I}$ with complement $\mathcal{A}$, $A_{\mathcal{I}} = A_{\mathcal{I}\mathcal{I}}$ is the principal submatrix on $\mathcal{I}$, and $A_{\mathcal{I}\mathcal{A}}$ has rows in $\mathcal{I}$ and columns in $\mathcal{A}$.
--
--   6. **The norm $\|B_+\|_1$** (p. 8). For a rectangular matrix $B$, $B_+$ is the matrix of positive parts $\max(0, b_{ij})$, and $\|\cdot\|_1$ is the matrix norm subordinate to the one-norms, i.e. the maximal absolute column sum. Since the entries of $B_+$ are nonnegative,
--   $$\|B_+\|_1 = \max_j \sum_i \max(0, b_{ij}),$$
--   and $\|B_+\|_1 = 0$ when $B$ has no columns.
--
--   7. **M-matrix** (p. 7). $M$ is an M-matrix if it is nonsingular, $m_{ij} \le 0$ for $i \ne j$, and $M^{-1} \ge 0$ entrywise.
--
--   These objects are the vocabulary of Theorem 3.3, its proof and Remark 3.3.
--
--   **Formalization Note** Vectors are `Fin n → ℝ` and matrices `Matrix (Fin n) (Fin n) ℝ`. Index sets are `Finset (Fin n)`; blocks are `Matrix.submatrix` along the subtype inclusions. The maximum in $\|B_+\|_1$ is a supremum in $\mathbb{R}_{\ge 0}$ over the (finite) set of columns, whose value on an empty column set is $0$, the norm of the empty matrix; this matters for the partition $\mathcal{A} = \emptyset$. Nonsingularity of an M-matrix is `IsUnit M.det`, needed because Lean's `M⁻¹` is the zero matrix for a singular `M`. A run is a relation, not a function: the step is determined only when $A_{\mathcal{I}}$ is invertible.
-- source:
--   Hintermüller, Ito, Kunisch, The primal-dual active set strategy as a semismooth Newton method, HAL hal-01660511v1, pp. 4–8: §2 algorithm steps (i)–(iv) and block notation (pp. 4–5), (3.1) (p. 6), M-matrix (p. 7), the norm ‖B₊‖₁ (p. 8)

import Mathlib
import Definitions.Def_PDASNewton_Local_Setting
import Definitions.Def_PDASNewton_MMatrix_Setting

namespace PDASNewton.NormCone

open Matrix

variable {n : ℕ}

/-- `‖B₊‖₁`, p. 8: the matrix norm subordinate to the one-norms (the maximum
absolute column sum) of the positive part `B₊ = (max 0 bᵢⱼ)` of `B`.
Its value is `0` for a matrix with no columns (supremum over an empty set
in `ℝ≥0`). -/
noncomputable def posPartOneNorm {m p : Type*} [Fintype m] [Fintype p]
    (B : Matrix m p ℝ) : ℝ :=
  ((Finset.univ.sup fun j : p => (∑ i, max 0 (B i j)).toNNReal : NNReal) : ℝ)

end PDASNewton.NormCone


