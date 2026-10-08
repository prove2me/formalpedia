-- Prove2me | Definitions.Def_PDASNewton_MMatrix_Setting
-- name    : PDASNewton_MMatrix_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T02:11:59.609554+00:00
-- url     : https://prove2.me/theorems/5e90ccdd-961e-41e2-9399-81d28ab5fcd2
-- title:
--   §2–§3, pp. 4–7 — problem (3.1), the primal-dual active set step (ii)–(iii), runs, active sets, M-matrix, blocks A_𝓘 and A_𝓘𝓐
-- statement:
--   This module fixes the finite-dimensional setting of Hintermüller, Ito and Kunisch. Throughout, $n \ge 0$, $A \in \mathbb{R}^{n\times n}$, $f, \psi \in \mathbb{R}^n$ and $c \in \mathbb{R}$; vectors are ordered componentwise. The paper writes $A$ for the matrix and calligraphic $\mathcal{A}$, $\mathcal{I}$ for the active and inactive index sets; in Lean the matrix is `A` and an index set is a finite set `S`.
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
--   5. **M-matrix** (p. 7). $M$ is an M-matrix if it is nonsingular, $m_{ij} \le 0$ for $i \ne j$, and $M^{-1} \ge 0$ entrywise.
--
--   6. **Blocks** (p. 5). For an index set $\mathcal{I}$ with complement $\mathcal{A}$, $A_{\mathcal{I}} = A_{\mathcal{I}\mathcal{I}}$ is the principal submatrix on $\mathcal{I}$, and $A_{\mathcal{I}\mathcal{A}}$ has rows in $\mathcal{I}$ and columns in $\mathcal{A}$.
--
--   These objects are the vocabulary of Theorem 3.2 and of every step of its proof in Appendix A.
--
--   **Formalization Note** Vectors are `Fin n → ℝ` and matrices `Matrix (Fin n) (Fin n) ℝ`. Nonsingularity is `IsUnit M.det`; it is essential, since Lean's `M⁻¹` is the zero matrix for a singular `M`, and without it every singular matrix with nonpositive off-diagonal entries would qualify. Index sets are `Finset (Fin n)`, blocks are `Matrix.submatrix` along the subtype inclusions. A run is a relation, not a function: the step is determined only when $A_{\mathcal{I}}$ is invertible.
-- source:
--   Hintermüller, Ito, Kunisch, The primal-dual active set strategy as a semismooth Newton method, HAL hal-01660511v1, pp. 4–7: §2 algorithm steps (i)–(iv) and block notation (pp. 4–5), (3.1) (p. 6), M-matrix (p. 7)

import Mathlib
import Definitions.Def_PDASNewton_Local_Setting

namespace PDASNewton.MMatrix

open Matrix

variable {n : ℕ}

/-- M-matrix, p. 7: nonsingular, off-diagonal entries `≤ 0`, inverse entrywise `≥ 0`. -/
def IsMMatrix (M : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  IsUnit M.det ∧ (∀ i j, i ≠ j → M i j ≤ 0) ∧ ∀ i j, 0 ≤ M⁻¹ i j

/-- The principal block `A_𝓘 = A_{𝓘𝓘}` of `A` on the index set `S` (p. 5). -/
def principal (A : Matrix (Fin n) (Fin n) ℝ) (S : Finset (Fin n)) : Matrix S S ℝ :=
  A.submatrix (fun i : S => (i : Fin n)) (fun i : S => (i : Fin n))

/-- The off-diagonal block `A_{𝓘𝓐}` of `A`: rows in `S`, columns in its complement `Sᶜ` (p. 5). -/
def offDiag (A : Matrix (Fin n) (Fin n) ℝ) (S : Finset (Fin n)) :
    Matrix S (Sᶜ : Finset (Fin n)) ℝ :=
  A.submatrix (fun i : S => (i : Fin n)) (fun j : (Sᶜ : Finset (Fin n)) => (j : Fin n))

end PDASNewton.MMatrix


