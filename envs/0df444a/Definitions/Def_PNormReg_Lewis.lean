-- Prove2me | Definitions.Def_PNormReg_Lewis
-- name    : PNormReg_Lewis
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:38:14.453499+00:00
-- url     : https://prove2.me/theorems/1433dcb8-1b3e-47bb-8600-e5b5f702bc45
-- title:
--   Leverage scores and $\ell_p$ Lewis weight overestimates (Definition 4)
-- statement:
--   The leverage scores of a matrix $A$ are $\sigma(A)_i=A_{i:}(A^\top A)^{-1}A_{i:}^\top$. A vector $w\in\mathbb R^n_{\ge0}$ is a family of $\ell_p$ Lewis weight overestimates of $A$ if it is positive on the nonzero rows of $A$ and zero on its zero rows, satisfies $k\le\|w\|_1\le2k$ for the number $k$ of columns of $A$, and
--
--   $$w_i\ge\sigma(W^{1/2-1/p}A)_i\quad\text{for all }i,\qquad W=\mathrm{Diag}(w).$$
--
--   In powers of $W$ the $i$th diagonal entry is zero whenever $w_i=0$.
--
--   These weights replace the factor $n^{1/2-1/p}$ of the plain $\ell_2$-$\ell_p$ norm comparison with one depending on the number of columns only.
--
--   **Formalization Note** The parameter is $1/p\in[0,1]$, so that $p=\infty$ is $1/p=0$ (p.15). Only the overestimates of Definition 4 are defined; the exact Lewis weights are not used by any statement of the mission.
-- source:
--   Adil, Bullins, O'Carroll, Sidford, Solving p-norm regression in matrix multiplication time, STOC 2027 submission (manuscript sha256 e335b2fa…), Definitions 3–4 and the convention before them, p.15

import Mathlib

open Matrix

namespace PNormReg

/-!
# Leverage scores and `ℓ_p` Lewis weight overestimates

Adil, Bullins, O'Carroll, Sidford, *Solving p-norm regression in matrix multiplication time*,
STOC 2027 submission (manuscript sha256 e335b2fa…), Definitions 3–4 and the convention before them,
p.15.

**Formalization Note.** `pInv` stands for `1/p`, so `pInv = 0` is `p = ∞` (p.15, "with 1/p = 0"). The
ball constraint `d ≤ ∥w∥₁ ≤ 2d` uses the number of columns of the matrix at hand: `k` for `A = NZ ∈
ℝ^{n×k}`. On a full column rank `A`, the inverse in the leverage score of `W^{1/2−1/p}A` is a true
inverse, because a nonzero row has positive weight.
-/

/-- The diagonal of `W^e` for `W = Diag(w)`: "we set the ith diagonal entry to zero whenever
`w_i = 0`" (p.15), also at `e = 0`. -/
noncomputable def wPow {n : ℕ} (w : Fin n → ℝ) (e : ℝ) : Fin n → ℝ :=
  fun i => if w i = 0 then 0 else w i ^ e

/-- `W^e A`. -/
noncomputable def weightedMat {n k : ℕ} (w : Fin n → ℝ) (e : ℝ) (A : Matrix (Fin n) (Fin k) ℝ) :
    Matrix (Fin n) (Fin k) ℝ :=
  Matrix.diagonal (wPow w e) * A

/-- The leverage score `σ(A)_i := A_{i:}(A⊤A)^{−1}A⊤_{i:}` of Definition 3. -/
noncomputable def leverageScore {n k : ℕ} (A : Matrix (Fin n) (Fin k) ℝ) (i : Fin n) : ℝ :=
  A i ⬝ᵥ ((Aᵀ * A)⁻¹ *ᵥ A i)

/-- Definition 4 (`ℓ_p` Lewis weight overestimates, `1/p = pInv`): `w ≥ 0`, positive on nonzero rows of
`A` and zero on zero rows (p.15), `k ≤ ∥w∥₁ ≤ 2k`, and `w_i ≥ σ(W^{1/2−1/p}A)_i` for all `i`. -/
structure IsLewisOver {n k : ℕ} (A : Matrix (Fin n) (Fin k) ℝ) (pInv : ℝ) (w : Fin n → ℝ) :
    Prop where
  nonneg : ∀ i, 0 ≤ w i
  pos_of_row : ∀ i, A i ≠ 0 → 0 < w i
  zero_of_row : ∀ i, A i = 0 → w i = 0
  sum_ge : (k : ℝ) ≤ ∑ i, w i
  sum_le : ∑ i, w i ≤ 2 * (k : ℝ)
  leverage_le : ∀ i, leverageScore (weightedMat w (1 / 2 - pInv) A) i ≤ w i

end PNormReg


