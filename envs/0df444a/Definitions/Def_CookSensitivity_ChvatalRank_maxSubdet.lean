-- Prove2me | Definitions.Def_CookSensitivity_ChvatalRank_maxSubdet
-- name    : CookSensitivity_ChvatalRank_maxSubdet
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T09:12:34.285621+00:00
-- url     : https://prove2.me/theorems/7be37185-2d39-48a5-b82d-5bf22fd45006
-- title:
--   $\Delta(A)$, the $\ell_\infty$-norm and the $\ell_1$-norm
-- statement:
--   Let $A$ be an integral $m \times n$ matrix. A **square submatrix** of $A$ of order $k$ (with $1 \le k \le \min(m,n)$) is obtained by choosing $k$ distinct rows and $k$ distinct columns of $A$. Define
--
--   $$\Delta(A) = \max\{\, |\det B| \;:\; B \text{ a square submatrix of } A \text{ of order } k,\ 1 \le k \le \min(m,n) \,\},$$
--
--   the largest absolute value of a subdeterminant of $A$. Only nonempty submatrices count, so $\Delta(0) = 0$, and $\Delta(A) = 0$ whenever $m = 0$ or $n = 0$; for $A \neq 0$ one has $\Delta(A) \ge 1$.
--
--   For a rational vector $x = (x_1,\dots,x_k)$ we also write
--   $$\|x\|_\infty = \max\{|x_i| : i = 1,\dots,k\}, \qquad \|x\|_1 = \sum_{i=1}^k |x_i|,$$
--   with $\|x\|_\infty = 0$ for the empty vector ($k=0$).
--
--   These are the three quantities in which every bound of Cook, Gerards, Schrijver and Tardos is expressed.
--
--   **Formalization Note** `maxSubdet A : ℕ` takes the maximum of `Int.natAbs (det (A.submatrix f g))` over all injective row maps `f : Fin (k+1) ↪ Fin m` and column maps `g : Fin (k+1) ↪ Fin n`, `k < min m n`; ordering rows and columns differently only changes the sign of the determinant, so this is the paper's $\Delta(A)$. `supNorm` is a `Finset.fold max 0` of the absolute values, `l1Norm` the sum of absolute values; both are on `Fin k → ℚ`.
-- source:
--   Cook, Gerards, Schrijver, Tardos, Sensitivity theorems in integer linear programming, Math. Programming 34 (1986), p. 252, §1 (notation)

import Mathlib

namespace CookSensitivity.ChvatalRank

/-- `Δ(A)`: the maximum of the absolute values of the determinants of the (nonempty) square
submatrices of the integral `m × n` matrix `A`. A `(k+1) × (k+1)` submatrix is given by an
injective choice of rows `f` and of columns `g`; reordering rows or columns only changes the
sign of the determinant. The `0 × 0` submatrix is excluded, so `Δ(0) = 0`, and `Δ(A) = 0`
when `m = 0` or `n = 0`. -/
noncomputable def maxSubdet {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) : ℕ :=
  Finset.univ.sup fun k : Fin (min m n) =>
    Finset.univ.sup fun f : Fin (k.val + 1) ↪ Fin m =>
      Finset.univ.sup fun g : Fin (k.val + 1) ↪ Fin n =>
        (A.submatrix f g).det.natAbs

/-- The `ℓ∞`-norm `‖x‖∞ = max {|xᵢ| : i = 1, …, k}` of a rational vector (equal to `0` for
`k = 0`). -/
def supNorm {k : ℕ} (x : Fin k → ℚ) : ℚ :=
  Finset.univ.fold max 0 fun i => |x i|

/-- The `ℓ1`-norm `‖x‖₁ = ∑ |xᵢ|` of a rational vector. -/
def l1Norm {k : ℕ} (x : Fin k → ℚ) : ℚ :=
  ∑ i, |x i|

end CookSensitivity.ChvatalRank


