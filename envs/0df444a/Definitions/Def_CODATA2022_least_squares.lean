-- Prove2me | Definitions.Def_CODATA2022_least_squares
-- name    : CODATA2022_least_squares
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-20T23:03:29.722861+00:00
-- url     : https://prove2.me/theorems/ba0e0ba9-cd8d-4d13-b19d-8ab49cd72a32
-- title:
--   The CODATA least-squares adjustment: $\chi^2$, Birge ratio, normalized residual
-- statement:
--   The objects of the CODATA least-squares adjustment. For a design matrix $A$ of $N$ linearized observational equations in $M$ adjusted constants, input data $z \in \mathbb{R}^N$ and a weight matrix $W$ (the inverse covariance matrix of the data), the statistic $\chi^2(x) = (z-Ax)^{\mathsf T}W(z-Ax)$; the degrees of freedom $\nu = N-M$ (as an integer); the Birge ratio $R_B = (\chi^2/\nu)^{1/2}$; and the normalized residual $r = (X-\langle X\rangle)/u(X)$ of an input datum with adjusted value $\langle X\rangle$ and standard uncertainty $u(X)$.
-- source:
--   Mohr, Newell, Taylor, Tiesinga, CODATA recommended values of the fundamental physical constants: 2022, Rev. Mod. Phys. 97, 025002 (2025), https://doi.org/10.1103/RevModPhys.97.025002, Sec. XIV.A (the 2022 adjustment: $N=133$, $M=79$, $\nu=54$, $\chi^2$, expansion factors) and the Nomenclature entries for $\nu$, $R_B$ and $r_i$.

import Mathlib

/-!
# The CODATA least-squares adjustment (LSA)

The adjustment fits `M` adjusted constants `x` to `N` input data `z` through linear
observational equations `z ≐ A x`, weighting the residuals by a symmetric positive definite
weight matrix `W` (the inverse of the covariance matrix of the input data).

Notation follows Mohr, Newell, Taylor, Tiesinga, Rev. Mod. Phys. **97**, 025002 (2025):
Sec. XIV.A and the Nomenclature entries for `ν = N − M`, `R_B = (χ²/ν)^{1/2}` and
`r_i = (X_i − ⟨X_i⟩)/u(X_i)`.
-/

noncomputable section

namespace CODATA2022

open Matrix

/-- The statistic `χ² = (z − A x)ᵀ W (z − A x)` of a linear least-squares adjustment with
design matrix `A`, weight matrix `W`, input data `z` and parameter vector `x`. -/
def chiSquare {N M : ℕ} (A : Matrix (Fin N) (Fin M) ℝ) (W : Matrix (Fin N) (Fin N) ℝ)
    (z : Fin N → ℝ) (x : Fin M → ℝ) : ℝ :=
  (z - A.mulVec x) ⬝ᵥ W.mulVec (z - A.mulVec x)

/-- Degrees of freedom `ν = N − M` of an adjustment with `N` input data and `M` adjusted
constants, as an integer (so that no truncation occurs when `M > N`). -/
def degreesOfFreedom (N M : ℕ) : ℤ := (N : ℤ) - (M : ℤ)

/-- Birge ratio `R_B = (χ²/ν)^{1/2}`. -/
def birgeRatio (chiSq nu : ℝ) : ℝ := Real.sqrt (chiSq / nu)

/-- Normalized residual `r = (X − ⟨X⟩)/u(X)` of an input datum `X` with adjusted value
`Xadj` and standard uncertainty `u`. -/
def normalizedResidual (X Xadj u : ℝ) : ℝ := (X - Xadj) / u

end CODATA2022

end


