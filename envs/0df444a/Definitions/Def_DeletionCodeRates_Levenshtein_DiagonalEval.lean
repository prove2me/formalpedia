-- Prove2me | Definitions.Def_DeletionCodeRates_Levenshtein_DiagonalEval
-- name    : DeletionCodeRates_Levenshtein_DiagonalEval
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T02:20:43.490121+00:00
-- url     : https://prove2.me/theorems/7c18fa07-f661-4b80-99bf-d34dc1eac0ca
-- title:
--   Diagonal real evaluation of the transfer weights, $A_1(x,y)$ and the exponent $\Phi_{1,\delta,\rho}$
-- statement:
--   At a real point $(x,y)$ (diagonal substitution $x_1=x_2=x$, $y_1=y_2=y$):
--
--   * $G_s=1+\frac{xy^2}{1-x}$, $G_s^+=\frac{xy^2}{1-x}$, $G_f=\frac{y}{1-x}$, $G_f^+=\frac{xy}{1-x}$ (`gsR`, `gsPlusR`, `gfR`, `gfPlusR`);
--   * (27): $S_1=G_s^2-(G_s^+)^2$, $F_1=G_f^2-(G_f^+)^2$, $\mathbf T^{(1)}_{\mathrm{del}}(x,y)=\begin{pmatrix}S_1&F_1\\F_1&S_1\end{pmatrix}$ (`S1R`, `F1R`, `TdelR`);
--   * (31): $A_1(x,y)=\big(\frac{y}{1-x(1+y)}\big)^2$ (`A1R`);
--   * p. 15: $\Phi_{1,\delta,\rho}(x,y)=(1-\delta)\log_2\lambda^{(1)}_{\mathrm{del}}(x,y)-2\delta\log_2x-2\rho\log_2y$ (`Phi δ ρ x y`).
-- source:
--   Kiah, Wei, Zeng, Exponentially Larger Deletion-Correcting Codes and Constant-List-Decodable Insertion–Deletion Codes, arXiv:2609.21395 (PDF sha256 bc43cfa2…4d02), (27) p. 14 (PDF 16); (31) and Φ_{1,δ,ρ}, p. 15 (PDF 17)

import Mathlib
import Definitions.Def_DeletionCodeRates_Levenshtein_RateFunctions

set_option autoImplicit false

namespace DeletionCodeRates.Levenshtein

/-! # Diagonal real evaluation of the transfer weights, and the exponent `Φ_{1,δ,ρ}`

Kiah, Wei, Zeng, arXiv:2609.21395 (PDF sha256 bc43cfa2…), (27) printed p. 14 (PDF 16), (31) and
the definition of `Φ_{1,δ,ρ}`, printed p. 15 (PDF 17). All local factors are evaluated at the
real point `(x, y)` (diagonal substitution `x₁ = x₂ = x`, `y₁ = y₂ = y`). -/

/-- `G_s(x, y) = 1 + x y² / (1 - x)` at a real point. -/
noncomputable def gsR (x y : ℝ) : ℝ := 1 + x * y ^ 2 / (1 - x)

/-- `G_s⁺(x, y) = x y² / (1 - x)` at a real point. -/
noncomputable def gsPlusR (x y : ℝ) : ℝ := x * y ^ 2 / (1 - x)

/-- `G_f(x, y) = y / (1 - x)` at a real point. -/
noncomputable def gfR (x y : ℝ) : ℝ := y / (1 - x)

/-- `G_f⁺(x, y) = x y / (1 - x)` at a real point. -/
noncomputable def gfPlusR (x y : ℝ) : ℝ := x * y / (1 - x)

/-- (27): `S₁ = G_s² - (G_s⁺)²` at `(x, y)`. -/
noncomputable def S1R (x y : ℝ) : ℝ := gsR x y ^ 2 - gsPlusR x y ^ 2

/-- (27): `F₁ = G_f² - (G_f⁺)²` at `(x, y)`. -/
noncomputable def F1R (x y : ℝ) : ℝ := gfR x y ^ 2 - gfPlusR x y ^ 2

/-- (27): `T^{(1)}_del(x, y) = [[S₁, F₁], [F₁, S₁]]`. -/
noncomputable def TdelR (x y : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![S1R x y, F1R x y; F1R x y, S1R x y]

/-- (31): `A₁(x, y) = (y / (1 - x(1 + y)))²`. -/
noncomputable def A1R (x y : ℝ) : ℝ := (y / (1 - x * (1 + y))) ^ 2

/-- `Φ_{1,δ,ρ}(x, y) = (1 - δ) log₂ λ^{(1)}_del(x, y) - 2δ log₂ x - 2ρ log₂ y` (p. 15). -/
noncomputable def Phi (δ ρ x y : ℝ) : ℝ :=
  (1 - δ) * Real.logb 2 (lambdaDel x y) - 2 * δ * Real.logb 2 x - 2 * ρ * Real.logb 2 y

end DeletionCodeRates.Levenshtein


