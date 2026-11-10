-- Prove2me | Definitions.Def_DeletionCodeRates_Levenshtein_GenFun
-- name    : DeletionCodeRates_Levenshtein_GenFun
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T02:20:41.918098+00:00
-- url     : https://prove2.me/theorems/80dbfd6d-15b0-4fc8-8119-a061c7316475
-- title:
--   Local factors (Table 1), the fixed-witness generating function $F_{\boldsymbol w}$ and the two-codeword transfer matrix
-- statement:
--   Generating functions are formal power series with rational coefficients (`MvPowerSeries σ ℚ`). For series $x,y$ (used with $x$ a variable, so that the inverses below are the geometric series):
--
--   * Table 1: $G_s(x,y)=1+\dfrac{xy^2}{1-x}$, $G_s^+(x,y)=\dfrac{xy^2}{1-x}$, $G_f(x,y)=\dfrac{y}{1-x}$, $G_f^+(x,y)=\dfrac{xy}{1-x}$, $T_{\mathrm{tail}}(x,y)=\dfrac{1}{1-x(1+y)}$ (`Gs`, `GsPlus`, `Gf`, `GfPlus`, `Ttail`; $(\cdot)^{-1}$ is the power-series inverse over $\mathbb Q$).
--   * (22): for a binary witness $\boldsymbol w$ of length $\ell$, $F_{\boldsymbol w}(x,y)=\sum_{\boldsymbol c\text{ starts with }0,\ \boldsymbol w\preceq\boldsymbol c}x^{|\boldsymbol c|-\ell}y^{\mathrm{runs}(\boldsymbol c)}$ in the two variables $x=X_0$, $y=X_1$ (`Fw w`). Grouping by monomial, its coefficient of $x^dy^r$ is $|\{\boldsymbol c\in\mathcal U(\ell+d,r):\boldsymbol w\preceq\boldsymbol c\}|$, as in (23).
--   * $G_{a,b}=G_s$ if $a=b$ and $G_f$ otherwise (`Gtrans a b`, in $x=X_0,y=X_1$).
--   * Theorem 13, in the four variables $x_1=X_0,\ y_1=X_1,\ x_2=X_2,\ y_2=X_3$: $S_1=G_s(x_1,y_1)G_s(x_2,y_2)-G_s^+(x_1,y_1)G_s^+(x_2,y_2)$, $F_1=G_f(x_1,y_1)G_f(x_2,y_2)-G_f^+(x_1,y_1)G_f^+(x_2,y_2)$, $T^{(1)}_{\mathrm{del}}=\begin{pmatrix}S_1&F_1\\F_1&S_1\end{pmatrix}$ (rows and columns indexed by the previous and next witness symbol, order $0,1$), $Q_1=S_1+F_1$, $A_1=y_1y_2T_{\mathrm{tail}}(x_1,y_1)T_{\mathrm{tail}}(x_2,y_2)$ (`S1`, `F1`, `Tdel`, `Q1`, `A1`).
--   * `mono2 d r` is the exponent $x^dy^r$, and `mono4 d r` is $x_1^dx_2^dy_1^ry_2^r$.
-- source:
--   Kiah, Wei, Zeng, Exponentially Larger Deletion-Correcting Codes and Constant-List-Decodable Insertion–Deletion Codes, arXiv:2609.21395 (PDF sha256 bc43cfa2…4d02), §4.2, Table 1 and (22), pp. 12–13 (PDF 14–15); Theorem 13, p. 14 (PDF 16)

import Mathlib
import Definitions.Def_DeletionCodeRates_Levenshtein_RunEnsemble

set_option autoImplicit false

namespace DeletionCodeRates.Levenshtein

/-! # Local factors, the fixed-witness generating function and the two-codeword transfer matrix

Kiah, Wei, Zeng, arXiv:2609.21395 (PDF sha256 bc43cfa2…), §4.2, Table 1, (22), printed
pp. 12–13 (PDF 14–15), and Theorem 13, printed p. 14 (PDF 16).

Generating functions are formal power series with rational coefficients. The local factors are
written as functions of two series `x`, `y`; they are used with `x` a variable (zero constant
coefficient), so `(1 - x)⁻¹ = ∑_{a ≥ 0} xᵃ` and `(1 - x(1 + y))⁻¹ = ∑_{t ≥ 0} (x(1+y))ᵗ` are the
genuine inverses (`MvPowerSeries` inverse over the field `ℚ`). -/

open MvPowerSeries

variable {σ : Type*}

/-- `G_s(x, y) = 1 + x y² / (1 - x)` (Table 1). -/
noncomputable def Gs (x y : MvPowerSeries σ ℚ) : MvPowerSeries σ ℚ := 1 + x * y ^ 2 * (1 - x)⁻¹

/-- `G_s⁺(x, y) = x y² / (1 - x)` (Table 1, nonempty gap). -/
noncomputable def GsPlus (x y : MvPowerSeries σ ℚ) : MvPowerSeries σ ℚ := x * y ^ 2 * (1 - x)⁻¹

/-- `G_f(x, y) = y / (1 - x)` (Table 1). -/
noncomputable def Gf (x y : MvPowerSeries σ ℚ) : MvPowerSeries σ ℚ := y * (1 - x)⁻¹

/-- `G_f⁺(x, y) = x y / (1 - x)` (Table 1, nonempty gap). -/
noncomputable def GfPlus (x y : MvPowerSeries σ ℚ) : MvPowerSeries σ ℚ := x * y * (1 - x)⁻¹

/-- `T_tail(x, y) = 1 / (1 - x(1 + y))` (Table 1). -/
noncomputable def Ttail (x y : MvPowerSeries σ ℚ) : MvPowerSeries σ ℚ := (1 - x * (1 + y))⁻¹

/-- The exponent `x^d y^r` in the two variables `x = X 0`, `y = X 1`. -/
noncomputable def mono2 (d r : ℕ) : Fin 2 →₀ ℕ := Finsupp.equivFunOnFinite.symm ![d, r]

open Classical in
/-- (22): `F_w(x, y) = ∑_{c starts with 0, w ⪯ c} x^{|c| - ℓ} y^{runs(c)}` with `ℓ = |w|`,
`x = X 0`, `y = X 1`. The words of length `ℓ + d` starting with `0` with `r` runs are `U(ℓ+d, r)`,
so the coefficient of `x^d y^r` is the number of `c ∈ U(ℓ + d, r)` containing `w`. -/
noncomputable def Fw (w : List (Fin 2)) : MvPowerSeries (Fin 2) ℚ :=
  fun e => (((U (w.length + e 0) (e 1)).filter (fun c => List.Sublist w c)).card : ℚ)

/-- The transition factor of Lemma 12: `G_{a,b} = G_s` if `a = b` and `G_f` otherwise, in
`x = X 0`, `y = X 1`. -/
noncomputable def Gtrans (a b : Fin 2) : MvPowerSeries (Fin 2) ℚ :=
  if a = b then Gs (X 0) (X 1) else Gf (X 0) (X 1)

/-! ## Two codewords: variables `x₁ = X 0`, `y₁ = X 1`, `x₂ = X 2`, `y₂ = X 3` -/

/-- `S₁ = G_s(x₁,y₁) G_s(x₂,y₂) - G_s⁺(x₁,y₁) G_s⁺(x₂,y₂)` (Theorem 13). -/
noncomputable def S1 : MvPowerSeries (Fin 4) ℚ :=
  Gs (X 0) (X 1) * Gs (X 2) (X 3) - GsPlus (X 0) (X 1) * GsPlus (X 2) (X 3)

/-- `F₁ = G_f(x₁,y₁) G_f(x₂,y₂) - G_f⁺(x₁,y₁) G_f⁺(x₂,y₂)` (Theorem 13). -/
noncomputable def F1 : MvPowerSeries (Fin 4) ℚ :=
  Gf (X 0) (X 1) * Gf (X 2) (X 3) - GfPlus (X 0) (X 1) * GfPlus (X 2) (X 3)

/-- `T^{(1)}_del = [[S₁, F₁], [F₁, S₁]]`, rows and columns indexed by the previous and next
witness symbols in the order `0, 1` (Theorem 13). -/
noncomputable def Tdel : Matrix (Fin 2) (Fin 2) (MvPowerSeries (Fin 4) ℚ) :=
  !![S1, F1; F1, S1]

/-- `Q₁ = S₁ + F₁` (Theorem 13). -/
noncomputable def Q1 : MvPowerSeries (Fin 4) ℚ := S1 + F1

/-- `A₁ = y₁ y₂ T_tail(x₁, y₁) T_tail(x₂, y₂)` (Theorem 13). -/
noncomputable def A1 : MvPowerSeries (Fin 4) ℚ :=
  X 1 * X 3 * Ttail (X 0) (X 1) * Ttail (X 2) (X 3)

/-- The exponent `x₁^d x₂^d y₁^r y₂^r` of the coefficient extraction in (25). -/
noncomputable def mono4 (d r : ℕ) : Fin 4 →₀ ℕ := Finsupp.equivFunOnFinite.symm ![d, r, d, r]

end DeletionCodeRates.Levenshtein


