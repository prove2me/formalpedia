-- Prove2me | Definitions.Def_RandOrderKnapGAP_Integral_Constants
-- name    : RandOrderKnapGAP_Integral_Constants
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T04:26:07.474202+00:00
-- url     : https://prove2.me/theorems/783cc22b-288f-4cdf-b54f-e43d6ef226dc
-- title:
--   The constants $\gamma^*$ (B.48), $A$ (B.54) and the sum-of-squares bound $J$ of Lemma B.7
-- statement:
--   $$\gamma^*=\frac{307770970018984529425873353861053278824139}{1200000005486015625000000000000000000000000}\approx0.2564758,$$
--   the limiting comparison coefficient (B.48);
--   $$A=\frac{4718849996128173}{17000000000}<277580,$$
--   the constant of the finite-horizon loss $A/N$ (B.54), equal to the expression (B.53) with $H_{\mathrm{coef}}=1200000000001/10^{11}$, $C_{\mathrm{tail}}=8549714592/14111328125$, $E=71$, $D=2$, $M=16$, $T=17/4$. For $\delta>0$ and $C\in\mathbb R$,
--   $$J(C)=m\delta^2+(C-m\delta)^2,\qquad m=\lfloor C/\delta\rfloor .$$
--
--   **Formalization Note.** $\gamma^*$ and $A$ are rationals (`ℚ`), cast to `ℝ` where used; $J$ takes $\delta$ as an argument (the paper fixes $\delta=1/3$ from §B.4 on).
-- source:
--   Agrawal, Khan, Pareek, Improved Algorithms in the Random-Order Model: Knapsack, GAP, and Beyond, STOC 2027 submission (manuscript sha256 7825a05f…), pp. 50, 55, 60 (PDF 52, 57, 62), Lemma B.7, (B.48), (B.53), (B.54)

import Mathlib

namespace RandOrderKnapGAP.Integral

/-!
# Explicit constants and the sum-of-squares bound `J`

Agrawal, Khan, Pareek, *Improved Algorithms in the Random-Order Model: Knapsack, GAP, and
Beyond*, STOC 2027 submission: `γ*` is (B.48), p. 55; `A` is (B.54), p. 60 (equal to the
expression (B.53) with the values of (B.54)); `J` is the function of Lemma B.7, p. 50.
-/

/-- `γ*` of (B.48), the limiting comparison coefficient. -/
def gammaStar : ℚ :=
  307770970018984529425873353861053278824139 / 1200000005486015625000000000000000000000000

/-- `A` of (B.54), the constant of the finite-horizon loss `A/N`. -/
def Aconst : ℚ := 4718849996128173 / 17000000000

/-- `J(C) = m δ² + (C − m δ)²` with `m = ⌊C/δ⌋` (Lemma B.7): the largest sum of squares of
sizes in `[0, δ]` with total `C`. -/
noncomputable def Jbound (δ C : ℝ) : ℝ :=
  (⌊C / δ⌋ : ℝ) * δ ^ 2 + (C - (⌊C / δ⌋ : ℝ) * δ) ^ 2

end RandOrderKnapGAP.Integral


