-- Prove2me | Definitions.Def_IterRoundDet_Regularizer
-- name    : IterRoundDet_Regularizer
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:54:24.419109+00:00
-- url     : https://prove2.me/theorems/c4119b64-cd68-41c9-8cf4-4cc9fe9b55a4
-- title:
--   The regularizer $g=\min\{g_1,g_2\}$ and the objective $\Psi=f-g$
-- statement:
--   With zero terms when $x_i=0$,
--
--   $$H_+(a,x)=-\sum_i a_i\log x_i,\qquad H_-(a,x)=\sum_i\Big[(x_i-a_i)\log\Big(1-\frac{a_i}{x_i}\Big)-(1-a_i)\log(1-a_i)\Big],$$
--
--   $$g_1=12H_-+2d,\quad g_2=2H_++3H_-,\quad g=\min\{g_1,g_2\},\quad \Psi=f-g.$$
--
--   The rounding walk increases $\Psi$ until $x$ is integral; $0\le g\le 14d$ is the source of the factor $e^{14d}$.
--
--   **Formalization Note** Under $a\le x$, the Lean conventions $\log 0=0$ and $y/0=0$ give the page's zero terms. The sanity file checks the cases $x_i=0$, $x_i=1$, $a_i=x_i$ and $a_i=1$.
-- source:
--   Bansal, Li, Singh, Xu, Iterative Rounding for Determinant Maximization and Real Stable Polynomials, STOC 2027 submission (manuscript sha256 aa18bcee…), (22), (23), p.16

import Mathlib
import Definitions.Def_IterRoundDet_Relaxation

set_option autoImplicit false

namespace IterRoundDet

/-!
# The regularizer `g` and the regularized objective `Ψ`

Bansal, Li, Singh, Xu, STOC 2027 submission (manuscript sha256 aa18bcee…), (22), (23), p.16.

**Formalization Note.** Under `a ≤ x`, `Real.log 0 = 0` and `y / 0 = 0` give the page's conventions:
at `x_i = 0` (so `a_i = 0`) each term is `0`; at `a_i = x_i` the first summand of `H₋` is `0 · log 0 = 0`,
leaving `−(1 − a_i) log(1 − a_i)`; at `a_i = 1` both summands are `0`.
-/

variable {n : ℕ}

/-- `H₊(a, x) = −∑_i a_i log x_i`, (22), p.16. -/
noncomputable def Hplus (a x : Fin n → ℝ) : ℝ :=
  -∑ i, a i * Real.log (x i)

/-- `H₋(a, x) = ∑_i [(x_i − a_i) log(1 − a_i/x_i) − (1 − a_i) log(1 − a_i)]`, (22), p.16. -/
noncomputable def Hminus (a x : Fin n → ℝ) : ℝ :=
  ∑ i, ((x i - a i) * Real.log (1 - a i / x i) - (1 - a i) * Real.log (1 - a i))

/-- `g₁(a, x) = 12 H₋(a, x) + 2d`, p.16. -/
noncomputable def g1 (d : ℕ) (a x : Fin n → ℝ) : ℝ := 12 * Hminus a x + 2 * d

/-- `g₂(a, x) = 2 H₊(a, x) + 3 H₋(a, x)`, p.16. -/
noncomputable def g2 (a x : Fin n → ℝ) : ℝ := 2 * Hplus a x + 3 * Hminus a x

/-- `g(a, x) = min{g₁(a, x), g₂(a, x)}`, (23), p.16. -/
noncomputable def gReg (d : ℕ) (a x : Fin n → ℝ) : ℝ := min (g1 d a x) (g2 a x)

/-- `Ψ(a, x) = f(a, x) − g(a, x)`, (23), p.16. -/
noncomputable def Psi (c : Finset (Fin n) → ℝ) (d : ℕ) (a x : Fin n → ℝ) : ℝ :=
  relaxObj c a x - gReg d a x

/-- The branch `f − g₁` of `Ψ`, (23), p.16. -/
noncomputable def fMinusG1 (c : Finset (Fin n) → ℝ) (d : ℕ) (a x : Fin n → ℝ) : ℝ :=
  relaxObj c a x - g1 d a x

/-- The branch `f − g₂` of `Ψ`, (23), p.16. -/
noncomputable def fMinusG2 (c : Finset (Fin n) → ℝ) (a x : Fin n → ℝ) : ℝ :=
  relaxObj c a x - g2 a x

end IterRoundDet


