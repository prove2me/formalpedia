-- Prove2me | Definitions.Def_Random2SATWindow_CriticalLaw_Airy
-- name    : Random2SATWindow_CriticalLaw_Airy
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T03:40:09.487484+00:00
-- url     : https://prove2.me/theorems/92a3b99a-c486-45ff-a9ee-5b57b473855a
-- title:
--   Generalized Airy functions $A_\alpha$, $A_{\alpha;k}$ and the critical quotient transform $Q_{\alpha;k}$
-- statement:
--   Airy notations (printed p. 14). Fix $c>0$ and let $\Pi$ follow the lower ray $c+te^{-i\pi/3}$ from $t=\infty$ to $t=0$, then the upper ray $c+te^{i\pi/3}$ from $t=0$ to $\infty$. Here $c=1$: `contourPi g` $=\int_0^\infty\big(g(1+te^{i\pi/3})e^{i\pi/3}-g(1+te^{-i\pi/3})e^{-i\pi/3}\big)\,dt=\int_\Pi g(T)\,dT$. Powers are principal, $T^\alpha=\exp(\alpha\operatorname{Log}T)$ (`Complex.cpow`); $\operatorname{Re}T\ge1$ on $\Pi$.
--
--   * (30) $A_\alpha(z)=\dfrac1{2\pi i}\displaystyle\int_\Pi T^\alpha\exp\Big(\frac{T^3}3-zT\Big)dT$ (`airyA α z`, $\alpha\in\mathbb R$, $z\in\mathbb C$). By (31), $A_0=\mathrm{Ai}$ and $A_1=-\mathrm{Ai}'$.
--   * (32) $A_{\alpha;k}(z;\sigma)=\dfrac1{2\pi i}\displaystyle\int_\Pi T^\alpha\prod_{j=1}^k(T+\sigma_j)^{-1}\exp\Big(\frac{T^3}3-zT\Big)dT$ for $\sigma\in[0,\infty)^k$ (`airyAk α k σ z`).
--   * (34) $Q_{\alpha;k}(x;\sigma)=\dfrac{\sqrt\pi\,e^{-x^3/6}}{2\pi}\displaystyle\int_{\mathbb R}e^{-i2^{-2/3}x\theta}\,\frac{A_{\alpha;k}(-i2^{-1/3}\theta;\sigma)}{A_1(-i2^{1/3}\theta)}\,d\theta$ (`quotientQ α k σ x`).
--
--   **Formalization Note.** The value of (30) does not depend on $c>0$ (the paper's remark, and Cauchy's theorem), so fixing $c=1$ changes nothing. The integrand decays like $e^{-t^3/3}$ along both rays, so the Bochner integral is the convergent contour integral. A numerical check of this parametrization reproduces $\mathrm{Ai}(0)$, $-\mathrm{Ai}'(0.7)$ and $\mathrm{Ai}(-2+i)$ to 12 digits.
-- source:
--   Ravelomanana, Inside the Critical Window of Random 2-SAT, STOC 2027 submission (manuscript sha256 eef2fa67…), Airy notations (30)–(34), printed p. 14 (PDF 16)

import Mathlib

set_option autoImplicit false

open Complex MeasureTheory

namespace Random2SATWindow.CriticalLaw

/-! # Generalized Airy functions `A_α`, `A_{α;k}` and the quotient transform `Q_{α;k}`

Ravelomanana, *Inside the Critical Window of Random 2-SAT*, STOC 2027 submission (manuscript
sha256 eef2fa67…), Airy notations (30)–(34), printed p. 14 (PDF 16).

The contour `Π` follows the lower ray `c + t e^{-iπ/3}` from `t = ∞` to `t = 0`, then the upper
ray `c + t e^{iπ/3}` from `t = 0` to `t = ∞`; the paper allows any `c > 0` and the value does not
depend on it. Here `c = 1`. Powers `T^α` are principal (`Complex.cpow`, `-π < arg T ≤ π`), and
`T` stays in `Re T ≥ 1` on `Π`. -/

/-- `e^{iπ/3}`, the direction of the upper ray of `Π`. -/
noncomputable def rayDir : ℂ := Complex.exp (Complex.I * (Real.pi / 3 : ℝ))

/-- `∫_Π g(T) dT` for the contour `Π` with `c = 1`, parametrized by arc length `t ∈ (0, ∞)`:
the upper ray contributes `∫_0^∞ g(1 + t e^{iπ/3}) e^{iπ/3} dt` and the lower ray, traversed
from `∞` to `0`, contributes `-∫_0^∞ g(1 + t e^{-iπ/3}) e^{-iπ/3} dt`. -/
noncomputable def contourPi (g : ℂ → ℂ) : ℂ :=
  ∫ t in Set.Ioi (0 : ℝ),
    (g (1 + (t : ℂ) * rayDir) * rayDir - g (1 + (t : ℂ) * (starRingEnd ℂ rayDir)) *
      (starRingEnd ℂ rayDir))

/-- The generalized Airy function (30): `A_α(z) = (1/(2πi)) ∫_Π T^α exp(T³/3 - zT) dT`
(`α` real, `z` complex, principal power). -/
noncomputable def airyA (α : ℝ) (z : ℂ) : ℂ :=
  (2 * Real.pi * Complex.I)⁻¹ *
    contourPi (fun T => T ^ (α : ℂ) * Complex.exp (T ^ 3 / 3 - z * T))

/-- The marked generalized Airy function (32):
`A_{α;k}(z; σ) = (1/(2πi)) ∫_Π T^α ∏_{j=1}^k (T + σ_j)^{-1} exp(T³/3 - zT) dT`,
for `σ ∈ [0, ∞)^k` (the contour lies to the right of `0` and of every pole `-σ_j`). -/
noncomputable def airyAk (α : ℝ) (k : ℕ) (σ : Fin k → ℝ) (z : ℂ) : ℂ :=
  (2 * Real.pi * Complex.I)⁻¹ *
    contourPi (fun T => T ^ (α : ℂ) * (∏ j, (T + (σ j : ℂ))⁻¹) * Complex.exp (T ^ 3 / 3 - z * T))

/-- The critical quotient transform (34):
`Q_{α;k}(x; σ) = (√π e^{-x³/6} / (2π)) ∫_ℝ e^{-i 2^{-2/3} x θ} A_{α;k}(-i 2^{-1/3} θ; σ) /
A_1(-i 2^{1/3} θ) dθ`. -/
noncomputable def quotientQ (α : ℝ) (k : ℕ) (σ : Fin k → ℝ) (x : ℝ) : ℂ :=
  ((Real.sqrt Real.pi * Real.exp (-x ^ 3 / 6) / (2 * Real.pi) : ℝ) : ℂ) *
    ∫ θ : ℝ, Complex.exp (-Complex.I * ((2 : ℝ) ^ (-(2 / 3 : ℝ)) * x * θ : ℝ)) *
      airyAk α k σ (-Complex.I * ((2 : ℝ) ^ (-(1 / 3 : ℝ)) * θ : ℝ)) /
      airyA 1 (-Complex.I * ((2 : ℝ) ^ (1 / 3 : ℝ) * θ : ℝ))

end Random2SATWindow.CriticalLaw


