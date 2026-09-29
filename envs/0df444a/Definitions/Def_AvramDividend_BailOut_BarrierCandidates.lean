-- Prove2me | Definitions.Def_AvramDividend_BailOut_BarrierCandidates
-- name    : AvramDividend_BailOut_BarrierCandidates
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T18:03:28.108292+00:00
-- url     : https://prove2.me/theorems/d585da01-4af7-449f-bef4-999ccc1e0658
-- title:
--   The candidate value $\bar v_a$ (5.4), the level $d^*$ (5.6) and the generator $\Gamma$
-- statement:
--   Let $X$ be a spectrally negative Lévy process with triplet $(c,\sigma,\nu)$, $q>0$, $\varphi>1$, and let $W=W^{(q)}$, $Z=Z^{(q)}$, $\overline Z=\overline Z^{(q)}$ be its scale functions. Write $\psi'(0+)=E[X_1]$.
--
--   For $a\ge0$ the **candidate value** of the double-barrier strategy $\bar\pi_{0,a}$ is, by formula (5.4),
--
--   $$\bar v_a(x)=\begin{cases}\varphi\bigl(\overline Z(x)+\psi'(0+)/q\bigr)+Z(x)\,\dfrac{1-\varphi Z(a)}{qW(a)}, & x\le a,\\[2mm] x-a+\bar v_a(a), & x>a.\end{cases}$$
--
--   For $x<0$ the first line equals $\bar v_a(0)+\varphi x$, which is the extension of $\bar v_{d^*}$ to the negative half-line used on p. 20. For $a=0$ and bounded variation, $W(0)=1/d$ and the formula is (5.5): $\bar v_0(x)=x+[\varphi\psi'(0+)+(1-\varphi)d]/q$.
--
--   With $G(a)=[\varphi Z(a)-1]W'(a)-\varphi qW(a)^2$, the **barrier level** is
--
--   $$d^*=\inf\{a>0:G(a)\le 0\}\in[0,\infty],\qquad \inf\emptyset=\infty .$$
--
--   The **generator** of $X$ acts on $f:\mathbb R\to\mathbb R$ by
--
--   $$\Gamma f(x)=\frac{\sigma^2}{2}f''(x)+cf'(x)+\int_{(-\infty,0)}\bigl[f(x+y)-f(x)-f'(x)y\,\mathbf 1_{\{|y|<1\}}\bigr]\,\nu(dy).$$
--
--   These objects state the candidate solution and the verification conditions of the bail-out problem.
--
--   **Formalization Note** $W'$ is `deriv W`, $f'$ and $f''$ are `deriv` and `iteratedDeriv 2`, and the $\nu$-integral is a Bochner integral. The statements that use $\Gamma$ also assert or assume integrability of its integrand. $d^*$ takes values in $[0,\infty]$, so an empty set gives $\infty$ and not $0$. Formula (5.4) is written for every real $a$. For $a=0$ in unbounded variation ($W(0)=0$) it divides by zero, and the paper does not define $\bar v_0$ there; no statement of the mission uses that case.
-- source:
--   Avram, Palmowski, Pistorius, On the optimal dividend problem for a spectrally negative Lévy process, arXiv:math/0702893v1, p. 14 (generator Γ; eq. (5.4)), p. 15 (eqs. (5.5), (5.6)), p. 20 (extension to x < 0)

import Mathlib
import Definitions.Def_AvramDividend_BailOut_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_BailOut_ScaleFunction

open MeasureTheory
open scoped NNReal ENNReal

namespace AvramDividend.BailOut

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}

/-- The candidate value `v̄_a` of the double-barrier strategy `π̄_{0,a}`, formula (5.4), p. 14:
`v̄_a(x) = φ(Z̄(x) + ψ'(0+)/q) + Z(x)[1 - φZ(a)]/[qW(a)]` for `x ≤ a` and
`v̄_a(x) = x - a + v̄_a(a)` for `x > a`. For `x < 0` the first branch equals `v̄_a(0) + φx`
(since `Z̄(x) = x`, `Z(x) = 1` there), the extension of p. 20. For `a = 0` and bounded variation
(`W(0) = 1/d`) it is (5.5). -/
noncomputable def vbar (Lv : SpectrallyNegativeLevy P 𝓕) (q φ : ℝ) (W : ℝ → ℝ) (a x : ℝ) : ℝ :=
  if x ≤ a then
    φ * (Zbar q W x + Lv.psiDerivZero / q) + Zq q W x * ((1 - φ * Zq q W a) / (q * W a))
  else
    x - a + (φ * (Zbar q W a + Lv.psiDerivZero / q) +
      Zq q W a * ((1 - φ * Zq q W a) / (q * W a)))

/-- `G(a) = [φZ(a) - 1]W'(a) - φqW(a)²`, (5.6), p. 15, with `W' = deriv W`. -/
noncomputable def Gfun (q φ : ℝ) (W : ℝ → ℝ) (a : ℝ) : ℝ :=
  (φ * Zq q W a - 1) * deriv W a - φ * q * W a ^ 2

/-- The barrier level `d* = inf {a > 0 : G(a) ≤ 0}`, (5.6), p. 15, as an element of `[0, ∞]`
(the infimum of the empty set is `∞`). -/
noncomputable def dStar (q φ : ℝ) (W : ℝ → ℝ) : ℝ≥0∞ :=
  ⨅ (a : ℝ) (_ : 0 < a) (_ : Gfun q φ W a ≤ 0), ENNReal.ofReal a

/-- The generator `Γ` of `X` (p. 14):
`Γf(x) = σ²/2 f''(x) + c f'(x) + ∫_{(-∞,0)} [f(x+y) - f(x) - f'(x) y 1_{|y|<1}] ν(dy)`. -/
noncomputable def generator (T : LevyTriplet) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  T.σ ^ 2 / 2 * iteratedDeriv 2 f x + T.c * deriv f x +
    ∫ y, (f (x + y) - f x - (if |y| < 1 then deriv f x * y else 0)) ∂T.ν

end AvramDividend.BailOut


