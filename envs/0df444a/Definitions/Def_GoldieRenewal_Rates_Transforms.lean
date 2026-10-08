-- Prove2me | Definitions.Def_GoldieRenewal_Rates_Transforms
-- name    : GoldieRenewal_Rates_Transforms
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T19:09:18.886335+00:00
-- url     : https://prove2.me/theorems/abae4d59-d3ac-48cf-a797-53a4b129aada
-- title:
--   §1 and Theorem 3.1 objects: convolution powers, renewal measure, spread-out laws, transforms μ̃, μ̂, f̂, admissible contours, conditions (3.1)
-- statement:
--   This file collects the measure-theoretic and transform objects of Goldie's rate theory.
--
--   1. **Convolution powers.** For a measure $\mu$ on $\mathbb R$, $\mu^{(0)}=\delta_0$ (unit mass at $0$) and $\mu^{(n+1)}=\mu^{(n)}*\mu$, where $*$ is convolution of measures (the published definition `QueueingFundamentals.MG1.convPow`, reused here).
--   2. **Renewal measure.** $\nu:=\sum_{n=0}^\infty \mu^{(n)}$; it is in general an infinite measure.
--   3. **Spread-out law.** $\mu$ is spread out if some convolution power $\mu^{(n)}$, $n\ge 1$, has a nonzero absolutely continuous component, i.e. is not singular with respect to Lebesgue measure.
--   4. **Transforms.** For real $\beta$, $\tilde\mu(\beta)=\int e^{\beta t}\,\mu(dt)\in[0,\infty]$. For complex $\theta$,
--   $$\hat\mu(\theta)=\int_{\mathbb R} e^{i\theta t}\,\mu(dt),\qquad \hat f(\theta)=\int_{\mathbb R} e^{i\theta t} f(t)\,dt .$$
--   5. **Admissible contour.** Given $h:\mathbb C\to\mathbb C$ and $\beta$, a rectangle with lower-left corner $z$ and upper-right corner $w$ is admissible if its closure lies in the strip $D=\{\theta:-\beta<\Im\theta<0\}$ and every zero of $h$ in $D$ lies in the open rectangle. Its positively oriented boundary plays the role of the contour $\mathscr C$ "enclosing all the zeroes of $1-\hat\eta$ in $D$".
--   6. **Conditions (3.1).** A law $\eta$ satisfies (3.1) and the subsequent conditions of Theorem 3.1 at $\beta$ if for some $n_0$
--   $$\eta^{(n_0)}=(1-\delta)\varphi_0+\delta\varphi_1,$$
--   with $\delta\in[0,1)$, $\varphi_0,\varphi_1$ probability measures, $\varphi_0$ absolutely continuous, $\delta\tilde\varphi_1(\beta)<1$, and moreover $\hat\eta(\theta)\neq 1$ on the line $\Im\theta=-\beta$.
--
--   These are the hypotheses of the explicit-rate Stone decomposition (Theorem 3.1) and of the rate theorem (Theorem 3.2).
--
--   **Formalization Note** $\tilde\mu$ is a lower Lebesgue integral, so $\tilde\mu(\beta)<\infty$ is meaningful. $\hat\mu$ and $\hat f$ are Bochner integrals, meaningful where the integrand is integrable (for $\hat\eta$: on $-\beta\le\Im\theta\le 0$ when $\tilde\eta(\beta)<\infty$). Functions are complex valued in $\hat f$; a real function enters through its coercion. The contour is a rectangle boundary; the contour integral itself is `RectangleIntegral` from the referenced definition `ResidueCalcOnRectangles_defs` (counterclockwise).
-- source:
--   Goldie, Implicit renewal theory and tails of solutions of random equations, Ann. Appl. Probab. 1(1):126–166 (1991), DOI 10.1214/aoap/1177005985, p. 127 (§1, spread-out laws), p. 128 (§1, convolution powers and transforms), p. 131, Theorem 3.1, (3.1)

import Mathlib
import Definitions.Def_QueueingFundamentals_MG1_transforms

open MeasureTheory Complex
open QueueingFundamentals.MG1 (convPow)

namespace GoldieRenewal.Rates

/-- The renewal measure `ν := Σ_{n=0}^∞ μ^{(n)}` of a law `μ` on `ℝ`
(Goldie 1991, Theorem 3.1, p. 131). It may be an infinite measure. The convolution powers
`μ^{(n)}` (Goldie 1991, §1, p. 128: `μ^{(0)} = δ₀`, `μ^{(n+1)} = μ^{(n)} ∗ μ`) are the published
`QueueingFundamentals.MG1.convPow`. -/
noncomputable def renewalMeasure (μ : Measure ℝ) : Measure ℝ :=
  Measure.sum (fun n => convPow μ n)

/-- A law on `ℝ` is **spread out** when some convolution power has an absolutely continuous
component (Goldie 1991, §1, p. 127). Formalization Note: "has a nonzero absolutely continuous
component" is encoded as "is not mutually singular with Lebesgue measure" (the Lebesgue
decomposition makes these equivalent). Only powers `n ≥ 1` are considered; `μ^{(0)} = δ₀` is
singular anyway. -/
def SpreadOut (μ : Measure ℝ) : Prop :=
  ∃ n : ℕ, 1 ≤ n ∧ ¬ (convPow μ n ⟂ₘ volume)

/-- The real exponential transform `μ̃(β) = ∫ e^{βt} μ(dt)` at a real argument
(Goldie 1991, §1, p. 128), valued in `[0, ∞]` so that `μ̃(β) < ∞` is a meaningful condition. -/
noncomputable def expTransform (μ : Measure ℝ) (β : ℝ) : ENNReal :=
  ∫⁻ t, ENNReal.ofReal (Real.exp (β * t)) ∂μ

/-- The transform `μ̂(θ) = ∫ e^{iθt} μ(dt)` of a measure at a complex argument `θ`
(Goldie 1991, §1, p. 128; note the `+i` sign). Formalization Note: a Bochner integral; it is
meaningful wherever `t ↦ e^{iθt}` is `μ`-integrable, e.g. for `−β ≤ ℑθ ≤ 0` when `μ` is
finite and `μ̃(β) < ∞`. -/
noncomputable def charTransform (μ : Measure ℝ) (θ : ℂ) : ℂ :=
  ∫ t : ℝ, Complex.exp (I * θ * t) ∂μ

/-- The transform `f̂(θ) = ∫ e^{iθt} f(t) dt` of a (complex-valued) function on `ℝ` at a complex
argument `θ` (Goldie 1991, §1, p. 128; note the `+i` sign). A real function `g` enters through its
coercion `fun t => (g t : ℂ)`. Formalization Note: a Bochner integral with respect to Lebesgue
measure; it is meaningful wherever `t ↦ e^{iθt} f(t)` is integrable. -/
noncomputable def fourierTransform (f : ℝ → ℂ) (θ : ℂ) : ℂ :=
  ∫ t : ℝ, Complex.exp (I * θ * t) * f t

/-- Admissible contour data (Goldie 1991, Theorem 3.1, p. 131: "`𝒞` is a simple closed contour
in the domain `D := {θ : −β < ℑθ < 0}`, enclosing all the zeroes of `1 − η̂` in `D`").
Formalization Note: the contour is the positively oriented boundary of the axis-parallel
rectangle with lower-left corner `z` and upper-right corner `w`. The closed rectangle lies in
`D` (`−β < ℑz < ℑw < 0`), and every zero of `h` in the open strip `D` lies in the **open**
rectangle (so none lies on the contour). -/
def EnclosesZerosInStrip (h : ℂ → ℂ) (β : ℝ) (z w : ℂ) : Prop :=
  z.re < w.re ∧ -β < z.im ∧ z.im < w.im ∧ w.im < 0 ∧
    ∀ θ : ℂ, -β < θ.im → θ.im < 0 → h θ = 0 →
      (z.re < θ.re ∧ θ.re < w.re ∧ z.im < θ.im ∧ θ.im < w.im)

/-- The decomposition hypothesis (3.1) of Goldie 1991, Theorem 3.1 (p. 131), together with the
"subsequent conditions" of that theorem: for some `n₀`,
`η^{(n₀)} = (1 − δ)φ₀ + δφ₁` with `δ ∈ [0, 1)` constant, `φ₀`, `φ₁` probability measures,
`φ₀` absolutely continuous, `δ φ̃₁(β) < 1`, and `η̂(θ) ≠ 1` on the line `ℑθ = −β`. -/
def StoneConditions (η : Measure ℝ) (β : ℝ) : Prop :=
  (∃ (n₀ : ℕ) (δ : ℝ) (φ₀ φ₁ : Measure ℝ),
      0 ≤ δ ∧ δ < 1 ∧ IsProbabilityMeasure φ₀ ∧ IsProbabilityMeasure φ₁ ∧
      φ₀ ≪ volume ∧
      convPow η n₀ = ENNReal.ofReal (1 - δ) • φ₀ + ENNReal.ofReal δ • φ₁ ∧
      ENNReal.ofReal δ * expTransform φ₁ β < 1) ∧
    ∀ θ : ℂ, θ.im = -β → charTransform η θ ≠ 1

end GoldieRenewal.Rates


