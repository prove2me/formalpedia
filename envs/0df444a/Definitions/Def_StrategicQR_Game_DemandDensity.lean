-- Prove2me | Definitions.Def_StrategicQR_Game_DemandDensity
-- name    : StrategicQR_Game_DemandDensity
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T18:55:13.84937+00:00
-- url     : https://prove2.me/theorems/1154f062-e4ef-4f97-b4ed-bc5c6aecaf60
-- title:
--   Sec. 3, p. 6 — demand density on $[0,\infty)$ with finite mean, its distribution function $F$, and the MSLR property (Definition 1)
-- statement:
--   The first-period demand of the model is a nonnegative continuous random variable $D$ with density $f$ and distribution function $F$. This module fixes three objects.
--
--   1. A **demand density** is a function $f:\mathbb R\to\mathbb R$ with $f\ge 0$, $f(x)=0$ for $x<0$, $\int_{\mathbb R} f = 1$, and finite mean, $\int_{\mathbb R} |x|\,f(x)\,dx<\infty$.
--   2. Its **distribution function** is
--   $$F(x)=\int_{(-\infty,x]} f(y)\,dy=\int_0^x f(y)\,dy .$$
--   3. The density satisfies the **monotone scaled likelihood ratio (MSLR) property** (Definition 1 of the paper) if, for every scale $\lambda\in(0,1]$, the ratio
--   $$x\longmapsto \frac{f(\lambda x)}{f(x)}$$
--   is monotonic (nondecreasing or nonincreasing) on the support $\{x : f(x)>0\}$.
--
--   The paper names the gamma, Weibull, uniform, exponential, power, beta, chi and chi-squared distributions as MSLR examples. MSLR is the paper's standing assumption on demand; footnote 2 says it is used for the existence of an equilibrium.
--
--   **Formalization Note** The finite mean is added: the profit with quick response contains $\mathbb E[p\xi D]$, and without it the Lean integral would silently be $0$. In MSLR the monotonicity direction may depend on $\lambda$, which is how the page phrases it ("for all $\lambda\le 1$ … $f(\lambda x)/f(x)$ is monotonic in $x$"). The support is read as $\{f>0\}$, so the ratio never divides by zero. Scales $\lambda\le 0$ are left out: for $\lambda<0$ the ratio is $0$ on $(0,\infty)$, and at $\lambda=0$ it would depend on the value of the density at the single point $0$.
-- source:
--   Cachon, Swinney, Purchasing, Pricing, and Quick Response in the Presence of Strategic Consumers, working paper (rev. Nov. 25, 2007), p. 6, Section 3 (demand D, F, f) and Definition 1 (MSLR); p. 7, footnote 2

import Mathlib

namespace StrategicQR.Game

open MeasureTheory

/-- A probability density of a nonnegative random variable with finite mean (Cachon–Swinney,
§3, p. 6: "a random variable `D ≥ 0` with distribution `F(·)` … and density `f(·)`"):
`f` is nonnegative, vanishes on `(-∞, 0)`, integrates to `1`, and `x ↦ x f(x)` is integrable. -/
structure IsDemandDensity (f : ℝ → ℝ) : Prop where
  nonneg : ∀ x, 0 ≤ f x
  eq_zero_of_neg : ∀ x, x < 0 → f x = 0
  integrable : Integrable f
  integral_eq_one : ∫ x, f x = 1
  integrable_mul_id : Integrable (fun x => x * f x)

/-- The distribution function `F(x) = ∫_{(-∞, x]} f = ∫_{[0, x]} f` of the density `f`. -/
noncomputable def demandCdf (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ y in Set.Iic x, f y

/-- Definition 1 (p. 6), the monotone scaled likelihood ratio (MSLR) property: for every
scale `l ∈ (0, 1]`, the ratio `x ↦ f(l x) / f(x)` is monotonic (nondecreasing or nonincreasing;
the direction may depend on `l`) on the support `{x | 0 < f x}` of `f`. -/
def MSLR (f : ℝ → ℝ) : Prop :=
  ∀ l : ℝ, 0 < l → l ≤ 1 →
    MonotoneOn (fun x => f (l * x) / f x) {x | 0 < f x} ∨
      AntitoneOn (fun x => f (l * x) / f x) {x | 0 < f x}

end StrategicQR.Game


