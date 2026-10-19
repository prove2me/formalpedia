-- Prove2me | Definitions.Def_CrowdContest_Pooling_Density
-- name    : CrowdContest_Pooling_Density
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T20:11:10.559394+00:00
-- url     : https://prove2.me/theorems/83a1ba9e-531b-46fd-a7e1-8aac34824e9d
-- title:
--   §3 p. 12, §4.2 p. 16, (A.4) OA p. 2 — densities, symmetric log-concave densities, cdf Ψ, convolution ψ°, quantile Ψ⁻¹, expected maximum E(ξ_(n))
-- statement:
--   General objects for a real random variable with a density, used throughout the Hu–Wang contest model.
--
--   1. A **density** is a measurable function $\varphi:\mathbb R\to[0,\infty)$ with $\int_{\mathbb R}\varphi(x)\,dx = 1$.
--   2. A **symmetric log-concave density** is a density $\psi$ with $\psi(-x)=\psi(x)$ for all $x$ that is log-concave in the multiplicative form
--   $$\psi(x)^{a}\,\psi(y)^{b}\le\psi(ax+by)\qquad(a,b\ge 0,\ a+b=1),$$
--   which allows $\psi$ to vanish outside an interval. This is the standing assumption on the random factors of the paper (§3, p. 12).
--   3. The **cdf** of a density $\psi$ is $\Psi(x)=\int_{(-\infty,x]}\psi(t)\,dt$.
--   4. The **convolution** $\psi^\circ(x)=\int_{\mathbb R}\psi(t)\,\psi(x-t)\,dt$ is the density of $\xi^1+\xi^2$ when $\xi^1,\xi^2$ are independent with density $\psi$; its cdf is $\Psi^\circ$.
--   5. The **quantile function** of a distribution function $F$ is $F^{-1}(u)=\inf\{x : u\le F(x)\}$.
--   6. The **expected maximum** of $n$ independent draws from $\psi$ is written through the density $n\Psi^{n-1}\psi$ of the maximum,
--   $$\mathsf E(\xi_{(n)})=\int_{-\infty}^{+\infty}\xi\, n\,\Psi(\xi)^{n-1}\psi(\xi)\,d\xi,$$
--   the first expression of display (A.4).
--
--   These objects describe the random factors of the contest model and the expected best random factor among $n$ contestants.
--
--   **Formalization Note** Log-concavity is the published platform definition `ConvexOptimization.LogConcaveOn` on all of $\mathbb R$, in the power form above; it is not the concavity of `Real.log ∘ ψ`, which would read $\log 0$ as $0$. The paper's "mean 0 and standard deviation $\sigma>0$" are not separate conditions: a log-concave density has finite moments of all orders, so symmetry gives mean $0$, and every density has positive variance. All integrals are Bochner integrals, which are $0$ for non-integrable integrands; under the density hypotheses every integrand used is integrable ($0\le\Psi\le 1$, and a log-concave density is bounded with exponential tails), and $\int\varphi=1$ itself forces integrability. The quantile is a real `sInf`; it is a true infimum for $u\in(0,1)$ and is only used there.
-- source:
--   Hu & Wang, Joint vs. Separate Crowdsourcing Contests, authors' accepted manuscript (TSpace; SSRN 2892683; Manag. Sci. doi:10.1287/mnsc.2020.3683), §3, p. 12 (Ψ, ψ, symmetric log-concave); §4.2, p. 16 (ξ° = ξ¹ + ξ², ψ°, Ψ°); Assumption (R), p. 17 (quantile functions); proof of Lemma 4, (A.4), OA p. 2 (E(ξ_(n)))

import Mathlib
import Definitions.Def_LogConcaveOn

open MeasureTheory

namespace CrowdContest.Pooling

/-- `φ : ℝ → ℝ` is a probability density on `ℝ`: measurable, nonnegative, with total
(Lebesgue) integral `1`. Since a non-integrable function has Bochner integral `0`, the condition
`∫ φ = 1` forces `φ` to be integrable. -/
def IsDensity (φ : ℝ → ℝ) : Prop :=
  Measurable φ ∧ (∀ x, 0 ≤ φ x) ∧ ∫ x, φ x = 1

/-- The standing distributional assumption of Hu & Wang (§3, p. 12): the random factor has a
density `ψ` that is symmetric about `0` and log-concave. Log-concavity is the published
`ConvexOptimization.LogConcaveOn` in its power form `ψ x ^ a * ψ y ^ b ≤ ψ (a x + b y)`, which
allows `ψ` to vanish. -/
def IsSymLogConcaveDensity (ψ : ℝ → ℝ) : Prop :=
  IsDensity ψ ∧ (∀ x, ψ (-x) = ψ x) ∧ ConvexOptimization.LogConcaveOn Set.univ ψ

/-- The cumulative distribution function `Ψ(x) = ∫_{(-∞, x]} ψ` of the density `ψ`. -/
noncomputable def cdf (ψ : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ t in Set.Iic x, ψ t

/-- The convolution `ψ°(x) = ∫ ψ(t) ψ(x - t) dt`: the density of `ξ¹ + ξ²` for independent
`ξ¹, ξ²` with common density `ψ`. Its cdf is `Ψ° = cdf (convDensity ψ)`. -/
noncomputable def convDensity (ψ : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ t, ψ t * ψ (x - t)

/-- The (left-continuous) quantile function `F⁻¹(u) = inf {x | u ≤ F x}` of a distribution
function `F`. For a cdf `F` and `u ∈ (0,1)` the set is nonempty and bounded below; at `u ∉ (0,1)`
the value is a junk value and is never used. -/
noncomputable def quantile (F : ℝ → ℝ) (u : ℝ) : ℝ :=
  sInf {x : ℝ | u ≤ F x}

/-- The expected value of the largest of `n` independent draws from the density `ψ`, written
through the density `n Ψ^{n-1} ψ` of the maximum:
`E(ξ_(n)) = ∫ ξ n Ψ(ξ)^{n-1} ψ(ξ) dξ` (first expression of (A.4), Hu & Wang, OA p. 2). -/
noncomputable def expMax (ψ : ℝ → ℝ) (n : ℕ) : ℝ :=
  ∫ ξ, ξ * (n : ℝ) * cdf ψ ξ ^ (n - 1) * ψ ξ

end CrowdContest.Pooling


