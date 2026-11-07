-- Prove2me | Definitions.Def_OMSRArbitrary_Guarantees
-- name    : OMSRArbitrary_Guarantees
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:35:17.90345+00:00
-- url     : https://prove2.me/theorems/76752e20-b29a-4d2c-b9cb-b782cd2fc876
-- title:
--   The guarantees $\alpha(g)$ of (3), $\alpha_\Lambda(g,c)$ of (4) and $\alpha_\infty(g,c)$ of (5)
-- statement:
--   Let $g:[0,1]\to[0,1]$ be the perturbation function of Perturbed Greedy and $c$ a tradeoff function with $0\le c\le g$. Put
--   $$\sigma(x)=\frac{1-g(1)}{1-g(x)},\qquad \sigma_\Lambda(x)=\frac{\sigma(x)}{\Lambda}\quad(\Lambda\in[1,\infty]).$$
--
--   1. **Unweighted guarantee**, eq. (3): $\alpha(g)=\min\{\alpha_1(g),\ \min_{y\in[0,1]}\alpha_2(g,y)\}$ with
--   $$\alpha_1(g)=\int_0^1\min\{g(x),\ \sigma(x)g(x)+1-g(x)\}\,dx,\qquad \alpha_2(g,y)=1-g(y)+\int_0^y\min\{g(x),\ \sigma(x)g(x)+g(y)-g(x)\}\,dx.$$
--   2. **Weighted guarantee**, eq. (4): $\alpha_\Lambda(g,c)=\min\{\alpha_{\Lambda,1}(g,c),\ \min_{y\in[0,1]}\alpha_{\Lambda,2}(g,c,y)\}$ with
--   $$\alpha_{\Lambda,1}(g,c)=\int_0^1\big(\min\{1-g(x)+(g(x)-c(x))\sigma_\Lambda(x),\ g(x)-c(x)\}+c(x)\big)\,dx,$$
--   $$\alpha_{\Lambda,2}(g,c,y)=1-g(y)+\int_0^y\Big(\min\{g(y)-g(x)+(g(x)-c(x))\sigma_\Lambda(x),\ g(x)-c(x)\}+c(x)\min\Big\{1,\frac{g(y)-g(x)}{(1-g(x))(1-\sigma_\Lambda(x))}\Big\}\Big)dx,$$
--   where the last minimum is read as $1$ when $\sigma_\Lambda(x)=1$.
--   3. **Arbitrary weights**, eq. (5):
--   $$\alpha_\infty(g,c)=\min\Big\{\int_0^1\big(\min\{g(x)-c(x),1-g(x)\}+c(x)\big)dx,\ \min_{y\in[0,1]}\Big[1-g(y)+\int_0^y\Big(\min\{g(x)-c(x),g(y)-g(x)\}+c(x)\frac{g(y)-g(x)}{1-g(x)}\Big)dx\Big]\Big\}.$$
--
--   These are the competitive ratios of Theorems 3 and 4.
--
--   **Formalization Note** $\Lambda$ is written through $\rho=1/\Lambda\in[0,1]$, so $\sigma_\Lambda=\rho\,\sigma$ (`sigmaW`); $\rho=0$ is $\Lambda=\infty$. "Read as 1" is an explicit case split, since Lean's division by zero returns $0$. The minima over $y$ are infima over the subtype $[0,1]$ of families that are nonnegative for admissible $g,c$; they are attained. $\alpha_\infty$ is written out as printed in (5). Integrals are interval integrals of bounded a.e.-measurable functions.
-- source:
--   Udwani, Online Matching with Arbitrary Stochastic Rewards, arXiv:2611.03598, §3, pp.12–13, eqs. (3), (4), (5)

import Mathlib

open MeasureTheory
noncomputable section

namespace OMSRArbitrary

/-- **The function σ**, Udwani, *Online Matching with Arbitrary Stochastic Rewards*,
arXiv:2611.03598, §3, p.12: `σ(x) := (1 − g(1))/(1 − g(x))`.

**Formalization Note.** The perturbation function `g` is a function `ℝ → ℝ`; every statement of
the mission assumes the paper's hypotheses on `[0,1]` only (continuous, nondecreasing, values in
`[0,1]`, `g(1) < 1`), so `1 − g(x) ≥ 1 − g(1) > 0` there and the division is genuine. -/
def sigma (g : ℝ → ℝ) (x : ℝ) : ℝ := (1 - g 1) / (1 - g x)

/-- **The weighted function σ_Λ**, arXiv:2611.03598, §3, p.12:
`σ_Λ(x) := σ(x)/Λ = (1 − g(1))/(Λ(1 − g(x)))` for `Λ ∈ [1, ∞]`.

**Formalization Note.** `Λ` is written through its reciprocal `ρ = 1/Λ ∈ [0,1]`, so
`σ_Λ = ρ σ`; `ρ = 0` is `Λ = ∞` (`σ_∞ ≡ 0`, p.13) and `ρ = 1` is `Λ = 1`. -/
def sigmaW (g : ℝ → ℝ) (ρ : ℝ) (x : ℝ) : ℝ := ρ * sigma g x

/-- `α₁(g) := ∫₀¹ min{g(x), σ(x)g(x) + 1 − g(x)} dx`, arXiv:2611.03598, §3, p.12. -/
def alpha1 (g : ℝ → ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1, min (g x) (sigma g x * g x + 1 - g x)

/-- `α₂(g, y) := 1 − g(y) + ∫₀^y min{g(x), σ(x)g(x) + g(y) − g(x)} dx`,
arXiv:2611.03598, §3, p.12. -/
def alpha2 (g : ℝ → ℝ) (y : ℝ) : ℝ :=
  1 - g y + ∫ x in (0 : ℝ)..y, min (g x) (sigma g x * g x + g y - g x)

/-- **The unweighted guarantee** `α(g) := min{α₁(g), min_{y∈[0,1]} α₂(g, y)}`, eq. (3),
arXiv:2611.03598, §3, p.12.

**Formalization Note.** The inner minimum is the infimum over the subtype `[0,1]`. For an
admissible `g` the family `α₂(g, ·)` is bounded below by `0` on `[0,1]` (both terms of the
integrand are nonnegative for `x ≤ y`), so the real infimum is the true infimum, and it is
attained by continuity. -/
def alpha (g : ℝ → ℝ) : ℝ :=
  min (alpha1 g) (⨅ y : Set.Icc (0 : ℝ) 1, alpha2 g y)

/-- `α_{Λ,1}(g, c) := ∫₀¹ (min{1 − g(x) + (g(x) − c(x))σ_Λ(x), g(x) − c(x)} + c(x)) dx`,
arXiv:2611.03598, §3, p.13 (with `σ_Λ = ρ σ`, `ρ = 1/Λ`). -/
def alphaW1 (g c : ℝ → ℝ) (ρ : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1, (min (1 - g x + (g x - c x) * sigmaW g ρ x) (g x - c x) + c x)

/-- `α_{Λ,2}(g, c, y) := 1 − g(y) + ∫₀^y ( min{g(y) − g(x) + (g(x) − c(x))σ_Λ(x), g(x) − c(x)}
+ c(x) min{1, (g(y) − g(x))/((1 − g(x))(1 − σ_Λ(x)))} ) dx` "(read as 1 if σ_Λ(x) = 1)",
arXiv:2611.03598, §3, p.13.

**Formalization Note.** The parenthetical "read as 1 if σ_Λ(x) = 1" is the explicit `if`;
without it Lean's `a / 0 = 0` would give the factor `min{1, 0} = 0`. -/
def alphaW2 (g c : ℝ → ℝ) (ρ y : ℝ) : ℝ :=
  1 - g y + ∫ x in (0 : ℝ)..y,
    (min (g y - g x + (g x - c x) * sigmaW g ρ x) (g x - c x) +
      c x * (if sigmaW g ρ x = 1 then 1 else
        min 1 ((g y - g x) / ((1 - g x) * (1 - sigmaW g ρ x)))))

/-- **The weighted guarantee** `α_Λ(g, c) := min{α_{Λ,1}(g, c), min_{y∈[0,1]} α_{Λ,2}(g, c, y)}`,
eq. (4), arXiv:2611.03598, §3, pp.12–13, written with `ρ = 1/Λ`.

**Formalization Note.** As for `alpha`, the inner minimum is an infimum over the subtype `[0,1]`
of a family bounded below by `0` for admissible `g, c`. -/
def alphaW (g c : ℝ → ℝ) (ρ : ℝ) : ℝ :=
  min (alphaW1 g c ρ) (⨅ y : Set.Icc (0 : ℝ) 1, alphaW2 g c ρ y)

/-- **The guarantee for arbitrary weights**, eq. (5), arXiv:2611.03598, §3, p.13:
`α_∞(g, c) = min{ ∫₀¹ (min{g(x) − c(x), 1 − g(x)} + c(x)) dx,
min_{y∈[0,1]} [1 − g(y) + ∫₀^y (min{g(x) − c(x), g(y) − g(x)} + c(x)(g(y) − g(x))/(1 − g(x))) dx] }`,
written out as printed (not as `alphaW` at `ρ = 0`). -/
def alphaInf (g c : ℝ → ℝ) : ℝ :=
  min (∫ x in (0 : ℝ)..1, (min (g x - c x) (1 - g x) + c x))
    (⨅ y : Set.Icc (0 : ℝ) 1,
      (1 - g y + ∫ x in (0 : ℝ)..(y : ℝ),
        (min (g x - c x) (g y - g x) + c x * ((g y - g x) / (1 - g x)))))

end OMSRArbitrary


