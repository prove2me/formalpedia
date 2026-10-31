-- Prove2me | Definitions.Def_PersuasionNetworks_Quantile
-- name    : PersuasionNetworks_Quantile
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:28:19.226289+00:00
-- url     : https://prove2.me/theorems/d6336ac9-51f4-4822-8006-2b8d8eda8b6a
-- title:
--   Quantile $F^{-1}$, extended CDF and $g(y)=\int_{1-y}^1 F^{-1}$
-- statement:
--   Let $F$ be the cumulative distribution function of the state, with law $\mu$, and let $\mathcal T\subseteq\mathbb R$ be the state space. This item fixes three objects.
--
--   1. The quantile function
--   $$
--   F^{-1}(q)=\inf\{t\in\mathcal T\mid F(t)\ge q\},
--   $$
--   with the infimum taken in the extended reals and $\inf\emptyset=+\infty$.
--
--   2. The extension of $F$ to the extended reals, with $F(-\infty)=0$ and $F(+\infty)=1$.
--
--   3. The function
--   $$
--   g(y)=\int_{1-y}^{1}F^{-1}(x)\,dx,\qquad y\in[0,1],
--   $$
--   which is the right-hand side of the first constraint of the program (OPT).
--
--   The two end points matter: $F^{-1}(0)=\inf\mathcal T$ can be $-\infty$, and $F^{-1}(1)$ can be $+\infty$. Algorithm 1 evaluates $F$ at such points.
--
--   **Formalization Note** The values of $F^{-1}$ on $(0,1)$ are real numbers under the standing assumptions, and the integrand of $g$ is the real part of the extended value; its junk value at $\pm\infty$ can occur only at $x=0,1$, a null set. No arithmetic is done in the extended reals.
-- source:
--   Candogan, Persuasion in Networks: Public Signals and Cores, SSRN 3346144 (preprint), https://ssrn.com/abstract=3346144, §2, p.9 (quantile); footnote 24, p.19 (end points); Proof of Lemma 3, p.40 (g)

import Mathlib

open MeasureTheory ProbabilityTheory

namespace PersuasionNetworks

/-- The **quantile function of the state**, `F⁻¹(q) = inf {t ∈ 𝒯 | F(t) ≥ q}`, where `F` is the
cumulative distribution function of `μ`. Candogan, *Persuasion in Networks: Public Signals and
Cores*, SSRN 3346144 (preprint), §2, p.9.

**Formalization Note.** The infimum is taken in `EReal`, with `inf ∅ = ⊤`, because `F⁻¹(0)` may be
`-∞` (when `𝒯` is unbounded below) and `F⁻¹(1)` may be `+∞` (when `F < 1` everywhere); footnote 24,
p.19, uses both endpoints. No arithmetic is ever done in `EReal`. -/
noncomputable def stateQuantile (μ : Measure ℝ) (𝒯 : Set ℝ) (q : ℝ) : EReal :=
  sInf ((fun t : ℝ => (t : EReal)) '' {t ∈ 𝒯 | q ≤ cdf μ t})

/-- The cumulative distribution function `F` of `μ` extended to the extended reals by `F(-∞) = 0`
and `F(+∞) = 1`. Candogan, SSRN 3346144 (preprint), footnote 24, p.19 and Algorithm 1, p.20, where
`F` is evaluated at the end points `tᵢ`, which may be infinite.

**Formalization Note.** This is the only way the extended end points enter the arithmetic of
(9)–(10). -/
noncomputable def extCdf (μ : Measure ℝ) (x : EReal) : ℝ :=
  if x = ⊥ then 0 else if x = ⊤ then 1 else cdf μ x.toReal

/-- The function `g(y) = ∫_{1-y}^{1} F⁻¹(x) dx`, for `y ∈ [0, 1]`, the right-hand side of the first
constraint of (OPT). Candogan, SSRN 3346144 (preprint), Proof of Lemma 3, p.40.

**Formalization Note.** `(stateQuantile μ 𝒯 x).toReal` is the real number `F⁻¹(x)` for `x ∈ (0, 1)`;
the junk value `0` of `toReal` at `±∞` can occur only at `x = 0, 1`, which no integral sees. `g` is
meaningful only on `[0, 1]`; constraints (O3)–(O4) keep its arguments there. -/
noncomputable def g (μ : Measure ℝ) (𝒯 : Set ℝ) (y : ℝ) : ℝ :=
  ∫ x in (1 - y)..1, (stateQuantile μ 𝒯 x).toReal

end PersuasionNetworks


