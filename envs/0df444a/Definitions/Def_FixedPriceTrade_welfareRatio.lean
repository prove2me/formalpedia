-- Prove2me | Definitions.Def_FixedPriceTrade_welfareRatio
-- name    : FixedPriceTrade_welfareRatio
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:40:52.297767+00:00
-- url     : https://prove2.me/theorems/3c8ef0f4-3b4b-4108-8bfa-5635ecb0b849
-- title:
--   Admissible pairs, $M$, $G$, $\Gamma(z)$, $\Gamma_{\max}$ and the fixed-price welfare ratio
-- statement:
--   A seller with value $V_s$ and a buyer with value $V_b$ have **independent nonnegative values** with
--   $$
--   0<\mathbb E\max\{V_s,V_b\}<\infty .
--   $$
--   A pair of laws $(F_s,F_b)$ with these properties is called **admissible**. A deterministic price $z\ge0$ trades when $V_s\le z\le V_b$ (inclusive at both ends). Define
--   $$
--   M=\mathbb E V_s,\qquad G=\mathbb E(V_b-V_s)_+,\qquad \Gamma(z)=\mathbb E\big[(V_b-V_s)\mathbf 1\{V_s\le z\le V_b\}\big],
--   $$
--   $\Gamma_{\max}=\max_{z\ge0}\Gamma(z)$, and the **best fixed-price welfare ratio**
--   $$
--   r(F_s,F_b)=\frac{M+\Gamma_{\max}}{\mathbb E\max\{V_s,V_b\}} .
--   $$
--   The numerator is the welfare of the best price (the seller keeps the good unless trade happens) and the denominator is first-best welfare $M+G$.
--
--   These are the objects of the whole mission: Theorem A computes the infimum of $r$ over all admissible pairs.
--
--   **Formalization Note** Independence is the product $\mu_s\otimes\mu_b$ of the two laws on $\mathbb R$; nonnegativity is almost sure; $0<\mathbb E\max<\infty$ is integrability and positivity of $\int\max$. The gain from trade is the published `BilateralRegret.GFT`, $(b-s)\mathbf 1\{s\le z\le b\}$. $\Gamma_{\max}$ is written as the supremum of $\Gamma$ over $z\ge0$; the existence of the maximum is a theorem of the mission.
-- source:
--   Lin, Shi, Dong, Li, Yu, Zhang, The Exact Welfare Guarantee of Fixed-Price Bilateral Trade, arXiv:2609.35888 (held PDF sha256 26832346…), §3, (1)–(2), p.10; Theorem A, p.22

import Mathlib
import Definitions.Def_BilateralRegret_GFT

set_option autoImplicit false

namespace FixedPriceTrade

open MeasureTheory Set

/-- **Admissible pair of value laws** — Lin, Shi, Dong, Li, Yu, Zhang, *The Exact Welfare
Guarantee of Fixed-Price Bilateral Trade*, arXiv:2609.35888 (held PDF sha256 26832346…), §3, p.10:
"The independent values `V_s, V_b` are nonnegative and satisfy `0 < E max{V_s, V_b} < ∞`."

`μs` is the law of the seller's value `V_s`, `μb` the law of the buyer's value `V_b`.

**Formalization Note.** Independence is encoded by taking the joint law to be the product
`μs.prod μb` (for independent variables the joint law is the product, and every quantity of the
paper depends only on the joint law). Nonnegativity is almost sure: `μs (Iio 0) = 0`,
`μb (Iio 0) = 0`. Atoms and unbounded supports are allowed. "`E max < ∞`" is integrability of
`max` on the product. -/
def IsAdmissiblePair (μs μb : Measure ℝ) : Prop :=
  IsProbabilityMeasure μs ∧ IsProbabilityMeasure μb ∧ μs (Iio 0) = 0 ∧ μb (Iio 0) = 0 ∧
    Integrable (fun v : ℝ × ℝ => max v.1 v.2) (μs.prod μb) ∧
    0 < ∫ v, max v.1 v.2 ∂(μs.prod μb)

/-- `M = E V_s`, the seller's mean value ((1), p.10). -/
noncomputable def sellerMean (μs : Measure ℝ) : ℝ := ∫ s, s ∂μs

/-- `G = E (V_b − V_s)₊`, the first-best gains from trade ((1), p.10). -/
noncomputable def firstBestGFT (μs μb : Measure ℝ) : ℝ :=
  ∫ v, max (v.2 - v.1) 0 ∂(μs.prod μb)

/-- `Γ(z) = E[(V_b − V_s) 1{V_s ≤ z ≤ V_b}]`, the gains from trade at the fixed price `z`
((1), p.10), with the inclusive convention at both ends, through the published
`BilateralRegret.GFT z s b = (b − s)·𝕀{s ≤ z ≤ b}`. -/
noncomputable def priceGFT (μs μb : Measure ℝ) (z : ℝ) : ℝ :=
  ∫ v, BilateralRegret.GFT z v.1 v.2 ∂(μs.prod μb)

/-- `Γ_max = max_{z ≥ 0} Γ(z)` ((2), p.10), written as the supremum of `Γ` over `z ≥ 0`.

**Formalization Note.** The paper writes a maximum; its existence is a theorem (§3, p.10), and
the goal states it. Where the maximum exists, this supremum is the maximum. -/
noncomputable def gammaMax (μs μb : Measure ℝ) : ℝ :=
  sSup (priceGFT μs μb '' Ici 0)

/-- `E max{V_s, V_b}`, first-best welfare `W_FB = M + G` (p.10, p.22). -/
noncomputable def expectedMax (μs μb : Measure ℝ) : ℝ :=
  ∫ v, max v.1 v.2 ∂(μs.prod μb)

/-- **Best fixed-price welfare ratio** of a pair (Theorem A, p.22):
`max_{z ≥ 0} (E V_s + E[(V_b − V_s) 1{V_s ≤ z ≤ V_b}]) / E max{V_s, V_b} = (M + Γ_max) / E max`.

**Formalization Note.** The denominator is `E max{V_s, V_b}`, as printed in Theorem A; on an
admissible pair it is positive, so the division is genuine. -/
noncomputable def welfareRatio (μs μb : Measure ℝ) : ℝ :=
  (sellerMean μs + gammaMax μs μb) / expectedMax μs μb

end FixedPriceTrade


