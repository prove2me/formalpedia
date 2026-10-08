-- Prove2me | Definitions.Def_RiskControl_Optimal_Setting
-- name    : RiskControl_Optimal_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T03:35:14.56048+00:00
-- url     : https://prove2.me/theorems/53c29deb-7b10-497c-8b26-4d68c7066fd4
-- title:
--   §2.1, p. 4 and §4.3, p. 13 — the integral loss L(y; S) = ∫_{S^c} ℓ(y, z) dμ(z), the risk R(T), E[ℓ(Y; z) | X = x], the threshold sets (11) and E[|T(X)|]
-- statement:
--   These are the objects of §4.3 of Bates, Angelopoulos, Lei, Malik and Jordan, together with the risk of §2.1.
--
--   Let $(X, Y)$ take values in $\mathcal X \times \mathcal Y$ with law $P$, and let $\mathcal Z$ be a measurable space in which prediction sets live, so that a **set-valued predictor** is a map $\mathcal T : \mathcal X \to 2^{\mathcal Z}$ (in the paper's examples $\mathcal Z = \mathcal Y$). Fix a nonnegative cost $\ell : \mathcal Y \times \mathcal Z \to [0, \infty)$, where $\ell(y, z)$ is the cost of not including $z$ in the prediction set when the true response is $y$, and a measure $\mu$ on $\mathcal Z$.
--
--   1. **Loss.** For $y \in \mathcal Y$ and $\mathcal S \subseteq \mathcal Z$,
--   $$L(y; \mathcal S) = \int_{z \in \mathcal S^c} \ell(y, z)\, d\mu(z) \in [0, \infty].$$
--   2. **Risk.** The risk of a set-valued predictor $\mathcal T$ is $R(\mathcal T) = \mathbb E[L(Y, \mathcal T(X))] = \int L(y; \mathcal T(x))\, dP(x, y)$.
--   3. **Conditional expected cost.** For a Markov kernel $\kappa$ from $\mathcal X$ to $\mathcal Y$,
--   $$\mathbb E[\ell(Y; z) \mid X = x] = \int \ell(y, z)\, d\kappa(x)(y).$$
--   4. **Threshold predictor (11).** For $\lambda \in \mathbb R$,
--   $$\mathcal T_\lambda(x) = \{z \in \mathcal Z : \mathbb E[\ell(Y; z) \mid X = x] \ge -\lambda\}.$$
--   5. **Expected set size.** $\mathbb E[|\mathcal T(X)|] = \int \mu(\mathcal T(x))\, dP_X(x)$, where $P_X$ is the marginal law of $X$ and the size of a set is its $\mu$-measure.
--
--   These are the objects of Theorem 8: among all predictors whose risk does not exceed that of $\mathcal T_\lambda$, the threshold predictor (11) has the smallest expected size.
--
--   **Formalization Note** All integrals are lower Lebesgue integrals with values in $[0, \infty]$, so an infinite loss or risk is $+\infty$ and no integrability hypothesis is needed. The conditional expectation is computed through a kernel $\kappa$; every statement assumes that $\kappa$ disintegrates $P$ (i.e. $P$ is the composition of the marginal $P_X$ with $\kappa$), so that $\kappa(x)$ is a regular conditional distribution of $Y$ given $X = x$ and the formula in item 3 is a version of $\mathbb E[\ell(Y; z) \mid X = x]$. In (11) the threshold $-\lambda$ enters as the extended nonnegative real $\max(-\lambda, 0)$, which is $-\lambda$ for every $\lambda \le 0$. The size $|\cdot|$ is the measure $\mu$ of the loss (the paper's p. 13 describes $|\cdot|$ as Lebesgue or counting measure for Theorem 7; for Theorem 8 its proof measures sets with $\mu$).
-- source:
--   Bates, Angelopoulos, Lei, Malik & Jordan, arXiv:2101.02703v3, §2.1, risk R(𝒯), p. 4; §4.3, loss L(y; 𝒮) and (11), p. 13; Theorem 8 and |·|, p. 13

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace RiskControl.Optimal

/-- The loss `L(y; 𝒮) = ∫_{z ∈ 𝒮ᶜ} ℓ(y, z) dμ(z)` of §4.3 (Bates, Angelopoulos, Lei, Malik & Jordan,
arXiv:2101.02703v3, p. 13): the `μ`-integral of the nonnegative cost `ℓ(y, ·)` of *not* including
`z` in the prediction set `𝒮 ⊆ 𝒵`, when the true response is `y`. It is a lower Lebesgue integral
with values in `[0, ∞]`, so an infinite loss is `∞`, never a junk `0`. -/
noncomputable def setLoss {𝒴 𝒵 : Type*} [MeasurableSpace 𝒵] (μ : Measure 𝒵)
    (ℓ : 𝒴 → 𝒵 → ℝ≥0) (y : 𝒴) (S : Set 𝒵) : ℝ≥0∞ :=
  ∫⁻ z in Sᶜ, (ℓ y z : ℝ≥0∞) ∂μ

/-- The risk `R(𝒯) = 𝔼[L(Y, 𝒯(X))]` of a set-valued predictor `𝒯 : 𝒳 → 2^𝒵` (arXiv:2101.02703v3,
§2.1, p. 4) for the loss `L = setLoss μ ℓ` of §4.3, where `(X, Y)` has law `P`. A lower Lebesgue
integral in `[0, ∞]`. -/
noncomputable def risk {𝒳 𝒴 𝒵 : Type*} [MeasurableSpace 𝒳] [MeasurableSpace 𝒴]
    [MeasurableSpace 𝒵] (P : Measure (𝒳 × 𝒴)) (μ : Measure 𝒵) (ℓ : 𝒴 → 𝒵 → ℝ≥0)
    (T : 𝒳 → Set 𝒵) : ℝ≥0∞ :=
  ∫⁻ p, setLoss μ ℓ p.2 (T p.1) ∂P

/-- The conditional expected cost `𝔼[ℓ(Y; z) | X = x] = ∫ ℓ(y, z) dκ(x)(y)` (arXiv:2101.02703v3,
(11), p. 13), computed with a Markov kernel `κ` from `𝒳` to `𝒴`. Every statement using it assumes
that `κ` disintegrates the law `P` of `(X, Y)`, i.e. `P.fst ⊗ₘ κ = P`: then `κ x` is a regular
conditional distribution of `Y` given `X = x`, and `condLoss κ ℓ x z` is a version of the
conditional expectation `𝔼[ℓ(Y; z) | X = x]`. -/
noncomputable def condLoss {𝒳 𝒴 𝒵 : Type*} [MeasurableSpace 𝒳] [MeasurableSpace 𝒴]
    (κ : Kernel 𝒳 𝒴) (ℓ : 𝒴 → 𝒵 → ℝ≥0) (x : 𝒳) (z : 𝒵) : ℝ≥0∞ :=
  ∫⁻ y, (ℓ y z : ℝ≥0∞) ∂(κ x)

/-- The set-valued predictor (11) of arXiv:2101.02703v3, p. 13:
`𝒯_λ(x) = {z : 𝔼[ℓ(Y; z) | X = x] ≥ −λ}`, with the non-strict inequality as printed. For `λ ≤ 0`,
`ENNReal.ofReal (-lam)` is `−λ` itself. -/
def thresholdSet {𝒳 𝒴 𝒵 : Type*} [MeasurableSpace 𝒳] [MeasurableSpace 𝒴]
    (κ : Kernel 𝒳 𝒴) (ℓ : 𝒴 → 𝒵 → ℝ≥0) (lam : ℝ) (x : 𝒳) : Set 𝒵 :=
  {z | ENNReal.ofReal (-lam) ≤ condLoss κ ℓ x z}

/-- The expected set size `𝔼[|𝒯(X)|] = ∫ μ(𝒯(x)) dP_X(x)` of Theorem 8 (arXiv:2101.02703v3, p. 13),
where the size `|·|` is measured by the finite measure `μ` of §4.3 and `X` has the marginal law
`P.fst` of `P`. -/
noncomputable def expSize {𝒳 𝒴 𝒵 : Type*} [MeasurableSpace 𝒳] [MeasurableSpace 𝒴]
    [MeasurableSpace 𝒵] (P : Measure (𝒳 × 𝒴)) (μ : Measure 𝒵) (T : 𝒳 → Set 𝒵) : ℝ≥0∞ :=
  ∫⁻ x, μ (T x) ∂P.fst

end RiskControl.Optimal


