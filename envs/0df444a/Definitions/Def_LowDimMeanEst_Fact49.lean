-- Prove2me | Definitions.Def_LowDimMeanEst_Fact49
-- name    : LowDimMeanEst_Fact49
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T04:44:27.663954+00:00
-- url     : https://prove2.me/theorems/0ef0589e-1beb-45b1-a77d-0c0f1cd42792
-- title:
--   Fact 49's guarantee on an initial estimator: $\|\kappa-\mu\|\le C_F(\sqrt{\mathrm{Tr}\Sigma/m}+\sqrt{\|\Sigma\|_{op}\log(1/\delta)/m})$ w.p. $1-\delta$
-- statement:
--   Fact 49 of the paper, quoted from Diakonikolas, Kane and Pensia [DKP20], provides the initial estimate of Algorithm 1. Its guarantee is the following.
--
--   A family of estimators $\kappa_{d,m,\delta}:(\mathbb R^d)^m\to\mathbb R^d$ **has Fact 49's guarantee with constants** $(C_F,\Xi_F,\delta_F)$ if, for every $d\ge1$, $m\ge1$ and $\delta\in(0,\delta_F)$ with $m\ge\Xi_F\log\frac1\delta$, the map $\kappa_{d,m,\delta}$ is measurable and for every distribution $D$ on $\mathbb R^d$ with finite second moment, mean $\mu$ and covariance $\Sigma$,
--
--   $$\Pr_{y_1,\dots,y_m\sim D}\Big[\ \|\kappa_{d,m,\delta}(y)-\mu\|_2> C_F\Big(\sqrt{\tfrac{\mathrm{Tr}(\Sigma)}{m}}+\sqrt{\tfrac{\|\Sigma\|_{op}\log(1/\delta)}{m}}\Big)\Big]\le\delta .$$
--
--   The paper's main theorem is stated for every estimator family with this guarantee.
--
--   **Formalization Note** $\mathrm{Tr}(\Sigma)=\mathbb E\|X-\mu\|^2$ and $\|\Sigma\|_{op}=\sup_{\|z\|=1}\mathbb E\langle X-\mu,z\rangle^2$. The guarantee does not include the polynomial running time or the shift-scale-and-rotation equivariance of [DKP20]'s estimator. Measurability is required because the analysis conditions on the initial estimate.
-- source:
--   Lee, Mathashery, Valiant, Wang, Optimal Sub-Gaussian Mean Estimation in Low Dimensions, STOC 2027 submission (manuscript sha256 7316d30e…), Fact 49, p.87 (citing [DKP20], Proposition 1.6)

import Mathlib
import Definitions.Def_LowDimMeanEst_Basic

open MeasureTheory

namespace LowDimMeanEst

/-!
# The guarantee of Fact 49 on an initial estimator

Lee, Mathashery, Valiant, Wang, *Optimal Sub-Gaussian Mean Estimation in Low Dimensions*, STOC 2027
submission (manuscript sha256 7316d30e…), Fact 49, p.87 (citing [DKP20], Proposition 1.6):

"Consider a failure probability δ and sample size n ≥ Ξ log(1/δ) for some constant Ξ > 0. There
exists a polynomial time algorithm that, given n i.i.d. samples from any distribution D over ℝᵈ
with unknown mean µ and covariance Σ, outputs κ such that with probability at least 1 − δ,
∥κ − µ∥₂ ≤ O(√(Tr(Σ)/n) + √(∥Σ∥op log(1/δ)/n)). Furthermore, this estimator is
shift-scale-and-rotation equivariant."

**Formalization Note.**
* The paper uses Fact 49 as a black box. `IsFact49Estimator CF ΞF δF κ` states its error guarantee
  for a family of deterministic estimators `κ d m δ : (Fin m → E d) → E d` (one per dimension `d`,
  sample size `m` and confidence `δ`), with `CF` the constant of the `O(·)`, `ΞF` the sample-size
  constant, and the guarantee required only for `δ ∈ (0, δF)`. The estimator is required to be
  measurable (it is the output map of an algorithm; the analysis conditions on it).
* Equivariance and polynomial running time are **not** part of this predicate.
* `Tr(Σ) = E‖X − µ‖²` is `totalVar D`, and `∥Σ∥op = sup_{‖z‖=1} E⟨X − µ, z⟩²` is `opVar D`
  (a supremum of a nonempty set bounded by `totalVar D` when `d ≥ 1` and `MemLp id 2 D`).
-/

/-- `Tr(Σ) = E‖X − µ‖²`. -/
noncomputable def totalVar {d : ℕ} (D : Measure (E d)) : ℝ := ∫ x, ‖x - popMean D‖ ^ 2 ∂D

/-- `∥Σ∥op = sup_{‖z‖ = 1} E⟨X − µ, z⟩²`. -/
noncomputable def opVar {d : ℕ} (D : Measure (E d)) : ℝ :=
  sSup ((fun z => dirVar D z) '' Metric.sphere (0 : E d) 1)

/-- The guarantee of Fact 49: for every `d ≥ 1`, `m ≥ 1` and `δ ∈ (0, δF)` with `m ≥ ΞF log(1/δ)`,
the estimator `κ d m δ` is measurable, and for every probability distribution `D` on `ℝ^d` with
finite second moment, mean `µ` and covariance `Σ`,
`P_{D^m}[ ‖κ d m δ (y) − µ‖ > CF (√(Tr Σ/m) + √(∥Σ∥op log(1/δ)/m)) ] ≤ δ`. -/
def IsFact49Estimator (CF ΞF δF : ℝ) (κ : (d : ℕ) → (m : ℕ) → ℝ → (Fin m → E d) → E d) : Prop :=
  ∀ (d m : ℕ) (δ : ℝ), 1 ≤ d → 1 ≤ m → 0 < δ → δ < δF → ΞF * logInv δ ≤ (m : ℝ) →
    Measurable (κ d m δ) ∧
      ∀ (D : Measure (E d)) [IsProbabilityMeasure D], MemLp id 2 D →
        (Measure.pi fun _ : Fin m => D)
            {y | CF * (Real.sqrt (totalVar D / m) + Real.sqrt (opVar D * logInv δ / m)) <
                ‖κ d m δ y - popMean D‖} ≤ ENNReal.ofReal δ

end LowDimMeanEst


