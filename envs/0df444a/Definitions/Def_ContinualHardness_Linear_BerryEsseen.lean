-- Prove2me | Definitions.Def_ContinualHardness_Linear_BerryEsseen
-- name    : ContinualHardness_Linear_BerryEsseen
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T14:11:13.312194+00:00
-- url     : https://prove2.me/theorems/59eb195d-fa2d-4354-87fa-04247b21464b
-- title:
--   Berry–Esseen constants for independent, non-identically distributed summands (Eq. (5))
-- statement:
--   A real number $c_1$ is a **Berry–Esseen constant** (`IsBerryEsseenConstant c₁`) if $c_1>0$ and the following holds. For every $n\ge1$, every probability space $(\Omega,\Pr)$ and all independent real random variables $X_1,\dots,X_n$ with $\mathbb E[X_i]=0$, variances $\operatorname{Var}[X_i]=\sigma_i^2>0$ and finite third absolute moments, put $\sigma^2=\sum_{i}\sigma_i^2$ and $\gamma=\sigma^{-1}\max_{i\in[n]}\mathbb E[|X_i|^3]/\sigma_i^2$. Then for every $t\in\mathbb R$
--   $$\Big|\Pr\Big[\sigma^{-1}\sum_{i\in[n]}X_i\le t\Big]-\Phi(t)\Big|\le c_1\gamma,$$
--   where $\Phi$ is the CDF of the standard Gaussian $N(0,1)$. Theorem A.1 asserts that such a constant exists; the parameter $\tau$ of the dictatorship test (7) is computed from it.
--
--   **Formalization Note.** $\Omega$ ranges over all measurable spaces in `Type`; $\Phi$ is `cdf (gaussianReal 0 1)`; the maximum over $[n]$ is a supremum over the finite nonempty index set `Fin n`.
-- source:
--   Saket, Intractability of Continual Learning using Parametric Models with Unlimited Replay Buffer, STOC 2027 submission (manuscript sha256 86821df1…), p. 16, Theorem A.1, Eq. (5) (PDF p. 17)

import Mathlib

namespace ContinualHardness.Linear

open MeasureTheory ProbabilityTheory

/-! # Berry–Esseen constants (Theorem A.1, Eq. (5))

`IsBerryEsseenConstant c₁` says that `c₁ > 0` and the Berry–Esseen inequality (5) holds with the
constant `c₁` for every finite family of independent, centred, real random variables with
positive variances and finite third absolute moments, on every probability space. -/

/-- `c₁` is a Berry–Esseen constant: `c₁ > 0`, and for every `n ≥ 1`, every probability space
`(Ω, P)` and all independent random variables `X₁, …, Xₙ` with `E[Xᵢ] = 0`, `Var[Xᵢ] = σᵢ² > 0`
and `E|Xᵢ|³ < ∞`, writing `σ² = ∑ᵢ σᵢ²` and `γ = σ⁻¹ maxᵢ E[|Xᵢ|³]/σᵢ²`,
`sup_{t ∈ ℝ} |Pr[σ⁻¹ ∑ᵢ Xᵢ ≤ t] − Φ(t)| ≤ c₁ γ`, with `Φ` the CDF of `N(0, 1)`. -/
def IsBerryEsseenConstant (c₁ : ℝ) : Prop :=
  0 < c₁ ∧
  ∀ (n : ℕ), 0 < n →
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (X : Fin n → Ω → ℝ),
      (∀ i, Measurable (X i)) → iIndepFun X P → (∀ i, MemLp (X i) 3 P) →
      (∀ i, P[X i] = 0) → (∀ i, 0 < variance (X i) P) →
      ∀ t : ℝ,
        |(P {ω | (Real.sqrt (∑ i, variance (X i) P))⁻¹ * ∑ i, X i ω ≤ t}).toReal
            - cdf (gaussianReal 0 1) t|
          ≤ c₁ * ((Real.sqrt (∑ i, variance (X i) P))⁻¹ *
              ⨆ i, (P[fun ω => |X i ω| ^ 3] / variance (X i) P))

end ContinualHardness.Linear


