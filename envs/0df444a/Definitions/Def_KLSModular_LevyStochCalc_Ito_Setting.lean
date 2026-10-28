-- Prove2me | Definitions.Def_KLSModular_LevyStochCalc_Ito_Setting
-- name    : KLSModular_LevyStochCalc_Ito_Setting
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T17:14:07.728117+00:00
-- url     : https://prove2.me/theorems/791dec12-d4eb-42e1-82f3-a7db61af16a7
-- title:
--   Jump-diffusion coefficient bundles and hypotheses
-- statement:
--   Vendored from the LevyStochCalc library (https://github.com/cgarryZA/LevyStochCalc). `JumpDiffusionCoeffs n d E` packages a drift $\mu:\mathbb{R}\times(\mathrm{Fin}\,n\to\mathbb{R})\to(\mathrm{Fin}\,n\to\mathbb{R})$, a diffusion coefficient $\sigma$ valued in $n\times d$ real matrices, and a jump coefficient $\gamma$ with mark space $E$. `JumpDiffusionCoeffs.IsLipschitz` requires a nonnegative constant and uniform state-Lipschitz bounds for $\mu$, the squared Frobenius-type diffusion difference, and the $L^2(\nu)$ jump difference; `JumpDiffusionCoeffs.IsRegular` requires joint measurability and finite $\mathbb{R}_{\ge 0}\cup\{\infty\}$-valued squared coefficient energies at the zero state on every positive finite time interval.
--
--   **Original module imports**
--
--   ```lean
--   import LevyStochCalc.Brownian.Multidim
--   import LevyStochCalc.Brownian.MultidimIto
--   import LevyStochCalc.Poisson.L2Isometry
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   structure JumpDiffusionCoeffs (n d : ℕ) (E : Type v) where
--     μ : ℝ → (Fin n → ℝ) → (Fin n → ℝ)
--     σ : ℝ → (Fin n → ℝ) → (Fin n → Fin d → ℝ)
--     γ : ℝ → (Fin n → ℝ) → E → (Fin n → ℝ)
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`LevyStochCalc/Brownian/Multidim`](https://prove2.me/theorems/e25335d2-7bb4-48bc-88b0-e5f06cc2eee3), [`LevyStochCalc/Brownian/MultidimIto`](https://prove2.me/theorems/6413978c-e660-4650-9908-2c63e1da7b0f), [`LevyStochCalc/Poisson/L2Isometry`](https://prove2.me/theorems/b0a5e53b-eaa8-4b6f-9af9-19e2336c33f9).
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Ito/Setting.lean) · `LevyStochCalc.Ito.Setting` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Ito/Setting.lean#L61-L108 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Ito.Setting`, definition bundle `KLSModular_LevyStochCalc_Ito_Setting`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Multidim
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_MultidimIto
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_L2Isometry

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Ito/Setting.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace LevyStochCalc
namespace Ito
namespace Setting
universe u v
section Coefficients
variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]
/-- Coefficient bundle for a jump diffusion: drift `μ`, diffusion `σ`, jump
size `γ`. Lipschitz / measurability hypotheses live on the headline theorem. -/
structure JumpDiffusionCoeffs (n d : ℕ) (E : Type v) where
  μ : ℝ → (Fin n → ℝ) → (Fin n → ℝ)
  σ : ℝ → (Fin n → ℝ) → (Fin n → Fin d → ℝ)
  γ : ℝ → (Fin n → ℝ) → E → (Fin n → ℝ)
/-- Joint Lipschitz hypothesis on the jump-diffusion coefficients
`(μ, σ, γ)`. Required for `JumpDiffusion.exists_unique` (Applebaum 2009
Thm 6.2.9 — without this, Tanaka's example shows uniqueness can fail,
e.g. `dX_t = |X_t|^α dW_t` for `α < 1/2` has infinitely many strong
solutions; cf. Karatzas-Shreve 5.3.2). -/
def JumpDiffusionCoeffs.IsLipschitz {n d : ℕ}
    (coeffs : JumpDiffusionCoeffs n d E) (ν : Measure E) (L : ℝ) : Prop :=
  0 ≤ L ∧
  -- μ uniformly Lipschitz in x:
  (∀ s : ℝ, ∀ x₁ x₂ : Fin n → ℝ,
    ‖coeffs.μ s x₁ - coeffs.μ s x₂‖ ≤ L * ‖x₁ - x₂‖) ∧
  -- σ uniformly Lipschitz in x (with the Frobenius / Euclidean norm on matrices):
  (∀ s : ℝ, ∀ x₁ x₂ : Fin n → ℝ,
    (∑ i, ∑ j, (coeffs.σ s x₁ i j - coeffs.σ s x₂ i j) ^ 2)
      ≤ L ^ 2 * ‖x₁ - x₂‖ ^ 2) ∧
  -- γ uniformly Lipschitz in x (L²-in-e sense):
  (∀ s : ℝ, ∀ x₁ x₂ : Fin n → ℝ,
    ∫⁻ e, (‖coeffs.γ s x₁ e - coeffs.γ s x₂ e‖₊ : ℝ≥0∞) ^ 2 ∂ν
      ≤ ENNReal.ofReal (L ^ 2 * ‖x₁ - x₂‖ ^ 2))
/-- Regularity of the jump-diffusion coefficients in the time and mark variables: joint
measurability, and square integrability in `s` at a single state.

`JumpDiffusionCoeffs.IsLipschitz` constrains `(μ, σ, γ)` only in the state variable, while the
`is_solution` field of `JumpDiffusion` needs joint measurability, progressive measurability and
`L²` bounds of the integrands along the path. Together with the Lipschitz clauses, the bounds
below give those `L²` bounds along any `L²`-bounded path, since Lipschitz continuity in the
state gives `‖f s x‖ ≤ ‖f s 0‖ + L ‖x‖`. -/
def JumpDiffusionCoeffs.IsRegular {n d : ℕ}
    (coeffs : JumpDiffusionCoeffs n d E) (ν : Measure E) : Prop :=
  Measurable (Function.uncurry coeffs.μ) ∧
  Measurable (Function.uncurry coeffs.σ) ∧
  Measurable (fun p : ℝ × (Fin n → ℝ) × E => coeffs.γ p.1 p.2.1 p.2.2) ∧
  (∀ T : ℝ, 0 < T →
    ∫⁻ s in Set.Icc (0 : ℝ) T, (‖coeffs.μ s 0‖₊ : ℝ≥0∞) ^ 2 ∂volume < ⊤) ∧
  (∀ T : ℝ, 0 < T →
    ∫⁻ s in Set.Icc (0 : ℝ) T, ∑ i, ∑ j,
      (‖coeffs.σ s 0 i j‖₊ : ℝ≥0∞) ^ 2 ∂volume < ⊤) ∧
  (∀ T : ℝ, 0 < T →
    ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖coeffs.γ s 0 e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume < ⊤)
end Coefficients
end Setting
end Ito
end LevyStochCalc


