-- Prove2me | Definitions.Def_KLSModular_LevyStochCalc_Brownian_PolarisedQuadVar
-- name    : KLSModular_LevyStochCalc_Brownian_PolarisedQuadVar
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T17:13:22.176104+00:00
-- url     : https://prove2.me/theorems/00553e93-f879-4904-9333-b2c00471b79f
-- title:
--   Polarised compensated quadratic increment
-- statement:
--   Vendored from the LevyStochCalc library at https://github.com/cgarryZA/LevyStochCalc, commit 984dbf0b790031eac05d56fe5a84b65e15e1e932. Given two progressively measurable square-integrable integrands $H_1,H_2$ for the same Brownian motion, `polarQuadVarIncrement` is the product of their Itô-integral increments across $(a,b]$ minus the Lebesgue integral of $H_1H_2$ over the corresponding interval difference $[0,b]-[0,a]$.
--
--   **Original module imports**
--
--   ```lean
--   import LevyStochCalc.Brownian.ItoQuadVarSum
--   import LevyStochCalc.Brownian.ItoLinear
--   import LevyStochCalc.Brownian.DriftIncrement
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   noncomputable def polarQuadVarIncrement (a b : ℝ) (ω : Ω) : ℝ :=
--     (stochasticIntegralBrownian W ℱ hℱ H₁ hm₁ hp₁ hq₁ b ω
--         - stochasticIntegralBrownian W ℱ hℱ H₁ hm₁ hp₁ hq₁ a ω)
--       * (stochasticIntegralBrownian W ℱ hℱ H₂ hm₂ hp₂ hq₂ b ω
--         - stochasticIntegralBrownian W ℱ hℱ H₂ hm₂ hp₂ hq₂ a ω)
--       - ((∫ u in Set.Icc (0 : ℝ) b, H₁ ω u * H₂ ω u ∂volume)
--         - ∫ u in Set.Icc (0 : ℝ) a, H₁ ω u * H₂ ω u ∂volume)
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`LevyStochCalc/Brownian/ItoQuadVarSum`](https://prove2.me/theorems/1add907f-537c-4a62-9c27-fe90c9b4a510), [`LevyStochCalc/Brownian/ItoLinear`](https://prove2.me/theorems/0a2c3dbb-5791-49a2-875b-20068ab8311a), [`LevyStochCalc/Brownian/DriftIncrement`](https://prove2.me/theorems/46f140f5-271c-46b4-a62d-8c251e00fc2b).
--
--   Theorems in source order:
--
--   - [`compensator_add_sq_eq`](https://prove2.me/theorems/89a9fb44-6d50-4dd1-8c08-30019bcfbb53)
--   - [`memLp_two_polarQuadVarIncrement`](https://prove2.me/theorems/e1f3d644-9e95-4545-bc1a-84c062eb6f44)
--   - [`condExp_polarQuadVarIncrement`](https://prove2.me/theorems/90ba8838-f516-4c4a-a54e-03f7270ecbb4)
--   - [`stronglyMeasurable_polarQuadVarIncrement`](https://prove2.me/theorems/257fc5bd-0d48-42b0-a71b-4fcd26b462bd)
--   - [`integral_sq_polarQuadVarIncrement_le`](https://prove2.me/theorems/3e500a78-fa1d-4509-8fce-e931788339ed)
--   - [`integral_sq_weighted_polarQuadVarSum_le`](https://prove2.me/theorems/194ed6f8-bb43-4c00-b88b-c7080958b1e9)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/PolarisedQuadVar.lean) · `LevyStochCalc.Brownian.PolarisedQuadVar` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/PolarisedQuadVar.lean#L54-L62 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.PolarisedQuadVar`, definition bundle `KLSModular_LevyStochCalc_Brownian_PolarisedQuadVar`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoQuadVarSum
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoLinear
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_DriftIncrement

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/PolarisedQuadVar.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
namespace LevyStochCalc
namespace Brownian
namespace Ito
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
section Polarised
variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
  (H₁ H₂ : Ω → ℝ → ℝ)
  (hm₁ : Measurable (Function.uncurry H₁)) (hm₂ : Measurable (Function.uncurry H₂))
  (hp₁ : Probability.ProgressivelyMeasurable ℱ H₁)
  (hp₂ : Probability.ProgressivelyMeasurable ℱ H₂)
  (hq₁ : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
  (hq₂ : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
  (hma : Measurable (Function.uncurry fun ω s => H₁ ω s + H₂ ω s))
  (hpa : Probability.ProgressivelyMeasurable ℱ fun ω s => H₁ ω s + H₂ ω s)
  (hqa : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H₁ ω s + H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
/-- The product of the increments of the Itô integrals of `H₁` and `H₂` against the same Brownian
motion, compensated by the window integral of `H₁·H₂`. -/
noncomputable def polarQuadVarIncrement (a b : ℝ) (ω : Ω) : ℝ :=
  (stochasticIntegralBrownian W ℱ hℱ H₁ hm₁ hp₁ hq₁ b ω
      - stochasticIntegralBrownian W ℱ hℱ H₁ hm₁ hp₁ hq₁ a ω)
    * (stochasticIntegralBrownian W ℱ hℱ H₂ hm₂ hp₂ hq₂ b ω
      - stochasticIntegralBrownian W ℱ hℱ H₂ hm₂ hp₂ hq₂ a ω)
    - ((∫ u in Set.Icc (0 : ℝ) b, H₁ ω u * H₂ ω u ∂volume)
      - ∫ u in Set.Icc (0 : ℝ) a, H₁ ω u * H₂ ω u ∂volume)
end Polarised
end Ito
end Brownian
end LevyStochCalc


