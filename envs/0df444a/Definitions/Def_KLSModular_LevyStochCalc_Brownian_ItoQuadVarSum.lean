-- Prove2me | Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoQuadVarSum
-- name    : KLSModular_LevyStochCalc_Brownian_ItoQuadVarSum
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T17:08:18.743383+00:00
-- url     : https://prove2.me/theorems/1add907f-537c-4a62-9c27-fe90c9b4a510
-- title:
--   Compensated square increments of a Brownian Itô integral
-- statement:
--   Vendored from the LevyStochCalc library at https://github.com/cgarryZA/LevyStochCalc, commit 984dbf0b790031eac05d56fe5a84b65e15e1e932. Given a Brownian motion $W$ under a probability measure $P$, a filtration satisfying `IsBrownianFiltration`, and a progressively measurable integrand $H$ with finite $L^2$ energy on every positive window, `quadVarIncrement W ℱ hℱ H ... a b ω` is $(M_b-M_a)^2-\int_{[0,b]}H_s^2\,ds+\int_{[0,a]}H_s^2\,ds$, where $M_t$ is the Brownian Itô integral of $H$.
--
--   **Original module imports**
--
--   ```lean
--   import LevyStochCalc.Brownian.ItoIncrementMoment
--   import LevyStochCalc.Probability.MartingaleDifference
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   noncomputable def quadVarIncrement (a b : ℝ) (ω : Ω) : ℝ :=
--     (stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
--         - stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 2
--       - ((∫ u in Set.Icc (0 : ℝ) b, (H ω u) ^ 2 ∂volume)
--           - ∫ u in Set.Icc (0 : ℝ) a, (H ω u) ^ 2 ∂volume)
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`LevyStochCalc/Brownian/ItoIncrementMoment`](https://prove2.me/theorems/9d2f693b-1d18-45b2-b295-411fcadbdbe2), [`LevyStochCalc/Probability/MartingaleDifference`](https://prove2.me/theorems/11d45bb7-a48e-4057-92a2-d82e2c13aef6).
--
--   Theorems in source order:
--
--   - [`condExp_quadVarIncrement`](https://prove2.me/theorems/cb7ab2d0-c60c-4b01-a336-abec1be3188b)
--   - [`compensator_sub_bounds`](https://prove2.me/theorems/5e8ee404-c1c1-469d-8d85-45ab11b64d10)
--   - [`memLp_two_sq_increment`](https://prove2.me/theorems/bdf6946b-1242-4316-90ea-7306d70caa0e)
--   - [`integral_sq_quadVarIncrement_le`](https://prove2.me/theorems/bb94fb53-5983-4031-9e2b-578cca0d2b19)
--   - [`exists_continuous_modification_stochasticIntegralBrownian`](https://prove2.me/theorems/e5f854d8-aecd-421d-a4fc-24ba2b3c40e0)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoQuadVarSum.lean) · `LevyStochCalc.Brownian.ItoQuadVarSum` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ItoQuadVarSum.lean#L49-L54 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ItoQuadVarSum`, definition bundle `KLSModular_LevyStochCalc_Brownian_ItoQuadVarSum`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoIncrementMoment
import Definitions.Def_KLSModular_LevyStochCalc_Probability_MartingaleDifference

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoQuadVarSum.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
namespace LevyStochCalc
namespace Brownian
namespace Ito
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
section QuadVarIncrement
variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
  (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
  (hp : Probability.ProgressivelyMeasurable ℱ H)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
/-- The compensated square increment `(M_b − M_a)² − ∫_a^b H_s² ds` of the Itô integral. -/
noncomputable def quadVarIncrement (a b : ℝ) (ω : Ω) : ℝ :=
  (stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
      - stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 2
    - ((∫ u in Set.Icc (0 : ℝ) b, (H ω u) ^ 2 ∂volume)
        - ∫ u in Set.Icc (0 : ℝ) a, (H ω u) ^ 2 ∂volume)
end QuadVarIncrement
end Ito
end Brownian
end LevyStochCalc


