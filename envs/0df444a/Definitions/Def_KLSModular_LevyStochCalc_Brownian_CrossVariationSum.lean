-- Prove2me | Definitions.Def_KLSModular_LevyStochCalc_Brownian_CrossVariationSum
-- name    : KLSModular_LevyStochCalc_Brownian_CrossVariationSum
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T17:11:55.722369+00:00
-- url     : https://prove2.me/theorems/a1ff2b05-5818-415f-a2f2-029a029a1d6c
-- title:
--   Cross increments of two Brownian Itô integrals
-- statement:
--   Vendored from the LevyStochCalc library at https://github.com/cgarryZA/LevyStochCalc, commit 984dbf0b790031eac05d56fe5a84b65e15e1e932. Under the stated probability, Brownian-filtration, measurability, progressive-measurability, and finite-energy assumptions for $H$ and $K$, `crossIncrement W ℱ hcoord H K i j a b ω` is the product of the increment of the Itô integral of $H$ against coordinate $i$ and the increment of the Itô integral of $K$ against coordinate $j$ across $(a,b]$.
--
--   **Original module imports**
--
--   ```lean
--   import LevyStochCalc.Brownian.CrossVariation
--   import LevyStochCalc.Brownian.ItoIncrementMoment
--   import LevyStochCalc.Probability.MartingaleDifference
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   noncomputable def crossIncrement (i j : Fin d) (a b : ℝ) (ω : Ω) : ℝ :=
--     (stochasticIntegralBrownian (W.W i) ℱ (hcoord i) H hHm hHp hHs b ω
--         - stochasticIntegralBrownian (W.W i) ℱ (hcoord i) H hHm hHp hHs a ω)
--       * (stochasticIntegralBrownian (W.W j) ℱ (hcoord j) K hKm hKp hKs b ω
--         - stochasticIntegralBrownian (W.W j) ℱ (hcoord j) K hKm hKp hKs a ω)
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`LevyStochCalc/Brownian/CrossVariation`](https://prove2.me/theorems/1ab4e629-ed7f-48bb-b1cc-41ccac0e463c), [`LevyStochCalc/Brownian/ItoIncrementMoment`](https://prove2.me/theorems/9d2f693b-1d18-45b2-b295-411fcadbdbe2), [`LevyStochCalc/Probability/MartingaleDifference`](https://prove2.me/theorems/11d45bb7-a48e-4057-92a2-d82e2c13aef6).
--
--   Theorems in source order:
--
--   - [`integrable_sq_mul_and_le`](https://prove2.me/theorems/9194c79a-683c-4a17-8bf7-6d933792ea69)
--   - [`integral_sq_weighted_crossSum_le`](https://prove2.me/theorems/5d328781-1a8c-43bf-be55-0a5141e07939)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/CrossVariationSum.lean) · `LevyStochCalc.Brownian.CrossVariationSum` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/CrossVariationSum.lean#L76-L82 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.CrossVariationSum`, definition bundle `KLSModular_LevyStochCalc_Brownian_CrossVariationSum`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_CrossVariation
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoIncrementMoment
import Definitions.Def_KLSModular_LevyStochCalc_Probability_MartingaleDifference

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/CrossVariationSum.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
namespace LevyStochCalc
namespace Brownian
namespace Ito
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
section CrossSum
open LevyStochCalc.Brownian.Multidim
variable {d : ℕ} (W : Multidim.MultidimBrownianMotion P d)
  (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ)
  {H K : Ω → ℝ → ℝ} (hHm : Measurable (Function.uncurry H))
  (hHp : Probability.ProgressivelyMeasurable ℱ H)
  (hHs : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
  (hKm : Measurable (Function.uncurry K))
  (hKp : Probability.ProgressivelyMeasurable ℱ K)
  (hKs : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖K ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
/-- The product of the increments of the Itô integrals against the coordinates `i` and `j`
across `(a, b]`. -/
noncomputable def crossIncrement (i j : Fin d) (a b : ℝ) (ω : Ω) : ℝ :=
  (stochasticIntegralBrownian (W.W i) ℱ (hcoord i) H hHm hHp hHs b ω
      - stochasticIntegralBrownian (W.W i) ℱ (hcoord i) H hHm hHp hHs a ω)
    * (stochasticIntegralBrownian (W.W j) ℱ (hcoord j) K hKm hKp hKs b ω
      - stochasticIntegralBrownian (W.W j) ℱ (hcoord j) K hKm hKp hKs a ω)
variable {CH CK : ℝ} (hCH0 : 0 ≤ CH) (hCH : ∀ ω s, |H ω s| ≤ CH)
  (hCK0 : 0 ≤ CK) (hCK : ∀ ω s, |K ω s| ≤ CK)
end CrossSum
end Ito
end Brownian
end LevyStochCalc


