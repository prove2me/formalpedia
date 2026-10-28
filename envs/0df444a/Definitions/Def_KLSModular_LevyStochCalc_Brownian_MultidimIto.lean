-- Prove2me | Definitions.Def_KLSModular_LevyStochCalc_Brownian_MultidimIto
-- name    : KLSModular_LevyStochCalc_Brownian_MultidimIto
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T16:22:28.333162+00:00
-- url     : https://prove2.me/theorems/6413978c-e660-4650-9908-2c63e1da7b0f
-- title:
--   Multidimensional Brownian Itô integral
-- statement:
--   Vendored from the LevyStochCalc library (https://github.com/cgarryZA/LevyStochCalc), commit 984dbf0b790031eac05d56fe5a84b65e15e1e932. For a $d$-dimensional Brownian motion $W$ on a probability space, a filtration $\mathcal F$ for which every coordinate is Brownian, and a vector-valued integrand $Z:\mathbb R\to\Omega\to(\mathrm{Fin}\,d\to\mathbb R)$, `MultidimBrownianMotion.stochasticIntegral` is defined by $$\sum_{i\in\mathrm{Fin}\,d}\int_0^T Z_s^i\,dW_s^i.$$ Each component is required to be jointly measurable, progressively measurable, and square-integrable on every positive finite horizon. The definition is a finite sum of the one-dimensional `stochasticIntegral` constructions.
--
--   **Original module imports**
--
--   ```lean
--   import LevyStochCalc.Brownian.MultidimFiltered
--   import LevyStochCalc.Brownian.ItoL2Completion
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context. Body omitted.
--
--   ```lean
--   noncomputable def stochasticIntegral
--       (W : MultidimBrownianMotion P d)
--       (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : ∀ i, IsBrownianFiltration (W.W i) ℱ)
--       (Z : ℝ → Ω → (Fin d → ℝ))
--       (h_meas : ∀ i : Fin d, Measurable (Function.uncurry (fun ω s => Z s ω i)))
--       (h_progMeas : ∀ i : Fin d, Probability.ProgressivelyMeasurable ℱ (fun ω s => Z s ω i))
--       (h_sq_int_global : ∀ i : Fin d, ∀ T : ℝ, 0 < T →
--         ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
--           (‖Z s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
--       (T : ℝ) : Ω → ℝ
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`LevyStochCalc/Brownian/MultidimFiltered`](https://prove2.me/theorems/b4d1ac23-3fea-40f2-8621-83c034eb1b1a), [`LevyStochCalc/Brownian/ItoL2Completion`](https://prove2.me/theorems/15202148-c170-44c6-9af7-b9de285595f1).
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/MultidimIto.lean) · `LevyStochCalc.Brownian.MultidimIto` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/MultidimIto.lean#L50-L74 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.MultidimIto`, definition bundle `KLSModular_LevyStochCalc_Brownian_MultidimIto`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_MultidimFiltered
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoL2Completion

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/MultidimIto.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace LevyStochCalc
namespace Brownian
namespace Multidim
namespace MultidimBrownianMotion
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P]
variable {d : ℕ}
/-- The multidim Brownian Itô integral
`(∫_0^T Z_s · dW_s)(ω) = ∑_i ∫_0^T Z_s^i dW_s^i (ω)`.

`Z s ω i` is the `i`-th component of the integrand at `(s, ω)`. The result
at time `T` is the sum (over components) of the 1D Itô integrals against
the component Brownian motions `W.W i`.

Each component's 1D integral is `LevyStochCalc.Brownian.Ito.stochasticIntegral`
(`Brownian/ItoL2Completion.lean`), the coherent `L²`-limit of simple integrals
whose martingale, quadratic-variation and isometry properties are packaged in
`itoIsometry_brownian_unified_existence`. -/
noncomputable def stochasticIntegral
    (W : MultidimBrownianMotion P d)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : ∀ i, IsBrownianFiltration (W.W i) ℱ)
    (Z : ℝ → Ω → (Fin d → ℝ))
    (h_meas : ∀ i : Fin d, Measurable (Function.uncurry (fun ω s => Z s ω i)))
    (h_progMeas : ∀ i : Fin d, Probability.ProgressivelyMeasurable ℱ (fun ω s => Z s ω i))
    (h_sq_int_global : ∀ i : Fin d, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖Z s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (T : ℝ) : Ω → ℝ :=
  fun ω => ∑ i : Fin d,
    LevyStochCalc.Brownian.Ito.stochasticIntegral
      (W.W i) ℱ (hℱ i) (fun ω' s => Z s ω' i)
      (h_meas i) (h_progMeas i) (h_sq_int_global i) T ω
end MultidimBrownianMotion
end Multidim
end Brownian
end LevyStochCalc


