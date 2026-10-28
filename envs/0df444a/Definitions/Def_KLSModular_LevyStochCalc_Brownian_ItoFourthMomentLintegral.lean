-- Prove2me | Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoFourthMomentLintegral
-- name    : KLSModular_LevyStochCalc_Brownian_ItoFourthMomentLintegral
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T16:57:45.293833+00:00
-- url     : https://prove2.me/theorems/e9dd3a38-7a56-4504-970d-056a933b183f
-- title:
--   Coefficient truncation for simple predictable integrands
-- statement:
--   Vendored from the LevyStochCalc library at https://github.com/cgarryZA/LevyStochCalc, commit 984dbf0b790031eac05d56fe5a84b65e15e1e932. `SimplePredictable.truncate G C` preserves the partition and replaces every coefficient of the simple predictable integrand $G$ by $\max(-C,\min(C,G))$, so the coefficients lie in $[-|C|,|C|]$ and remain measurable.
--
--   **Original module imports**
--
--   ```lean
--   import LevyStochCalc.Brownian.ItoFourthMomentPartialSums
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context. Body omitted.
--
--   ```lean
--   noncomputable def SimplePredictable.truncate {T : ℝ} (G : SimplePredictable Ω T) (C : ℝ) :
--       SimplePredictable Ω T
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`LevyStochCalc/Brownian/ItoFourthMomentPartialSums`](https://prove2.me/theorems/705e75c1-4971-40ae-82c1-068282421322).
--
--   Theorems in source order:
--
--   - [`comp_sum_ite`](https://prove2.me/theorems/d50428dd-fbc4-4845-8772-c63abee73b25)
--   - [`abs_clamp_sub_le`](https://prove2.me/theorems/1920857f-1d3d-455c-88bd-4b390cbdc408)
--   - [`SimplePredictable.lintegral_pow_four_eq`](https://prove2.me/theorems/2e23b33c-826a-4615-a6b9-f62674c63f74)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoFourthMomentLintegral.lean) · `LevyStochCalc.Brownian.ItoFourthMomentLintegral` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ItoFourthMomentLintegral.lean#L57-L70 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ItoFourthMomentLintegral`, definition bundle `KLSModular_LevyStochCalc_Brownian_ItoFourthMomentLintegral`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoFourthMomentPartialSums

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoFourthMomentLintegral.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
namespace LevyStochCalc
namespace Brownian
namespace Ito
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
/-- The coefficients of a simple integrand clamped to `[-C, C]`. -/
noncomputable def SimplePredictable.truncate {T : ℝ} (G : SimplePredictable Ω T) (C : ℝ) :
    SimplePredictable Ω T where
  N := G.N
  partition := G.partition
  partition_zero := G.partition_zero
  partition_le_T := G.partition_le_T
  partition_strictMono := G.partition_strictMono
  ξ := fun i ω => max (-C) (min C (G.ξ i ω))
  ξ_bounded := fun i => ⟨|C|, fun ω => abs_le.mpr
    ⟨le_max_of_le_left (neg_le_neg (le_abs_self C)),
      max_le (neg_le_abs C) ((min_le_left C (G.ξ i ω)).trans (le_abs_self C))⟩⟩
  ξ_measurable := fun i =>
    measurable_const.max (measurable_const.min (G.ξ_measurable i))
end Ito
end Brownian
end LevyStochCalc


