-- Prove2me | Definitions.Def_KLSModular_LevyStochCalc_Poisson_CompensatedMartingaleQuadratic
-- name    : KLSModular_LevyStochCalc_Poisson_CompensatedMartingaleQuadratic
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T15:53:42.207994+00:00
-- url     : https://prove2.me/theorems/f3d82b2f-75d7-4041-85d5-1289f2494d75
-- title:
--   L² membership for compensated simple integrals
-- statement:
--   Vendored from the LevyStochCalc library (https://github.com/cgarryZA/LevyStochCalc), commit 984dbf0b790031eac05d56fe5a84b65e15e1e932. `simpleIntegral_memLp_at` states that for every running time $t$, the compensated simple integral $\omega\mapsto\operatorname{simpleIntegral}(N,\phi,t)(\omega)$ belongs to `MemLp` with exponent $2$ under $P$. No adaptedness assumption is required for this declaration; bounded coefficients and finite-intensity mark sets suffice. The surrounding module is intended for quadratic-variation and compensator identities, but this bundle provides the stated $L^2$ membership result.
--
--   **Original module imports**
--
--   ```lean
--   import LevyStochCalc.Poisson.CompensatedMartingaleIncrement
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context. Body omitted.
--
--   ```lean
--   lemma simpleIntegral_memLp_at
--       {P : Measure Ω} [IsProbabilityMeasure P]
--       {ν : Measure E} [SigmaFinite ν]
--       (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
--       {T : ℝ} (φ : SimplePredictable Ω E ν T) (t : ℝ) :
--       MeasureTheory.MemLp (fun ω => simpleIntegral N φ t ω) 2 P
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`LevyStochCalc/Poisson/CompensatedMartingaleIncrement`](https://prove2.me/theorems/4c7e0253-7601-418d-9e60-01ba66a1ba96).
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Poisson/CompensatedMartingaleQuadratic.lean) · `LevyStochCalc.Poisson.CompensatedMartingaleQuadratic` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Poisson/CompensatedMartingaleQuadratic.lean#L151-L181 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Poisson.CompensatedMartingaleQuadratic`, definition bundle `KLSModular_LevyStochCalc_Poisson_CompensatedMartingaleQuadratic`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Poisson_CompensatedMartingaleIncrement

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Poisson/CompensatedMartingaleQuadratic.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace LevyStochCalc
namespace Poisson
namespace Compensated
universe u v
variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]
/-- **`simpleIntegral N φ t ∈ L²(P)` at every running time `t`.** Each summand
`ξᵢ·Ñ(timeRect i t)` is the product of a bounded coefficient and a compensated mass
in `L²` (`compensated_sq_integrable`), so the finite sum is in `L²`. No adaptedness
needed (unlike the full-horizon isometry route). -/
lemma simpleIntegral_memLp_at
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    {T : ℝ} (φ : SimplePredictable Ω E ν T) (t : ℝ) :
    MeasureTheory.MemLp (fun ω => simpleIntegral N φ t ω) 2 P := by
  have h_unfold : (fun ω => simpleIntegral N φ t ω)
      = ∑ i : Fin φ.N, fun ω => φ.ξ i ω * N.compensated (φ.timeRect i t) ω := by
    funext ω; rw [Finset.sum_apply]; rfl
  rw [h_unfold]
  refine MeasureTheory.memLp_finsetSum' _ (fun i _ => ?_)
  obtain ⟨M, hM⟩ := φ.ξ_bounded i
  have hmeas : MeasurableSet (φ.timeRect i t) := measurableSet_Ioc.prod (φ.A_measurable i)
  have hÑ_aesm : MeasureTheory.AEStronglyMeasurable
      (fun ω => N.compensated (φ.timeRect i t) ω) P :=
    ((ENNReal.measurable_toReal.comp (N.measurable_eval hmeas)).sub_const _).aestronglyMeasurable
  have hÑ_memLp : MeasureTheory.MemLp (fun ω => N.compensated (φ.timeRect i t) ω) 2 P :=
    (MeasureTheory.memLp_two_iff_integrable_sq hÑ_aesm).mpr
      (compensated_sq_integrable N hmeas (referenceIntensity_timeRect_ne_top φ i t))
  refine MeasureTheory.MemLp.mono' (hÑ_memLp.norm.const_mul |M|)
    ((φ.ξ_measurable i).aestronglyMeasurable.mul hÑ_aesm) ?_
  filter_upwards with ω
  change ‖φ.ξ i ω * N.compensated (φ.timeRect i t) ω‖
    ≤ |M| * ‖N.compensated (φ.timeRect i t) ω‖
  rw [norm_mul]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  rw [Real.norm_eq_abs]; exact (hM ω).trans (le_abs_self M)
end Compensated
end Poisson
end LevyStochCalc


