-- Prove2me | Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoPullOut
-- name    : KLSModular_LevyStochCalc_Brownian_ItoPullOut
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T17:00:55.976977+00:00
-- url     : https://prove2.me/theorems/ec224d62-6516-4a47-919c-197424d19554
-- title:
--   Past-weighted interval-step integrands
-- statement:
--   Vendored from the LevyStochCalc library at https://github.com/cgarryZA/LevyStochCalc, commit 984dbf0b790031eac05d56fe5a84b65e15e1e932. `stepIocMul Ω ha hab V hVb hVm` is the simple predictable integrand with coefficient $0$ before $a$ and coefficient $V$ on $(a,b]$, for a bounded measurable $V$ and $0<a<b$. `stepIocMul₀` gives the analogous coefficient-$V$ integrand on $(0,b]$.
--
--   **Original module imports**
--
--   ```lean
--   import LevyStochCalc.Brownian.ItoIncrement
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context. Body omitted.
--
--   ```lean
--   noncomputable def stepIocMul (Ω) [MeasurableSpace Ω] {a b : ℝ} (ha : 0 < a) (hab : a < b)
--       (V : Ω → ℝ) (hVb : ∃ M : ℝ, ∀ ω, |V ω| ≤ M) (hVm : Measurable V) :
--       SimplePredictable Ω b
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`LevyStochCalc/Brownian/ItoIncrement`](https://prove2.me/theorems/0dacfd17-a335-4bce-a734-7c09a89723d3).
--
--   Theorems in source order:
--
--   - [`stepIocMul_eval`](https://prove2.me/theorems/78e7de7a-b770-4a24-b582-8eedc3ca2e86)
--   - [`stepIocMul₀_eval`](https://prove2.me/theorems/56a8ce59-b36c-4fd6-8596-a506da0ad724)
--   - [`progressivelyMeasurable_mul_indIoc`](https://prove2.me/theorems/030165f7-acc3-4866-b777-afeba0e9b4de)
--   - [`mul_stochasticIntegralBrownian_indIoc`](https://prove2.me/theorems/13bdf081-9a6f-4dc1-a40f-ce4f657ba4ff)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoPullOut.lean) · `LevyStochCalc.Brownian.ItoPullOut` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ItoPullOut.lean (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ItoPullOut`, definition bundle `KLSModular_LevyStochCalc_Brownian_ItoPullOut`; the repository is private at upload time); vendored copy patched by formalization/vendor/port.patch (project file formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoPullOut.lean, lines 27-66). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoIncrement

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Modified 2026-10-12 by the KLS formalization project: ported to Lean v4.33.0 and
-- Mathlib db584cd. The changes are listed in vendor/README.md and vendor/port.patch.
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoPullOut.lean; Apache-2.0; locally patched, see formalization/vendor/port.patch; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
namespace LevyStochCalc
namespace Brownian
namespace Ito
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
/-- The simple integrand `V · 1_{(a, b]}`, for `0 < a < b` and a bounded measurable `V`. -/
noncomputable def stepIocMul (Ω) [MeasurableSpace Ω] {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (V : Ω → ℝ) (hVb : ∃ M : ℝ, ∀ ω, |V ω| ≤ M) (hVm : Measurable V) :
    SimplePredictable Ω b where
  N := 2
  partition := ![0, a, b]
  partition_zero := by simp
  partition_le_T := by simp
  partition_strictMono := by
    refine Fin.strictMono_iff_lt_succ.mpr fun i => ?_
    fin_cases i
    · simpa using ha
    · simpa using hab
  ξ := ![fun _ => 0, V]
  ξ_bounded := by
    intro i
    fin_cases i
    · exact ⟨0, fun ω => by norm_num⟩
    · exact hVb
  ξ_measurable := by
    intro i
    fin_cases i
    · exact measurable_const
    · exact hVm
/-- The simple integrand `V · 1_{(0, b]}`, for `0 < b` and a bounded measurable `V`. -/
noncomputable def stepIocMul₀ (Ω) [MeasurableSpace Ω] {b : ℝ} (hb : 0 < b)
    (V : Ω → ℝ) (hVb : ∃ M : ℝ, ∀ ω, |V ω| ≤ M) (hVm : Measurable V) :
    SimplePredictable Ω b where
  N := 1
  partition := ![0, b]
  partition_zero := by simp
  partition_le_T := by simp
  partition_strictMono := by
    refine Fin.strictMono_iff_lt_succ.mpr fun i => ?_
    fin_cases i
    simpa using hb
  ξ := ![V]
  ξ_bounded := by intro i; fin_cases i; exact hVb
  ξ_measurable := by intro i; fin_cases i; exact hVm
end Ito
end Brownian
end LevyStochCalc


