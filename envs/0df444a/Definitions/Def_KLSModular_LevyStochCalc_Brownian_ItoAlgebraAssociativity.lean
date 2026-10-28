-- Prove2me | Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoAlgebraAssociativity
-- name    : KLSModular_LevyStochCalc_Brownian_ItoAlgebraAssociativity
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T16:50:30.694717+00:00
-- url     : https://prove2.me/theorems/738b1003-832c-420c-a910-2008630209bc
-- title:
--   Step-function simple predictable integrands
-- statement:
--   Vendored from the LevyStochCalc library at https://github.com/cgarryZA/LevyStochCalc, commit 984dbf0b790031eac05d56fe5a84b65e15e1e932. For a measurable sample space $\Omega$, `stepIoc Ω ha hab` is the simple predictable integrand with partition $0<a<b$ and coefficient $1$ on the tile $(a,b]$, while `stepIoc₀ Ω hb` is the corresponding integrand on the single tile $(0,b]$ for $0<b$.
--
--   **Original module imports**
--
--   ```lean
--   import LevyStochCalc.Brownian.ItoAlgebraProduct
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context. Body omitted.
--
--   ```lean
--   noncomputable def stepIoc (Ω) [MeasurableSpace Ω] {a b : ℝ} (ha : 0 < a) (hab : a < b) :
--       SimplePredictable Ω b
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`LevyStochCalc/Brownian/ItoAlgebraProduct`](https://prove2.me/theorems/99205bea-847c-43ba-a041-1e0384d4d19c).
--
--   Theorems in source order:
--
--   - [`stochasticIntegralBrownian_integralAgainst`](https://prove2.me/theorems/ad605701-48f4-400c-83de-f35b5212c9ce)
--   - [`stepIoc_eval`](https://prove2.me/theorems/229a87fb-276d-451b-880f-3ee228acc687)
--   - [`stepIoc₀_eval`](https://prove2.me/theorems/2c0d5744-8278-417f-9f9c-dd287d9c0a4f)
--   - [`stochasticIntegralBrownian_indicator_Ioc`](https://prove2.me/theorems/bcc8c011-e83f-4b9e-a0e6-5de008451e39)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoAlgebraAssociativity.lean) · `LevyStochCalc.Brownian.ItoAlgebraAssociativity` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ItoAlgebraAssociativity.lean (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ItoAlgebraAssociativity`, definition bundle `KLSModular_LevyStochCalc_Brownian_ItoAlgebraAssociativity`; the repository is private at upload time); vendored copy patched by formalization/vendor/port.patch (project file formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoAlgebraAssociativity.lean, lines 273-302). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoAlgebraProduct

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Modified 2026-10-12 by the KLS formalization project: ported to Lean v4.33.0 and
-- Mathlib db584cd. The changes are listed in vendor/README.md and vendor/port.patch.
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoAlgebraAssociativity.lean; Apache-2.0; locally patched, see formalization/vendor/port.patch; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
namespace LevyStochCalc
namespace Brownian
namespace Ito
open MeasureTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
/-- The simple integrand `1_{(a, b]}`, for `0 < a < b`. -/
noncomputable def stepIoc (Ω) [MeasurableSpace Ω] {a b : ℝ} (ha : 0 < a) (hab : a < b) :
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
  ξ := ![fun _ => 0, fun _ => 1]
  ξ_bounded := by intro i; fin_cases i <;> exact ⟨1, fun ω => by norm_num⟩
  ξ_measurable := by intro i; fin_cases i <;> exact measurable_const
/-- The simple integrand `1_{(0, b]}`, for `0 < b`. -/
noncomputable def stepIoc₀ (Ω) [MeasurableSpace Ω] {b : ℝ} (hb : 0 < b) :
    SimplePredictable Ω b where
  N := 1
  partition := ![0, b]
  partition_zero := by simp
  partition_le_T := by simp
  partition_strictMono := by
    refine Fin.strictMono_iff_lt_succ.mpr fun i => ?_
    fin_cases i
    simpa using hb
  ξ := ![fun _ => 1]
  ξ_bounded := by intro i; fin_cases i; exact ⟨1, fun ω => by norm_num⟩
  ξ_measurable := by intro i; fin_cases i; exact measurable_const
end Ito
end Brownian
end LevyStochCalc


