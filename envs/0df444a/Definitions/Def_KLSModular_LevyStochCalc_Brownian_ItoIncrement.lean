-- Prove2me | Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoIncrement
-- name    : KLSModular_LevyStochCalc_Brownian_ItoIncrement
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T16:56:30.310326+00:00
-- url     : https://prove2.me/theorems/0dacfd17-a335-4bce-a734-7c09a89723d3
-- title:
--   Indicator integrand for a time interval
-- statement:
--   Vendored from the LevyStochCalc library at https://github.com/cgarryZA/LevyStochCalc, commit 984dbf0b790031eac05d56fe5a84b65e15e1e932. `indIoc Ω a b` is the process independent of $\omega$ whose time profile is the indicator $1_{(a,b]}$ with values in $\mathbb R$.
--
--   **Original module imports**
--
--   ```lean
--   import LevyStochCalc.Brownian.ItoAlgebra
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   noncomputable def indIoc (Ω) [MeasurableSpace Ω] (a b : ℝ) : Ω → ℝ → ℝ :=
--     fun _ s => (Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`LevyStochCalc/Brownian/ItoAlgebra`](https://prove2.me/theorems/602bc476-bf93-48d5-972e-3d6b80e662e4).
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoIncrement.lean) · `LevyStochCalc.Brownian.ItoIncrement` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ItoIncrement.lean#L26-L28 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ItoIncrement`, definition bundle `KLSModular_LevyStochCalc_Brownian_ItoIncrement`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoAlgebra

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoIncrement.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
namespace LevyStochCalc
namespace Brownian
namespace Ito
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
section Indicator
/-- The indicator integrand of a time window, as a process constant in the sample point. -/
noncomputable def indIoc (Ω) [MeasurableSpace Ω] (a b : ℝ) : Ω → ℝ → ℝ :=
  fun _ s => (Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s
variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
end Indicator
end Ito
end Brownian
end LevyStochCalc


