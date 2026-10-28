-- Prove2me | Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoOptionalStopping
-- name    : KLSModular_LevyStochCalc_Brownian_ItoOptionalStopping
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T17:05:52.49246+00:00
-- url     : https://prove2.me/theorems/1d25c358-1966-4cac-ba37-96d7bf5aaf7d
-- title:
--   Finite-range stopping-time integrand terms
-- statement:
--   Vendored from the LevyStochCalc library at https://github.com/cgarryZA/LevyStochCalc, commit 984dbf0b790031eac05d56fe5a84b65e15e1e932. Under a probability measure $P$, `hitInd τ c` is the indicator of the event $\{\omega:\tau(\omega)=c\}$, `cutTerm τ H c t` is this indicator multiplied by the interval indicator $1_{(c,t]}$ and $H$, and `indTerm τ H c t` is the same interval restriction with unit weight. The auxiliary theorem `energy_lt_top_of_abs_le` transfers finite $L^2$ energy from $G$ to $K$ under the pointwise domination $|K(\omega,s)|\le|G(\omega,s)|$.
--
--   **Original module imports**
--
--   ```lean
--   import LevyStochCalc.Brownian.ItoFinsetSum
--   import LevyStochCalc.Brownian.ItoPullOut
--   import LevyStochCalc.Probability.StoppedProgressive
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   noncomputable def hitInd (c : ℝ) : Ω → ℝ :=
--     Set.indicator {ω | τ ω = ((c : ℝ) : WithTop ℝ)} fun _ => (1 : ℝ)
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`LevyStochCalc/Brownian/ItoFinsetSum`](https://prove2.me/theorems/3c65a1ac-837e-48a1-b323-dc87feeb6397), [`LevyStochCalc/Brownian/ItoPullOut`](https://prove2.me/theorems/ec224d62-6516-4a47-919c-197424d19554), [`LevyStochCalc/Probability/StoppedProgressive`](https://prove2.me/theorems/602d883b-27f9-43ed-bb5c-77dd184db556).
--
--   Theorems in source order:
--
--   - [`stopped_eq_sub_sum`](https://prove2.me/theorems/ca6db2c8-b052-412e-99f9-f5b6637e3786)
--   - [`stochasticIntegralBrownian_stopped`](https://prove2.me/theorems/ed4209dc-2e3a-4843-8705-dade9e7c1cbc)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoOptionalStopping.lean) · `LevyStochCalc.Brownian.ItoOptionalStopping` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ItoOptionalStopping.lean#L36-L110 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ItoOptionalStopping`, definition bundle `KLSModular_LevyStochCalc_Brownian_ItoOptionalStopping`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoFinsetSum
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoPullOut
import Definitions.Def_KLSModular_LevyStochCalc_Probability_StoppedProgressive

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoOptionalStopping.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
namespace LevyStochCalc
namespace Brownian
namespace Ito
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
omit [IsProbabilityMeasure P] in
/-- Square-integrability transfers along a pointwise domination of the integrands. -/
theorem energy_lt_top_of_abs_le {K G : Ω → ℝ → ℝ} (h : ∀ ω s, |K ω s| ≤ |G ω s|)
    (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖G ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖K ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
  intro T hT
  refine lt_of_le_of_lt (lintegral_mono fun ω => lintegral_mono fun s => ?_) (hq T hT)
  have hle : (‖K ω s‖₊ : ℝ≥0∞) ≤ (‖G ω s‖₊ : ℝ≥0∞) := by
    refine ENNReal.coe_le_coe.mpr ?_
    rw [← NNReal.coe_le_coe]
    simpa [Real.norm_eq_abs] using h ω s
  gcongr
section Stopped
variable (τ : Ω → WithTop ℝ)
/-- The indicator of the event that the stopping time takes the value `c`. -/
noncomputable def hitInd (c : ℝ) : Ω → ℝ :=
  Set.indicator {ω | τ ω = ((c : ℝ) : WithTop ℝ)} fun _ => (1 : ℝ)
/-- The part of the integrand that the cut at `τ = c` removes from the window `(c, t]`. -/
noncomputable def cutTerm (H : Ω → ℝ → ℝ) (c t : ℝ) : Ω → ℝ → ℝ :=
  fun ω s => hitInd τ c ω * indIoc Ω c t ω s * H ω s
/-- The integrand restricted to a window, as a `cutTerm` with unit weight. -/
noncomputable def indTerm (H : Ω → ℝ → ℝ) (c t : ℝ) : Ω → ℝ → ℝ :=
  fun ω s => indIoc Ω c t ω s * H ω s
end Stopped
end Ito
end Brownian
end LevyStochCalc


