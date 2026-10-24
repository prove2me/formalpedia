-- Prove2me | Definitions.Def_KLS408915f_LevyStochCalc_Probability_DoobContinuous
-- name    : KLS408915f_LevyStochCalc_Probability_DoobContinuous
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T11:02:04.241806+00:00
-- url     : https://prove2.me/theorems/b97a0b6c-a7aa-413e-be79-a88a2f3b1763
-- title:
--   Dyadic sampling data for continuous-time Doob estimates
-- statement:
--   Vendored from the LevyStochCalc library (https://github.com/cgarryZA/LevyStochCalc). `Filtration.compMono` restricts a filtration along a monotone time map, and `dyadicTime` gives the point of the dyadic partition of $[0,T]$ at level $n$, capped at $T$. `dyadicRunMax` is the finite supremum of the norm of a process over those partition points, while `dyadicIndex` is the nonnegative integer ceiling of $t2^n/T$. These declarations provide sampling data and filtration restriction for continuous-time maximal-inequality developments.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Probability/DoobContinuous.lean#L36-L155 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Probability.DoobContinuous`, definition bundle `KLS408915f_LevyStochCalc_Probability_DoobContinuous`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLS408915f_LevyStochCalc_Probability_Progressive
import Definitions.Def_KLS408915f_LevyStochCalc_Probability_ProgressiveCadlag
import Definitions.Def_KLS408915f_MathFin_Foundations_DoobLpMaximalInequality
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.Probability.Process.Adapted

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Probability/DoobContinuous.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace LevyStochCalc
namespace Probability
variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable (mΩ) in
/-- The filtration sampled along a monotone time map. -/
def Filtration.compMono {ι ι' : Type*} [Preorder ι] [Preorder ι']
    (ℱ : Filtration ι' mΩ) (τ : ι → ι') (hτ : Monotone τ) : Filtration ι mΩ where
  seq i := ℱ (τ i)
  mono' _ _ hij := ℱ.mono' (hτ hij)
  le' i := ℱ.le' (τ i)
@[simp] theorem Filtration.compMono_apply {ι ι' : Type*} [Preorder ι] [Preorder ι']
    (ℱ : Filtration ι' mΩ) (τ : ι → ι') (hτ : Monotone τ) (i : ι) :
    Filtration.compMono mΩ ℱ τ hτ i = ℱ (τ i) := rfl
/-- The `k`-th dyadic partition point of `[0, T]` at level `n`, frozen at the horizon. -/
noncomputable def dyadicTime (T : ℝ) (n k : ℕ) : ℝ := min ((k : ℝ) * T / 2 ^ n) T
variable {M : ℝ → Ω → ℝ} {T : ℝ}
/-- The running maximum of the sampled path over the dyadic partition of level `n`. -/
noncomputable def dyadicRunMax (M : ℝ → Ω → ℝ) (T : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (Finset.range (2 ^ n + 1)).sup' Finset.nonempty_range_add_one
    fun k => ‖M (dyadicTime T n k) ω‖
/-- The dyadic index whose partition point is the first at or after `t`. -/
noncomputable def dyadicIndex (T t : ℝ) (n : ℕ) : ℕ := ⌈t * 2 ^ n / T⌉₊
end Probability
end LevyStochCalc


