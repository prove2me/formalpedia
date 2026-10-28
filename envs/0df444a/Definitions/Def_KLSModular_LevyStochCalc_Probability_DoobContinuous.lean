-- Prove2me | Definitions.Def_KLSModular_LevyStochCalc_Probability_DoobContinuous
-- name    : KLSModular_LevyStochCalc_Probability_DoobContinuous
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T15:48:52.611078+00:00
-- url     : https://prove2.me/theorems/948ff195-c1ab-45a5-b573-556d15dca780
-- title:
--   Dyadic sampling data for continuous-time Doob estimates
-- statement:
--   Vendored from the LevyStochCalc library (https://github.com/cgarryZA/LevyStochCalc). `Filtration.compMono` restricts a filtration along a monotone time map, and `dyadicTime` gives the point of the dyadic partition of $[0,T]$ at level $n$, capped at $T$. `dyadicRunMax` is the finite supremum of the norm of a process over those partition points, while `dyadicIndex` is the nonnegative integer ceiling of $t2^n/T$. These declarations provide sampling data and filtration restriction for continuous-time maximal-inequality developments.
--
--   **Original module imports**
--
--   ```lean
--   import Mathlib.Probability.Martingale.Basic
--   import LevyStochCalc.Probability.ProgressiveCadlag
--   import MathFin.Foundations.DoobLpMaximalInequality
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   def Filtration.compMono {ι ι' : Type*} [Preorder ι] [Preorder ι']
--       (ℱ : Filtration ι' mΩ) (τ : ι → ι') (hτ : Monotone τ) : Filtration ι mΩ where
--     seq i := ℱ (τ i)
--     mono' _ _ hij := ℱ.mono' (hτ hij)
--     le' i := ℱ.le' (τ i)
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`LevyStochCalc/Probability/ProgressiveCadlag`](https://prove2.me/theorems/0c73ac5b-2d29-4994-a4d0-58d02dcdb9a3), [`MathFin/Foundations/DoobLpMaximalInequality`](https://prove2.me/theorems/246417cb-a393-4700-8546-3a2d7f728869).
--
--   Theorems in source order:
--
--   - [`enorm_dyadicRunMax`](https://prove2.me/theorems/df28b675-5880-4511-8fdc-de21a750c0cb)
--   - [`tendsto_dyadicTime_dyadicIndex`](https://prove2.me/theorems/5e110120-ccfd-4354-afb0-032615a35b6a)
--   - [`iSup_enorm_eq_iSup_dyadicRunMax`](https://prove2.me/theorems/acb0a4f1-b242-45cd-80de-139b129bb826)
--   - [`lintegral_sq_dyadicRunMax_le`](https://prove2.me/theorems/c1b80434-c26c-49be-a883-841d52382ee6)
--   - [`sq_sum_le_card_sq_mul`](https://prove2.me/theorems/7c556d30-1476-4749-9b82-7ef598da576d)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Probability/DoobContinuous.lean) · `LevyStochCalc.Probability.DoobContinuous` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Probability/DoobContinuous.lean#L36-L155 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Probability.DoobContinuous`, definition bundle `KLSModular_LevyStochCalc_Probability_DoobContinuous`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Mathlib.Probability.Martingale.Basic
import Definitions.Def_KLSModular_LevyStochCalc_Probability_ProgressiveCadlag
import Definitions.Def_KLSModular_MathFin_Foundations_DoobLpMaximalInequality

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


