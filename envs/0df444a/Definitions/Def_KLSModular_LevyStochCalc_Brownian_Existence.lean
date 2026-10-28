-- Prove2me | Definitions.Def_KLSModular_LevyStochCalc_Brownian_Existence
-- name    : KLSModular_LevyStochCalc_Brownian_Existence
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T15:44:09.668162+00:00
-- url     : https://prove2.me/theorems/10f8be28-ef23-4221-869d-2a746f8fe042
-- title:
--   Extension of pre-Brownian processes to real-time Brownian motion
-- statement:
--   Vendored from LevyStochCalc, repository https://github.com/cgarryZA/LevyStochCalc, commit 984dbf0b790031eac05d56fe5a84b65e15e1e932. The definition `realTime` extends an ℝ≥0-indexed process X to real time by t ↦ X(t⁺) − X(0), and `realTime_sub` gives its increment identity; `continuous_realTime` proves pathwise continuity when the original paths are continuous. Under `IsPreBrownianReal`, measurable time slices, and continuous paths, `BrownianMotion.ofIsPreBrownianReal` constructs a `BrownianMotion P` with the required measurability, Gaussian increments, initial and nonpositive-time behavior, continuous paths, and independence of past and future increments.
--
--   **Original module imports**
--
--   ```lean
--   import LevyStochCalc.Brownian.Construction
--   import BrownianMotion.Gaussian.BrownianMotion
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   noncomputable def realTime (X : ℝ≥0 → Ω → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
--     X (Real.toNNReal t) ω - X 0 ω
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`LevyStochCalc/Brownian/Construction`](https://prove2.me/theorems/742cb048-99b1-4e53-bf9d-ffd292ffaaa3), [`BrownianMotion/Gaussian/BrownianMotion`](https://prove2.me/theorems/649e1eeb-150a-4919-a925-1b143db57096).
--
--   Theorems in source order:
--
--   - [`BrownianMotion.exists`](https://prove2.me/theorems/d52e5c72-47ca-41b1-83e3-5e8da38f1f08)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/Existence.lean) · `LevyStochCalc.Brownian.Existence` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/Existence.lean#L35-L102 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.Existence`, definition bundle `KLSModular_LevyStochCalc_Brownian_Existence`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
import Definitions.Def_KLSModular_BrownianMotion_Gaussian_BrownianMotion

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/Existence.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
namespace LevyStochCalc
namespace Brownian
open MeasureTheory ProbabilityTheory
open scoped NNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
/-- Real-time extension of an `ℝ≥0`-indexed process: `t ↦ X (t⁺) − X 0`. -/
noncomputable def realTime (X : ℝ≥0 → Ω → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  X (Real.toNNReal t) ω - X 0 ω
omit [MeasurableSpace Ω] in
theorem realTime_sub (X : ℝ≥0 → Ω → ℝ) (s t : ℝ) :
    (fun ω => realTime X t ω - realTime X s ω)
      = fun ω => X (Real.toNNReal t) ω - X (Real.toNNReal s) ω := by
  funext ω; simp only [realTime]; ring
omit [MeasurableSpace Ω] in
theorem continuous_realTime {X : ℝ≥0 → Ω → ℝ} (hcont : ∀ ω, Continuous (X · ω)) (ω : Ω) :
    Continuous (fun t : ℝ => realTime X t ω) :=
  ((hcont ω).comp continuous_real_toNNReal).sub continuous_const
/-- A pre-Brownian process with measurable marginals and continuous paths is a Brownian motion
in real time. -/
noncomputable def BrownianMotion.ofIsPreBrownianReal {X : ℝ≥0 → Ω → ℝ}
    (hX : IsPreBrownianReal X P) (hmeas : ∀ t, Measurable (X t))
    (hcont : ∀ ω, Continuous (X · ω)) : BrownianMotion P where
  W := realTime X
  measurable_eval _ := (hmeas _).sub (hmeas 0)
  joint_measurable :=
    measurable_uncurry_of_continuous_of_measurable (continuous_realTime hcont)
      fun _ => (hmeas _).sub (hmeas 0)
  initial_zero := ae_of_all _ fun ω => by simp [realTime]
  increment_gaussian := by
    intro s t hs hst
    have ht : 0 ≤ t := hs.trans hst.le
    have hd : nndist (Real.toNNReal t).1 (Real.toNNReal s).1 = ⟨t - s, by linarith⟩ := by
      apply NNReal.coe_injective
      simp only [NNReal.val_eq_coe, coe_nndist, Real.dist_eq, Real.coe_toNNReal _ ht,
        Real.coe_toNNReal _ hs, abs_of_pos (sub_pos.mpr hst)]
      rfl
    have h := (hX.hasLaw_sub (Real.toNNReal t) (Real.toNNReal s)).map_eq
    rw [hd] at h
    rw [realTime_sub]
    exact h
  continuous_paths := ae_of_all _ (continuous_realTime hcont)
  negative_zero := fun s hs => ae_of_all _ fun ω => by
    simp [realTime, Real.toNNReal_of_nonpos hs.le]
  joint_increment_independent := by
    intro s t hs hst
    have hst' : Real.toNNReal s ≤ Real.toNNReal t := Real.toNNReal_le_toNNReal hst.le
    have h : Indep
        (MeasurableSpace.comap (fun ω (r : Set.Iic (Real.toNNReal s)) => X r ω) inferInstance)
        (MeasurableSpace.comap
          (fun ω (r : ℝ≥0) => X (Real.toNNReal s + r) ω - X (Real.toNNReal s) ω) inferInstance)
        P :=
      (hX.indepFun_shift (Real.toNNReal s)).symm
    refine indep_of_indep_of_le_left (indep_of_indep_of_le_right h ?_) ?_
    · rw [realTime_sub]
      have : (fun ω => X (Real.toNNReal t) ω - X (Real.toNNReal s) ω)
          = (fun p : ℝ≥0 → ℝ => p (Real.toNNReal t - Real.toNNReal s))
            ∘ (fun ω (r : ℝ≥0) => X (Real.toNNReal s + r) ω - X (Real.toNNReal s) ω) := by
        funext ω; simp [add_tsub_cancel_of_le hst']
      rw [this]
      refine Measurable.comap_le ?_
      exact (measurable_pi_apply _).comp (Measurable.of_comap_le le_rfl)
    · refine iSup₂_le fun j hj => ?_
      have hj' : Real.toNNReal j ≤ Real.toNNReal s := Real.toNNReal_le_toNNReal hj
      have : realTime X j
          = (fun p : Set.Iic (Real.toNNReal s) → ℝ => p ⟨Real.toNNReal j, hj'⟩ - p ⟨0, by simp⟩)
            ∘ (fun ω (r : Set.Iic (Real.toNNReal s)) => X r ω) := by
        funext ω; rfl
      rw [this]
      refine Measurable.comap_le (Measurable.comp ?_ (Measurable.of_comap_le le_rfl))
      exact (measurable_pi_apply _).sub (measurable_pi_apply _)
end Brownian
end LevyStochCalc


