-- Prove2me | Definitions.Def_SourceProof_1a4af5ffbf7aaf4aaa194358
-- name    : SourceProof_1a4af5ffbf7aaf4aaa194358
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:15:34.554172+00:00
-- url     : https://prove2.me/theorems/6fa510b0-1621-4589-81f5-59ac3a40a78f
-- title:
--   LevyStochCalc source module: SourceProof_1a4af5ffbf7aaf4aaa194358
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_congr_of_lt` comes from the `LevyStochCalc.Brownian.ItoLocalityStrict` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_SourceProof_331df1c7e78036fb9af022ae
import Definitions.Def_SourceProof_c2510fef121a9f6103ef8e5e

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Strict locality of the Itô integral

Two integrands that agree almost everywhere on a window have almost surely equal integrals
(`stochasticIntegralBrownian_congr_ae`), because the difference isometry turns the vanishing of
the energy of their difference into the vanishing of the second moment of the difference of the
integrals.

That upgrades the locality statement of `Brownian/ItoLocality.lean` from agreement at the times
`s ≤ τ ω` to agreement at the times `s < τ ω` (`stochasticIntegralBrownian_congr_of_lt`): the two
cut-off integrands then differ at the single time `s = τ ω`, a Lebesgue-null set of times. The
strict form is what a càdlàg path needs, since two integrands read along it can disagree exactly
at a jump time.

## Main statements

* `stochasticIntegralBrownian_congr_ae` — almost-everywhere equal integrands, almost surely
  equal integrals.
* `stochasticIntegralBrownian_congr_of_lt` — integrands agreeing strictly below a stopping time
  have the same integral at a time that stopping time has not reached.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Brownian.Ito

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)

variable {τ : Ω → WithTop ℝ}


theorem _root_.Prove2MeSourceProof.h_1a4af5ffbf7aaf4aaa194358
    (hτ : MeasureTheory.IsStoppingTime ℱ τ)
    {H₁ H₂ : Ω → ℝ → ℝ} (hm₁ : Measurable (Function.uncurry H₁))
    (hp₁ : Probability.ProgressivelyMeasurable ℱ H₁)
    (hq₁ : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hm₂ : Measurable (Function.uncurry H₂))
    (hp₂ : Probability.ProgressivelyMeasurable ℱ H₂)
    (hq₂ : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hagree : ∀ (ω : Ω) (s : ℝ), 0 < s → ((s : ℝ) : WithTop ℝ) < τ ω → H₁ ω s = H₂ ω s)
    {t : ℝ} (ht : 0 < t) :
    ∀ᵐ ω ∂P, ((t : ℝ) : WithTop ℝ) ≤ τ ω →
      stochasticIntegralBrownian W ℱ hℱ H₁ hm₁ hp₁ hq₁ t ω
        = stochasticIntegralBrownian W ℱ hℱ H₂ hm₂ hp₂ hq₂ t ω := by
  classical
  have e1 := _root_.Prove2MeSourceProof.h_331df1c7e78036fb9af022ae τ W ℱ hℱ hτ hm₁ hp₁ hq₁ ht
  have e2 := _root_.Prove2MeSourceProof.h_331df1c7e78036fb9af022ae τ W ℱ hℱ hτ hm₂ hp₂ hq₂ ht
  -- the cut integrands agree off the time `0` and the value of the stopping time
  have hstop : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) t)),
      LevyStochCalc.Probability.stopped τ H₁ ω s = LevyStochCalc.Probability.stopped τ H₂ ω s := by
    refine Filter.Eventually.of_forall fun ω => ?_
    have hnull : (volume.restrict (Set.Icc (0 : ℝ) t))
        ({(0 : ℝ)} ∪ {s : ℝ | ((s : ℝ) : WithTop ℝ) = τ ω}) = 0 := by
      refine measure_union_null (by simp) ?_
      rcases eq_or_ne (τ ω) ⊤ with hτω | hτω
      · have hempty : {s : ℝ | ((s : ℝ) : WithTop ℝ) = τ ω} = ∅ := by
          ext s
          simp [hτω]
        rw [hempty]
        exact measure_empty
      · obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hτω
        have hsing : {s : ℝ | ((s : ℝ) : WithTop ℝ) = τ ω} = {r} := by
          ext s
          rw [Set.mem_setOf_eq, Set.mem_singleton_iff, ← hr]
          exact ⟨fun h => by exact_mod_cast h, fun h => by exact_mod_cast h⟩
        rw [hsing]
        simp
    filter_upwards [compl_mem_ae_iff.mpr hnull, ae_restrict_mem measurableSet_Icc]
      with s hs0 hs
    have hsn : ¬ s = 0 ∧ ¬ ((s : ℝ) : WithTop ℝ) = τ ω := by
      simpa [not_or] using hs0
    have hspos : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hsn.1)
    unfold LevyStochCalc.Probability.stopped
    by_cases hle : ((s : ℝ) : WithTop ℝ) ≤ τ ω
    · rw [if_pos hle, if_pos hle, hagree ω s hspos (lt_of_le_of_ne hle hsn.2)]
    · rw [if_neg hle, if_neg hle]
  have e3 := _root_.Prove2MeSourceProof.h_c2510fef121a9f6103ef8e5e W ℱ hℱ
    (LevyStochCalc.Probability.measurable_uncurry_stopped hτ hm₁)
    (_root_.Prove2MeSourceProof.h_4014cddbf3dd1c22757fef9e hτ hp₁)
    (LevyStochCalc.Brownian.Ito.energy_lt_top_of_abs_le (fun ω s => LevyStochCalc.Probability.abs_stopped_le τ H₁ ω s) hq₁)
    (LevyStochCalc.Probability.measurable_uncurry_stopped hτ hm₂)
    (_root_.Prove2MeSourceProof.h_4014cddbf3dd1c22757fef9e hτ hp₂)
    (LevyStochCalc.Brownian.Ito.energy_lt_top_of_abs_le (fun ω s => LevyStochCalc.Probability.abs_stopped_le τ H₂ ω s) hq₂)
    ht hstop
  filter_upwards [e1, e2, e3] with ω h1 h2 h3 hle
  rw [← h1 hle, ← h2 hle, h3]
end LevyStochCalc.Brownian.Ito


