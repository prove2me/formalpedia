-- Prove2me | Definitions.Def_SourceProof_ac85444679aa3a412d1927d4
-- name    : SourceProof_ac85444679aa3a412d1927d4
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T20:13:00.145045+00:00
-- url     : https://prove2.me/theorems/89056bdb-8c47-4ad9-9a27-7277ba36a130
-- title:
--   LevyStochCalc source module: SourceProof_ac85444679aa3a412d1927d4
-- statement:
--   The original source theorem `LevyStochCalc.Ito.Picard.markedProgressivelyMeasurable_comp_state` comes from the `LevyStochCalc.Ito.PicardIntegrandBounds` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardBieleckiContractionTight_F000
import Definitions.Def_SourceProof_e303374519c4de703021a2f6

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Square integrability of the Picard integrands along a state process

Linear growth of the coefficients, read off the Lipschitz hypothesis by comparison with the
state `0`, turns the bounds at that single state recorded by `IsRegular` into bounds along a
state process: whenever the state has finite energy over every horizon, the drift, diffusion
and jump integrands evaluated along it are square integrable at every horizon, and a member of
the process space frozen at `T` has that energy. Composing a jointly measurable coefficient
with a measurable, respectively progressively measurable, state process supplies the matching
measurability of the integrands.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.Picard

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]


theorem _root_.Prove2MeSourceProof.h_ac85444679aa3a412d1927d4 {n : ℕ}
    {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›} {X : ℝ → Ω → (Fin n → ℝ)}
    (hX : ∀ i : Fin n, Probability.ProgressivelyMeasurable ℱ (fun ω s => X s ω i))
    {g : ℝ → (Fin n → ℝ) → E → ℝ}
    (hg : Measurable fun p : ℝ × (Fin n → ℝ) × E => g p.1 p.2.1 p.2.2) :
    Probability.MarkedProgressivelyMeasurable ℱ (fun ω s e => g s (X s ω) e) := by
  intro t
  letI : MeasurableSpace Ω := ℱ t
  have hXm : Measurable fun q : Set.Iic t × Ω => (X (q.1 : ℝ) q.2 : Fin n → ℝ) :=
    measurable_pi_lambda _ fun i => ((_root_.Prove2MeSourceProof.h_e303374519c4de703021a2f6 (hX i)) t).measurable
  have hbase : Measurable fun q : (Set.Iic t × Ω) × E =>
      g (q.1.1 : ℝ) (X (q.1.1 : ℝ) q.1.2) q.2 :=
    hg.comp (((measurable_subtype_coe.comp measurable_fst).comp measurable_fst).prodMk
      ((hXm.comp measurable_fst).prodMk measurable_snd))
  have he : Measurable fun p : Ω × ℝ × E =>
      (((⟨min p.2.1 t, Set.mem_Iic.mpr (min_le_right _ _)⟩ : Set.Iic t), p.1), p.2.2) :=
    (((measurable_fst.comp measurable_snd).min measurable_const).subtype_mk.prodMk
      measurable_fst).prodMk (measurable_snd.comp measurable_snd)
  have heq : (fun p : Ω × ℝ × E =>
        (Set.Iic t).indicator (fun s => g s (X s p.1) p.2.2) p.2.1)
      = (Set.univ ×ˢ (Set.Iic t ×ˢ Set.univ)).indicator
          ((fun q : (Set.Iic t × Ω) × E => g (q.1.1 : ℝ) (X (q.1.1 : ℝ) q.1.2) q.2)
            ∘ fun p : Ω × ℝ × E =>
              (((⟨min p.2.1 t, Set.mem_Iic.mpr (min_le_right _ _)⟩ : Set.Iic t), p.1),
                p.2.2)) := by
    funext p
    by_cases hp : p.2.1 ≤ t
    · simp [hp, Function.comp_def]
    · simp [hp, Function.comp_def]
  rw [heq]
  exact (hbase.comp he).stronglyMeasurable.indicator
    (MeasurableSet.univ.prod (measurableSet_Iic.prod MeasurableSet.univ))
end LevyStochCalc.Ito.Picard


