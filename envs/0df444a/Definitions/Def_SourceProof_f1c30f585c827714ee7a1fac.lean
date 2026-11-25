-- Prove2me | Definitions.Def_SourceProof_f1c30f585c827714ee7a1fac
-- name    : SourceProof_f1c30f585c827714ee7a1fac
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:38:13.612213+00:00
-- url     : https://prove2.me/theorems/7318e535-7ed8-4a4e-a829-32a8a4166887
-- title:
--   StochLean source theorem: MeasureTheory.isUIMartingale_indicator_sub_condExp_before

import Definitions.Def_SourceProof_3f8c9bee8c801981db97d019
import Definitions.Def_SourceProof_51740884f3e4929ebdd46661
import Definitions.Def_SourceProof_8d1ecfa3e3f6d8e45cbcc4bf

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Before-centered integrable single jumps are UI martingales

The coefficient is measurable at the stopping time, not necessarily before it.
If its conditional expectation before that time vanishes, its actual closed
lifetime step is a martingale. Integrable domination of all stopping values
gives Class D and hence uniform integrability.

No predictability of the lifetime is needed for this centered martingale
statement. Predictability is needed separately to identify the removed
before-conditional step as a predictable compensating process. Infinite
lifetimes never activate at finite time; coefficients are not assumed zero
there and no finite evaluation of an infinite stopping time is used.
-/

@[expose] public section

open ProbabilityTheory Filter Set
open scoped NNReal

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {τ : Ω → WithTop ℝ≥0} {Z : Ω → ℝ}


theorem _root_.Prove2MeSourceProof.h_f1c30f585c827714ee7a1fac
    (hτ : IsStoppingTime F τ) (hm : StronglyMeasurable[hτ.measurableSpace] Z)
    (hi : Integrable Z P) :
    IsUIMartingale (fun t : ℝ≥0 ↦ {ω | τ ω ≤ (t : WithTop ℝ≥0)}.indicator
      (Z - P[Z | hτ.measurableSpaceBefore])) F P := by
  have hK : StronglyMeasurable[hτ.measurableSpace] P[Z | hτ.measurableSpaceBefore] :=
    stronglyMeasurable_condExp.mono (_root_.Prove2MeSourceProof.h_51740884f3e4929ebdd46661 hτ)
  apply _root_.Prove2MeSourceProof.h_8d1ecfa3e3f6d8e45cbcc4bf
    hτ (hm.sub hK) (hi.sub integrable_condExp)
  have he := condExp_sub (m := hτ.measurableSpaceBefore) hi
    (integrable_condExp (f := Z) (m := hτ.measurableSpaceBefore))
  rw [condExp_of_stronglyMeasurable (_root_.Prove2MeSourceProof.h_3f8c9bee8c801981db97d019 hτ)
    stronglyMeasurable_condExp integrable_condExp] at he
  simpa only [sub_self] using he
end MeasureTheory


