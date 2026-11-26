-- Prove2me | Definitions.Def_SourceProof_b9fa7849de713fb134f04028
-- name    : SourceProof_b9fa7849de713fb134f04028
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T22:52:26.905882+00:00
-- url     : https://prove2.me/theorems/8187f2d6-21fe-4521-bf94-333419773141
-- title:
--   StochLean source theorem: ProbabilityTheory.HasLocallyIntegrableVariation.congr

import Definitions.Def_StochLean_Probability_Process_FiniteVariation_IntegrableAlgebra_F000
import Definitions.Def_StochLean_Probability_Process_FiniteVariation_LocallyIntegrable_F000
import Definitions.Def_SourceProof_508a0388fcd9912008955e80
import Definitions.Def_SourceProof_a239f509638bc9274841d0b5
import Definitions.Def_SourceProof_ae0266e80e099d3f3f27bbad

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Algebra of locally integrable variation

The only local predicate remains Mathlib's `Locally`, through the existing
unmasked stopped-variation criterion. Indistinguishability and negation reuse
the same localizing sequence without any process measurability assumption.

For addition, the native minimum of two localizing sequences retains their
almost-sure monotonicity; no pointwise monotonicity is imposed. Actual stopping
and sum variation are measurable because the processes are adapted and cadlag
on a usual filtration. Variation domination alone is not used to infer that
measurability. Subtraction then follows from addition and exact negation.

None of these results assumes a finite measure, integrable initial random
values, or zero initial values. No new local predicate or selector is defined.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {F : Filtration ℝ≥0 mΩ} {X Y : ℝ≥0 → Ω → ℝ}

namespace HasLocallyIntegrableVariation

theorem _root_.Prove2MeSourceProof.h_b9fa7849de713fb134f04028 (hX : HasLocallyIntegrableVariation X F P)
    (hXY : Indistinguishable X Y P) : HasLocallyIntegrableVariation Y F P := by
  obtain ⟨τ, hτ, hv⟩ := _root_.Prove2MeSourceProof.h_ae0266e80e099d3f3f27bbad.mp hX
  exact _root_.Prove2MeSourceProof.h_ae0266e80e099d3f3f27bbad.mpr
    ⟨τ, hτ, fun n ↦ (_root_.Prove2MeSourceProof.h_508a0388fcd9912008955e80 (hv n)) ((_root_.Prove2MeSourceProof.h_a239f509638bc9274841d0b5 hXY) (τ n))⟩
end HasLocallyIntegrableVariation

end ProbabilityTheory


