-- Prove2me | Definitions.Def_SourceProof_543644674db164bf73853b19
-- name    : SourceProof_543644674db164bf73853b19
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:27:07.498858+00:00
-- url     : https://prove2.me/theorems/9b37ec53-7ab6-45ef-8abf-f223c4a23ab2
-- title:
--   StochLean source theorem: MeasureTheory.Martingale.uniformIntegrable_of_integrable_closing

import Definitions.Def_StochLean_Probability_Process_Filtration_Reindex_F000
import Definitions.Def_StochLean_Probability_Process_LocalMartingale_F000
import Definitions.Def_StochLean_Probability_Process_LocalMartingale_F001
import Mathlib.Probability.Martingale.Convergence

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Closing a continuous-time uniformly integrable martingale

An integer-time restriction supplies an actual integrable terminal variable.
The tower property then closes every real-time coordinate. This implication
requires no path regularity; the almost-sure limit over the entire half-line
is a separate assertion, not confused with convergence along the integers.

Source: the closed/UI equivalence in Protter I.13 (martingale part).
-/

@[expose] public section

open ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace MeasureTheory.Martingale

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ} [IsFiniteMeasure P]

theorem _root_.Prove2MeSourceProof.h_543644674db164bf73853b19 {Z : Ω → ℝ}
    (hi : Integrable Z P) (hclose : ∀ t, X t =ᵐ[P] P[Z | F t]) :
    UniformIntegrable X 1 P :=
  (hi.uniformIntegrable_condExp F.le).ae_eq (fun t ↦ (hclose t).symm)
end MeasureTheory.Martingale


