-- Prove2me | Definitions.Def_SourceProof_079c7ce547fc1a0e6f00ab0a
-- name    : SourceProof_079c7ce547fc1a0e6f00ab0a
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T20:20:54.531796+00:00
-- url     : https://prove2.me/theorems/2163da17-530b-4229-90be-81a871b5707b
-- title:
--   StochLean source theorem: ProbabilityTheory.isSemimartingale_of_locally_squareIntegrableMartingale

import Definitions.Def_SourceProof_1557efb7e848f4cf57c0170c
import Definitions.Def_SourceProof_5be316bda063706d2135fb14
import Definitions.Def_SourceProof_7e41a7708f0759111a0ce622
import Definitions.Def_SourceProof_9f462e2767fad5b3edec7d2e
import Definitions.Def_SourceProof_a3c1e53eb5c3f652441db1d0
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Integral.Indicator
import Mathlib.Probability.Process.HittingTime
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Order.Compact

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Locally square-integrable and continuous local martingale examples

The existing bounded masked localization supplies the L2 witnesses for continuous local
martingales. No L1 or L2 assumption on their unmasked initial values is introduced.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} [IsFiniteMeasure P] [SigmaFiniteFiltration P F]
  {X : ℝ≥0 → Ω → ℝ}

theorem _root_.Prove2MeSourceProof.h_079c7ce547fc1a0e6f00ab0a
    (hF : F.IsUsual P) (hc : HasCadlagPaths X P)
    (hL : Locally (fun Y ↦ IsSquareIntegrableMartingale Y F P) F X P) :
    IsSemimartingale X F P := by
  obtain ⟨τ, hτ, hY⟩ := hL
  apply _root_.Prove2MeSourceProof.h_9f462e2767fad5b3edec7d2e
    ((_root_.Prove2MeSourceProof.h_a3c1e53eb5c3f652441db1d0 hτ.toIsPreLocalizingSequence) hF
      (fun n ↦ (hY n).1.stronglyAdapted.adapted)) hc hτ.toIsPreLocalizingSequence
  intro n
  exact (_root_.Prove2MeSourceProof.h_5be316bda063706d2135fb14 (hY n).1) hF
    ((_root_.Prove2MeSourceProof.h_1557efb7e848f4cf57c0170c ((_root_.Prove2MeSourceProof.h_7e41a7708f0759111a0ce622 hc) {ω | 0 < τ n ω})) (τ n)) (hY n).2
end ProbabilityTheory


