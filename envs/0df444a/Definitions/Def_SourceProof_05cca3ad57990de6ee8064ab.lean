-- Prove2me | Definitions.Def_SourceProof_05cca3ad57990de6ee8064ab
-- name    : SourceProof_05cca3ad57990de6ee8064ab
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T20:08:47.472556+00:00
-- url     : https://prove2.me/theorems/c1be9215-eec5-4e0a-999f-6618cd69ae40
-- title:
--   StochLean source theorem: MeasureTheory.Martingale.isTotalSemimartingale_min_const_of_memLp

import Definitions.Def_SourceProof_056f0ffa0965e1b3a522e2ff
import Definitions.Def_SourceProof_2cbb2ed1687ae3057f41e0d2
import Definitions.Def_SourceProof_38b6716030de814054336ad8
import Definitions.Def_SourceProof_95717ff969660c2022f9fd24
import Definitions.Def_SourceProof_9f2f3563711c68b81e63664c
import Definitions.Def_SourceProof_cf9df1889fcdf452e5271cc5

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Square-integrable martingales are source semimartingales

The good-integrator property is proved from the elementary L2 estimate and Markov's
inequality, not assumed as part of a martingale definition or inferred from a decomposition.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} [IsFiniteMeasure P] {X : ℝ≥0 → Ω → ℝ}

variable [SigmaFiniteFiltration P F]

theorem _root_.Prove2MeSourceProof.h_05cca3ad57990de6ee8064ab
    (hX : Martingale X F P) (hF : F.IsUsual P) (hc : HasCadlagPaths X P)
    (T : ℝ≥0) (hXT : MemLp (X T) 2 P) :
    IsTotalSemimartingale (fun t ↦ X (min t T)) F P :=
  ⟨((_root_.Prove2MeSourceProof.h_95717ff969660c2022f9fd24 hX) T).stronglyAdapted.adapted, hc.mono (fun _ h ↦ (_root_.Prove2MeSourceProof.h_056f0ffa0965e1b3a522e2ff h) T),
    (_root_.Prove2MeSourceProof.h_cf9df1889fcdf452e5271cc5 hX) hF (_root_.Prove2MeSourceProof.h_9f2f3563711c68b81e63664c hc) T hXT⟩
end ProbabilityTheory


