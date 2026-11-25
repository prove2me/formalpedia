-- Prove2me | Definitions.Def_SourceProof_578bbe5ab7e6004e9a789433
-- name    : SourceProof_578bbe5ab7e6004e9a789433
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:28:12.503818+00:00
-- url     : https://prove2.me/theorems/1c6e12c3-4f87-4ca1-816a-e5566dc902cf
-- title:
--   StochLean source theorem: ProbabilityTheory.SimplePredictableRep.memLp_integral_min_const_of_coefficients

import Definitions.Def_StochLean_Probability_Process_Filtration_Usual_F001
import Definitions.Def_StochLean_Probability_Process_Path_RightContinuous_F000
import Definitions.Def_SourceProof_2113cbfa026fcf89ba3d35af
import Definitions.Def_SourceProof_29c5ae821e5120b570769687
import Definitions.Def_SourceProof_51cff7b6f18c4ccd4d6713f8
import Definitions.Def_SourceProof_94b26ceff87499d497c994b8
import Definitions.Def_SourceProof_9a05df2506f159e4ed7b785f
import Definitions.Def_SourceProof_d36deae29721c35a59f8058d
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # The source elementary-integral L2 estimate

For a martingale stopped at a finite deterministic horizon `T`, a uniform process bound `C`
on a simple predictable integrand gives `E[(H · X^T)^2] ≤ C^2 E[X_T^2]`. The source initial
term is retained, random endpoints are not bounded deterministically, and coefficients on
empty intervals are normalized before applying the discrete martingale estimate.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} [IsFiniteMeasure P] [SigmaFiniteFiltration P F]
  {X : ℝ≥0 → Ω → ℝ}

namespace SimplePredictableRep

theorem _root_.Prove2MeSourceProof.h_578bbe5ab7e6004e9a789433 (H : SimplePredictableRep F)
    (hX : Martingale X F P) (hF : F.IsUsual P) (hr : HasRightContinuousPaths X P)
    (T : ℝ≥0) (hXT : MemLp (X T) 2 P) (C : ℝ≥0)
    (hinit : ∀ ω, ‖H.initial ω‖ ≤ C) (hb : ∀ i ω, ‖H.coefficient i ω‖ ≤ C) :
    MemLp (H.integral (fun t ↦ X (min t T))) 2 P := by
  let M := H.partition.sampledProcess (fun t ↦ X (min t T))
  have hlp : ∀ n, MemLp (M n) 2 P :=
    (_root_.Prove2MeSourceProof.h_9a05df2506f159e4ed7b785f H.partition) hX hF hr T (by norm_num) hXT
  have htop : MemLp H.initial ∞ P := memLp_top_of_bound
    (H.measurable_initial.mono (F.le 0) le_rfl).aestronglyMeasurable C (ae_of_all _ hinit)
  have hZlp : MemLp (fun ω ↦ H.initial ω * X 0 ω) 2 P := by
    simpa only [M, _root_.Prove2MeSourceProof.h_29c5ae821e5120b570769687, zero_min] using (hlp 0).mul' htop
  rw [(_root_.Prove2MeSourceProof.h_2113cbfa026fcf89ba3d35af H)]
  simp only [zero_min]
  exact hZlp.add
    (_root_.Prove2MeSourceProof.h_94b26ceff87499d497c994b8 hlp (_root_.Prove2MeSourceProof.h_d36deae29721c35a59f8058d H)
      (fun n ↦ ⟨C, ae_of_all _ ((_root_.Prove2MeSourceProof.h_51cff7b6f18c4ccd4d6713f8 H) C.coe_nonneg hb n)⟩) H.partition.size)
end SimplePredictableRep

namespace IsSimplePredictable

variable {H : ℝ≥0 → Ω → ℝ}

end IsSimplePredictable
end ProbabilityTheory


