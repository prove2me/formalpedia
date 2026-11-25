-- Prove2me | Definitions.Def_SourceProof_bf3b4f0165446cd3affab35f
-- name    : SourceProof_bf3b4f0165446cd3affab35f
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:29:18.361298+00:00
-- url     : https://prove2.me/theorems/da98edee-370f-49b2-8a25-8419aabbee68
-- title:
--   StochLean source theorem: ProbabilityTheory.CagladApproximation.norm_toProcess_sub_le

import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_OscillationApproximation_F000
import Definitions.Def_SourceProof_45763a1547f08491c4364e73
import Definitions.Def_SourceProof_6703eac8a77f9a75e40ca8b1
import Definitions.Def_SourceProof_6a6a05e8c02fb98984eb1a4a
import Definitions.Def_SourceProof_8f7895612117943074291d58
import Definitions.Def_SourceProof_a9c44e06617a4753cffd0417
import Definitions.Def_SourceProof_bdc7d79620058d0bf6b1336e
import Definitions.Def_SourceProof_ee0958f607118d8fce16af89
import Definitions.Def_SourceProof_f6f1afca5016f9c6b2d52e3e
import Definitions.Def_SourceProof_fff880ea6c6a7bb34bef28fb

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Actual finite simple approximants from oscillation partitions

The first interval is included. The source initial value is sampled independently;
positive-time coefficients sample the right-limit process at finite capped left
endpoints, never at infinity. Bounds hold on the original common caglad path event.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal

namespace ProbabilityTheory.CagladApproximation

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ} {P : Measure Ω}
  (H : ℝ≥0 → Ω → ℝ) (ha : Adapted F H) (hF : F.IsUsual P) (hc : HasCagladPaths H P)

theorem _root_.Prove2MeSourceProof.h_bf3b4f0165446cd3affab35f (ε : ℝ) (hε : 0 ≤ ε) (n : ℕ) (T : ℝ≥0)
    {ω : Ω} (hω : IsCagladPath (H · ω)) {t : ℝ≥0} (htT : t ≤ T)
    (htn : (t : WithTop ℝ≥0) ≤ oscillationTimes (rightLimitProcess H) ε n ω) :
    ‖(representation H ha hF hc ε hε n T).toProcess t ω - H t ω‖ ≤ ε := by
  let π := ProbabilityTheory.CagladApproximation.partition H ha hF hc ε hε n T
  let R := ProbabilityTheory.CagladApproximation.representation H ha hF hc ε hε n T
  change ‖R.toProcess t ω - H t ω‖ ≤ ε
  by_cases ht0 : t = 0
  · subst t
    rw [(_root_.Prove2MeSourceProof.h_a9c44e06617a4753cffd0417 R)]
    change ‖H 0 ω - H 0 ω‖ ≤ ε
    simpa only [sub_self, norm_zero] using hε
  · have htpos : (0 : ℝ≥0) < t := pos_iff_ne_zero.mpr ht0
    have hterminal : t ≤ π.terminal ω :=
      _root_.Prove2MeSourceProof.h_f6f1afca5016f9c6b2d52e3e _ _ _ _ n T htT htn
    have hcell : ∃ i : Fin n, π.point i.castSucc ω < t ∧ t ≤ π.point i.succ ω :=
      (_root_.Prove2MeSourceProof.h_8f7895612117943074291d58 (π.path ω)) ⟨htpos, hterminal⟩
    obtain ⟨i, hi⟩ := hcell
    have horiginal : ProbabilityTheory.oscillationTimes (ProbabilityTheory.rightLimitProcess H) ε i ω =
        (π.point i.castSucc ω : WithTop ℝ≥0) :=
      _root_.Prove2MeSourceProof.h_6703eac8a77f9a75e40ca8b1 _ _ _ _ n T
        (hi.1.trans_le htT)
    have hleft : ProbabilityTheory.oscillationTimes (ProbabilityTheory.rightLimitProcess H) ε i ω < (t : WithTop ℝ≥0) := by
      rw [horiginal]
      exact WithTop.coe_lt_coe.mpr hi.1
    have hright : (t : WithTop ℝ≥0) ≤
        ProbabilityTheory.nextOscillationTime (ProbabilityTheory.rightLimitProcess H) ε
          (ProbabilityTheory.oscillationTimes (ProbabilityTheory.rightLimitProcess H) ε i) ω :=
      (WithTop.coe_le_coe.mpr hi.2).trans
        (_root_.Prove2MeSourceProof.h_6a6a05e8c02fb98984eb1a4a _ _ _ _ n T i.succ ω)
    have hb := _root_.Prove2MeSourceProof.h_bdc7d79620058d0bf6b1336e
      (ProbabilityTheory.oscillationTimes (ProbabilityTheory.rightLimitProcess H) ε i) (_root_.Prove2MeSourceProof.h_fff880ea6c6a7bb34bef28fb hω) hleft hright
    rw [(_root_.Prove2MeSourceProof.h_ee0958f607118d8fce16af89 hω) ht0, horiginal] at hb
    rw [(_root_.Prove2MeSourceProof.h_45763a1547f08491c4364e73 (i := i) R) hi]
    change ‖ProbabilityTheory.rightLimitProcess H (π.point i.castSucc ω) ω - H t ω‖ ≤ ε
    simpa only [WithTop.untopA, WithTop.untopD_coe, norm_sub_rev] using hb
end ProbabilityTheory.CagladApproximation


