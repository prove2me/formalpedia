-- Prove2me | Definitions.Def_SourceProof_954e10b76576263a9def2e7a
-- name    : SourceProof_954e10b76576263a9def2e7a
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T21:35:14.441999+00:00
-- url     : https://prove2.me/theorems/cf188780-9f55-5231-9220-87d4623bb60f
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.continuousQuadraticCovariation_const_mul_left

import Definitions.Def_StochLean_Probability_Process_Semimartingale_QuadraticCovariation_ContinuousPart_F000
import Definitions.Def_SourceProof_1d0b25291561423c84395ca8
import Definitions.Def_SourceProof_4d9ac1d8fdeead36a7d9ab22
import Definitions.Def_SourceProof_60b183cce884b1ffa7a599f8
import Definitions.Def_SourceProof_8c18053bf585bd3a019ad5a3
import Definitions.Def_SourceProof_f3df3adc8be51e4f63a6abca

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Bilinearity of continuous covariation

The common-event raw identities and absolutely summable jump series give the
algebraic identities. No varying-integrator UCP continuity principle is assumed.
-/

@[expose] public section

open MeasureTheory StochLean Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X Y Z X' Y' : ℝ≥0 → Ω → ℝ}

namespace IsSemimartingale
theorem _root_.Prove2MeSourceProof.h_954e10b76576263a9def2e7a
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P) (c : ℝ) :
    Indistinguishable (((_root_.Prove2MeSourceProof.h_8c18053bf585bd3a019ad5a3 hX) c).continuousQuadraticCovariation hY hF)
      (c • hX.continuousQuadraticCovariation hY hF) P := by
  filter_upwards [(_root_.Prove2MeSourceProof.h_1d0b25291561423c84395ca8 ((_root_.Prove2MeSourceProof.h_8c18053bf585bd3a019ad5a3 hX) c)) hY hF,
    (_root_.Prove2MeSourceProof.h_1d0b25291561423c84395ca8 hX) hY hF,
    (_root_.Prove2MeSourceProof.h_f3df3adc8be51e4f63a6abca hX) hY hF c, (_root_.Prove2MeSourceProof.h_60b183cce884b1ffa7a599f8 hX)]
    with ω hc hx hraw hcx t
  have hj : (∑' s : Ioc 0 t, ProbabilityTheory.jumpProcess (fun u v ↦ c * X u v) s ω * ProbabilityTheory.jumpProcess Y s ω) =
      c * (∑' s : Ioc 0 t, ProbabilityTheory.jumpProcess X s ω * ProbabilityTheory.jumpProcess Y s ω) := by
    calc
      _ = ∑' s : Ioc 0 t, c * (ProbabilityTheory.jumpProcess X s ω * ProbabilityTheory.jumpProcess Y s ω) := by
        apply tsum_congr
        intro s
        rw [(_root_.Prove2MeSourceProof.h_4d9ac1d8fdeead36a7d9ab22 hcx) c s]
        ring
      _ = _ := (hx t).1.of_abs.tsum_mul_left c
  have h := (hc t).2
  rw [hraw t, hj] at h
  simp only [Pi.smul_apply, smul_eq_mul] at h ⊢
  linear_combination c * (hx t).2 - h
end IsSemimartingale

end ProbabilityTheory


