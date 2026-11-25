-- Prove2me | Definitions.Def_SourceProof_693094da5a8c94cbc1a6a90b
-- name    : SourceProof_693094da5a8c94cbc1a6a90b
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:26:08.924334+00:00
-- url     : https://prove2.me/theorems/10e85b99-9b10-513c-a12a-f58fc4fa212b
-- title:
--   StochLean source theorem: ProbabilityTheory.SimplePredictableRep.jumpProcess_integralProcess

import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_IntegralProcess_F001
import Definitions.Def_SourceProof_0146b8a6534f7d6ff6a61309
import Definitions.Def_SourceProof_0cd12103eb000692396f52e4
import Definitions.Def_SourceProof_36f071daa4d958dd1bd65126
import Definitions.Def_SourceProof_5caa95db89fdd596c2cde105
import Definitions.Def_SourceProof_a9c44e06617a4753cffd0417
import Definitions.Def_SourceProof_fc4a2bac5634cdbfe2b154e5
import Mathlib.Topology.Order.DenselyOrdered

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Jumps of the source elementary integral process

Actual left limits of the finite stopped summands give the formula at every time.
The coefficient on `(T_i,T_(i+1)]` is used at its right endpoint, with the separate
initial coefficient at zero. Repeated endpoints and unbounded coefficients are allowed.
-/

@[expose] public section

open MeasureTheory Filter Set Finset
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {X : ℝ≥0 → Ω → ℝ} {ω : Ω}

namespace SimplePredictableRep
theorem _root_.Prove2MeSourceProof.h_693094da5a8c94cbc1a6a90b (H : SimplePredictableRep F)
    (hX : IsCadlagPath (X · ω)) (t : ℝ≥0) :
    jumpProcess (H.integralProcess X) t ω = H.toProcess t ω * jumpProcess X t ω := by
  by_cases ht : t = 0
  · subst t
    simp only [_root_.Prove2MeSourceProof.h_36f071daa4d958dd1bd65126, (_root_.Prove2MeSourceProof.h_0146b8a6534f7d6ff6a61309 H), (_root_.Prove2MeSourceProof.h_a9c44e06617a4753cffd0417 H)]
  · let : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, pos_iff_ne_zero.mpr ht⟩
    let L : ℝ≥0 → ℝ := fun a ↦ if a < t then X a ω else ProbabilityTheory.leftLimitProcess X t ω
    have hlim : Tendsto (fun s ↦ H.integralProcess X s ω) (𝓝[<] t)
        (𝓝 (H.initial ω * X 0 ω + ∑ i : Fin H.partition.size, H.coefficient i ω *
          (L (H.partition.point i.succ ω) - L (H.partition.point i.castSucc ω)))) := by
      have hs := tendsto_finsetSum univ (fun i (_ : i ∈ (univ : Finset (Fin H.partition.size))) ↦
        (((_root_.Prove2MeSourceProof.h_0cd12103eb000692396f52e4 hX) ht (H.partition.point i.succ ω)).sub
          ((_root_.Prove2MeSourceProof.h_0cd12103eb000692396f52e4 hX) ht (H.partition.point i.castSucc ω))).const_mul
            (H.coefficient i ω))
      simpa only [(_root_.Prove2MeSourceProof.h_5caa95db89fdd596c2cde105 H), L] using hs.const_add (H.initial ω * X 0 ω)
    have hleft : ProbabilityTheory.leftLimitProcess (H.integralProcess X) t ω =
        H.initial ω * X 0 ω + ∑ i : Fin H.partition.size, H.coefficient i ω *
          (L (H.partition.point i.succ ω) - L (H.partition.point i.castSucc ω)) := by
      simp only [ProbabilityTheory.leftLimitProcess, if_neg ht]
      exact leftLim_eq_of_tendsto hlim
    change H.integralProcess X t ω - ProbabilityTheory.leftLimitProcess (H.integralProcess X) t ω = _
    rw [hleft, (_root_.Prove2MeSourceProof.h_5caa95db89fdd596c2cde105 H)]
    simp only [ProbabilityTheory.SimplePredictableRep.toProcess, if_neg ht]
    rw [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    have horder : H.partition.point i.castSucc ω ≤ H.partition.point i.succ ω :=
      (_root_.Prove2MeSourceProof.h_fc4a2bac5634cdbfe2b154e5 (H.partition.path ω)) i
    by_cases hl : H.partition.point i.castSucc ω < t
    · by_cases hr : t ≤ H.partition.point i.succ ω
      · simp only [L, if_pos hl, if_neg (not_lt_of_ge hr), min_eq_right hr,
          min_eq_left hl.le, hl, hr, and_self, if_true, ProbabilityTheory.jumpProcess, Pi.sub_apply]
        ring
      · have hr' := lt_of_not_ge hr
        simp only [L, if_pos hl, if_pos hr', min_eq_left hl.le, min_eq_left hr'.le,
          hl, hr, and_false, if_false, sub_self, zero_mul]
    · have hl' := le_of_not_gt hl
      have hr := hl'.trans horder
      simp only [L, if_neg hl, if_neg (not_lt_of_ge hr), min_eq_right hl', min_eq_right hr,
        hl, false_and, if_false, sub_self, mul_zero, zero_mul]
end SimplePredictableRep

end ProbabilityTheory


