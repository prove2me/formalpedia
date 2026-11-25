-- Prove2me | Definitions.Def_SourceProof_eb79ab10a8ab282316156b75
-- name    : SourceProof_eb79ab10a8ab282316156b75
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:09:39.422085+00:00
-- url     : https://prove2.me/theorems/2db7d047-2099-531b-9b4f-53b51700d693
-- title:
--   StochLean source theorem: ProbabilityTheory.StoppingTimePartition.quadraticCovariationSumProcess_eq_product_sub_riemann

import Definitions.Def_StochLean_Probability_Process_Partition_CrossSums_F000
import Definitions.Def_SourceProof_e1f3ecca529106853c30fa13
import Definitions.Def_SourceProof_fc4a2bac5634cdbfe2b154e5

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Exact integration by parts for the finite mixed increment sums

No path regularity is needed. The moving partial cell and repeated endpoints
are included, and the terminal product is evaluated at the capped horizon.
-/

@[expose] public section

open MeasureTheory Finset
open scoped NNReal

namespace ProbabilityTheory.StoppingTimePartition

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}

theorem _root_.Prove2MeSourceProof.h_eb79ab10a8ab282316156b75 (π : StoppingTimePartition F)
    (X Y : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) :
    π.quadraticCovariationSumProcess X Y t ω =
      X (min (π.terminal ω) t) ω * Y (min (π.terminal ω) t) ω -
        π.leftRiemannSumProcess X Y t ω - π.leftRiemannSumProcess Y X t ω := by
  let ρ := π.path ω
  have htel := (_root_.Prove2MeSourceProof.h_e1f3ecca529106853c30fa13 ρ) (fun u ↦ X (min u t) ω * Y (min u t) ω)
  simp only [StochLean.TimePartition.increment, zero_min] at htel
  have hcell (i : Fin π.size) :
      (X (min (π.point i.succ ω) t) ω - X (min (π.point i.castSucc ω) t) ω) *
        (Y (min (π.point i.succ ω) t) ω - Y (min (π.point i.castSucc ω) t) ω) =
      (X (min (π.point i.succ ω) t) ω * Y (min (π.point i.succ ω) t) ω -
        X (min (π.point i.castSucc ω) t) ω * Y (min (π.point i.castSucc ω) t) ω) -
      X (π.point i.castSucc ω) ω *
        (Y (min (π.point i.succ ω) t) ω - Y (min (π.point i.castSucc ω) t) ω) -
      Y (π.point i.castSucc ω) ω *
        (X (min (π.point i.succ ω) t) ω - X (min (π.point i.castSucc ω) t) ω) := by
    by_cases hi : π.point i.castSucc ω ≤ t
    · rw [min_eq_left hi]
      ring
    · have ht : t ≤ π.point i.castSucc ω := (lt_of_not_ge hi).le
      have htr : t ≤ π.point i.succ ω := ht.trans ((_root_.Prove2MeSourceProof.h_fc4a2bac5634cdbfe2b154e5 ρ) i)
      simp only [min_eq_right ht, min_eq_right htr, sub_self, mul_zero]
  have hs := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl (fun i _ ↦ hcell i)
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib] at hs
  change (∑ i : Fin π.size,
    (X (min (π.point i.succ ω) t) ω * Y (min (π.point i.succ ω) t) ω -
      X (min (π.point i.castSucc ω) t) ω * Y (min (π.point i.castSucc ω) t) ω)) = _ at htel
  rw [htel] at hs
  change X 0 ω * Y 0 ω + (∑ i : Fin π.size,
    (X (min (π.point i.succ ω) t) ω - X (min (π.point i.castSucc ω) t) ω) *
      (Y (min (π.point i.succ ω) t) ω - Y (min (π.point i.castSucc ω) t) ω)) = _
  rw [hs]
  change _ = _ - (∑ i : Fin π.size, _) - (∑ i : Fin π.size, _)
  ring
end ProbabilityTheory.StoppingTimePartition


