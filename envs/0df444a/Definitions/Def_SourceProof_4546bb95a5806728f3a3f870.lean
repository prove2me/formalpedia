-- Prove2me | Definitions.Def_SourceProof_4546bb95a5806728f3a3f870
-- name    : SourceProof_4546bb95a5806728f3a3f870
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:13:29.490081+00:00
-- url     : https://prove2.me/theorems/9b9d4f52-82ec-47dd-8da9-a1eb30299e39
-- title:
--   StochLean source theorem: StochLean.tendsto_derivativeSum_of_continuous_bv

import Definitions.Def_SourceProof_2ba9ae385eb9bd368051c43f
import Definitions.Def_SourceProof_6d08683551c02469b0aeb8c7
import Definitions.Def_SourceProof_906c58377c1118998bf68c2d
import Definitions.Def_SourceProof_be4dfea3ac57333b7efb8bb1
import Definitions.Def_SourceProof_dbbad2cd68b24a5f73db699c
import Definitions.Def_SourceProof_e1f3ecca529106853c30fa13

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # C1 change of variables along a continuous finite-variation path

The first-order remainders are bounded by their derivative oscillation times
the path variation. Actual left Riemann sums identify the Stieltjes integral.
The increment formula excludes the separately owned source initial term.
-/

@[expose] public section

open Filter Set MeasureTheory
open scoped NNReal Topology

namespace StochLean

theorem _root_.Prove2MeSourceProof.h_4546bb95a5806728f3a3f870 {T : ℝ≥0} {x : ℝ≥0 → ℝ}
    (hx : ContinuousOn x (Icc 0 T)) (hv : BoundedVariationOn x (Icc 0 T))
    {φ φ' : ℝ → ℝ} (hφ : ∀ z, HasDerivAt φ (φ' z) z) (hc : Continuous φ')
    {π : ℕ → TimePartition T}
    (hmesh : Tendsto (fun n ↦ ((π n).mesh : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n ↦ ∑ i : Fin (π n).size, φ' (x ((π n).left i)) * (π n).increment x i)
      atTop (𝓝 (φ (x T) - φ (x 0))) := by
  obtain ⟨R, hR⟩ := (isCompact_Icc.image_of_continuousOn hx).isBounded.exists_norm_le
  have hxR (t : ℝ≥0) (ht : t ∈ Icc 0 T) : x t ∈ Icc (-R) R := by
    have h := hR _ (mem_image_of_mem x ht)
    change -R ≤ x t ∧ x t ≤ R
    simpa only [Real.norm_eq_abs, abs_le] using h
  let V : ℝ := (eVariationOn x (Icc 0 T)).toReal
  have hV : 0 ≤ V := ENNReal.toReal_nonneg
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hη : 0 < ε / (V + 1) := div_pos hε (by linarith)
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous (hc.continuousOn (s := Icc (-R) R)))
    (ε / (V + 1)) hη
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    ((_root_.Prove2MeSourceProof.h_be4dfea3ac57333b7efb8bb1 hx hmesh).eventually_lt_const hδ)
  refine ⟨N, fun n hn ↦ ?_⟩
  have hi (i : Fin (π n).size) :
      ‖φ (x ((π n).right i)) - φ (x ((π n).left i)) -
        φ' (x ((π n).left i)) * (π n).increment x i‖ ≤
          ε / (V + 1) * |(π n).increment x i| := by
    apply _root_.Prove2MeSourceProof.h_6d08683551c02469b0aeb8c7 hφ
    intro z hz
    have hl := hxR ((π n).left i) ⟨bot_le, (_root_.Prove2MeSourceProof.h_2ba9ae385eb9bd368051c43f (π n)) _⟩
    have hr := hxR ((π n).right i) ⟨bot_le, (_root_.Prove2MeSourceProof.h_2ba9ae385eb9bd368051c43f (π n)) _⟩
    have hzR := uIcc_subset_Icc hl hr hz
    have hd : dist z (x ((π n).left i)) < δ := by
      calc
        _ = dist (x ((π n).left i)) z := dist_comm _ _
        _ ≤ dist (x ((π n).left i)) (x ((π n).right i)) := Real.dist_left_le_of_mem_uIcc hz
        _ = |(π n).increment x i| := by rw [dist_comm, Real.dist_eq, StochLean.TimePartition.increment]
        _ ≤ ((π n).maxIncrement x : ℝ) := (_root_.Prove2MeSourceProof.h_906c58377c1118998bf68c2d (π n)) x i
        _ < δ := hN n hn
    exact (hmod z hzR (x ((π n).left i)) hl hd).le
  have hsum : ‖(φ (x T) - φ (x 0)) -
      ∑ i : Fin (π n).size, φ' (x ((π n).left i)) * (π n).increment x i‖ ≤ ε / (V + 1) * V := by
    rw [← (_root_.Prove2MeSourceProof.h_e1f3ecca529106853c30fa13 (π n)) (fun t ↦ φ (x t)), ← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ i : Fin (π n).size, ‖(π n).increment (fun t ↦ φ (x t)) i -
          φ' (x ((π n).left i)) * (π n).increment x i‖ := norm_sum_le _ _
      _ ≤ ∑ i : Fin (π n).size, ε / (V + 1) * |(π n).increment x i| :=
        Finset.sum_le_sum fun i _ ↦ hi i
      _ = ε / (V + 1) * ∑ i : Fin (π n).size, |(π n).increment x i| := by rw [Finset.mul_sum]
      _ ≤ ε / (V + 1) * V := mul_le_mul_of_nonneg_left ((_root_.Prove2MeSourceProof.h_dbbad2cd68b24a5f73db699c (π n)) hv) hη.le
  rw [dist_comm, dist_eq_norm_sub]
  apply hsum.trans_lt
  calc
    _ < ε / (V + 1) * (V + 1) := mul_lt_mul_of_pos_left (by linarith) hη
    _ = ε := div_mul_cancel₀ _ (by linarith)
end StochLean


