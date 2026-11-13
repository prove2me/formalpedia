-- Prove2me | Definitions.Def_ProbabilityTheory_chapter_01_def_1_3_F002
-- name    : ProbabilityTheory_chapter_01_def_1_3_F002
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-12T19:48:57.666592+00:00
-- url     : https://prove2.me/theorems/491aeb9a-b08c-4213-a8a4-040a0de6253e
-- title:
--   Chapter 1, def_1_3: supporting Lean bundle F002
-- statement:
--   Supporting Lean declarations for Chapter 1, source module `def_1_3`: `upperStep_id`, `lowerStep_id`, `upperStep_mem`, `lowerStep_mem`, `step_bound`. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/def_1_3.lean

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_def_1_3_F001
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

noncomputable section

end   

noncomputable section DiscreteExpectation

namespace DiscreteExpectation

variable {a b : ℝ}

lemma upperStep_id (P : Partition a b) (i : Fin P.n) :
    upperStep P (fun x => x) i = P.pts i.succ := by
  unfold upperStep Partition.subinterval
  have h_img : (fun x => x) '' Set.Icc (P.pts i.castSucc) (P.pts i.succ) = Set.Icc (P.pts i.castSucc) (P.pts i.succ) := by
    ext x
    simp only [Set.mem_image, Set.mem_Icc]
    constructor
    · rintro ⟨y, hy, rfl⟩; exact hy
    · intro hx; exact ⟨x, hx, rfl⟩
  rw [h_img]
  have hab : P.pts i.castSucc ≤ P.pts i.succ := (P.strict_mono (Fin.castSucc_lt_succ)).le
  have H_greatest : IsGreatest (Set.Icc (P.pts i.castSucc) (P.pts i.succ)) (P.pts i.succ) :=
    ⟨⟨hab, le_rfl⟩, fun _ hx => hx.2⟩
  exact IsGreatest.csSup_eq H_greatest
lemma lowerStep_id (P : Partition a b) (i : Fin P.n) :
    lowerStep P (fun x => x) i = P.pts i.castSucc := by
  unfold lowerStep Partition.subinterval
  have h_img : (fun x => x) '' Set.Icc (P.pts i.castSucc) (P.pts i.succ) = Set.Icc (P.pts i.castSucc) (P.pts i.succ) := by
    ext x
    simp only [Set.mem_image, Set.mem_Icc]
    constructor
    · rintro ⟨y, hy, rfl⟩; exact hy
    · intro hx; exact ⟨x, hx, rfl⟩
  rw [h_img]
  have hab : P.pts i.castSucc ≤ P.pts i.succ := (P.strict_mono (Fin.castSucc_lt_succ)).le
  have H_least : IsLeast (Set.Icc (P.pts i.castSucc) (P.pts i.succ)) (P.pts i.castSucc) :=
    ⟨⟨le_rfl, hab⟩, fun _ hx => hx.1⟩
  exact IsLeast.csInf_eq H_least
lemma upperStep_mem (P : Partition a b) (i : Fin P.n) :
    upperStep P (fun x => x) i ∈ Partition.subinterval P i := by
  rw [upperStep_id]
  exact ⟨(P.strict_mono (Fin.castSucc_lt_succ )).le, le_rfl⟩
lemma lowerStep_mem (P : Partition a b) (i : Fin P.n) :
    lowerStep P (fun x => x) i ∈ Partition.subinterval P i := by
  rw [lowerStep_id]
  exact ⟨le_rfl, (P.strict_mono (Fin.castSucc_lt_succ )).le⟩
lemma step_bound (P : Partition a b) (c : ℝ) (i : Fin P.n) (x : ℝ)
    (hx : x ∈ Partition.subinterval P i) :
    |x - c| * (stepIndicator c (P.pts i.succ) - stepIndicator c (P.pts i.castSucc)) ≤
      P.mesh * (stepIndicator c (P.pts i.succ) - stepIndicator c (P.pts i.castSucc)) := by
  let Δ := stepIndicator c (P.pts i.succ) - stepIndicator c (P.pts i.castSucc)
  dsimp only [stepIndicator]
  split_ifs with h1 h2
  · ring_nf; rfl
  · rw [sub_zero, mul_one, mul_one]
    have h3 : P.pts i.castSucc < c := not_le.mp h2
    have abs_bound : |x - c| ≤ P.pts i.succ - P.pts i.castSucc :=
      abs_le.mpr ⟨by linarith [hx.1, h1], by linarith [hx.2, h3]⟩

    have H_mesh : P.pts i.succ - P.pts i.castSucc ≤ P.mesh := by
      unfold Partition.mesh

      exact Finset.le_sup' (fun j => P.pts j.succ - P.pts j.castSucc) (Finset.mem_univ i)

    exact le_trans abs_bound H_mesh
  · exfalso
    have h_strict : P.pts i.castSucc < P.pts i.succ
      := P.strict_mono Fin.castSucc_lt_succ
    linarith

  · ring_nf; rfl

end DiscreteExpectation   
end DiscreteExpectation   

section ContinuousExpectation

namespace ContinuousExpectation

end ContinuousExpectation   
end ContinuousExpectation


