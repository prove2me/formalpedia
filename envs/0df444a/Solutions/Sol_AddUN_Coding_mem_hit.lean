-- Prove2me | solution 1 for AddUN.Coding.mem_hit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:30:28.241747+00:00
-- url     : https://prove2.me/submissions/d15e0082-a45e-4484-8cbe-d24580a0268f

module
public import Definitions.Def_AddUN_SecondMoment
public import Definitions.Def_AddUN_TheoremB
public import Definitions.Def_AddUN_Coding
public import Theorems.Thm_AddUN_Coding_stage_coord
public import Theorems.Thm_MeasureTheory_flip_apply_self
public import Theorems.Thm_MeasureTheory_flip_flip
attribute [local simp] MeasureTheory.flip_apply_self
attribute [local simp] MeasureTheory.flip_flip


attribute [local simp] AddUN.Coding.stage_coord

set_option autoImplicit false
@[expose] public section
public section
open Set Filter MeasureTheory
open AddUN
open AddUN.Coding
namespace AddUN.Coding
theorem _root_.solution {c : ℕ → Bool} {n k : ℕ} {w : ℕ → Bool} :
    w ∈ hit c n k ↔ ∀ j < mu n + n, w (coord n k j) = pattern c (coord n k j) := by
  simp [hit, cylinderOn, block]
end AddUN.Coding
