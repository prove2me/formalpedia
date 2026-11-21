-- Prove2me | solution 1 for AlgoPrinciplesMulticlass.NoEnvelope.condition1_ds_ge
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T09:52:59.197347+00:00
-- url     : https://prove2.me/submissions/505c790c-64d9-4983-bde2-606ccdd1dee9

import Mathlib
import Definitions.Def_MulticlassDS_Compress_Dimensions
import Definitions.Def_AlgoPrinciplesMulticlass_NoEnvelope_Construction

section
namespace AlgoPrinciplesMulticlass
open NoEnvelope

theorem chk_condition1_ds_ge (F : Set (Pt → Label)) (d : ℕ) (hd : 1 ≤ d)
    (h1 : Condition1 F d) :
    (d : ℕ∞) ≤ MulticlassDS.Compress.dsDim F := by
  obtain ⟨v, hv⟩ := h1
  have hsh : MulticlassDS.Compress.DSShatters F (block d v) := by
    refine ⟨{w | ∃ c : Fin d → Bool, w = fun j => Label.pub (c j)}, ?_, ?_, ?_, ?_⟩
    · rintro w ⟨c, rfl⟩
      obtain ⟨f, hf, hfc⟩ := hv c
      exact ⟨f, hf, funext fun j => hfc j⟩
    · exact ⟨fun _ => Label.pub false, fun _ => false, rfl⟩
    · exact (Set.finite_range (fun c : Fin d → Bool => fun j => Label.pub (c j))).subset
        (by rintro w ⟨c, rfl⟩; exact ⟨c, rfl⟩)
    · rintro w ⟨c, rfl⟩ i
      refine ⟨fun j => Label.pub (Function.update c i (!c i) j), ⟨_, rfl⟩, ?_, ?_⟩
      · simp
      · intro j hj; simp [Function.update_of_ne hj]
  exact le_iSup_of_le d (le_iSup_of_le (block d v) (le_iSup_of_le hsh le_rfl))
end AlgoPrinciplesMulticlass
end

theorem solution : type_of% @AlgoPrinciplesMulticlass.chk_condition1_ds_ge := @AlgoPrinciplesMulticlass.chk_condition1_ds_ge
