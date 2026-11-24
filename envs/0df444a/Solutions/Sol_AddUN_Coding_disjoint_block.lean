-- Prove2me | solution 1 for AddUN.Coding.disjoint_block
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:37:46.969833+00:00
-- url     : https://prove2.me/submissions/fb020a8d-176e-4968-b621-10e76af6a413

module
public import Definitions.Def_AddUN_SecondMoment
public import Definitions.Def_AddUN_TheoremB
public import Definitions.Def_AddUN_Coding
public import Theorems.Thm_AddUN_Coding_coord_inj

set_option autoImplicit false
@[expose] public section
public section
open Set Filter MeasureTheory
open AddUN
open AddUN.Coding
namespace AddUN.Coding
theorem _root_.solution {n k k' : ℕ} (h : k ≠ k') : Disjoint (block n k) (block n k') := by
  rw [Finset.disjoint_left]
  intro i hi hi'
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hi
  obtain ⟨j', -, h'⟩ := Finset.mem_image.1 hi'
  exact h (coord_inj.1 h').2.1.symm
end AddUN.Coding
