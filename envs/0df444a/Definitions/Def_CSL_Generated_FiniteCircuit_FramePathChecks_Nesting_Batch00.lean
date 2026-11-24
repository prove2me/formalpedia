-- Prove2me | Definitions.Def_CSL_Generated_FiniteCircuit_FramePathChecks_Nesting_Batch00
-- name    : CSL_Generated_FiniteCircuit_FramePathChecks_Nesting_Batch00
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T14:12:51.082897+00:00
-- url     : https://prove2.me/theorems/651c2237-d8d7-4311-996c-94b35b848500
-- title:
--   Coded sorting library: Generated / FiniteCircuit / FramePathChecks / Nesting / Batch00
-- statement:
--   Module `CodedSorting.Generated.FiniteCircuit.FramePathChecks.Nesting.Batch00` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   Generated physical-frame checks. Uncompiled until a build record exists.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Generated.FiniteCircuit.FramePathChecks.Nesting.Batch00

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Generated_FiniteCircuit_FramePathChecks_Entries_Batch00
import Definitions.Def_CSL_Generated_FiniteCircuit_FramePathChecks_Entries_Batch01
import Definitions.Def_CSL_Generated_FiniteCircuit_FramePathChecks_Entries_Batch02
import Definitions.Def_CSL_Generated_FiniteCircuit_FramePathChecks_Entries_Batch03
import Definitions.Def_CSL_Generated_FiniteCircuit_FramePathChecks_Entries_Batch04
import Definitions.Def_CSL_Generated_FiniteCircuit_FramePathChecks_TrivialNesting

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem canClimb_0_2 : canClimb 0 2 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup002]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq002]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_3 : canClimb 0 3 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup003]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq003]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_4 : canClimb 0 4 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup004]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq004]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_5 : canClimb 0 5 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup005]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq005]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_6 : canClimb 0 6 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup006]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq006]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_7 : canClimb 0 7 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup007]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq007]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_8 : canClimb 0 8 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup008]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq008]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_9 : canClimb 0 9 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup009]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq009]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_10 : canClimb 0 10 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup010]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq010]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_11 : canClimb 0 11 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup011]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq011]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_12 : canClimb 0 12 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup012]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq012]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_13 : canClimb 0 13 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup013]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq013]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_14 : canClimb 0 14 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup014]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq014]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_15 : canClimb 0 15 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup015]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq015]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_16 : canClimb 0 16 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup016]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq016]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_17 : canClimb 0 17 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup017]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq017]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_18 : canClimb 0 18 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup018]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq018]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_19 : canClimb 0 19 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup019]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq019]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_20 : canClimb 0 20 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup020]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq020]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_21 : canClimb 0 21 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup021]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq021]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_22 : canClimb 0 22 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup022]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq022]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_23 : canClimb 0 23 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup023]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq023]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_24 : canClimb 0 24 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup024]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq024]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_25 : canClimb 0 25 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup025]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq025]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem canClimb_0_26 : canClimb 0 26 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup026]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq026]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_27 : canClimb 0 27 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup027]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq027]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_28 : canClimb 0 28 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup028]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq028]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_29 : canClimb 0 29 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup029]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq029]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_30 : canClimb 0 30 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup030]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq030]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_31 : canClimb 0 31 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup031]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq031]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_32 : canClimb 0 32 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup032]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq032]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_33 : canClimb 0 33 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup033]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq033]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_34 : canClimb 0 34 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup034]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq034]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_35 : canClimb 0 35 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup035]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq035]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_36 : canClimb 0 36 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup036]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq036]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_37 : canClimb 0 37 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup037]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq037]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_38 : canClimb 0 38 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup038]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq038]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_39 : canClimb 0 39 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup039]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq039]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_40 : canClimb 0 40 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup040]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq040]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_41 : canClimb 0 41 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup041]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq041]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_42 : canClimb 0 42 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup042]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq042]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_43 : canClimb 0 43 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup043]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq043]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_44 : canClimb 0 44 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup044]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq044]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_45 : canClimb 0 45 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup045]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq045]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_46 : canClimb 0 46 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup046]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq046]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_47 : canClimb 0 47 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup047]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq047]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_48 : canClimb 0 48 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup048]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq048]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_49 : canClimb 0 49 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup049]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq049]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem canClimb_0_50 : canClimb 0 50 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup050]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq050]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_51 : canClimb 0 51 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup051]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq051]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_52 : canClimb 0 52 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup052]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq052]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_53 : canClimb 0 53 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup053]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq053]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_54 : canClimb 0 54 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup054]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq054]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_55 : canClimb 0 55 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup055]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq055]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_56 : canClimb 0 56 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup056]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq056]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_57 : canClimb 0 57 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup057]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq057]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_58 : canClimb 0 58 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup058]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq058]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_59 : canClimb 0 59 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup059]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq059]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_60 : canClimb 0 60 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup060]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq060]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_61 : canClimb 0 61 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup061]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq061]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_62 : canClimb 0 62 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup062]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq062]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_63 : canClimb 0 63 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup063]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq063]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_64 : canClimb 0 64 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup064]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq064]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_65 : canClimb 0 65 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup065]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq065]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_66 : canClimb 0 66 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup066]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq066]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_67 : canClimb 0 67 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup067]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq067]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_68 : canClimb 0 68 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup068]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq068]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_69 : canClimb 0 69 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup069]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq069]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_70 : canClimb 0 70 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup070]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq070]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_71 : canClimb 0 71 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup071]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq071]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_72 : canClimb 0 72 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup072]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq072]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_73 : canClimb 0 73 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup073]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq073]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem canClimb_0_74 : canClimb 0 74 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup074]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq074]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_75 : canClimb 0 75 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup075]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq075]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_76 : canClimb 0 76 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup076]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq076]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_77 : canClimb 0 77 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup077]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq077]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_78 : canClimb 0 78 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup078]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq078]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_79 : canClimb 0 79 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup079]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq079]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_80 : canClimb 0 80 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup080]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq080]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_81 : canClimb 0 81 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup081]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq081]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_82 : canClimb 0 82 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup082]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq082]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_83 : canClimb 0 83 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup083]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq083]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_84 : canClimb 0 84 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup084]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq084]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_85 : canClimb 0 85 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup085]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq085]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_86 : canClimb 0 86 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup086]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq086]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_87 : canClimb 0 87 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup087]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq087]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_88 : canClimb 0 88 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup088]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq088]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_89 : canClimb 0 89 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup089]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq089]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_90 : canClimb 0 90 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup090]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq090]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_91 : canClimb 0 91 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup091]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq091]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_92 : canClimb 0 92 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup092]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq092]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_93 : canClimb 0 93 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup093]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq093]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_94 : canClimb 0 94 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup094]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq094]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_95 : canClimb 0 95 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup095]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq095]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_96 : canClimb 0 96 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup096]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq096]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_97 : canClimb 0 97 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup097]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq097]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem canClimb_0_98 : canClimb 0 98 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup098]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq098]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_99 : canClimb 0 99 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup099]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq099]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_100 : canClimb 0 100 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup100]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq100]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_101 : canClimb 0 101 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup101]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq101]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_102 : canClimb 0 102 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup102]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq102]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_103 : canClimb 0 103 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup103]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq103]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_104 : canClimb 0 104 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup104]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq104]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_105 : canClimb 0 105 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup105]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq105]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_106 : canClimb 0 106 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup106]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq106]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_107 : canClimb 0 107 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup107]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq107]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_108 : canClimb 0 108 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup108]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq108]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_109 : canClimb 0 109 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup109]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq109]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_110 : canClimb 0 110 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup110]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq110]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_111 : canClimb 0 111 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup111]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq111]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_112 : canClimb 0 112 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup112]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq112]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_113 : canClimb 0 113 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup113]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq113]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_114 : canClimb 0 114 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup114]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq114]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_115 : canClimb 0 115 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup115]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq115]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_116 : canClimb 0 116 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup116]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq116]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_117 : canClimb 0 117 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup117]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq117]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_118 : canClimb 0 118 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup118]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq118]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_119 : canClimb 0 119 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup119]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq119]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_120 : canClimb 0 120 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup120]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq120]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_121 : canClimb 0 121 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup121]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq121]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem canClimb_0_122 : canClimb 0 122 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup122]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq122]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_123 : canClimb 0 123 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup123]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq123]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_124 : canClimb 0 124 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup124]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq124]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_125 : canClimb 0 125 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup125]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq125]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_126 : canClimb 0 126 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup126]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq126]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_127 : canClimb 0 127 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup127]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq127]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_128 : canClimb 0 128 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup128]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq128]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_129 : canClimb 0 129 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup129]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq129]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_130 : canClimb 0 130 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup130]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq130]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_131 : canClimb 0 131 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup131]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq131]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_132 : canClimb 0 132 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup132]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq132]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_133 : canClimb 0 133 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup133]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq133]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_134 : canClimb 0 134 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup134]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq134]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_135 : canClimb 0 135 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup135]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq135]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_136 : canClimb 0 136 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup136]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq136]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_137 : canClimb 0 137 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup137]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq137]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_138 : canClimb 0 138 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup138]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq138]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_139 : canClimb 0 139 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup139]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq139]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_140 : canClimb 0 140 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup140]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq140]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_141 : canClimb 0 141 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup141]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq141]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_142 : canClimb 0 142 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup142]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq142]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_143 : canClimb 0 143 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup143]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq143]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_144 : canClimb 0 144 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup144]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq144]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_145 : canClimb 0 145 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup145]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq145]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem canClimb_0_146 : canClimb 0 146 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup146]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq146]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_147 : canClimb 0 147 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup147]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq147]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_148 : canClimb 0 148 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup148]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq148]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_149 : canClimb 0 149 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup149]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq149]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_150 : canClimb 0 150 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup150]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq150]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_151 : canClimb 0 151 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup151]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq151]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_152 : canClimb 0 152 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup152]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq152]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_153 : canClimb 0 153 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup153]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq153]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_154 : canClimb 0 154 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup154]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq154]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_155 : canClimb 0 155 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup155]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq155]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_156 : canClimb 0 156 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup156]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq156]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_157 : canClimb 0 157 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup157]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq157]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_158 : canClimb 0 158 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup158]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq158]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_159 : canClimb 0 159 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup159]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq159]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_160 : canClimb 0 160 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup160]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq160]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_161 : canClimb 0 161 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup161]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq161]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_162 : canClimb 0 162 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup162]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq162]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_163 : canClimb 0 163 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup163]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq163]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_164 : canClimb 0 164 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup164]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq164]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_165 : canClimb 0 165 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup165]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq165]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_166 : canClimb 0 166 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup166]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq166]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_167 : canClimb 0 167 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup167]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq167]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_168 : canClimb 0 168 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup168]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq168]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_169 : canClimb 0 169 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup169]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq169]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem canClimb_0_170 : canClimb 0 170 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup170]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq170]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_171 : canClimb 0 171 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup171]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq171]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_172 : canClimb 0 172 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup172]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq172]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_173 : canClimb 0 173 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup173]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq173]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_174 : canClimb 0 174 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup174]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq174]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_175 : canClimb 0 175 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup175]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq175]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_176 : canClimb 0 176 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup176]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq176]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_177 : canClimb 0 177 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup177]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq177]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_178 : canClimb 0 178 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup178]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq178]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_179 : canClimb 0 179 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup179]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq179]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_180 : canClimb 0 180 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup180]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq180]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_181 : canClimb 0 181 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup181]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq181]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_182 : canClimb 0 182 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup182]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq182]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_183 : canClimb 0 183 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup183]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq183]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_184 : canClimb 0 184 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup184]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq184]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_185 : canClimb 0 185 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup185]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq185]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_186 : canClimb 0 186 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup186]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq186]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_187 : canClimb 0 187 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup187]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq187]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_188 : canClimb 0 188 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup188]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq188]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_189 : canClimb 0 189 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup189]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq189]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_190 : canClimb 0 190 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup190]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq190]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_191 : canClimb 0 191 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup191]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq191]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_192 : canClimb 0 192 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup192]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq192]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_193 : canClimb 0 193 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup193]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq193]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem canClimb_0_194 : canClimb 0 194 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup194]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq194]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_195 : canClimb 0 195 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup195]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq195]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_196 : canClimb 0 196 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup196]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq196]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_197 : canClimb 0 197 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup197]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq197]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_198 : canClimb 0 198 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup198]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq198]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_199 : canClimb 0 199 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup199]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq199]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_200 : canClimb 0 200 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup200]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq200]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_201 : canClimb 0 201 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup201]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq201]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_202 : canClimb 0 202 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup202]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq202]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_203 : canClimb 0 203 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup203]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq203]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_204 : canClimb 0 204 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup204]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq204]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_205 : canClimb 0 205 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup205]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq205]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_206 : canClimb 0 206 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup206]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq206]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_207 : canClimb 0 207 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup207]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq207]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_208 : canClimb 0 208 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup208]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq208]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_209 : canClimb 0 209 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup209]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq209]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_210 : canClimb 0 210 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup210]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq210]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_211 : canClimb 0 211 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup211]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq211]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_212 : canClimb 0 212 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup212]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq212]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_213 : canClimb 0 213 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup213]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq213]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_214 : canClimb 0 214 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup214]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq214]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_215 : canClimb 0 215 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup215]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq215]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_216 : canClimb 0 216 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup216]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq216]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_217 : canClimb 0 217 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup217]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq217]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem canClimb_0_218 : canClimb 0 218 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup218]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq218]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_219 : canClimb 0 219 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup219]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq219]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_220 : canClimb 0 220 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup220]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq220]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_221 : canClimb 0 221 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup221]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq221]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_222 : canClimb 0 222 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup222]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq222]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_223 : canClimb 0 223 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup223]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq223]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_224 : canClimb 0 224 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup224]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq224]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_225 : canClimb 0 225 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup225]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq225]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_226 : canClimb 0 226 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup226]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq226]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_227 : canClimb 0 227 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup227]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq227]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_228 : canClimb 0 228 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup228]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq228]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_229 : canClimb 0 229 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup229]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq229]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_230 : canClimb 0 230 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup230]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq230]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_231 : canClimb 0 231 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup231]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq231]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_232 : canClimb 0 232 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup232]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq232]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_233 : canClimb 0 233 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup233]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq233]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_234 : canClimb 0 234 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup234]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq234]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_235 : canClimb 0 235 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup235]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq235]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_236 : canClimb 0 236 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup236]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq236]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_237 : canClimb 0 237 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup237]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq237]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_238 : canClimb 0 238 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup238]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq238]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_239 : canClimb 0 239 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup239]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq239]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_240 : canClimb 0 240 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup240]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq240]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_241 : canClimb 0 241 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup241]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq241]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem canClimb_0_242 : canClimb 0 242 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup242]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq242]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_243 : canClimb 0 243 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup243]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq243]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_244 : canClimb 0 244 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup244]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq244]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_245 : canClimb 0 245 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup245]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq245]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_246 : canClimb 0 246 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup246]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq246]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_247 : canClimb 0 247 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup247]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq247]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_248 : canClimb 0 248 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup248]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq248]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_249 : canClimb 0 249 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup249]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq249]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_250 : canClimb 0 250 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup250]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq250]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_251 : canClimb 0 251 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup251]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq251]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_252 : canClimb 0 252 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup252]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq252]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_253 : canClimb 0 253 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup253]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq253]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_254 : canClimb 0 254 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup254]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq254]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_255 : canClimb 0 255 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup255]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq255]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_256 : canClimb 0 256 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup256]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq256]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_257 : canClimb 0 257 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup257]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq257]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_258 : canClimb 0 258 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup258]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq258]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_259 : canClimb 0 259 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup259]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq259]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_260 : canClimb 0 260 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup260]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq260]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_261 : canClimb 0 261 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup261]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq261]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_262 : canClimb 0 262 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup262]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq262]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_263 : canClimb 0 263 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup263]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq263]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_264 : canClimb 0 264 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup264]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq264]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_265 : canClimb 0 265 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup265]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq265]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem canClimb_0_528 : canClimb 0 528 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup528]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq528]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_534 : canClimb 0 534 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup534]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq534]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_547 : canClimb 0 547 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup547]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq547]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_571 : canClimb 0 571 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup571]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq571]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_585 : canClimb 0 585 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup585]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq585]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_586 : canClimb 0 586 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup586]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq586]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_591 : canClimb 0 591 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup591]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq591]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_597 : canClimb 0 597 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup597]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq597]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_0_599 : canClimb 0 599 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup000, nestingLookup599]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq000 nestingEntries_eq599]
  rw [nestingEntries_zero, functionNestedCheck_zero]
  decide

theorem canClimb_2_125 : canClimb 2 125 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup002, nestingLookup125]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq002 nestingEntries_eq125]
  decide

theorem canClimb_2_126 : canClimb 2 126 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup002, nestingLookup126]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq002 nestingEntries_eq126]
  decide

theorem canClimb_2_270 : canClimb 2 270 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup002, nestingLookup270]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq002 nestingEntries_eq270]
  decide

theorem canClimb_2_272 : canClimb 2 272 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup002, nestingLookup272]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq002 nestingEntries_eq272]
  decide

theorem canClimb_2_507 : canClimb 2 507 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup002, nestingLookup507]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq002 nestingEntries_eq507]
  decide

theorem canClimb_2_536 : canClimb 2 536 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup002, nestingLookup536]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq002 nestingEntries_eq536]
  decide

theorem canClimb_3_212 : canClimb 3 212 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup003, nestingLookup212]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq003 nestingEntries_eq212]
  decide

theorem canClimb_3_213 : canClimb 3 213 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup003, nestingLookup213]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq003 nestingEntries_eq213]
  decide

theorem canClimb_3_214 : canClimb 3 214 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup003, nestingLookup214]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq003 nestingEntries_eq214]
  decide

theorem canClimb_4_230 : canClimb 4 230 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup004, nestingLookup230]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq004 nestingEntries_eq230]
  decide

theorem canClimb_4_231 : canClimb 4 231 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup004, nestingLookup231]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq004 nestingEntries_eq231]
  decide

theorem canClimb_4_232 : canClimb 4 232 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup004, nestingLookup232]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq004 nestingEntries_eq232]
  decide

theorem canClimb_5_125 : canClimb 5 125 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup005, nestingLookup125]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq005 nestingEntries_eq125]
  decide

theorem canClimb_5_127 : canClimb 5 127 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup005, nestingLookup127]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq005 nestingEntries_eq127]
  decide

theorem canClimb_5_269 : canClimb 5 269 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup005, nestingLookup269]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq005 nestingEntries_eq269]
  decide

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem canClimb_5_275 : canClimb 5 275 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup005, nestingLookup275]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq005 nestingEntries_eq275]
  decide

theorem canClimb_5_336 : canClimb 5 336 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup005, nestingLookup336]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq005 nestingEntries_eq336]
  decide

theorem canClimb_6_230 : canClimb 6 230 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup006, nestingLookup230]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq006 nestingEntries_eq230]
  decide

theorem canClimb_6_233 : canClimb 6 233 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup006, nestingLookup233]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq006 nestingEntries_eq233]
  decide

theorem canClimb_6_234 : canClimb 6 234 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup006, nestingLookup234]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq006 nestingEntries_eq234]
  decide

theorem canClimb_7_113 : canClimb 7 113 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup007, nestingLookup113]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq007 nestingEntries_eq113]
  decide

theorem canClimb_7_114 : canClimb 7 114 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup007, nestingLookup114]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq007 nestingEntries_eq114]
  decide

theorem canClimb_7_272 : canClimb 7 272 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup007, nestingLookup272]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq007 nestingEntries_eq272]
  decide

theorem canClimb_7_273 : canClimb 7 273 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup007, nestingLookup273]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq007 nestingEntries_eq273]
  decide

theorem canClimb_7_506 : canClimb 7 506 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup007, nestingLookup506]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq007 nestingEntries_eq506]
  decide

theorem canClimb_8_113 : canClimb 8 113 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup008, nestingLookup113]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq008 nestingEntries_eq113]
  decide

theorem canClimb_8_115 : canClimb 8 115 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup008, nestingLookup115]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq008 nestingEntries_eq115]
  decide

theorem canClimb_8_268 : canClimb 8 268 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup008, nestingLookup268]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq008 nestingEntries_eq268]
  decide

theorem canClimb_8_269 : canClimb 8 269 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup008, nestingLookup269]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq008 nestingEntries_eq269]
  decide

theorem canClimb_8_328 : canClimb 8 328 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup008, nestingLookup328]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq008 nestingEntries_eq328]
  decide

theorem canClimb_9_212 : canClimb 9 212 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup009, nestingLookup212]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq009 nestingEntries_eq212]
  decide

theorem canClimb_9_215 : canClimb 9 215 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup009, nestingLookup215]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq009 nestingEntries_eq215]
  decide

theorem canClimb_9_216 : canClimb 9 216 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup009, nestingLookup216]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq009 nestingEntries_eq216]
  decide

theorem canClimb_10_248 : canClimb 10 248 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup010, nestingLookup248]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq010 nestingEntries_eq248]
  decide

theorem canClimb_10_249 : canClimb 10 249 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup010, nestingLookup249]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq010 nestingEntries_eq249]
  decide

theorem canClimb_10_250 : canClimb 10 250 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup010, nestingLookup250]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq010 nestingEntries_eq250]
  decide

theorem canClimb_11_114 : canClimb 11 114 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup011, nestingLookup114]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq011 nestingEntries_eq114]
  decide

theorem canClimb_11_115 : canClimb 11 115 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup011, nestingLookup115]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq011 nestingEntries_eq115]
  decide

theorem canClimb_11_266 : canClimb 11 266 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup011, nestingLookup266]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq011 nestingEntries_eq266]
  decide

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem canClimb_11_267 : canClimb 11 267 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup011, nestingLookup267]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq011 nestingEntries_eq267]
  decide

theorem canClimb_11_506 : canClimb 11 506 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup011, nestingLookup506]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq011 nestingEntries_eq506]
  decide

theorem canClimb_11_530 : canClimb 11 530 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup011, nestingLookup530]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq011 nestingEntries_eq530]
  decide

theorem canClimb_12_194 : canClimb 12 194 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup012, nestingLookup194]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq012 nestingEntries_eq194]
  decide

theorem canClimb_12_195 : canClimb 12 195 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup012, nestingLookup195]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq012 nestingEntries_eq195]
  decide

theorem canClimb_12_196 : canClimb 12 196 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup012, nestingLookup196]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq012 nestingEntries_eq196]
  decide

theorem canClimb_13_126 : canClimb 13 126 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup013, nestingLookup126]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq013 nestingEntries_eq126]
  decide

theorem canClimb_13_127 : canClimb 13 127 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup013, nestingLookup127]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq013 nestingEntries_eq127]
  decide

theorem canClimb_13_266 : canClimb 13 266 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup013, nestingLookup266]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq013 nestingEntries_eq266]
  decide

theorem canClimb_13_276 : canClimb 13 276 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup013, nestingLookup276]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq013 nestingEntries_eq276]
  decide

theorem canClimb_13_346 : canClimb 13 346 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup013, nestingLookup346]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq013 nestingEntries_eq346]
  decide

theorem canClimb_14_248 : canClimb 14 248 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup014, nestingLookup248]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq014 nestingEntries_eq248]
  decide

theorem canClimb_14_251 : canClimb 14 251 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup014, nestingLookup251]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq014 nestingEntries_eq251]
  decide

theorem canClimb_14_252 : canClimb 14 252 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup014, nestingLookup252]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq014 nestingEntries_eq252]
  decide

theorem canClimb_15_194 : canClimb 15 194 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup015, nestingLookup194]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq015 nestingEntries_eq194]
  decide

theorem canClimb_15_197 : canClimb 15 197 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup015, nestingLookup197]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq015 nestingEntries_eq197]
  decide

theorem canClimb_15_198 : canClimb 15 198 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup015, nestingLookup198]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq015 nestingEntries_eq198]
  decide

theorem canClimb_16_236 : canClimb 16 236 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup016, nestingLookup236]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq016 nestingEntries_eq236]
  decide

theorem canClimb_16_237 : canClimb 16 237 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup016, nestingLookup237]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq016 nestingEntries_eq237]
  decide

theorem canClimb_16_238 : canClimb 16 238 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup016, nestingLookup238]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq016 nestingEntries_eq238]
  decide

theorem canClimb_17_134 : canClimb 17 134 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup017, nestingLookup134]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq017 nestingEntries_eq134]
  decide

theorem canClimb_17_135 : canClimb 17 135 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup017, nestingLookup135]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq017 nestingEntries_eq135]
  decide

theorem canClimb_17_136 : canClimb 17 136 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup017, nestingLookup136]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq017 nestingEntries_eq136]
  decide

theorem canClimb_18_242 : canClimb 18 242 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup018, nestingLookup242]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq018 nestingEntries_eq242]
  decide

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem canClimb_18_243 : canClimb 18 243 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup018, nestingLookup243]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq018 nestingEntries_eq243]
  decide

theorem canClimb_18_244 : canClimb 18 244 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup018, nestingLookup244]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq018 nestingEntries_eq244]
  decide

theorem canClimb_19_182 : canClimb 19 182 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup019, nestingLookup182]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq019 nestingEntries_eq182]
  decide

theorem canClimb_19_183 : canClimb 19 183 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup019, nestingLookup183]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq019 nestingEntries_eq183]
  decide

theorem canClimb_19_280 : canClimb 19 280 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup019, nestingLookup280]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq019 nestingEntries_eq280]
  decide

theorem canClimb_19_321 : canClimb 19 321 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup019, nestingLookup321]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq019 nestingEntries_eq321]
  decide

theorem canClimb_19_421 : canClimb 19 421 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup019, nestingLookup421]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq019 nestingEntries_eq421]
  decide

theorem canClimb_20_242 : canClimb 20 242 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup020, nestingLookup242]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq020 nestingEntries_eq242]
  decide

theorem canClimb_20_245 : canClimb 20 245 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup020, nestingLookup245]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq020 nestingEntries_eq245]
  decide

theorem canClimb_20_246 : canClimb 20 246 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup020, nestingLookup246]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq020 nestingEntries_eq246]
  decide

theorem canClimb_21_152 : canClimb 21 152 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup021, nestingLookup152]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq021 nestingEntries_eq152]
  decide

theorem canClimb_21_153 : canClimb 21 153 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup021, nestingLookup153]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq021 nestingEntries_eq153]
  decide

theorem canClimb_21_154 : canClimb 21 154 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup021, nestingLookup154]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq021 nestingEntries_eq154]
  decide

theorem canClimb_21_508 : canClimb 21 508 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup021, nestingLookup508]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq021 nestingEntries_eq508]
  decide

theorem canClimb_22_236 : canClimb 22 236 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup022, nestingLookup236]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq022 nestingEntries_eq236]
  decide

theorem canClimb_22_239 : canClimb 22 239 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup022, nestingLookup239]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq022 nestingEntries_eq239]
  decide

theorem canClimb_22_240 : canClimb 22 240 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup022, nestingLookup240]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq022 nestingEntries_eq240]
  decide

theorem canClimb_23_164 : canClimb 23 164 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup023, nestingLookup164]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq023 nestingEntries_eq164]
  decide

theorem canClimb_23_165 : canClimb 23 165 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup023, nestingLookup165]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq023 nestingEntries_eq165]
  decide

theorem canClimb_23_166 : canClimb 23 166 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup023, nestingLookup166]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq023 nestingEntries_eq166]
  decide

theorem canClimb_24_182 : canClimb 24 182 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup024, nestingLookup182]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq024 nestingEntries_eq182]
  decide

theorem canClimb_24_184 : canClimb 24 184 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup024, nestingLookup184]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq024 nestingEntries_eq184]
  decide

theorem canClimb_24_293 : canClimb 24 293 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup024, nestingLookup293]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq024 nestingEntries_eq293]
  decide

theorem canClimb_24_303 : canClimb 24 303 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup024, nestingLookup303]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq024 nestingEntries_eq303]
  decide

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem canClimb_24_509 : canClimb 24 509 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup024, nestingLookup509]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq024 nestingEntries_eq509]
  decide

theorem canClimb_25_134 : canClimb 25 134 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup025, nestingLookup134]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq025 nestingEntries_eq134]
  decide

theorem canClimb_25_137 : canClimb 25 137 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup025, nestingLookup137]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq025 nestingEntries_eq137]
  decide

theorem canClimb_25_138 : canClimb 25 138 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup025, nestingLookup138]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq025 nestingEntries_eq138]
  decide

theorem canClimb_26_218 : canClimb 26 218 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup026, nestingLookup218]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq026 nestingEntries_eq218]
  decide

theorem canClimb_26_219 : canClimb 26 219 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup026, nestingLookup219]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq026 nestingEntries_eq219]
  decide

theorem canClimb_26_220 : canClimb 26 220 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup026, nestingLookup220]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq026 nestingEntries_eq220]
  decide

theorem canClimb_27_224 : canClimb 27 224 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup027, nestingLookup224]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq027 nestingEntries_eq224]
  decide

theorem canClimb_27_225 : canClimb 27 225 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup027, nestingLookup225]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq027 nestingEntries_eq225]
  decide

theorem canClimb_27_226 : canClimb 27 226 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup027, nestingLookup226]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq027 nestingEntries_eq226]
  decide

theorem canClimb_28_164 : canClimb 28 164 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup028, nestingLookup164]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq028 nestingEntries_eq164]
  decide

theorem canClimb_28_167 : canClimb 28 167 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup028, nestingLookup167]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq028 nestingEntries_eq167]
  decide

theorem canClimb_28_168 : canClimb 28 168 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup028, nestingLookup168]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq028 nestingEntries_eq168]
  decide

theorem canClimb_29_152 : canClimb 29 152 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup029, nestingLookup152]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq029 nestingEntries_eq152]
  decide

theorem canClimb_29_155 : canClimb 29 155 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup029, nestingLookup155]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq029 nestingEntries_eq155]
  decide

theorem canClimb_29_156 : canClimb 29 156 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup029, nestingLookup156]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq029 nestingEntries_eq156]
  decide

theorem canClimb_29_508 : canClimb 29 508 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup029, nestingLookup508]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq029 nestingEntries_eq508]
  decide

theorem canClimb_30_224 : canClimb 30 224 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup030, nestingLookup224]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq030 nestingEntries_eq224]
  decide

theorem canClimb_30_227 : canClimb 30 227 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup030, nestingLookup227]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq030 nestingEntries_eq227]
  decide

theorem canClimb_30_228 : canClimb 30 228 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup030, nestingLookup228]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq030 nestingEntries_eq228]
  decide

theorem canClimb_31_218 : canClimb 31 218 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup031, nestingLookup218]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq031 nestingEntries_eq218]
  decide

theorem canClimb_31_221 : canClimb 31 221 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup031, nestingLookup221]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq031 nestingEntries_eq221]
  decide

theorem canClimb_31_222 : canClimb 31 222 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup031, nestingLookup222]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq031 nestingEntries_eq222]
  decide

theorem canClimb_32_140 : canClimb 32 140 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup032, nestingLookup140]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq032 nestingEntries_eq140]
  decide

end CSL.Construction.PhysicalFramePaths


