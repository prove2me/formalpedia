-- Prove2me | Definitions.Def_CSL_Generated_FiniteCircuit_FramePathChecks_Paths_Batch00
-- name    : CSL_Generated_FiniteCircuit_FramePathChecks_Paths_Batch00
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T15:42:32.328543+00:00
-- url     : https://prove2.me/theorems/cea415b2-02ca-4219-bb38-31d3c390c556
-- title:
--   Coded sorting library: Generated / FiniteCircuit / FramePathChecks / Paths / Batch00
-- statement:
--   Module `CodedSorting.Generated.FiniteCircuit.FramePathChecks.Paths.Batch00` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   Generated physical-frame checks. Uncompiled until a build record exists.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Generated.FiniteCircuit.FramePathChecks.Paths.Batch00

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Generated_FiniteCircuit_FramePathChecks_Nesting_Batch00
import Definitions.Def_CSL_Generated_FiniteCircuit_FramePathChecks_Nesting_Batch01
import Definitions.Def_CSL_Generated_FiniteCircuit_FramePathChecks_Nesting_Batch02
import Definitions.Def_CSL_Generated_FiniteCircuit_FramePathChecks_Nesting_Batch03
import Definitions.Def_CSL_Generated_FiniteCircuit_FramePathChecks_Nesting_Batch04
import Definitions.Def_CSL_Generated_FiniteCircuit_FramePathChecks_Nesting_Batch05
import Definitions.Def_CSL_Generated_FiniteCircuit_FramePathChecks_Nesting_Batch06
import Definitions.Def_CSL_Generated_FiniteCircuit_FramePathChecks_VisitNumbers_Batch00
import Definitions.Def_CSL_Generated_FiniteCircuit_FramePathChecks_VisitNumbers_Bridge

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

attribute [local irreducible] canClimb
private theorem actualVisits000 : eventVisits 0 forwardEvents = [2, 2, 2, 2, 2, 507, 507, 507, 507, 507, 507, 326, 531, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits000
private theorem actualStart000 : startFrames[0]! = 2 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd000 : finalFrames[0]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid000 : forwardPathValid 0 = true := by
  rw [forwardPathValid, actualVisits000, actualStart000, actualEnd000]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_2_507, canClimb_326_531, canClimb_507_326, canClimb_531_1, Bool.true_and]

private theorem actualVisits001 : eventVisits 1 forwardEvents = [3, 3, 212, 212, 522, 522, 522, 522, 522, 522, 472, 634, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits001
private theorem actualStart001 : startFrames[1]! = 3 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd001 : finalFrames[1]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid001 : forwardPathValid 1 = true := by
  rw [forwardPathValid, actualVisits001, actualStart001, actualEnd001]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_3_212, canClimb_212_522, canClimb_472_634, canClimb_522_472, canClimb_634_1, Bool.true_and]

private theorem actualVisits002 : eventVisits 2 forwardEvents = [4, 4, 231, 231, 523, 523, 523, 523, 523, 523, 523, 523, 452, 532, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits002
private theorem actualStart002 : startFrames[2]! = 4 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd002 : finalFrames[2]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid002 : forwardPathValid 2 = true := by
  rw [forwardPathValid, actualVisits002, actualStart002, actualEnd002]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_4_231, canClimb_231_523, canClimb_452_532, canClimb_523_452, canClimb_532_1, Bool.true_and]

private theorem actualVisits003 : eventVisits 3 forwardEvents = [5, 5, 127, 127, 507, 507, 507, 507, 507, 507, 507, 507, 337, 579, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits003
private theorem actualStart003 : startFrames[3]! = 5 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd003 : finalFrames[3]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid003 : forwardPathValid 3 = true := by
  rw [forwardPathValid, actualVisits003, actualStart003, actualEnd003]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_5_127, canClimb_127_507, canClimb_337_579, canClimb_507_337, canClimb_579_1, Bool.true_and]

private theorem actualVisits004 : eventVisits 4 forwardEvents = [6, 6, 230, 230, 523, 523, 523, 523, 457, 633, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits004
private theorem actualStart004 : startFrames[4]! = 6 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd004 : finalFrames[4]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid004 : forwardPathValid 4 = true := by
  rw [forwardPathValid, actualVisits004, actualStart004, actualEnd004]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_6_230, canClimb_230_523, canClimb_457_633, canClimb_523_457, canClimb_633_1, Bool.true_and]

private theorem actualVisits005 : eventVisits 5 forwardEvents = [7, 7, 114, 114, 506, 506, 506, 506, 344, 528, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits005
private theorem actualStart005 : startFrames[5]! = 7 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd005 : finalFrames[5]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid005 : forwardPathValid 5 = true := by
  rw [forwardPathValid, actualVisits005, actualStart005, actualEnd005]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_7_114, canClimb_114_506, canClimb_344_528, canClimb_506_344, canClimb_528_1, Bool.true_and]

private theorem actualVisits006 : eventVisits 6 forwardEvents = [8, 8, 8, 113, 506, 506, 506, 506, 506, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits006
private theorem actualStart006 : startFrames[6]! = 8 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd006 : finalFrames[6]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid006 : forwardPathValid 6 = true := by
  rw [forwardPathValid, actualVisits006, actualStart006, actualEnd006]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_8_113, canClimb_113_506, canClimb_506_1, Bool.true_and]

private theorem actualVisits007 : eventVisits 7 forwardEvents = [9, 9, 215, 215, 522, 522, 522, 522, 522, 522, 522, 522, 473, 628, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits007
private theorem actualStart007 : startFrames[7]! = 9 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd007 : finalFrames[7]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid007 : forwardPathValid 7 = true := by
  rw [forwardPathValid, actualVisits007, actualStart007, actualEnd007]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_9_215, canClimb_215_522, canClimb_473_628, canClimb_522_473, canClimb_628_1, Bool.true_and]

theorem forwardPathBlock000 (f : Nat) (hl : 0 ≤ f) (hu : f < 8) : forwardPathValid f = true := by
  have hs : f = 0 ∨ f = 1 ∨ f = 2 ∨ f = 3 ∨ f = 4 ∨ f = 5 ∨ f = 6 ∨ f = 7 := by omega
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact forwardPathValid000
  · exact forwardPathValid001
  · exact forwardPathValid002
  · exact forwardPathValid003
  · exact forwardPathValid004
  · exact forwardPathValid005
  · exact forwardPathValid006
  · exact forwardPathValid007

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

attribute [local irreducible] canClimb
private theorem actualVisits008 : eventVisits 8 forwardEvents = [10, 10, 249, 249, 524, 524, 524, 524, 524, 524, 436, 632, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits008
private theorem actualStart008 : startFrames[8]! = 10 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd008 : finalFrames[8]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid008 : forwardPathValid 8 = true := by
  rw [forwardPathValid, actualVisits008, actualStart008, actualEnd008]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_10_249, canClimb_249_524, canClimb_436_632, canClimb_524_436, canClimb_632_1, Bool.true_and]

private theorem actualVisits009 : eventVisits 9 forwardEvents = [11, 11, 11, 11, 506, 506, 506, 506, 345, 525, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits009
private theorem actualStart009 : startFrames[9]! = 11 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd009 : finalFrames[9]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid009 : forwardPathValid 9 = true := by
  rw [forwardPathValid, actualVisits009, actualStart009, actualEnd009]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_11_506, canClimb_345_525, canClimb_506_345, canClimb_525_1, Bool.true_and]

private theorem actualVisits010 : eventVisits 10 forwardEvents = [12, 12, 195, 195, 521, 521, 521, 521, 521, 521, 521, 521, 493, 635, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits010
private theorem actualStart010 : startFrames[10]! = 12 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd010 : finalFrames[10]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid010 : forwardPathValid 10 = true := by
  rw [forwardPathValid, actualVisits010, actualStart010, actualEnd010]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_12_195, canClimb_195_521, canClimb_493_635, canClimb_521_493, canClimb_635_1, Bool.true_and]

private theorem actualVisits011 : eventVisits 11 forwardEvents = [13, 13, 13, 126, 507, 507, 507, 507, 507, 507, 338, 572, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits011
private theorem actualStart011 : startFrames[11]! = 13 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd011 : finalFrames[11]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid011 : forwardPathValid 11 = true := by
  rw [forwardPathValid, actualVisits011, actualStart011, actualEnd011]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_13_126, canClimb_126_507, canClimb_338_572, canClimb_507_338, canClimb_572_1, Bool.true_and]

private theorem actualVisits012 : eventVisits 12 forwardEvents = [14, 14, 252, 252, 524, 524, 524, 442, 610, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits012
private theorem actualStart012 : startFrames[12]! = 14 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd012 : finalFrames[12]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid012 : forwardPathValid 12 = true := by
  rw [forwardPathValid, actualVisits012, actualStart012, actualEnd012]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_14_252, canClimb_252_524, canClimb_442_610, canClimb_524_442, canClimb_610_1, Bool.true_and]

private theorem actualVisits013 : eventVisits 13 forwardEvents = [15, 15, 194, 194, 521, 521, 521, 521, 521, 521, 521, 503, 598, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits013
private theorem actualStart013 : startFrames[13]! = 15 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd013 : finalFrames[13]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid013 : forwardPathValid 13 = true := by
  rw [forwardPathValid, actualVisits013, actualStart013, actualEnd013]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_15_194, canClimb_194_521, canClimb_503_598, canClimb_521_503, canClimb_598_1, Bool.true_and]

private theorem actualVisits014 : eventVisits 14 forwardEvents = [16, 16, 236, 236, 523, 523, 523, 523, 523, 523, 468, 625, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits014
private theorem actualStart014 : startFrames[14]! = 16 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd014 : finalFrames[14]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid014 : forwardPathValid 14 = true := by
  rw [forwardPathValid, actualVisits014, actualStart014, actualEnd014]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_16_236, canClimb_236_523, canClimb_468_625, canClimb_523_468, canClimb_625_1, Bool.true_and]

private theorem actualVisits015 : eventVisits 15 forwardEvents = [17, 17, 134, 134, 519, 519, 519, 519, 519, 519, 519, 519, 519, 519, 519, 519, 413, 580, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits015
private theorem actualStart015 : startFrames[15]! = 17 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd015 : finalFrames[15]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid015 : forwardPathValid 15 = true := by
  rw [forwardPathValid, actualVisits015, actualStart015, actualEnd015]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_17_134, canClimb_134_519, canClimb_413_580, canClimb_519_413, canClimb_580_1, Bool.true_and]

theorem forwardPathBlock001 (f : Nat) (hl : 8 ≤ f) (hu : f < 16) : forwardPathValid f = true := by
  have hs : f = 8 ∨ f = 9 ∨ f = 10 ∨ f = 11 ∨ f = 12 ∨ f = 13 ∨ f = 14 ∨ f = 15 := by omega
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact forwardPathValid008
  · exact forwardPathValid009
  · exact forwardPathValid010
  · exact forwardPathValid011
  · exact forwardPathValid012
  · exact forwardPathValid013
  · exact forwardPathValid014
  · exact forwardPathValid015

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

attribute [local irreducible] canClimb
private theorem actualVisits016 : eventVisits 16 forwardEvents = [18, 18, 243, 243, 523, 523, 523, 523, 523, 462, 554, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits016
private theorem actualStart016 : startFrames[16]! = 18 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd016 : finalFrames[16]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid016 : forwardPathValid 16 = true := by
  rw [forwardPathValid, actualVisits016, actualStart016, actualEnd016]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_18_243, canClimb_243_523, canClimb_462_554, canClimb_523_462, canClimb_554_1, Bool.true_and]

private theorem actualVisits017 : eventVisits 17 forwardEvents = [19, 19, 19, 183, 509, 509, 509, 509, 509, 509, 509, 509, 509, 395, 582, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits017
private theorem actualStart017 : startFrames[17]! = 19 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd017 : finalFrames[17]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid017 : forwardPathValid 17 = true := by
  rw [forwardPathValid, actualVisits017, actualStart017, actualEnd017]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_19_183, canClimb_183_509, canClimb_395_582, canClimb_509_395, canClimb_582_1, Bool.true_and]

private theorem actualVisits018 : eventVisits 18 forwardEvents = [20, 20, 242, 242, 523, 523, 523, 523, 523, 523, 523, 523, 460, 626, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits018
private theorem actualStart018 : startFrames[18]! = 20 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd018 : finalFrames[18]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid018 : forwardPathValid 18 = true := by
  rw [forwardPathValid, actualVisits018, actualStart018, actualEnd018]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_20_242, canClimb_242_523, canClimb_460_626, canClimb_523_460, canClimb_626_1, Bool.true_and]

private theorem actualVisits019 : eventVisits 19 forwardEvents = [21, 21, 21, 152, 152, 508, 508, 508, 508, 508, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits019
private theorem actualStart019 : startFrames[19]! = 21 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd019 : finalFrames[19]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid019 : forwardPathValid 19 = true := by
  rw [forwardPathValid, actualVisits019, actualStart019, actualEnd019]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_21_152, canClimb_152_508, canClimb_508_1, Bool.true_and]

private theorem actualVisits020 : eventVisits 20 forwardEvents = [22, 22, 240, 240, 523, 523, 523, 523, 523, 523, 523, 523, 523, 523, 523, 523, 523, 523, 453, 631, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits020
private theorem actualStart020 : startFrames[20]! = 22 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd020 : finalFrames[20]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid020 : forwardPathValid 20 = true := by
  rw [forwardPathValid, actualVisits020, actualStart020, actualEnd020]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_22_240, canClimb_240_523, canClimb_453_631, canClimb_523_453, canClimb_631_1, Bool.true_and]

private theorem actualVisits021 : eventVisits 21 forwardEvents = [23, 23, 165, 165, 520, 520, 520, 520, 520, 520, 363, 540, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits021
private theorem actualStart021 : startFrames[21]! = 23 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd021 : finalFrames[21]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid021 : forwardPathValid 21 = true := by
  rw [forwardPathValid, actualVisits021, actualStart021, actualEnd021]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_23_165, canClimb_165_520, canClimb_363_540, canClimb_520_363, canClimb_540_1, Bool.true_and]

private theorem actualVisits022 : eventVisits 22 forwardEvents = [24, 24, 182, 182, 509, 509, 509, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits022
private theorem actualStart022 : startFrames[22]! = 24 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd022 : finalFrames[22]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid022 : forwardPathValid 22 = true := by
  rw [forwardPathValid, actualVisits022, actualStart022, actualEnd022]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_24_182, canClimb_182_509, canClimb_509_1, Bool.true_and]

private theorem actualVisits023 : eventVisits 23 forwardEvents = [25, 25, 137, 137, 519, 519, 519, 519, 398, 551, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits023
private theorem actualStart023 : startFrames[23]! = 25 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd023 : finalFrames[23]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid023 : forwardPathValid 23 = true := by
  rw [forwardPathValid, actualVisits023, actualStart023, actualEnd023]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_25_137, canClimb_137_519, canClimb_398_551, canClimb_519_398, canClimb_551_1, Bool.true_and]

theorem forwardPathBlock002 (f : Nat) (hl : 16 ≤ f) (hu : f < 24) : forwardPathValid f = true := by
  have hs : f = 16 ∨ f = 17 ∨ f = 18 ∨ f = 19 ∨ f = 20 ∨ f = 21 ∨ f = 22 ∨ f = 23 := by omega
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact forwardPathValid016
  · exact forwardPathValid017
  · exact forwardPathValid018
  · exact forwardPathValid019
  · exact forwardPathValid020
  · exact forwardPathValid021
  · exact forwardPathValid022
  · exact forwardPathValid023

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

attribute [local irreducible] canClimb
private theorem actualVisits024 : eventVisits 24 forwardEvents = [26, 26, 220, 220, 522, 522, 522, 522, 487, 613, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits024
private theorem actualStart024 : startFrames[24]! = 26 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd024 : finalFrames[24]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid024 : forwardPathValid 24 = true := by
  rw [forwardPathValid, actualVisits024, actualStart024, actualEnd024]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_26_220, canClimb_220_522, canClimb_487_613, canClimb_522_487, canClimb_613_1, Bool.true_and]

private theorem actualVisits025 : eventVisits 25 forwardEvents = [27, 27, 226, 226, 522, 522, 522, 522, 522, 522, 474, 529, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits025
private theorem actualStart025 : startFrames[25]! = 27 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd025 : finalFrames[25]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid025 : forwardPathValid 25 = true := by
  rw [forwardPathValid, actualVisits025, actualStart025, actualEnd025]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_27_226, canClimb_226_522, canClimb_474_529, canClimb_522_474, canClimb_529_1, Bool.true_and]

private theorem actualVisits026 : eventVisits 26 forwardEvents = [28, 28, 168, 168, 520, 520, 520, 520, 520, 520, 520, 373, 600, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits026
private theorem actualStart026 : startFrames[26]! = 28 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd026 : finalFrames[26]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid026 : forwardPathValid 26 = true := by
  rw [forwardPathValid, actualVisits026, actualStart026, actualEnd026]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_28_168, canClimb_168_520, canClimb_373_600, canClimb_520_373, canClimb_600_1, Bool.true_and]

private theorem actualVisits027 : eventVisits 27 forwardEvents = [29, 29, 29, 156, 156, 508, 508, 508, 508, 425, 563, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits027
private theorem actualStart027 : startFrames[27]! = 29 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd027 : finalFrames[27]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid027 : forwardPathValid 27 = true := by
  rw [forwardPathValid, actualVisits027, actualStart027, actualEnd027]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_29_156, canClimb_156_508, canClimb_425_563, canClimb_508_425, canClimb_563_1, Bool.true_and]

private theorem actualVisits028 : eventVisits 28 forwardEvents = [30, 30, 224, 224, 522, 522, 522, 522, 522, 522, 522, 522, 522, 522, 522, 522, 522, 522, 522, 522, 522, 522, 522, 522, 482, 543, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits028
private theorem actualStart028 : startFrames[28]! = 30 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd028 : finalFrames[28]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid028 : forwardPathValid 28 = true := by
  rw [forwardPathValid, actualVisits028, actualStart028, actualEnd028]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_30_224, canClimb_224_522, canClimb_482_543, canClimb_522_482, canClimb_543_1, Bool.true_and]

private theorem actualVisits029 : eventVisits 29 forwardEvents = [31, 31, 222, 222, 522, 522, 522, 522, 522, 522, 522, 522, 522, 479, 615, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits029
private theorem actualStart029 : startFrames[29]! = 31 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd029 : finalFrames[29]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid029 : forwardPathValid 29 = true := by
  rw [forwardPathValid, actualVisits029, actualStart029, actualEnd029]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_31_222, canClimb_222_522, canClimb_479_615, canClimb_522_479, canClimb_615_1, Bool.true_and]

private theorem actualVisits030 : eventVisits 30 forwardEvents = [32, 32, 140, 140, 519, 519, 519, 519, 519, 519, 415, 589, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits030
private theorem actualStart030 : startFrames[30]! = 32 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd030 : finalFrames[30]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid030 : forwardPathValid 30 = true := by
  rw [forwardPathValid, actualVisits030, actualStart030, actualEnd030]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_32_140, canClimb_140_519, canClimb_415_589, canClimb_519_415, canClimb_589_1, Bool.true_and]

private theorem actualVisits031 : eventVisits 31 forwardEvents = [33, 33, 256, 256, 524, 524, 524, 524, 524, 524, 524, 524, 434, 535, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits031
private theorem actualStart031 : startFrames[31]! = 33 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd031 : finalFrames[31]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid031 : forwardPathValid 31 = true := by
  rw [forwardPathValid, actualVisits031, actualStart031, actualEnd031]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_33_256, canClimb_256_524, canClimb_434_535, canClimb_524_434, canClimb_535_1, Bool.true_and]

theorem forwardPathBlock003 (f : Nat) (hl : 24 ≤ f) (hu : f < 32) : forwardPathValid f = true := by
  have hs : f = 24 ∨ f = 25 ∨ f = 26 ∨ f = 27 ∨ f = 28 ∨ f = 29 ∨ f = 30 ∨ f = 31 := by omega
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact forwardPathValid024
  · exact forwardPathValid025
  · exact forwardPathValid026
  · exact forwardPathValid027
  · exact forwardPathValid028
  · exact forwardPathValid029
  · exact forwardPathValid030
  · exact forwardPathValid031

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

attribute [local irreducible] canClimb
private theorem actualVisits032 : eventVisits 32 forwardEvents = [34, 34, 202, 202, 521, 521, 521, 521, 504, 570, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits032
private theorem actualStart032 : startFrames[32]! = 34 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd032 : finalFrames[32]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid032 : forwardPathValid 32 = true := by
  rw [forwardPathValid, actualVisits032, actualStart032, actualEnd032]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_34_202, canClimb_202_521, canClimb_504_570, canClimb_521_504, canClimb_570_1, Bool.true_and]

private theorem actualVisits033 : eventVisits 33 forwardEvents = [35, 35, 185, 185, 509, 509, 509, 509, 509, 509, 509, 383, 614, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits033
private theorem actualStart033 : startFrames[33]! = 35 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd033 : finalFrames[33]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid033 : forwardPathValid 33 = true := by
  rw [forwardPathValid, actualVisits033, actualStart033, actualEnd033]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_35_185, canClimb_185_509, canClimb_383_614, canClimb_509_383, canClimb_614_1, Bool.true_and]

private theorem actualVisits034 : eventVisits 34 forwardEvents = [36, 36, 204, 204, 521, 521, 521, 521, 521, 521, 521, 521, 488, 533, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits034
private theorem actualStart034 : startFrames[34]! = 36 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd034 : finalFrames[34]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid034 : forwardPathValid 34 = true := by
  rw [forwardPathValid, actualVisits034, actualStart034, actualEnd034]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_36_204, canClimb_204_521, canClimb_488_533, canClimb_521_488, canClimb_533_1, Bool.true_and]

private theorem actualVisits035 : eventVisits 35 forwardEvents = [37, 37, 159, 159, 508, 508, 508, 508, 508, 508, 508, 419, 547, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits035
private theorem actualStart035 : startFrames[35]! = 37 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd035 : finalFrames[35]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid035 : forwardPathValid 35 = true := by
  rw [forwardPathValid, actualVisits035, actualStart035, actualEnd035]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_37_159, canClimb_159_508, canClimb_419_547, canClimb_508_419, canClimb_547_1, Bool.true_and]

private theorem actualVisits036 : eventVisits 36 forwardEvents = [38, 38, 172, 172, 520, 520, 520, 520, 520, 520, 369, 555, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits036
private theorem actualStart036 : startFrames[36]! = 38 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd036 : finalFrames[36]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid036 : forwardPathValid 36 = true := by
  rw [forwardPathValid, actualVisits036, actualStart036, actualEnd036]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_38_172, canClimb_172_520, canClimb_369_555, canClimb_520_369, canClimb_555_1, Bool.true_and]

private theorem actualVisits037 : eventVisits 37 forwardEvents = [39, 39, 254, 254, 524, 524, 524, 524, 524, 450, 604, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits037
private theorem actualStart037 : startFrames[37]! = 39 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd037 : finalFrames[37]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid037 : forwardPathValid 37 = true := by
  rw [forwardPathValid, actualVisits037, actualStart037, actualEnd037]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_39_254, canClimb_254_524, canClimb_450_604, canClimb_524_450, canClimb_604_1, Bool.true_and]

private theorem actualVisits038 : eventVisits 38 forwardEvents = [40, 40, 40, 188, 188, 509, 509, 509, 509, 509, 389, 568, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits038
private theorem actualStart038 : startFrames[38]! = 40 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd038 : finalFrames[38]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid038 : forwardPathValid 38 = true := by
  rw [forwardPathValid, actualVisits038, actualStart038, actualEnd038]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_40_188, canClimb_188_509, canClimb_389_568, canClimb_509_389, canClimb_568_1, Bool.true_and]

private theorem actualVisits039 : eventVisits 39 forwardEvents = [41, 41, 207, 207, 521, 521, 521, 521, 492, 537, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits039
private theorem actualStart039 : startFrames[39]! = 41 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd039 : finalFrames[39]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid039 : forwardPathValid 39 = true := by
  rw [forwardPathValid, actualVisits039, actualStart039, actualEnd039]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_41_207, canClimb_207_521, canClimb_492_537, canClimb_521_492, canClimb_537_1, Bool.true_and]

theorem forwardPathBlock004 (f : Nat) (hl : 32 ≤ f) (hu : f < 40) : forwardPathValid f = true := by
  have hs : f = 32 ∨ f = 33 ∨ f = 34 ∨ f = 35 ∨ f = 36 ∨ f = 37 ∨ f = 38 ∨ f = 39 := by omega
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact forwardPathValid032
  · exact forwardPathValid033
  · exact forwardPathValid034
  · exact forwardPathValid035
  · exact forwardPathValid036
  · exact forwardPathValid037
  · exact forwardPathValid038
  · exact forwardPathValid039

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

attribute [local irreducible] canClimb
private theorem actualVisits040 : eventVisits 40 forwardEvents = [42, 42, 260, 260, 524, 524, 524, 524, 524, 524, 524, 524, 524, 524, 524, 524, 435, 629, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits040
private theorem actualStart040 : startFrames[40]! = 42 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd040 : finalFrames[40]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid040 : forwardPathValid 40 = true := by
  rw [forwardPathValid, actualVisits040, actualStart040, actualEnd040]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_42_260, canClimb_260_524, canClimb_435_629, canClimb_524_435, canClimb_629_1, Bool.true_and]

private theorem actualVisits041 : eventVisits 41 forwardEvents = [43, 43, 143, 143, 519, 519, 519, 519, 519, 519, 404, 569, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits041
private theorem actualStart041 : startFrames[41]! = 43 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd041 : finalFrames[41]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid041 : forwardPathValid 41 = true := by
  rw [forwardPathValid, actualVisits041, actualStart041, actualEnd041]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_43_143, canClimb_143_519, canClimb_404_569, canClimb_519_404, canClimb_569_1, Bool.true_and]

private theorem actualVisits042 : eventVisits 42 forwardEvents = [44, 44, 206, 206, 521, 521, 521, 521, 521, 521, 521, 496, 556, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits042
private theorem actualStart042 : startFrames[42]! = 44 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd042 : finalFrames[42]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid042 : forwardPathValid 42 = true := by
  rw [forwardPathValid, actualVisits042, actualStart042, actualEnd042]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_44_206, canClimb_206_521, canClimb_496_556, canClimb_521_496, canClimb_556_1, Bool.true_and]

private theorem actualVisits043 : eventVisits 43 forwardEvents = [45, 45, 45, 158, 508, 508, 508, 508, 508, 508, 508, 508, 508, 422, 558, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits043
private theorem actualStart043 : startFrames[43]! = 45 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd043 : finalFrames[43]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid043 : forwardPathValid 43 = true := by
  rw [forwardPathValid, actualVisits043, actualStart043, actualEnd043]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_45_158, canClimb_158_508, canClimb_422_558, canClimb_508_422, canClimb_558_1, Bool.true_and]

private theorem actualVisits044 : eventVisits 44 forwardEvents = [46, 46, 170, 170, 520, 520, 520, 520, 520, 520, 520, 520, 520, 520, 520, 520, 520, 520, 370, 607, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits044
private theorem actualStart044 : startFrames[44]! = 46 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd044 : finalFrames[44]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid044 : forwardPathValid 44 = true := by
  rw [forwardPathValid, actualVisits044, actualStart044, actualEnd044]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_46_170, canClimb_170_520, canClimb_370_607, canClimb_520_370, canClimb_607_1, Bool.true_and]

private theorem actualVisits045 : eventVisits 45 forwardEvents = [47, 47, 263, 263, 524, 524, 440, 557, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits045
private theorem actualStart045 : startFrames[45]! = 47 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd045 : finalFrames[45]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid045 : forwardPathValid 45 = true := by
  rw [forwardPathValid, actualVisits045, actualStart045, actualEnd045]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_47_263, canClimb_263_524, canClimb_440_557, canClimb_524_440, canClimb_557_1, Bool.true_and]

private theorem actualVisits046 : eventVisits 46 forwardEvents = [48, 48, 48, 48, 506, 506, 506, 506, 506, 354, 587, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits046
private theorem actualStart046 : startFrames[46]! = 48 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd046 : finalFrames[46]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid046 : forwardPathValid 46 = true := by
  rw [forwardPathValid, actualVisits046, actualStart046, actualEnd046]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_48_506, canClimb_354_587, canClimb_506_354, canClimb_587_1, Bool.true_and]

private theorem actualVisits047 : eventVisits 47 forwardEvents = [49, 49, 49, 121, 121, 506, 506, 506, 506, 356, 586, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits047
private theorem actualStart047 : startFrames[47]! = 49 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd047 : finalFrames[47]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid047 : forwardPathValid 47 = true := by
  rw [forwardPathValid, actualVisits047, actualStart047, actualEnd047]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_49_121, canClimb_121_506, canClimb_356_586, canClimb_506_356, canClimb_586_1, Bool.true_and]

theorem forwardPathBlock005 (f : Nat) (hl : 40 ≤ f) (hu : f < 48) : forwardPathValid f = true := by
  have hs : f = 40 ∨ f = 41 ∨ f = 42 ∨ f = 43 ∨ f = 44 ∨ f = 45 ∨ f = 46 ∨ f = 47 := by omega
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact forwardPathValid040
  · exact forwardPathValid041
  · exact forwardPathValid042
  · exact forwardPathValid043
  · exact forwardPathValid044
  · exact forwardPathValid045
  · exact forwardPathValid046
  · exact forwardPathValid047

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

attribute [local irreducible] canClimb
private theorem actualVisits048 : eventVisits 48 forwardEvents = [50, 50, 119, 119, 506, 506, 506, 506, 506, 506, 347, 536, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits048
private theorem actualStart048 : startFrames[48]! = 50 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd048 : finalFrames[48]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid048 : forwardPathValid 48 = true := by
  rw [forwardPathValid, actualVisits048, actualStart048, actualEnd048]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_50_119, canClimb_119_506, canClimb_347_536, canClimb_506_347, canClimb_536_1, Bool.true_and]

private theorem actualVisits049 : eventVisits 49 forwardEvents = [51, 51, 146, 146, 519, 519, 519, 519, 519, 519, 519, 405, 561, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits049
private theorem actualStart049 : startFrames[49]! = 51 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd049 : finalFrames[49]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid049 : forwardPathValid 49 = true := by
  rw [forwardPathValid, actualVisits049, actualStart049, actualEnd049]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_51_146, canClimb_146_519, canClimb_405_561, canClimb_519_405, canClimb_561_1, Bool.true_and]

private theorem actualVisits050 : eventVisits 50 forwardEvents = [52, 52, 52, 52, 52, 509, 509, 509, 509, 397, 590, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits050
private theorem actualStart050 : startFrames[50]! = 52 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd050 : finalFrames[50]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid050 : forwardPathValid 50 = true := by
  rw [forwardPathValid, actualVisits050, actualStart050, actualEnd050]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_52_509, canClimb_397_590, canClimb_509_397, canClimb_590_1, Bool.true_and]

private theorem actualVisits051 : eventVisits 51 forwardEvents = [53, 53, 178, 178, 520, 520, 520, 520, 520, 375, 574, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits051
private theorem actualStart051 : startFrames[51]! = 53 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd051 : finalFrames[51]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid051 : forwardPathValid 51 = true := by
  rw [forwardPathValid, actualVisits051, actualStart051, actualEnd051]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_53_178, canClimb_178_520, canClimb_375_574, canClimb_520_375, canClimb_574_1, Bool.true_and]

private theorem actualVisits052 : eventVisits 52 forwardEvents = [54, 54, 54, 120, 120, 506, 506, 506, 506, 506, 506, 506, 506, 506, 506, 506, 506, 506, 506, 506, 506, 506, 358, 593, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits052
private theorem actualStart052 : startFrames[52]! = 54 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd052 : finalFrames[52]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid052 : forwardPathValid 52 = true := by
  rw [forwardPathValid, actualVisits052, actualStart052, actualEnd052]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_54_120, canClimb_120_506, canClimb_358_593, canClimb_506_358, canClimb_593_1, Bool.true_and]

private theorem actualVisits053 : eventVisits 53 forwardEvents = [55, 55, 149, 149, 519, 519, 519, 519, 519, 519, 519, 414, 596, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits053
private theorem actualStart053 : startFrames[53]! = 55 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd053 : finalFrames[53]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid053 : forwardPathValid 53 = true := by
  rw [forwardPathValid, actualVisits053, actualStart053, actualEnd053]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_55_149, canClimb_149_519, canClimb_414_596, canClimb_519_414, canClimb_596_1, Bool.true_and]

private theorem actualVisits054 : eventVisits 54 forwardEvents = [56, 56, 56, 56, 56, 506, 506, 506, 355, 597, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits054
private theorem actualStart054 : startFrames[54]! = 56 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd054 : finalFrames[54]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid054 : forwardPathValid 54 = true := by
  rw [forwardPathValid, actualVisits054, actualStart054, actualEnd054]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_56_506, canClimb_355_597, canClimb_506_355, canClimb_597_1, Bool.true_and]

private theorem actualVisits055 : eventVisits 55 forwardEvents = [57, 57, 179, 179, 520, 520, 520, 520, 520, 520, 520, 520, 520, 520, 520, 520, 520, 520, 365, 616, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits055
private theorem actualStart055 : startFrames[55]! = 57 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd055 : finalFrames[55]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid055 : forwardPathValid 55 = true := by
  rw [forwardPathValid, actualVisits055, actualStart055, actualEnd055]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_57_179, canClimb_179_520, canClimb_365_616, canClimb_520_365, canClimb_616_1, Bool.true_and]

theorem forwardPathBlock006 (f : Nat) (hl : 48 ≤ f) (hu : f < 56) : forwardPathValid f = true := by
  have hs : f = 48 ∨ f = 49 ∨ f = 50 ∨ f = 51 ∨ f = 52 ∨ f = 53 ∨ f = 54 ∨ f = 55 := by omega
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact forwardPathValid048
  · exact forwardPathValid049
  · exact forwardPathValid050
  · exact forwardPathValid051
  · exact forwardPathValid052
  · exact forwardPathValid053
  · exact forwardPathValid054
  · exact forwardPathValid055

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

attribute [local irreducible] canClimb
private theorem actualVisits056 : eventVisits 56 forwardEvents = [58, 58, 58, 118, 506, 506, 506, 506, 506, 353, 594, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits056
private theorem actualStart056 : startFrames[56]! = 58 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd056 : finalFrames[56]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid056 : forwardPathValid 56 = true := by
  rw [forwardPathValid, actualVisits056, actualStart056, actualEnd056]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_58_118, canClimb_118_506, canClimb_353_594, canClimb_506_353, canClimb_594_1, Bool.true_and]

private theorem actualVisits057 : eventVisits 57 forwardEvents = [59, 59, 59, 161, 508, 508, 508, 430, 592, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits057
private theorem actualStart057 : startFrames[57]! = 59 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd057 : finalFrames[57]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid057 : forwardPathValid 57 = true := by
  rw [forwardPathValid, actualVisits057, actualStart057, actualEnd057]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_59_161, canClimb_161_508, canClimb_430_592, canClimb_508_430, canClimb_592_1, Bool.true_and]

private theorem actualVisits058 : eventVisits 58 forwardEvents = [60, 60, 124, 124, 506, 506, 506, 360, 588, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits058
private theorem actualStart058 : startFrames[58]! = 60 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd058 : finalFrames[58]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid058 : forwardPathValid 58 = true := by
  rw [forwardPathValid, actualVisits058, actualStart058, actualEnd058]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_60_124, canClimb_124_506, canClimb_360_588, canClimb_506_360, canClimb_588_1, Bool.true_and]

private theorem actualVisits059 : eventVisits 59 forwardEvents = [61, 61, 147, 147, 519, 519, 519, 519, 519, 519, 519, 519, 519, 519, 519, 519, 519, 519, 519, 519, 402, 627, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits059
private theorem actualStart059 : startFrames[59]! = 61 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd059 : finalFrames[59]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid059 : forwardPathValid 59 = true := by
  rw [forwardPathValid, actualVisits059, actualStart059, actualEnd059]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_61_147, canClimb_147_519, canClimb_402_627, canClimb_519_402, canClimb_627_1, Bool.true_and]

private theorem actualVisits060 : eventVisits 60 forwardEvents = [62, 62, 62, 62, 509, 509, 509, 396, 591, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits060
private theorem actualStart060 : startFrames[60]! = 62 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd060 : finalFrames[60]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid060 : forwardPathValid 60 = true := by
  rw [forwardPathValid, actualVisits060, actualStart060, actualEnd060]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_62_509, canClimb_396_591, canClimb_509_396, canClimb_591_1, Bool.true_and]

private theorem actualVisits061 : eventVisits 61 forwardEvents = [63, 63, 63, 63, 507, 507, 507, 507, 507, 507, 343, 583, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits061
private theorem actualStart061 : startFrames[61]! = 63 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd061 : finalFrames[61]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid061 : forwardPathValid 61 = true := by
  rw [forwardPathValid, actualVisits061, actualStart061, actualEnd061]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_63_507, canClimb_343_583, canClimb_507_343, canClimb_583_1, Bool.true_and]

private theorem actualVisits062 : eventVisits 62 forwardEvents = [64, 64, 129, 129, 507, 507, 507, 507, 507, 507, 507, 327, 530, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits062
private theorem actualStart062 : startFrames[62]! = 64 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd062 : finalFrames[62]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid062 : forwardPathValid 62 = true := by
  rw [forwardPathValid, actualVisits062, actualStart062, actualEnd062]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_64_129, canClimb_129_507, canClimb_327_530, canClimb_507_327, canClimb_530_1, Bool.true_and]

private theorem actualVisits063 : eventVisits 63 forwardEvents = [65, 65, 131, 131, 507, 507, 507, 507, 507, 507, 507, 342, 573, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits063
private theorem actualStart063 : startFrames[63]! = 65 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd063 : finalFrames[63]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid063 : forwardPathValid 63 = true := by
  rw [forwardPathValid, actualVisits063, actualStart063, actualEnd063]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_65_131, canClimb_131_507, canClimb_342_573, canClimb_507_342, canClimb_573_1, Bool.true_and]

theorem forwardPathBlock007 (f : Nat) (hl : 56 ≤ f) (hu : f < 64) : forwardPathValid f = true := by
  have hs : f = 56 ∨ f = 57 ∨ f = 58 ∨ f = 59 ∨ f = 60 ∨ f = 61 ∨ f = 62 ∨ f = 63 := by omega
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact forwardPathValid056
  · exact forwardPathValid057
  · exact forwardPathValid058
  · exact forwardPathValid059
  · exact forwardPathValid060
  · exact forwardPathValid061
  · exact forwardPathValid062
  · exact forwardPathValid063

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

attribute [local irreducible] canClimb
private theorem actualVisits064 : eventVisits 64 forwardEvents = [66, 66, 181, 181, 520, 520, 520, 520, 379, 584, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits064
private theorem actualStart064 : startFrames[64]! = 66 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd064 : finalFrames[64]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid064 : forwardPathValid 64 = true := by
  rw [forwardPathValid, actualVisits064, actualStart064, actualEnd064]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_66_181, canClimb_181_520, canClimb_379_584, canClimb_520_379, canClimb_584_1, Bool.true_and]

private theorem actualVisits065 : eventVisits 65 forwardEvents = [67, 67, 67, 67, 508, 508, 433, 585, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits065
private theorem actualStart065 : startFrames[65]! = 67 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd065 : finalFrames[65]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid065 : forwardPathValid 65 = true := by
  rw [forwardPathValid, actualVisits065, actualStart065, actualEnd065]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_67_508, canClimb_433_585, canClimb_508_433, canClimb_585_1, Bool.true_and]

private theorem actualVisits066 : eventVisits 66 forwardEvents = [68, 68, 68, 68, 508, 508, 508, 508, 508, 508, 508, 508, 508, 508, 508, 508, 508, 417, 617, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits066
private theorem actualStart066 : startFrames[66]! = 68 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd066 : finalFrames[66]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid066 : forwardPathValid 66 = true := by
  rw [forwardPathValid, actualVisits066, actualStart066, actualEnd066]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_68_508, canClimb_417_617, canClimb_508_417, canClimb_617_1, Bool.true_and]

private theorem actualVisits067 : eventVisits 67 forwardEvents = [69, 69, 69, 192, 509, 509, 509, 509, 387, 599, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits067
private theorem actualStart067 : startFrames[67]! = 69 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd067 : finalFrames[67]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid067 : forwardPathValid 67 = true := by
  rw [forwardPathValid, actualVisits067, actualStart067, actualEnd067]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_69_192, canClimb_192_509, canClimb_387_599, canClimb_509_387, canClimb_599_1, Bool.true_and]

private theorem actualVisits068 : eventVisits 68 forwardEvents = [70, 70, 70, 133, 507, 507, 507, 507, 507, 507, 507, 507, 507, 507, 507, 507, 507, 334, 581, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits068
private theorem actualStart068 : startFrames[68]! = 70 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd068 : finalFrames[68]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid068 : forwardPathValid 68 = true := by
  rw [forwardPathValid, actualVisits068, actualStart068, actualEnd068]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_70_133, canClimb_133_507, canClimb_334_581, canClimb_507_334, canClimb_581_1, Bool.true_and]

private theorem actualVisits069 : eventVisits 69 forwardEvents = [71, 71, 71, 128, 507, 507, 507, 507, 507, 507, 507, 507, 507, 507, 507, 329, 534, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits069
private theorem actualStart069 : startFrames[69]! = 71 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd069 : finalFrames[69]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid069 : forwardPathValid 69 = true := by
  rw [forwardPathValid, actualVisits069, actualStart069, actualEnd069]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_71_128, canClimb_128_507, canClimb_329_534, canClimb_507_329, canClimb_534_1, Bool.true_and]

private theorem actualVisits070 : eventVisits 70 forwardEvents = [72, 72, 150, 150, 519, 519, 519, 519, 519, 519, 409, 609, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits070
private theorem actualStart070 : startFrames[70]! = 72 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd070 : finalFrames[70]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid070 : forwardPathValid 70 = true := by
  rw [forwardPathValid, actualVisits070, actualStart070, actualEnd070]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_72_150, canClimb_150_519, canClimb_409_609, canClimb_519_409, canClimb_609_1, Bool.true_and]

private theorem actualVisits071 : eventVisits 71 forwardEvents = [73, 73, 180, 180, 520, 520, 520, 520, 377, 578, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits071
private theorem actualStart071 : startFrames[71]! = 73 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd071 : finalFrames[71]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid071 : forwardPathValid 71 = true := by
  rw [forwardPathValid, actualVisits071, actualStart071, actualEnd071]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_73_180, canClimb_180_520, canClimb_377_578, canClimb_520_377, canClimb_578_1, Bool.true_and]

theorem forwardPathBlock008 (f : Nat) (hl : 64 ≤ f) (hu : f < 72) : forwardPathValid f = true := by
  have hs : f = 64 ∨ f = 65 ∨ f = 66 ∨ f = 67 ∨ f = 68 ∨ f = 69 ∨ f = 70 ∨ f = 71 := by omega
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact forwardPathValid064
  · exact forwardPathValid065
  · exact forwardPathValid066
  · exact forwardPathValid067
  · exact forwardPathValid068
  · exact forwardPathValid069
  · exact forwardPathValid070
  · exact forwardPathValid071

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

attribute [local irreducible] canClimb
private theorem actualVisits072 : eventVisits 72 forwardEvents = [74, 74, 74, 74, 507, 507, 507, 507, 507, 333, 571, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits072
private theorem actualStart072 : startFrames[72]! = 74 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd072 : finalFrames[72]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid072 : forwardPathValid 72 = true := by
  rw [forwardPathValid, actualVisits072, actualStart072, actualEnd072]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_74_507, canClimb_333_571, canClimb_507_333, canClimb_571_1, Bool.true_and]

private theorem actualVisits073 : eventVisits 73 forwardEvents = [75, 75, 265, 265, 524, 524, 524, 524, 524, 524, 437, 538, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits073
private theorem actualStart073 : startFrames[73]! = 75 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd073 : finalFrames[73]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid073 : forwardPathValid 73 = true := by
  rw [forwardPathValid, actualVisits073, actualStart073, actualEnd073]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_75_265, canClimb_265_524, canClimb_437_538, canClimb_524_437, canClimb_538_1, Bool.true_and]

private theorem actualVisits074 : eventVisits 74 forwardEvents = [76, 76, 160, 160, 508, 508, 508, 508, 508, 508, 508, 508, 423, 602, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits074
private theorem actualStart074 : startFrames[74]! = 76 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd074 : finalFrames[74]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid074 : forwardPathValid 74 = true := by
  rw [forwardPathValid, actualVisits074, actualStart074, actualEnd074]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_76_160, canClimb_160_508, canClimb_423_602, canClimb_508_423, canClimb_602_1, Bool.true_and]

private theorem actualVisits075 : eventVisits 75 forwardEvents = [77, 77, 145, 145, 519, 519, 519, 519, 519, 519, 519, 519, 407, 605, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits075
private theorem actualStart075 : startFrames[75]! = 77 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd075 : finalFrames[75]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid075 : forwardPathValid 75 = true := by
  rw [forwardPathValid, actualVisits075, actualStart075, actualEnd075]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_77_145, canClimb_145_519, canClimb_407_605, canClimb_519_407, canClimb_605_1, Bool.true_and]

private theorem actualVisits076 : eventVisits 76 forwardEvents = [78, 78, 209, 209, 521, 521, 521, 521, 521, 521, 494, 562, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits076
private theorem actualStart076 : startFrames[76]! = 78 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd076 : finalFrames[76]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid076 : forwardPathValid 76 = true := by
  rw [forwardPathValid, actualVisits076, actualStart076, actualEnd076]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_78_209, canClimb_209_521, canClimb_494_562, canClimb_521_494, canClimb_562_1, Bool.true_and]

private theorem actualVisits077 : eventVisits 77 forwardEvents = [79, 79, 79, 186, 186, 509, 509, 509, 509, 386, 560, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits077
private theorem actualStart077 : startFrames[77]! = 79 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd077 : finalFrames[77]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid077 : forwardPathValid 77 = true := by
  rw [forwardPathValid, actualVisits077, actualStart077, actualEnd077]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_79_186, canClimb_186_509, canClimb_386_560, canClimb_509_386, canClimb_560_1, Bool.true_and]

private theorem actualVisits078 : eventVisits 78 forwardEvents = [80, 80, 264, 264, 524, 524, 524, 524, 524, 524, 446, 567, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits078
private theorem actualStart078 : startFrames[78]! = 80 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd078 : finalFrames[78]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid078 : forwardPathValid 78 = true := by
  rw [forwardPathValid, actualVisits078, actualStart078, actualEnd078]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_80_264, canClimb_264_524, canClimb_446_567, canClimb_524_446, canClimb_567_1, Bool.true_and]

private theorem actualVisits079 : eventVisits 79 forwardEvents = [81, 81, 211, 211, 521, 521, 521, 521, 521, 521, 521, 521, 521, 500, 565, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits079
private theorem actualStart079 : startFrames[79]! = 81 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd079 : finalFrames[79]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid079 : forwardPathValid 79 = true := by
  rw [forwardPathValid, actualVisits079, actualStart079, actualEnd079]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_81_211, canClimb_211_521, canClimb_500_565, canClimb_521_500, canClimb_565_1, Bool.true_and]

theorem forwardPathBlock009 (f : Nat) (hl : 72 ≤ f) (hu : f < 80) : forwardPathValid f = true := by
  have hs : f = 72 ∨ f = 73 ∨ f = 74 ∨ f = 75 ∨ f = 76 ∨ f = 77 ∨ f = 78 ∨ f = 79 := by omega
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact forwardPathValid072
  · exact forwardPathValid073
  · exact forwardPathValid074
  · exact forwardPathValid075
  · exact forwardPathValid076
  · exact forwardPathValid077
  · exact forwardPathValid078
  · exact forwardPathValid079

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

attribute [local irreducible] canClimb
private theorem actualVisits080 : eventVisits 80 forwardEvents = [82, 82, 173, 173, 520, 520, 520, 520, 520, 520, 366, 621, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits080
private theorem actualStart080 : startFrames[80]! = 82 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd080 : finalFrames[80]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid080 : forwardPathValid 80 = true := by
  rw [forwardPathValid, actualVisits080, actualStart080, actualEnd080]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_82_173, canClimb_173_520, canClimb_366_621, canClimb_520_366, canClimb_621_1, Bool.true_and]

private theorem actualVisits081 : eventVisits 81 forwardEvents = [83, 83, 257, 257, 524, 524, 524, 524, 448, 564, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits081
private theorem actualStart081 : startFrames[81]! = 83 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd081 : finalFrames[81]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid081 : forwardPathValid 81 = true := by
  rw [forwardPathValid, actualVisits081, actualStart081, actualEnd081]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_83_257, canClimb_257_524, canClimb_448_564, canClimb_524_448, canClimb_564_1, Bool.true_and]

private theorem actualVisits082 : eventVisits 82 forwardEvents = [84, 84, 144, 144, 519, 519, 519, 519, 519, 519, 519, 410, 576, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits082
private theorem actualStart082 : startFrames[82]! = 84 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd082 : finalFrames[82]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid082 : forwardPathValid 82 = true := by
  rw [forwardPathValid, actualVisits082, actualStart082, actualEnd082]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_84_144, canClimb_144_519, canClimb_410_576, canClimb_519_410, canClimb_576_1, Bool.true_and]

private theorem actualVisits083 : eventVisits 83 forwardEvents = [85, 85, 201, 201, 521, 521, 521, 521, 521, 521, 521, 521, 521, 521, 521, 521, 521, 521, 521, 521, 521, 521, 521, 498, 611, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits083
private theorem actualStart083 : startFrames[83]! = 85 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd083 : finalFrames[83]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid083 : forwardPathValid 83 = true := by
  rw [forwardPathValid, actualVisits083, actualStart083, actualEnd083]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_85_201, canClimb_201_521, canClimb_498_611, canClimb_521_498, canClimb_611_1, Bool.true_and]

private theorem actualVisits084 : eventVisits 84 forwardEvents = [86, 86, 174, 174, 520, 520, 520, 520, 520, 378, 595, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits084
private theorem actualStart084 : startFrames[84]! = 86 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd084 : finalFrames[84]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid084 : forwardPathValid 84 = true := by
  rw [forwardPathValid, actualVisits084, actualStart084, actualEnd084]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_86_174, canClimb_174_520, canClimb_378_595, canClimb_520_378, canClimb_595_1, Bool.true_and]

private theorem actualVisits085 : eventVisits 85 forwardEvents = [87, 87, 205, 205, 521, 521, 521, 521, 521, 502, 603, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits085
private theorem actualStart085 : startFrames[85]! = 87 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd085 : finalFrames[85]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid085 : forwardPathValid 85 = true := by
  rw [forwardPathValid, actualVisits085, actualStart085, actualEnd085]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_87_205, canClimb_205_521, canClimb_502_603, canClimb_521_502, canClimb_603_1, Bool.true_and]

private theorem actualVisits086 : eventVisits 86 forwardEvents = [88, 88, 259, 259, 524, 524, 524, 524, 524, 524, 443, 559, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits086
private theorem actualStart086 : startFrames[86]! = 88 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd086 : finalFrames[86]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid086 : forwardPathValid 86 = true := by
  rw [forwardPathValid, actualVisits086, actualStart086, actualEnd086]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_88_259, canClimb_259_524, canClimb_443_559, canClimb_524_443, canClimb_559_1, Bool.true_and]

private theorem actualVisits087 : eventVisits 87 forwardEvents = [89, 89, 189, 189, 509, 509, 509, 509, 509, 509, 509, 509, 509, 509, 509, 509, 509, 509, 509, 509, 384, 552, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits087
private theorem actualStart087 : startFrames[87]! = 89 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd087 : finalFrames[87]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid087 : forwardPathValid 87 = true := by
  rw [forwardPathValid, actualVisits087, actualStart087, actualEnd087]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_89_189, canClimb_189_509, canClimb_384_552, canClimb_509_384, canClimb_552_1, Bool.true_and]

theorem forwardPathBlock010 (f : Nat) (hl : 80 ≤ f) (hu : f < 88) : forwardPathValid f = true := by
  have hs : f = 80 ∨ f = 81 ∨ f = 82 ∨ f = 83 ∨ f = 84 ∨ f = 85 ∨ f = 86 ∨ f = 87 := by omega
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact forwardPathValid080
  · exact forwardPathValid081
  · exact forwardPathValid082
  · exact forwardPathValid083
  · exact forwardPathValid084
  · exact forwardPathValid085
  · exact forwardPathValid086
  · exact forwardPathValid087

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

attribute [local irreducible] canClimb
private theorem actualVisits088 : eventVisits 88 forwardEvents = [90, 90, 247, 247, 523, 523, 523, 523, 523, 523, 523, 523, 523, 463, 624, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits088
private theorem actualStart088 : startFrames[88]! = 90 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd088 : finalFrames[88]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid088 : forwardPathValid 88 = true := by
  rw [forwardPathValid, actualVisits088, actualStart088, actualEnd088]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_90_247, canClimb_247_523, canClimb_463_624, canClimb_523_463, canClimb_624_1, Bool.true_and]

private theorem actualVisits089 : eventVisits 89 forwardEvents = [91, 91, 155, 155, 508, 508, 508, 508, 508, 508, 508, 508, 508, 508, 508, 508, 429, 575, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits089
private theorem actualStart089 : startFrames[89]! = 91 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd089 : finalFrames[89]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid089 : forwardPathValid 89 = true := by
  rw [forwardPathValid, actualVisits089, actualStart089, actualEnd089]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_91_155, canClimb_155_508, canClimb_429_575, canClimb_508_429, canClimb_575_1, Bool.true_and]

private theorem actualVisits090 : eventVisits 90 forwardEvents = [92, 92, 239, 239, 523, 523, 523, 467, 623, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits090
private theorem actualStart090 : startFrames[90]! = 92 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd090 : finalFrames[90]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid090 : forwardPathValid 90 = true := by
  rw [forwardPathValid, actualVisits090, actualStart090, actualEnd090]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_92_239, canClimb_239_523, canClimb_467_623, canClimb_523_467, canClimb_623_1, Bool.true_and]

private theorem actualVisits091 : eventVisits 91 forwardEvents = [93, 93, 135, 135, 519, 519, 400, 546, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits091
private theorem actualStart091 : startFrames[91]! = 93 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd091 : finalFrames[91]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid091 : forwardPathValid 91 = true := by
  rw [forwardPathValid, actualVisits091, actualStart091, actualEnd091]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_93_135, canClimb_135_519, canClimb_400_546, canClimb_519_400, canClimb_546_1, Bool.true_and]

private theorem actualVisits092 : eventVisits 92 forwardEvents = [94, 94, 94, 184, 184, 509, 509, 509, 509, 509, 381, 544, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits092
private theorem actualStart092 : startFrames[92]! = 94 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd092 : finalFrames[92]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid092 : forwardPathValid 92 = true := by
  rw [forwardPathValid, actualVisits092, actualStart092, actualEnd092]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_94_184, canClimb_184_509, canClimb_381_544, canClimb_509_381, canClimb_544_1, Bool.true_and]

private theorem actualVisits093 : eventVisits 93 forwardEvents = [95, 95, 246, 246, 523, 523, 523, 523, 523, 523, 523, 454, 526, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits093
private theorem actualStart093 : startFrames[93]! = 95 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd093 : finalFrames[93]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid093 : forwardPathValid 93 = true := by
  rw [forwardPathValid, actualVisits093, actualStart093, actualEnd093]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_95_246, canClimb_246_523, canClimb_454_526, canClimb_523_454, canClimb_526_1, Bool.true_and]

private theorem actualVisits094 : eventVisits 94 forwardEvents = [96, 96, 167, 167, 520, 520, 520, 520, 520, 520, 362, 548, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits094
private theorem actualStart094 : startFrames[94]! = 96 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd094 : finalFrames[94]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid094 : forwardPathValid 94 = true := by
  rw [forwardPathValid, actualVisits094, actualStart094, actualEnd094]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_96_167, canClimb_167_520, canClimb_362_548, canClimb_520_362, canClimb_548_1, Bool.true_and]

private theorem actualVisits095 : eventVisits 95 forwardEvents = [97, 97, 241, 241, 523, 523, 523, 523, 523, 466, 550, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits095
private theorem actualStart095 : startFrames[95]! = 97 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd095 : finalFrames[95]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid095 : forwardPathValid 95 = true := by
  rw [forwardPathValid, actualVisits095, actualStart095, actualEnd095]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_97_241, canClimb_241_523, canClimb_466_550, canClimb_523_466, canClimb_550_1, Bool.true_and]

theorem forwardPathBlock011 (f : Nat) (hl : 88 ≤ f) (hu : f < 96) : forwardPathValid f = true := by
  have hs : f = 88 ∨ f = 89 ∨ f = 90 ∨ f = 91 ∨ f = 92 ∨ f = 93 ∨ f = 94 ∨ f = 95 := by omega
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact forwardPathValid088
  · exact forwardPathValid089
  · exact forwardPathValid090
  · exact forwardPathValid091
  · exact forwardPathValid092
  · exact forwardPathValid093
  · exact forwardPathValid094
  · exact forwardPathValid095

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

attribute [local irreducible] canClimb
private theorem actualVisits096 : eventVisits 96 forwardEvents = [98, 98, 139, 139, 519, 519, 519, 403, 619, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits096
private theorem actualStart096 : startFrames[96]! = 98 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd096 : finalFrames[96]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid096 : forwardPathValid 96 = true := by
  rw [forwardPathValid, actualVisits096, actualStart096, actualEnd096]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_98_139, canClimb_139_519, canClimb_403_619, canClimb_519_403, canClimb_619_1, Bool.true_and]

private theorem actualVisits097 : eventVisits 97 forwardEvents = [99, 99, 154, 154, 508, 508, 508, 508, 508, 508, 508, 508, 508, 416, 542, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits097
private theorem actualStart097 : startFrames[97]! = 99 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd097 : finalFrames[97]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid097 : forwardPathValid 97 = true := by
  rw [forwardPathValid, actualVisits097, actualStart097, actualEnd097]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_99_154, canClimb_154_508, canClimb_416_542, canClimb_508_416, canClimb_542_1, Bool.true_and]

private theorem actualVisits098 : eventVisits 98 forwardEvents = [100, 100, 229, 229, 522, 522, 522, 522, 480, 620, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits098
private theorem actualStart098 : startFrames[98]! = 100 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd098 : finalFrames[98]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid098 : forwardPathValid 98 = true := by
  rw [forwardPathValid, actualVisits098, actualStart098, actualEnd098]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_100_229, canClimb_229_522, canClimb_480_620, canClimb_522_480, canClimb_620_1, Bool.true_and]

private theorem actualVisits099 : eventVisits 99 forwardEvents = [101, 101, 219, 219, 522, 522, 522, 522, 471, 527, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits099
private theorem actualStart099 : startFrames[99]! = 101 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd099 : finalFrames[99]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid099 : forwardPathValid 99 = true := by
  rw [forwardPathValid, actualVisits099, actualStart099, actualEnd099]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_101_219, canClimb_219_522, canClimb_471_527, canClimb_522_471, canClimb_527_1, Bool.true_and]

private theorem actualVisits100 : eventVisits 100 forwardEvents = [102, 102, 228, 228, 522, 522, 522, 522, 476, 545, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits100
private theorem actualStart100 : startFrames[100]! = 102 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd100 : finalFrames[100]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid100 : forwardPathValid 100 = true := by
  rw [forwardPathValid, actualVisits100, actualStart100, actualEnd100]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_102_228, canClimb_228_522, canClimb_476_545, canClimb_522_476, canClimb_545_1, Bool.true_and]

private theorem actualVisits101 : eventVisits 101 forwardEvents = [103, 103, 223, 223, 522, 522, 522, 522, 522, 522, 522, 484, 541, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits101
private theorem actualStart101 : startFrames[101]! = 103 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd101 : finalFrames[101]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid101 : forwardPathValid 101 = true := by
  rw [forwardPathValid, actualVisits101, actualStart101, actualEnd101]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_103_223, canClimb_223_522, canClimb_484_541, canClimb_522_484, canClimb_541_1, Bool.true_and]

private theorem actualVisits102 : eventVisits 102 forwardEvents = [104, 104, 166, 166, 520, 520, 520, 520, 520, 368, 566, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits102
private theorem actualStart102 : startFrames[102]! = 104 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd102 : finalFrames[102]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid102 : forwardPathValid 102 = true := by
  rw [forwardPathValid, actualVisits102, actualStart102, actualEnd102]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_104_166, canClimb_166_520, canClimb_368_566, canClimb_520_368, canClimb_566_1, Bool.true_and]

private theorem actualVisits103 : eventVisits 103 forwardEvents = [105, 105, 233, 233, 523, 523, 523, 523, 523, 523, 523, 523, 523, 523, 523, 523, 523, 523, 523, 523, 464, 553, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits103
private theorem actualStart103 : startFrames[103]! = 105 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd103 : finalFrames[103]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid103 : forwardPathValid 103 = true := by
  rw [forwardPathValid, actualVisits103, actualStart103, actualEnd103]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_105_233, canClimb_233_523, canClimb_464_553, canClimb_523_464, canClimb_553_1, Bool.true_and]

theorem forwardPathBlock012 (f : Nat) (hl : 96 ≤ f) (hu : f < 104) : forwardPathValid f = true := by
  have hs : f = 96 ∨ f = 97 ∨ f = 98 ∨ f = 99 ∨ f = 100 ∨ f = 101 ∨ f = 102 ∨ f = 103 := by omega
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact forwardPathValid096
  · exact forwardPathValid097
  · exact forwardPathValid098
  · exact forwardPathValid099
  · exact forwardPathValid100
  · exact forwardPathValid101
  · exact forwardPathValid102
  · exact forwardPathValid103

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

attribute [local irreducible] canClimb
private theorem actualVisits104 : eventVisits 104 forwardEvents = [106, 106, 199, 199, 521, 521, 521, 521, 521, 521, 521, 521, 489, 630, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits104
private theorem actualStart104 : startFrames[104]! = 106 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd104 : finalFrames[104]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid104 : forwardPathValid 104 = true := by
  rw [forwardPathValid, actualVisits104, actualStart104, actualEnd104]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_106_199, canClimb_199_521, canClimb_489_630, canClimb_521_489, canClimb_630_1, Bool.true_and]

private theorem actualVisits105 : eventVisits 105 forwardEvents = [107, 107, 251, 251, 524, 524, 524, 524, 524, 524, 524, 451, 601, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits105
private theorem actualStart105 : startFrames[105]! = 107 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd105 : finalFrames[105]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid105 : forwardPathValid 105 = true := by
  rw [forwardPathValid, actualVisits105, actualStart105, actualEnd105]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_107_251, canClimb_251_524, canClimb_451_601, canClimb_524_451, canClimb_601_1, Bool.true_and]

private theorem actualVisits106 : eventVisits 106 forwardEvents = [108, 108, 217, 217, 522, 522, 522, 522, 477, 539, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits106
private theorem actualStart106 : startFrames[106]! = 108 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd106 : finalFrames[106]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid106 : forwardPathValid 106 = true := by
  rw [forwardPathValid, actualVisits106, actualStart106, actualEnd106]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_108_217, canClimb_217_522, canClimb_477_539, canClimb_522_477, canClimb_539_1, Bool.true_and]

private theorem actualVisits107 : eventVisits 107 forwardEvents = [109, 109, 198, 198, 521, 521, 521, 521, 521, 521, 521, 521, 521, 495, 606, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits107
private theorem actualStart107 : startFrames[107]! = 109 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd107 : finalFrames[107]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid107 : forwardPathValid 107 = true := by
  rw [forwardPathValid, actualVisits107, actualStart107, actualEnd107]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_109_198, canClimb_198_521, canClimb_495_606, canClimb_521_495, canClimb_606_1, Bool.true_and]

private theorem actualVisits108 : eventVisits 108 forwardEvents = [110, 110, 214, 214, 522, 522, 522, 522, 522, 522, 522, 522, 522, 522, 486, 618, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits108
private theorem actualStart108 : startFrames[108]! = 110 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd108 : finalFrames[108]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid108 : forwardPathValid 108 = true := by
  rw [forwardPathValid, actualVisits108, actualStart108, actualEnd108]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_110_214, canClimb_214_522, canClimb_486_618, canClimb_522_486, canClimb_618_1, Bool.true_and]

private theorem actualVisits109 : eventVisits 109 forwardEvents = [111, 111, 235, 235, 523, 523, 523, 523, 523, 459, 549, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits109
private theorem actualStart109 : startFrames[109]! = 111 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd109 : finalFrames[109]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid109 : forwardPathValid 109 = true := by
  rw [forwardPathValid, actualVisits109, actualStart109, actualEnd109]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_111_235, canClimb_235_523, canClimb_459_549, canClimb_523_459, canClimb_549_1, Bool.true_and]

private theorem actualVisits110 : eventVisits 110 forwardEvents = [112, 112, 250, 250, 524, 524, 524, 524, 524, 524, 524, 524, 524, 524, 524, 524, 524, 524, 524, 524, 524, 445, 608, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits110
private theorem actualStart110 : startFrames[110]! = 112 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd110 : finalFrames[110]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid110 : forwardPathValid 110 = true := by
  rw [forwardPathValid, actualVisits110, actualStart110, actualEnd110]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_112_250, canClimb_250_524, canClimb_445_608, canClimb_524_445, canClimb_608_1, Bool.true_and]

private theorem actualVisits111 : eventVisits 111 forwardEvents = [0, 0, 127, 525] := by
  rw [forward_visits_computed]
  exact computedForwardVisits111
private theorem actualStart111 : startFrames[111]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd111 : finalFrames[111]! = 525 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid111 : forwardPathValid 111 = true := by
  rw [forwardPathValid, actualVisits111, actualStart111, actualEnd111]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_127, canClimb_127_525, Bool.true_and]

theorem forwardPathBlock013 (f : Nat) (hl : 104 ≤ f) (hu : f < 112) : forwardPathValid f = true := by
  have hs : f = 104 ∨ f = 105 ∨ f = 106 ∨ f = 107 ∨ f = 108 ∨ f = 109 ∨ f = 110 ∨ f = 111 := by omega
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact forwardPathValid104
  · exact forwardPathValid105
  · exact forwardPathValid106
  · exact forwardPathValid107
  · exact forwardPathValid108
  · exact forwardPathValid109
  · exact forwardPathValid110
  · exact forwardPathValid111

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

attribute [local irreducible] canClimb
private theorem actualVisits112 : eventVisits 112 forwardEvents = [0, 0, 217, 526] := by
  rw [forward_visits_computed]
  exact computedForwardVisits112
private theorem actualStart112 : startFrames[112]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd112 : finalFrames[112]! = 526 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid112 : forwardPathValid 112 = true := by
  rw [forwardPathValid, actualVisits112, actualStart112, actualEnd112]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_217, canClimb_217_526, Bool.true_and]

private theorem actualVisits113 : eventVisits 113 forwardEvents = [0, 0, 233, 527] := by
  rw [forward_visits_computed]
  exact computedForwardVisits113
private theorem actualStart113 : startFrames[113]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd113 : finalFrames[113]! = 527 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid113 : forwardPathValid 113 = true := by
  rw [forwardPathValid, actualVisits113, actualStart113, actualEnd113]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_233, canClimb_233_527, Bool.true_and]

private theorem actualVisits114 : eventVisits 114 forwardEvents = [0, 0, 528] := by
  rw [forward_visits_computed]
  exact computedForwardVisits114
private theorem actualStart114 : startFrames[114]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd114 : finalFrames[114]! = 528 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid114 : forwardPathValid 114 = true := by
  rw [forwardPathValid, actualVisits114, actualStart114, actualEnd114]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_528, Bool.true_and]

private theorem actualVisits115 : eventVisits 115 forwardEvents = [0, 0, 235, 529] := by
  rw [forward_visits_computed]
  exact computedForwardVisits115
private theorem actualStart115 : startFrames[115]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd115 : finalFrames[115]! = 529 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid115 : forwardPathValid 115 = true := by
  rw [forwardPathValid, actualVisits115, actualStart115, actualEnd115]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_235, canClimb_235_529, Bool.true_and]

private theorem actualVisits116 : eventVisits 116 forwardEvents = [0, 0, 11, 530] := by
  rw [forward_visits_computed]
  exact computedForwardVisits116
private theorem actualStart116 : startFrames[116]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd116 : finalFrames[116]! = 530 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid116 : forwardPathValid 116 = true := by
  rw [forwardPathValid, actualVisits116, actualStart116, actualEnd116]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_11, canClimb_11_530, Bool.true_and]

private theorem actualVisits117 : eventVisits 117 forwardEvents = [0, 0, 114, 531] := by
  rw [forward_visits_computed]
  exact computedForwardVisits117
private theorem actualStart117 : startFrames[117]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd117 : finalFrames[117]! = 531 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid117 : forwardPathValid 117 = true := by
  rw [forwardPathValid, actualVisits117, actualStart117, actualEnd117]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_114, canClimb_114_531, Bool.true_and]

private theorem actualVisits118 : eventVisits 118 forwardEvents = [0, 0, 214, 532] := by
  rw [forward_visits_computed]
  exact computedForwardVisits118
private theorem actualStart118 : startFrames[118]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd118 : finalFrames[118]! = 532 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid118 : forwardPathValid 118 = true := by
  rw [forwardPathValid, actualVisits118, actualStart118, actualEnd118]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_214, canClimb_214_532, Bool.true_and]

private theorem actualVisits119 : eventVisits 119 forwardEvents = [0, 0, 252, 533] := by
  rw [forward_visits_computed]
  exact computedForwardVisits119
private theorem actualStart119 : startFrames[119]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd119 : finalFrames[119]! = 533 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid119 : forwardPathValid 119 = true := by
  rw [forwardPathValid, actualVisits119, actualStart119, actualEnd119]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_252, canClimb_252_533, Bool.true_and]

theorem forwardPathBlock014 (f : Nat) (hl : 112 ≤ f) (hu : f < 120) : forwardPathValid f = true := by
  have hs : f = 112 ∨ f = 113 ∨ f = 114 ∨ f = 115 ∨ f = 116 ∨ f = 117 ∨ f = 118 ∨ f = 119 := by omega
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact forwardPathValid112
  · exact forwardPathValid113
  · exact forwardPathValid114
  · exact forwardPathValid115
  · exact forwardPathValid116
  · exact forwardPathValid117
  · exact forwardPathValid118
  · exact forwardPathValid119

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

attribute [local irreducible] canClimb
private theorem actualVisits120 : eventVisits 120 forwardEvents = [0, 0, 534] := by
  rw [forward_visits_computed]
  exact computedForwardVisits120
private theorem actualStart120 : startFrames[120]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd120 : finalFrames[120]! = 534 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid120 : forwardPathValid 120 = true := by
  rw [forwardPathValid, actualVisits120, actualStart120, actualEnd120]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_534, Bool.true_and]

private theorem actualVisits121 : eventVisits 121 forwardEvents = [0, 0, 198, 535] := by
  rw [forward_visits_computed]
  exact computedForwardVisits121
private theorem actualStart121 : startFrames[121]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd121 : finalFrames[121]! = 535 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid121 : forwardPathValid 121 = true := by
  rw [forwardPathValid, actualVisits121, actualStart121, actualEnd121]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_198, canClimb_198_535, Bool.true_and]

private theorem actualVisits122 : eventVisits 122 forwardEvents = [0, 0, 2, 536] := by
  rw [forward_visits_computed]
  exact computedForwardVisits122
private theorem actualStart122 : startFrames[122]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd122 : finalFrames[122]! = 536 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid122 : forwardPathValid 122 = true := by
  rw [forwardPathValid, actualVisits122, actualStart122, actualEnd122]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_2, canClimb_2_536, Bool.true_and]

private theorem actualVisits123 : eventVisits 123 forwardEvents = [0, 0, 249, 537] := by
  rw [forward_visits_computed]
  exact computedForwardVisits123
private theorem actualStart123 : startFrames[123]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd123 : finalFrames[123]! = 537 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid123 : forwardPathValid 123 = true := by
  rw [forwardPathValid, actualVisits123, actualStart123, actualEnd123]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_249, canClimb_249_537, Bool.true_and]

private theorem actualVisits124 : eventVisits 124 forwardEvents = [0, 0, 199, 538] := by
  rw [forward_visits_computed]
  exact computedForwardVisits124
private theorem actualStart124 : startFrames[124]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd124 : finalFrames[124]! = 538 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid124 : forwardPathValid 124 = true := by
  rw [forwardPathValid, actualVisits124, actualStart124, actualEnd124]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_199, canClimb_199_538, Bool.true_and]

private theorem actualVisits125 : eventVisits 125 forwardEvents = [0, 0, 239, 539] := by
  rw [forward_visits_computed]
  exact computedForwardVisits125
private theorem actualStart125 : startFrames[125]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd125 : finalFrames[125]! = 539 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid125 : forwardPathValid 125 = true := by
  rw [forwardPathValid, actualVisits125, actualStart125, actualEnd125]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_239, canClimb_239_539, Bool.true_and]

private theorem actualVisits126 : eventVisits 126 forwardEvents = [0, 0, 139, 540] := by
  rw [forward_visits_computed]
  exact computedForwardVisits126
private theorem actualStart126 : startFrames[126]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd126 : finalFrames[126]! = 540 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid126 : forwardPathValid 126 = true := by
  rw [forwardPathValid, actualVisits126, actualStart126, actualEnd126]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_139, canClimb_139_540, Bool.true_and]

private theorem actualVisits127 : eventVisits 127 forwardEvents = [0, 0, 246, 541] := by
  rw [forward_visits_computed]
  exact computedForwardVisits127
private theorem actualStart127 : startFrames[127]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd127 : finalFrames[127]! = 541 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid127 : forwardPathValid 127 = true := by
  rw [forwardPathValid, actualVisits127, actualStart127, actualEnd127]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_246, canClimb_246_541, Bool.true_and]

theorem forwardPathBlock015 (f : Nat) (hl : 120 ≤ f) (hu : f < 128) : forwardPathValid f = true := by
  have hs : f = 120 ∨ f = 121 ∨ f = 122 ∨ f = 123 ∨ f = 124 ∨ f = 125 ∨ f = 126 ∨ f = 127 := by omega
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact forwardPathValid120
  · exact forwardPathValid121
  · exact forwardPathValid122
  · exact forwardPathValid123
  · exact forwardPathValid124
  · exact forwardPathValid125
  · exact forwardPathValid126
  · exact forwardPathValid127

end CSL.Construction.PhysicalFramePaths


