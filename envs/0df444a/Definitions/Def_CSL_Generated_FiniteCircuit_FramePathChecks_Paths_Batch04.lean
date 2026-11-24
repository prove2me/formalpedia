-- Prove2me | Definitions.Def_CSL_Generated_FiniteCircuit_FramePathChecks_Paths_Batch04
-- name    : CSL_Generated_FiniteCircuit_FramePathChecks_Paths_Batch04
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T14:46:32.868851+00:00
-- url     : https://prove2.me/theorems/00df4c0f-acb6-48d7-a0d2-24b059e4096e
-- title:
--   Coded sorting library: Generated / FiniteCircuit / FramePathChecks / Paths / Batch04
-- statement:
--   Module `CodedSorting.Generated.FiniteCircuit.FramePathChecks.Paths.Batch04` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   Generated physical-frame checks. Uncompiled until a build record exists.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Generated.FiniteCircuit.FramePathChecks.Paths.Batch04

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Generated_FiniteCircuit_FramePathChecks_Nesting_Batch00
import Definitions.Def_CSL_Generated_FiniteCircuit_FramePathChecks_Nesting_Batch01
import Definitions.Def_CSL_Generated_FiniteCircuit_FramePathChecks_Nesting_Batch02
import Definitions.Def_CSL_Generated_FiniteCircuit_FramePathChecks_Nesting_Batch03
import Definitions.Def_CSL_Generated_FiniteCircuit_FramePathChecks_Nesting_Batch04
import Definitions.Def_CSL_Generated_FiniteCircuit_FramePathChecks_Nesting_Batch05
import Definitions.Def_CSL_Generated_FiniteCircuit_FramePathChecks_Nesting_Batch06
import Definitions.Def_CSL_Generated_FiniteCircuit_FramePathChecks_VisitNumbers_Batch04
import Definitions.Def_CSL_Generated_FiniteCircuit_FramePathChecks_VisitNumbers_Bridge

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

attribute [local irreducible] canClimb
private theorem actualVisits512 : eventVisits 512 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 63, 299, 299, 299, 299, 299, 371, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits512
private theorem actualStart512 : startFrames[512]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd512 : finalFrames[512]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid512 : forwardPathValid 512 = true := by
  rw [forwardPathValid, actualVisits512, actualStart512, actualEnd512]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_63, canClimb_63_299, canClimb_299_371, canClimb_371_1, Bool.true_and]

private theorem actualVisits513 : eventVisits 513 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 132, 297, 297, 297, 297, 297, 444, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits513
private theorem actualStart513 : startFrames[513]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd513 : finalFrames[513]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid513 : forwardPathValid 513 = true := by
  rw [forwardPathValid, actualVisits513, actualStart513, actualEnd513]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_132, canClimb_132_297, canClimb_297_444, canClimb_444_1, Bool.true_and]

private theorem actualVisits514 : eventVisits 514 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 65, 296, 296, 296, 296, 296, 358, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits514
private theorem actualStart514 : startFrames[514]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd514 : finalFrames[514]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid514 : forwardPathValid 514 = true := by
  rw [forwardPathValid, actualVisits514, actualStart514, actualEnd514]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_65, canClimb_65_296, canClimb_296_358, canClimb_358_1, Bool.true_and]

private theorem actualVisits515 : eventVisits 515 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 133, 298, 298, 298, 298, 298, 381, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits515
private theorem actualStart515 : startFrames[515]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd515 : finalFrames[515]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid515 : forwardPathValid 515 = true := by
  rw [forwardPathValid, actualVisits515, actualStart515, actualEnd515]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_133, canClimb_133_298, canClimb_298_381, canClimb_381_1, Bool.true_and]

private theorem actualVisits516 : eventVisits 516 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 70, 301, 301, 301, 301, 301, 301, 301, 301, 356, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits516
private theorem actualStart516 : startFrames[516]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd516 : finalFrames[516]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid516 : forwardPathValid 516 = true := by
  rw [forwardPathValid, actualVisits516, actualStart516, actualEnd516]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_70, canClimb_70_301, canClimb_301_356, canClimb_356_1, Bool.true_and]

private theorem actualVisits517 : eventVisits 517 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 134, 307, 307, 307, 307, 307, 307, 307, 307, 367, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits517
private theorem actualStart517 : startFrames[517]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd517 : finalFrames[517]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid517 : forwardPathValid 517 = true := by
  rw [forwardPathValid, actualVisits517, actualStart517, actualEnd517]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_134, canClimb_134_307, canClimb_307_367, canClimb_367_1, Bool.true_and]

private theorem actualVisits518 : eventVisits 518 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 135, 306, 306, 306, 306, 306, 306, 306, 384, 384, 622, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits518
private theorem actualStart518 : startFrames[518]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd518 : finalFrames[518]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid518 : forwardPathValid 518 = true := by
  rw [forwardPathValid, actualVisits518, actualStart518, actualEnd518]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_135, canClimb_135_306, canClimb_306_384, canClimb_384_622, canClimb_622_1, Bool.true_and]

private theorem actualVisits519 : eventVisits 519 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 136, 305, 305, 305, 305, 305, 305, 305, 305, 401, 401, 619, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits519
private theorem actualStart519 : startFrames[519]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd519 : finalFrames[519]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid519 : forwardPathValid 519 = true := by
  rw [forwardPathValid, actualVisits519, actualStart519, actualEnd519]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_136, canClimb_136_305, canClimb_305_401, canClimb_401_619, canClimb_619_1, Bool.true_and]

theorem forwardPathBlock064 (f : Nat) (hl : 512 ≤ f) (hu : f < 520) : forwardPathValid f = true := by
  have hs : f = 512 ∨ f = 513 ∨ f = 514 ∨ f = 515 ∨ f = 516 ∨ f = 517 ∨ f = 518 ∨ f = 519 := by omega
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact forwardPathValid512
  · exact forwardPathValid513
  · exact forwardPathValid514
  · exact forwardPathValid515
  · exact forwardPathValid516
  · exact forwardPathValid517
  · exact forwardPathValid518
  · exact forwardPathValid519

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

attribute [local irreducible] canClimb
private theorem actualVisits520 : eventVisits 520 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 137, 304, 304, 304, 304, 304, 304, 304, 304, 364, 364, 540, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits520
private theorem actualStart520 : startFrames[520]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd520 : finalFrames[520]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid520 : forwardPathValid 520 = true := by
  rw [forwardPathValid, actualVisits520, actualStart520, actualEnd520]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_137, canClimb_137_304, canClimb_304_364, canClimb_364_540, canClimb_540_1, Bool.true_and]

private theorem actualVisits521 : eventVisits 521 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 138, 303, 303, 303, 303, 303, 303, 303, 303, 381, 381, 614, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits521
private theorem actualStart521 : startFrames[521]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd521 : finalFrames[521]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid521 : forwardPathValid 521 = true := by
  rw [forwardPathValid, actualVisits521, actualStart521, actualEnd521]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_138, canClimb_138_303, canClimb_303_381, canClimb_381_614, canClimb_614_1, Bool.true_and]

private theorem actualVisits522 : eventVisits 522 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 139, 302, 302, 302, 302, 302, 302, 302, 396, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits522
private theorem actualStart522 : startFrames[522]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd522 : finalFrames[522]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid522 : forwardPathValid 522 = true := by
  rw [forwardPathValid, actualVisits522, actualStart522, actualEnd522]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_139, canClimb_139_302, canClimb_302_396, canClimb_396_1, Bool.true_and]

private theorem actualVisits523 : eventVisits 523 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 140, 313, 313, 313, 313, 313, 313, 313, 313, 395, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits523
private theorem actualStart523 : startFrames[523]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd523 : finalFrames[523]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid523 : forwardPathValid 523 = true := by
  rw [forwardPathValid, actualVisits523, actualStart523, actualEnd523]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_140, canClimb_140_313, canClimb_313_395, canClimb_395_1, Bool.true_and]

private theorem actualVisits524 : eventVisits 524 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 141, 312, 312, 312, 312, 312, 312, 312, 312, 408, 408, 569, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits524
private theorem actualStart524 : startFrames[524]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd524 : finalFrames[524]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid524 : forwardPathValid 524 = true := by
  rw [forwardPathValid, actualVisits524, actualStart524, actualEnd524]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_141, canClimb_141_312, canClimb_312_408, canClimb_408_569, canClimb_569_1, Bool.true_and]

private theorem actualVisits525 : eventVisits 525 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 142, 311, 311, 311, 311, 311, 311, 311, 311, 371, 371, 566, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits525
private theorem actualStart525 : startFrames[525]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd525 : finalFrames[525]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid525 : forwardPathValid 525 = true := by
  rw [forwardPathValid, actualVisits525, actualStart525, actualEnd525]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_142, canClimb_142_311, canClimb_311_371, canClimb_371_566, canClimb_566_1, Bool.true_and]

private theorem actualVisits526 : eventVisits 526 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 143, 310, 310, 310, 310, 310, 310, 310, 389, 389, 599, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits526
private theorem actualStart526 : startFrames[526]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd526 : finalFrames[526]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid526 : forwardPathValid 526 = true := by
  rw [forwardPathValid, actualVisits526, actualStart526, actualEnd526]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_143, canClimb_143_310, canClimb_310_389, canClimb_389_599, canClimb_599_1, Bool.true_and]

private theorem actualVisits527 : eventVisits 527 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 144, 309, 309, 309, 309, 309, 309, 309, 440, 440, 559, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits527
private theorem actualStart527 : startFrames[527]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd527 : finalFrames[527]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid527 : forwardPathValid 527 = true := by
  rw [forwardPathValid, actualVisits527, actualStart527, actualEnd527]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_144, canClimb_144_309, canClimb_309_440, canClimb_440_559, canClimb_559_1, Bool.true_and]

theorem forwardPathBlock065 (f : Nat) (hl : 520 ≤ f) (hu : f < 528) : forwardPathValid f = true := by
  have hs : f = 520 ∨ f = 521 ∨ f = 522 ∨ f = 523 ∨ f = 524 ∨ f = 525 ∨ f = 526 ∨ f = 527 := by omega
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact forwardPathValid520
  · exact forwardPathValid521
  · exact forwardPathValid522
  · exact forwardPathValid523
  · exact forwardPathValid524
  · exact forwardPathValid525
  · exact forwardPathValid526
  · exact forwardPathValid527

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

attribute [local irreducible] canClimb
private theorem actualVisits528 : eventVisits 528 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 145, 308, 308, 308, 308, 308, 308, 308, 394, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits528
private theorem actualStart528 : startFrames[528]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd528 : finalFrames[528]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid528 : forwardPathValid 528 = true := by
  rw [forwardPathValid, actualVisits528, actualStart528, actualEnd528]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_145, canClimb_145_308, canClimb_308_394, canClimb_394_1, Bool.true_and]

private theorem actualVisits529 : eventVisits 529 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 146, 319, 319, 319, 319, 319, 319, 319, 447, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits529
private theorem actualStart529 : startFrames[529]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd529 : finalFrames[529]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid529 : forwardPathValid 529 = true := by
  rw [forwardPathValid, actualVisits529, actualStart529, actualEnd529]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_146, canClimb_146_319, canClimb_319_447, canClimb_447_1, Bool.true_and]

private theorem actualVisits530 : eventVisits 530 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 147, 318, 318, 318, 318, 318, 318, 318, 318, 378, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits530
private theorem actualStart530 : startFrames[530]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd530 : finalFrames[530]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid530 : forwardPathValid 530 = true := by
  rw [forwardPathValid, actualVisits530, actualStart530, actualEnd530]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_147, canClimb_147_318, canClimb_318_378, canClimb_378_1, Bool.true_and]

private theorem actualVisits531 : eventVisits 531 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 148, 317, 317, 317, 317, 317, 317, 317, 317, 391, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits531
private theorem actualStart531 : startFrames[531]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd531 : finalFrames[531]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid531 : forwardPathValid 531 = true := by
  rw [forwardPathValid, actualVisits531, actualStart531, actualEnd531]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_148, canClimb_148_317, canClimb_317_391, canClimb_391_1, Bool.true_and]

private theorem actualVisits532 : eventVisits 532 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 149, 316, 316, 316, 316, 316, 316, 316, 316, 386, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits532
private theorem actualStart532 : startFrames[532]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd532 : finalFrames[532]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid532 : forwardPathValid 532 = true := by
  rw [forwardPathValid, actualVisits532, actualStart532, actualEnd532]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_149, canClimb_149_316, canClimb_316_386, canClimb_386_1, Bool.true_and]

private theorem actualVisits533 : eventVisits 533 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 150, 315, 315, 315, 315, 315, 315, 315, 315, 385, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits533
private theorem actualStart533 : startFrames[533]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd533 : finalFrames[533]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid533 : forwardPathValid 533 = true := by
  rw [forwardPathValid, actualVisits533, actualStart533, actualEnd533]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_150, canClimb_150_315, canClimb_315_385, canClimb_385_1, Bool.true_and]

private theorem actualVisits534 : eventVisits 534 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 151, 314, 314, 314, 314, 314, 314, 314, 314, 374, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits534
private theorem actualStart534 : startFrames[534]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd534 : finalFrames[534]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid534 : forwardPathValid 534 = true := by
  rw [forwardPathValid, actualVisits534, actualStart534, actualEnd534]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_151, canClimb_151_314, canClimb_314_374, canClimb_374_1, Bool.true_and]

private theorem actualVisits535 : eventVisits 535 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 152, 315, 315, 315, 315, 315, 375, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits535
private theorem actualStart535 : startFrames[535]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd535 : finalFrames[535]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid535 : forwardPathValid 535 = true := by
  rw [forwardPathValid, actualVisits535, actualStart535, actualEnd535]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_152, canClimb_152_315, canClimb_315_375, canClimb_375_1, Bool.true_and]

theorem forwardPathBlock066 (f : Nat) (hl : 528 ≤ f) (hu : f < 536) : forwardPathValid f = true := by
  have hs : f = 528 ∨ f = 529 ∨ f = 530 ∨ f = 531 ∨ f = 532 ∨ f = 533 ∨ f = 534 ∨ f = 535 := by omega
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact forwardPathValid528
  · exact forwardPathValid529
  · exact forwardPathValid530
  · exact forwardPathValid531
  · exact forwardPathValid532
  · exact forwardPathValid533
  · exact forwardPathValid534
  · exact forwardPathValid535

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

attribute [local irreducible] canClimb
private theorem actualVisits536 : eventVisits 536 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 153, 306, 306, 306, 306, 306, 306, 306, 306, 366, 366, 548, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits536
private theorem actualStart536 : startFrames[536]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd536 : finalFrames[536]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid536 : forwardPathValid 536 = true := by
  rw [forwardPathValid, actualVisits536, actualStart536, actualEnd536]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_153, canClimb_153_306, canClimb_306_366, canClimb_366_548, canClimb_548_1, Bool.true_and]

private theorem actualVisits537 : eventVisits 537 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 154, 321, 321, 321, 321, 321, 321, 321, 321, 419, 419, 617, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits537
private theorem actualStart537 : startFrames[537]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd537 : finalFrames[537]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid537 : forwardPathValid 537 = true := by
  rw [forwardPathValid, actualVisits537, actualStart537, actualEnd537]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_154, canClimb_154_321, canClimb_321_419, canClimb_419_617, canClimb_617_1, Bool.true_and]

private theorem actualVisits538 : eventVisits 538 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 155, 320, 320, 320, 320, 320, 320, 320, 320, 418, 418, 518, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits538
private theorem actualStart538 : startFrames[538]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd538 : finalFrames[538]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid538 : forwardPathValid 538 = true := by
  rw [forwardPathValid, actualVisits538, actualStart538, actualEnd538]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_155, canClimb_155_320, canClimb_320_418, canClimb_418_518, canClimb_518_1, Bool.true_and]

private theorem actualVisits539 : eventVisits 539 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 156, 303, 303, 303, 303, 303, 303, 303, 363, 363, 616, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits539
private theorem actualStart539 : startFrames[539]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd539 : finalFrames[539]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid539 : forwardPathValid 539 = true := by
  rw [forwardPathValid, actualVisits539, actualStart539, actualEnd539]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_156, canClimb_156_303, canClimb_303_363, canClimb_363_616, canClimb_616_1, Bool.true_and]

private theorem actualVisits540 : eventVisits 540 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 157, 318, 318, 318, 318, 318, 411, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits540
private theorem actualStart540 : startFrames[540]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd540 : finalFrames[540]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid540 : forwardPathValid 540 = true := by
  rw [forwardPathValid, actualVisits540, actualStart540, actualEnd540]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_157, canClimb_157_318, canClimb_318_411, canClimb_411_1, Bool.true_and]

private theorem actualVisits541 : eventVisits 541 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 158, 317, 317, 317, 317, 317, 317, 317, 377, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits541
private theorem actualStart541 : startFrames[541]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd541 : finalFrames[541]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid541 : forwardPathValid 541 = true := by
  rw [forwardPathValid, actualVisits541, actualStart541, actualEnd541]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_158, canClimb_158_317, canClimb_317_377, canClimb_377_1, Bool.true_and]

private theorem actualVisits542 : eventVisits 542 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 159, 323, 323, 323, 323, 323, 323, 323, 323, 426, 426, 612, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits542
private theorem actualStart542 : startFrames[542]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd542 : finalFrames[542]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid542 : forwardPathValid 542 = true := by
  rw [forwardPathValid, actualVisits542, actualStart542, actualEnd542]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_159, canClimb_159_323, canClimb_323_426, canClimb_426_612, canClimb_612_1, Bool.true_and]

private theorem actualVisits543 : eventVisits 543 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 37, 310, 310, 310, 310, 310, 310, 310, 310, 370, 370, 555, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits543
private theorem actualStart543 : startFrames[543]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd543 : finalFrames[543]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid543 : forwardPathValid 543 = true := by
  rw [forwardPathValid, actualVisits543, actualStart543, actualEnd543]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_37, canClimb_37_310, canClimb_310_370, canClimb_370_555, canClimb_555_1, Bool.true_and]

theorem forwardPathBlock067 (f : Nat) (hl : 536 ≤ f) (hu : f < 544) : forwardPathValid f = true := by
  have hs : f = 536 ∨ f = 537 ∨ f = 538 ∨ f = 539 ∨ f = 540 ∨ f = 541 ∨ f = 542 ∨ f = 543 := by omega
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact forwardPathValid536
  · exact forwardPathValid537
  · exact forwardPathValid538
  · exact forwardPathValid539
  · exact forwardPathValid540
  · exact forwardPathValid541
  · exact forwardPathValid542
  · exact forwardPathValid543

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

attribute [local irreducible] canClimb
private theorem actualVisits544 : eventVisits 544 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 160, 311, 311, 311, 311, 311, 407, 407, 569, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits544
private theorem actualStart544 : startFrames[544]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd544 : finalFrames[544]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid544 : forwardPathValid 544 = true := by
  rw [forwardPathValid, actualVisits544, actualStart544, actualEnd544]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_160, canClimb_160_311, canClimb_311_407, canClimb_407_569, canClimb_569_1, Bool.true_and]

private theorem actualVisits545 : eventVisits 545 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 45, 322, 322, 322, 322, 322, 322, 322, 451, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits545
private theorem actualStart545 : startFrames[545]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd545 : finalFrames[545]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid545 : forwardPathValid 545 = true := by
  rw [forwardPathValid, actualVisits545, actualStart545, actualEnd545]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_45, canClimb_45_322, canClimb_322_451, canClimb_451_1, Bool.true_and]

private theorem actualVisits546 : eventVisits 546 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 76, 316, 316, 316, 316, 316, 316, 376, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits546
private theorem actualStart546 : startFrames[546]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd546 : finalFrames[546]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid546 : forwardPathValid 546 = true := by
  rw [forwardPathValid, actualVisits546, actualStart546, actualEnd546]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_76, canClimb_76_316, canClimb_316_376, canClimb_376_1, Bool.true_and]

private theorem actualVisits547 : eventVisits 547 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 59, 325, 325, 325, 325, 325, 325, 325, 325, 428, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits547
private theorem actualStart547 : startFrames[547]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd547 : finalFrames[547]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid547 : forwardPathValid 547 = true := by
  rw [forwardPathValid, actualVisits547, actualStart547, actualEnd547]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_59, canClimb_59_325, canClimb_325_428, canClimb_428_1, Bool.true_and]

private theorem actualVisits548 : eventVisits 548 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 67, 302, 302, 302, 302, 302, 302, 362, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits548
private theorem actualStart548 : startFrames[548]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd548 : finalFrames[548]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid548 : forwardPathValid 548 = true := by
  rw [forwardPathValid, actualVisits548, actualStart548, actualEnd548]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_67, canClimb_67_302, canClimb_302_362, canClimb_362_1, Bool.true_and]

private theorem actualVisits549 : eventVisits 549 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 68, 313, 313, 313, 313, 313, 373, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits549
private theorem actualStart549 : startFrames[549]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd549 : finalFrames[549]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid549 : forwardPathValid 549 = true := by
  rw [forwardPathValid, actualVisits549, actualStart549, actualEnd549]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_68, canClimb_68_313, canClimb_313_373, canClimb_373_1, Bool.true_and]

private theorem actualVisits550 : eventVisits 550 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 161, 308, 308, 308, 308, 308, 308, 368, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits550
private theorem actualStart550 : startFrames[550]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd550 : finalFrames[550]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid550 : forwardPathValid 550 = true := by
  rw [forwardPathValid, actualVisits550, actualStart550, actualEnd550]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_161, canClimb_161_308, canClimb_308_368, canClimb_368_1, Bool.true_and]

private theorem actualVisits551 : eventVisits 551 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 162, 307, 307, 307, 307, 393, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits551
private theorem actualStart551 : startFrames[551]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd551 : finalFrames[551]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid551 : forwardPathValid 551 = true := by
  rw [forwardPathValid, actualVisits551, actualStart551, actualEnd551]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_162, canClimb_162_307, canClimb_307_393, canClimb_393_1, Bool.true_and]

theorem forwardPathBlock068 (f : Nat) (hl : 544 ≤ f) (hu : f < 552) : forwardPathValid f = true := by
  have hs : f = 544 ∨ f = 545 ∨ f = 546 ∨ f = 547 ∨ f = 548 ∨ f = 549 ∨ f = 550 ∨ f = 551 := by omega
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact forwardPathValid544
  · exact forwardPathValid545
  · exact forwardPathValid546
  · exact forwardPathValid547
  · exact forwardPathValid548
  · exact forwardPathValid549
  · exact forwardPathValid550
  · exact forwardPathValid551

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

attribute [local irreducible] canClimb
private theorem actualVisits552 : eventVisits 552 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 163, 324, 324, 324, 324, 324, 324, 324, 442, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits552
private theorem actualStart552 : startFrames[552]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd552 : finalFrames[552]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid552 : forwardPathValid 552 = true := by
  rw [forwardPathValid, actualVisits552, actualStart552, actualEnd552]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_163, canClimb_163_324, canClimb_324_442, canClimb_442_1, Bool.true_and]

private theorem actualVisits553 : eventVisits 553 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 164, 302, 302, 403, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits553
private theorem actualStart553 : startFrames[553]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd553 : finalFrames[553]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid553 : forwardPathValid 553 = true := by
  rw [forwardPathValid, actualVisits553, actualStart553, actualEnd553]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_164, canClimb_164_302, canClimb_302_403, canClimb_403_1, Bool.true_and]

private theorem actualVisits554 : eventVisits 554 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 165, 306, 306, 306, 306, 306, 306, 306, 306, 306, 420, 420, 547, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits554
private theorem actualStart554 : startFrames[554]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd554 : finalFrames[554]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid554 : forwardPathValid 554 = true := by
  rw [forwardPathValid, actualVisits554, actualStart554, actualEnd554]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_165, canClimb_165_306, canClimb_306_420, canClimb_420_547, canClimb_547_1, Bool.true_and]

private theorem actualVisits555 : eventVisits 555 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 166, 305, 305, 305, 305, 305, 305, 305, 305, 365, 365, 548, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits555
private theorem actualStart555 : startFrames[555]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd555 : finalFrames[555]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid555 : forwardPathValid 555 = true := by
  rw [forwardPathValid, actualVisits555, actualStart555, actualEnd555]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_166, canClimb_166_305, canClimb_305_365, canClimb_365_548, canClimb_548_1, Bool.true_and]

private theorem actualVisits556 : eventVisits 556 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 167, 304, 304, 304, 304, 304, 304, 304, 304, 400, 400, 627, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits556
private theorem actualStart556 : startFrames[556]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd556 : finalFrames[556]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid556 : forwardPathValid 556 = true := by
  rw [forwardPathValid, actualVisits556, actualStart556, actualEnd556]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_167, canClimb_167_304, canClimb_304_400, canClimb_400_627, canClimb_627_1, Bool.true_and]

private theorem actualVisits557 : eventVisits 557 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 168, 303, 303, 303, 303, 303, 303, 399, 399, 619, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits557
private theorem actualStart557 : startFrames[557]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd557 : finalFrames[557]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid557 : forwardPathValid 557 = true := by
  rw [forwardPathValid, actualVisits557, actualStart557, actualEnd557]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_168, canClimb_168_303, canClimb_303_399, canClimb_399_619, canClimb_619_1, Bool.true_and]

private theorem actualVisits558 : eventVisits 558 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 169, 307, 307, 307, 307, 307, 432, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits558
private theorem actualStart558 : startFrames[558]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd558 : finalFrames[558]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid558 : forwardPathValid 558 = true := by
  rw [forwardPathValid, actualVisits558, actualStart558, actualEnd558]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_169, canClimb_169_307, canClimb_307_432, canClimb_432_1, Bool.true_and]

private theorem actualVisits559 : eventVisits 559 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 170, 308, 308, 308, 308, 308, 409, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits559
private theorem actualStart559 : startFrames[559]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd559 : finalFrames[559]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid559 : forwardPathValid 559 = true := by
  rw [forwardPathValid, actualVisits559, actualStart559, actualEnd559]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_170, canClimb_170_308, canClimb_308_409, canClimb_409_1, Bool.true_and]

theorem forwardPathBlock069 (f : Nat) (hl : 552 ≤ f) (hu : f < 560) : forwardPathValid f = true := by
  have hs : f = 552 ∨ f = 553 ∨ f = 554 ∨ f = 555 ∨ f = 556 ∨ f = 557 ∨ f = 558 ∨ f = 559 := by omega
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact forwardPathValid552
  · exact forwardPathValid553
  · exact forwardPathValid554
  · exact forwardPathValid555
  · exact forwardPathValid556
  · exact forwardPathValid557
  · exact forwardPathValid558
  · exact forwardPathValid559

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

attribute [local irreducible] canClimb
private theorem actualVisits560 : eventVisits 560 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 171, 312, 312, 312, 312, 312, 445, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits560
private theorem actualStart560 : startFrames[560]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd560 : finalFrames[560]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid560 : forwardPathValid 560 = true := by
  rw [forwardPathValid, actualVisits560, actualStart560, actualEnd560]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_171, canClimb_171_312, canClimb_312_445, canClimb_445_1, Bool.true_and]

private theorem actualVisits561 : eventVisits 561 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 172, 311, 311, 311, 311, 311, 388, 388, 560, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits561
private theorem actualStart561 : startFrames[561]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd561 : finalFrames[561]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid561 : forwardPathValid 561 = true := by
  rw [forwardPathValid, actualVisits561, actualStart561, actualEnd561]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_172, canClimb_172_311, canClimb_311_388, canClimb_388_560, canClimb_560_1, Bool.true_and]

private theorem actualVisits562 : eventVisits 562 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 173, 310, 310, 310, 310, 310, 310, 406, 406, 609, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits562
private theorem actualStart562 : startFrames[562]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd562 : finalFrames[562]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid562 : forwardPathValid 562 = true := by
  rw [forwardPathValid, actualVisits562, actualStart562, actualEnd562]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_173, canClimb_173_310, canClimb_310_406, canClimb_406_609, canClimb_609_1, Bool.true_and]

private theorem actualVisits563 : eventVisits 563 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 174, 309, 309, 309, 309, 309, 405, 405, 605, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits563
private theorem actualStart563 : startFrames[563]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd563 : finalFrames[563]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid563 : forwardPathValid 563 = true := by
  rw [forwardPathValid, actualVisits563, actualStart563, actualEnd563]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_174, canClimb_174_309, canClimb_309_405, canClimb_405_605, canClimb_605_1, Bool.true_and]

private theorem actualVisits564 : eventVisits 564 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 175, 313, 313, 313, 404, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits564
private theorem actualStart564 : startFrames[564]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd564 : finalFrames[564]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid564 : forwardPathValid 564 = true := by
  rw [forwardPathValid, actualVisits564, actualStart564, actualEnd564]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_175, canClimb_175_313, canClimb_313_404, canClimb_404_1, Bool.true_and]

private theorem actualVisits565 : eventVisits 565 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 176, 314, 314, 314, 314, 314, 450, 450, 567, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits565
private theorem actualStart565 : startFrames[565]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd565 : finalFrames[565]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid565 : forwardPathValid 565 = true := by
  rw [forwardPathValid, actualVisits565, actualStart565, actualEnd565]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_176, canClimb_176_314, canClimb_314_450, canClimb_450_567, canClimb_567_1, Bool.true_and]

private theorem actualVisits566 : eventVisits 566 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 177, 315, 315, 315, 414, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits566
private theorem actualStart566 : startFrames[566]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd566 : finalFrames[566]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid566 : forwardPathValid 566 = true := by
  rw [forwardPathValid, actualVisits566, actualStart566, actualEnd566]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_177, canClimb_177_315, canClimb_315_414, canClimb_414_1, Bool.true_and]

private theorem actualVisits567 : eventVisits 567 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 178, 316, 316, 316, 316, 316, 413, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits567
private theorem actualStart567 : startFrames[567]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd567 : finalFrames[567]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid567 : forwardPathValid 567 = true := by
  rw [forwardPathValid, actualVisits567, actualStart567, actualEnd567]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_178, canClimb_178_316, canClimb_316_413, canClimb_413_1, Bool.true_and]

theorem forwardPathBlock070 (f : Nat) (hl : 560 ≤ f) (hu : f < 568) : forwardPathValid f = true := by
  have hs : f = 560 ∨ f = 561 ∨ f = 562 ∨ f = 563 ∨ f = 564 ∨ f = 565 ∨ f = 566 ∨ f = 567 := by omega
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact forwardPathValid560
  · exact forwardPathValid561
  · exact forwardPathValid562
  · exact forwardPathValid563
  · exact forwardPathValid564
  · exact forwardPathValid565
  · exact forwardPathValid566
  · exact forwardPathValid567

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

attribute [local irreducible] canClimb
private theorem actualVisits568 : eventVisits 568 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 179, 317, 317, 317, 317, 317, 317, 317, 459, 459, 624, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits568
private theorem actualStart568 : startFrames[568]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd568 : finalFrames[568]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid568 : forwardPathValid 568 = true := by
  rw [forwardPathValid, actualVisits568, actualStart568, actualEnd568]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_179, canClimb_179_317, canClimb_317_459, canClimb_459_624, canClimb_624_1, Bool.true_and]

private theorem actualVisits569 : eventVisits 569 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 180, 318, 318, 318, 318, 318, 380, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits569
private theorem actualStart569 : startFrames[569]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd569 : finalFrames[569]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid569 : forwardPathValid 569 = true := by
  rw [forwardPathValid, actualVisits569, actualStart569, actualEnd569]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_180, canClimb_180_318, canClimb_318_380, canClimb_380_1, Bool.true_and]

private theorem actualVisits570 : eventVisits 570 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 181, 319, 319, 319, 319, 319, 379, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits570
private theorem actualStart570 : startFrames[570]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd570 : finalFrames[570]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid570 : forwardPathValid 570 = true := by
  rw [forwardPathValid, actualVisits570, actualStart570, actualEnd570]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_181, canClimb_181_319, canClimb_319_379, canClimb_379_1, Bool.true_and]

private theorem actualVisits571 : eventVisits 571 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 182, 318, 318, 318, 318, 318, 318, 318, 444, 444, 559, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits571
private theorem actualStart571 : startFrames[571]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd571 : finalFrames[571]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid571 : forwardPathValid 571 = true := by
  rw [forwardPathValid, actualVisits571, actualStart571, actualEnd571]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_182, canClimb_182_318, canClimb_318_444, canClimb_444_559, canClimb_559_1, Bool.true_and]

private theorem actualVisits572 : eventVisits 572 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 183, 306, 306, 306, 306, 306, 306, 306, 306, 452, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits572
private theorem actualStart572 : startFrames[572]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd572 : finalFrames[572]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid572 : forwardPathValid 572 = true := by
  rw [forwardPathValid, actualVisits572, actualStart572, actualEnd572]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_183, canClimb_183_306, canClimb_306_452, canClimb_452_1, Bool.true_and]

private theorem actualVisits573 : eventVisits 573 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 19, 321, 321, 321, 321, 321, 321, 321, 321, 383, 383, 552, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits573
private theorem actualStart573 : startFrames[573]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd573 : finalFrames[573]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid573 : forwardPathValid 573 = true := by
  rw [forwardPathValid, actualVisits573, actualStart573, actualEnd573]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_19, canClimb_19_321, canClimb_321_383, canClimb_383_552, canClimb_552_1, Bool.true_and]

private theorem actualVisits574 : eventVisits 574 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 184, 320, 320, 320, 320, 320, 320, 320, 320, 382, 382, 622, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits574
private theorem actualStart574 : startFrames[574]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd574 : finalFrames[574]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid574 : forwardPathValid 574 = true := by
  rw [forwardPathValid, actualVisits574, actualStart574, actualEnd574]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_184, canClimb_184_320, canClimb_320_382, canClimb_382_622, canClimb_622_1, Bool.true_and]

private theorem actualVisits575 : eventVisits 575 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24, 303, 303, 303, 303, 303, 303, 457, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits575
private theorem actualStart575 : startFrames[575]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd575 : finalFrames[575]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid575 : forwardPathValid 575 = true := by
  rw [forwardPathValid, actualVisits575, actualStart575, actualEnd575]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_24, canClimb_24_303, canClimb_303_457, canClimb_457_1, Bool.true_and]

theorem forwardPathBlock071 (f : Nat) (hl : 568 ≤ f) (hu : f < 576) : forwardPathValid f = true := by
  have hs : f = 568 ∨ f = 569 ∨ f = 570 ∨ f = 571 ∨ f = 572 ∨ f = 573 ∨ f = 574 ∨ f = 575 := by omega
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact forwardPathValid568
  · exact forwardPathValid569
  · exact forwardPathValid570
  · exact forwardPathValid571
  · exact forwardPathValid572
  · exact forwardPathValid573
  · exact forwardPathValid574
  · exact forwardPathValid575

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

attribute [local irreducible] canClimb
private theorem actualVisits576 : eventVisits 576 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 94, 315, 315, 315, 315, 315, 441, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits576
private theorem actualStart576 : startFrames[576]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd576 : finalFrames[576]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid576 : forwardPathValid 576 = true := by
  rw [forwardPathValid, actualVisits576, actualStart576, actualEnd576]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_94, canClimb_94_315, canClimb_315_441, canClimb_441_1, Bool.true_and]

private theorem actualVisits577 : eventVisits 577 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 185, 316, 316, 316, 316, 316, 316, 462, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits577
private theorem actualStart577 : startFrames[577]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd577 : finalFrames[577]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid577 : forwardPathValid 577 = true := by
  rw [forwardPathValid, actualVisits577, actualStart577, actualEnd577]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_185, canClimb_185_316, canClimb_316_462, canClimb_462_1, Bool.true_and]

private theorem actualVisits578 : eventVisits 578 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 186, 323, 323, 323, 323, 323, 446, 446, 564, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits578
private theorem actualStart578 : startFrames[578]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd578 : finalFrames[578]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid578 : forwardPathValid 578 = true := by
  rw [forwardPathValid, actualVisits578, actualStart578, actualEnd578]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_186, canClimb_186_323, canClimb_323_446, canClimb_446_564, canClimb_564_1, Bool.true_and]

private theorem actualVisits579 : eventVisits 579 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 187, 310, 310, 310, 310, 310, 310, 439, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits579
private theorem actualStart579 : startFrames[579]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd579 : finalFrames[579]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid579 : forwardPathValid 579 = true := by
  rw [forwardPathValid, actualVisits579, actualStart579, actualEnd579]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_187, canClimb_187_310, canClimb_310_439, canClimb_439_1, Bool.true_and]

private theorem actualVisits580 : eventVisits 580 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 188, 311, 311, 311, 311, 311, 311, 311, 311, 434, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits580
private theorem actualStart580 : startFrames[580]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd580 : finalFrames[580]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid580 : forwardPathValid 580 = true := by
  rw [forwardPathValid, actualVisits580, actualStart580, actualEnd580]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_188, canClimb_188_311, canClimb_311_434, canClimb_434_1, Bool.true_and]

private theorem actualVisits581 : eventVisits 581 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 189, 322, 322, 322, 322, 322, 423, 423, 558, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits581
private theorem actualStart581 : startFrames[581]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd581 : finalFrames[581]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid581 : forwardPathValid 581 = true := by
  rw [forwardPathValid, actualVisits581, actualStart581, actualEnd581]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_189, canClimb_189_322, canClimb_322_423, canClimb_423_558, canClimb_558_1, Bool.true_and]

private theorem actualVisits582 : eventVisits 582 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 190, 317, 317, 317, 317, 317, 422, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits582
private theorem actualStart582 : startFrames[582]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd582 : finalFrames[582]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid582 : forwardPathValid 582 = true := by
  rw [forwardPathValid, actualVisits582, actualStart582, actualEnd582]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_190, canClimb_190_317, canClimb_317_422, canClimb_422_1, Bool.true_and]

private theorem actualVisits583 : eventVisits 583 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 52, 324, 324, 324, 324, 324, 433, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits583
private theorem actualStart583 : startFrames[583]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd583 : finalFrames[583]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid583 : forwardPathValid 583 = true := by
  rw [forwardPathValid, actualVisits583, actualStart583, actualEnd583]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_52, canClimb_52_324, canClimb_324_433, canClimb_433_1, Bool.true_and]

theorem forwardPathBlock072 (f : Nat) (hl : 576 ≤ f) (hu : f < 584) : forwardPathValid f = true := by
  have hs : f = 576 ∨ f = 577 ∨ f = 578 ∨ f = 579 ∨ f = 580 ∨ f = 581 ∨ f = 582 ∨ f = 583 := by omega
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact forwardPathValid576
  · exact forwardPathValid577
  · exact forwardPathValid578
  · exact forwardPathValid579
  · exact forwardPathValid580
  · exact forwardPathValid581
  · exact forwardPathValid582
  · exact forwardPathValid583

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

attribute [local irreducible] canClimb
private theorem actualVisits584 : eventVisits 584 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 191, 307, 307, 307, 307, 307, 307, 307, 398, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits584
private theorem actualStart584 : startFrames[584]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd584 : finalFrames[584]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid584 : forwardPathValid 584 = true := by
  rw [forwardPathValid, actualVisits584, actualStart584, actualEnd584]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_191, canClimb_191_307, canClimb_307_398, canClimb_398_1, Bool.true_and]

private theorem actualVisits585 : eventVisits 585 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 192, 308, 308, 431, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits585
private theorem actualStart585 : startFrames[585]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd585 : finalFrames[585]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid585 : forwardPathValid 585 = true := by
  rw [forwardPathValid, actualVisits585, actualStart585, actualEnd585]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_192, canClimb_192_308, canClimb_308_431, canClimb_431_1, Bool.true_and]

private theorem actualVisits586 : eventVisits 586 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 62, 313, 313, 313, 313, 313, 467, 467, 553, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits586
private theorem actualStart586 : startFrames[586]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd586 : finalFrames[586]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid586 : forwardPathValid 586 = true := by
  rw [forwardPathValid, actualVisits586, actualStart586, actualEnd586]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_62, canClimb_62_313, canClimb_313_467, canClimb_467_553, canClimb_553_1, Bool.true_and]

private theorem actualVisits587 : eventVisits 587 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 69, 302, 302, 302, 302, 302, 302, 302, 429, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits587
private theorem actualStart587 : startFrames[587]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd587 : finalFrames[587]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid587 : forwardPathValid 587 = true := by
  rw [forwardPathValid, actualVisits587, actualStart587, actualEnd587]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_69, canClimb_69_302, canClimb_302_429, canClimb_429_1, Bool.true_and]

private theorem actualVisits588 : eventVisits 588 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 193, 325, 325, 325, 325, 325, 443, 443, 608, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits588
private theorem actualStart588 : startFrames[588]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd588 : finalFrames[588]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid588 : forwardPathValid 588 = true := by
  rw [forwardPathValid, actualVisits588, actualStart588, actualEnd588]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_193, canClimb_193_325, canClimb_325_443, canClimb_443_608, canClimb_608_1, Bool.true_and]

private theorem actualVisits589 : eventVisits 589 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 194, 310, 310, 310, 310, 310, 310, 310, 425, 425, 602, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits589
private theorem actualStart589 : startFrames[589]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd589 : finalFrames[589]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid589 : forwardPathValid 589 = true := by
  rw [forwardPathValid, actualVisits589, actualStart589, actualEnd589]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_194, canClimb_194_310, canClimb_310_425, canClimb_425_602, canClimb_602_1, Bool.true_and]

private theorem actualVisits590 : eventVisits 590 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 195, 321, 321, 321, 321, 321, 321, 321, 469, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits590
private theorem actualStart590 : startFrames[590]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd590 : finalFrames[590]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid590 : forwardPathValid 590 = true := by
  rw [forwardPathValid, actualVisits590, actualStart590, actualEnd590]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_195, canClimb_195_321, canClimb_321_469, canClimb_469_1, Bool.true_and]

private theorem actualVisits591 : eventVisits 591 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 196, 304, 304, 304, 304, 304, 304, 304, 458, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits591
private theorem actualStart591 : startFrames[591]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd591 : finalFrames[591]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid591 : forwardPathValid 591 = true := by
  rw [forwardPathValid, actualVisits591, actualStart591, actualEnd591]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_196, canClimb_196_304, canClimb_304_458, canClimb_458_1, Bool.true_and]

theorem forwardPathBlock073 (f : Nat) (hl : 584 ≤ f) (hu : f < 592) : forwardPathValid f = true := by
  have hs : f = 584 ∨ f = 585 ∨ f = 586 ∨ f = 587 ∨ f = 588 ∨ f = 589 ∨ f = 590 ∨ f = 591 := by omega
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact forwardPathValid584
  · exact forwardPathValid585
  · exact forwardPathValid586
  · exact forwardPathValid587
  · exact forwardPathValid588
  · exact forwardPathValid589
  · exact forwardPathValid590
  · exact forwardPathValid591

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

attribute [local irreducible] canClimb
private theorem actualVisits592 : eventVisits 592 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 197, 305, 305, 305, 305, 305, 305, 463, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits592
private theorem actualStart592 : startFrames[592]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd592 : finalFrames[592]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid592 : forwardPathValid 592 = true := by
  rw [forwardPathValid, actualVisits592, actualStart592, actualEnd592]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_197, canClimb_197_305, canClimb_305_463, canClimb_463_1, Bool.true_and]

private theorem actualVisits593 : eventVisits 593 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 198, 320, 320, 320, 320, 320, 320, 320, 464, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits593
private theorem actualStart593 : startFrames[593]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd593 : finalFrames[593]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid593 : forwardPathValid 593 = true := by
  rw [forwardPathValid, actualVisits593, actualStart593, actualEnd593]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_198, canClimb_198_320, canClimb_320_464, canClimb_464_1, Bool.true_and]

private theorem actualVisits594 : eventVisits 594 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 199, 311, 311, 311, 311, 311, 311, 311, 311, 424, 424, 558, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits594
private theorem actualStart594 : startFrames[594]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd594 : finalFrames[594]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid594 : forwardPathValid 594 = true := by
  rw [forwardPathValid, actualVisits594, actualStart594, actualEnd594]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_199, canClimb_199_311, canClimb_311_424, canClimb_424_558, canClimb_558_1, Bool.true_and]

private theorem actualVisits595 : eventVisits 595 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 200, 312, 312, 312, 312, 312, 312, 312, 312, 372, 372, 607, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits595
private theorem actualStart595 : startFrames[595]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd595 : finalFrames[595]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid595 : forwardPathValid 595 = true := by
  rw [forwardPathValid, actualVisits595, actualStart595, actualEnd595]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_200, canClimb_200_312, canClimb_312_372, canClimb_372_607, canClimb_607_1, Bool.true_and]

private theorem actualVisits596 : eventVisits 596 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 201, 318, 318, 318, 318, 318, 318, 318, 421, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits596
private theorem actualStart596 : startFrames[596]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd596 : finalFrames[596]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid596 : forwardPathValid 596 = true := by
  rw [forwardPathValid, actualVisits596, actualStart596, actualEnd596]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_201, canClimb_201_318, canClimb_318_421, canClimb_421_1, Bool.true_and]

private theorem actualVisits597 : eventVisits 597 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 202, 325, 325, 325, 325, 325, 397, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits597
private theorem actualStart597 : startFrames[597]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd597 : finalFrames[597]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid597 : forwardPathValid 597 = true := by
  rw [forwardPathValid, actualVisits597, actualStart597, actualEnd597]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_202, canClimb_202_325, canClimb_325_397, canClimb_397_1, Bool.true_and]

private theorem actualVisits598 : eventVisits 598 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 203, 324, 324, 324, 324, 324, 324, 392, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits598
private theorem actualStart598 : startFrames[598]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd598 : finalFrames[598]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid598 : forwardPathValid 598 = true := by
  rw [forwardPathValid, actualVisits598, actualStart598, actualEnd598]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_203, canClimb_203_324, canClimb_324_392, canClimb_392_1, Bool.true_and]

private theorem actualVisits599 : eventVisits 599 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 204, 315, 315, 315, 315, 315, 315, 416, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits599
private theorem actualStart599 : startFrames[599]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd599 : finalFrames[599]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid599 : forwardPathValid 599 = true := by
  rw [forwardPathValid, actualVisits599, actualStart599, actualEnd599]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_204, canClimb_204_315, canClimb_315_416, canClimb_416_1, Bool.true_and]

theorem forwardPathBlock074 (f : Nat) (hl : 592 ≤ f) (hu : f < 600) : forwardPathValid f = true := by
  have hs : f = 592 ∨ f = 593 ∨ f = 594 ∨ f = 595 ∨ f = 596 ∨ f = 597 ∨ f = 598 ∨ f = 599 := by omega
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact forwardPathValid592
  · exact forwardPathValid593
  · exact forwardPathValid594
  · exact forwardPathValid595
  · exact forwardPathValid596
  · exact forwardPathValid597
  · exact forwardPathValid598
  · exact forwardPathValid599

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

attribute [local irreducible] canClimb
private theorem actualVisits600 : eventVisits 600 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 205, 309, 309, 309, 309, 309, 309, 309, 369, 369, 600, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits600
private theorem actualStart600 : startFrames[600]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd600 : finalFrames[600]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid600 : forwardPathValid 600 = true := by
  rw [forwardPathValid, actualVisits600, actualStart600, actualEnd600]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_205, canClimb_205_309, canClimb_309_369, canClimb_369_600, canClimb_600_1, Bool.true_and]

private theorem actualVisits601 : eventVisits 601 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 206, 322, 322, 322, 322, 322, 322, 387, 387, 560, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits601
private theorem actualStart601 : startFrames[601]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd601 : finalFrames[601]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid601 : forwardPathValid 601 = true := by
  rw [forwardPathValid, actualVisits601, actualStart601, actualEnd601]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_206, canClimb_206_322, canClimb_322_387, canClimb_387_560, canClimb_560_1, Bool.true_and]

private theorem actualVisits602 : eventVisits 602 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 207, 314, 314, 314, 314, 314, 415, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits602
private theorem actualStart602 : startFrames[602]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd602 : finalFrames[602]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid602 : forwardPathValid 602 = true := by
  rw [forwardPathValid, actualVisits602, actualStart602, actualEnd602]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_207, canClimb_207_314, canClimb_314_415, canClimb_415_1, Bool.true_and]

private theorem actualVisits603 : eventVisits 603 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 208, 307, 307, 307, 307, 307, 449, 449, 567, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits603
private theorem actualStart603 : startFrames[603]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd603 : finalFrames[603]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid603 : forwardPathValid 603 = true := by
  rw [forwardPathValid, actualVisits603, actualStart603, actualEnd603]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_208, canClimb_208_307, canClimb_307_449, canClimb_449_567, canClimb_567_1, Bool.true_and]

private theorem actualVisits604 : eventVisits 604 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 209, 302, 302, 302, 302, 302, 448, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits604
private theorem actualStart604 : startFrames[604]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd604 : finalFrames[604]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid604 : forwardPathValid 604 = true := by
  rw [forwardPathValid, actualVisits604, actualStart604, actualEnd604]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_209, canClimb_209_302, canClimb_302_448, canClimb_448_1, Bool.true_and]

private theorem actualVisits605 : eventVisits 605 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 210, 319, 319, 319, 319, 319, 319, 319, 410, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits605
private theorem actualStart605 : startFrames[605]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd605 : finalFrames[605]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid605 : forwardPathValid 605 = true := by
  rw [forwardPathValid, actualVisits605, actualStart605, actualEnd605]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_210, canClimb_210_319, canClimb_319_410, canClimb_410_1, Bool.true_and]

private theorem actualVisits606 : eventVisits 606 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 211, 323, 323, 323, 323, 323, 323, 323, 390, 390, 568, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits606
private theorem actualStart606 : startFrames[606]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd606 : finalFrames[606]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid606 : forwardPathValid 606 = true := by
  rw [forwardPathValid, actualVisits606, actualStart606, actualEnd606]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_211, canClimb_211_323, canClimb_323_390, canClimb_390_568, canClimb_568_1, Bool.true_and]

private theorem actualVisits607 : eventVisits 607 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 212, 303, 303, 303, 303, 303, 303, 303, 417, 417, 542, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits607
private theorem actualStart607 : startFrames[607]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd607 : finalFrames[607]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid607 : forwardPathValid 607 = true := by
  rw [forwardPathValid, actualVisits607, actualStart607, actualEnd607]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_212, canClimb_212_303, canClimb_303_417, canClimb_417_542, canClimb_542_1, Bool.true_and]

theorem forwardPathBlock075 (f : Nat) (hl : 600 ≤ f) (hu : f < 608) : forwardPathValid f = true := by
  have hs : f = 600 ∨ f = 601 ∨ f = 602 ∨ f = 603 ∨ f = 604 ∨ f = 605 ∨ f = 606 ∨ f = 607 := by omega
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact forwardPathValid600
  · exact forwardPathValid601
  · exact forwardPathValid602
  · exact forwardPathValid603
  · exact forwardPathValid604
  · exact forwardPathValid605
  · exact forwardPathValid606
  · exact forwardPathValid607

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

attribute [local irreducible] canClimb
private theorem actualVisits608 : eventVisits 608 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 213, 323, 323, 323, 323, 323, 323, 456, 456, 532, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits608
private theorem actualStart608 : startFrames[608]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd608 : finalFrames[608]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid608 : forwardPathValid 608 = true := by
  rw [forwardPathValid, actualVisits608, actualStart608, actualEnd608]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_213, canClimb_213_323, canClimb_323_456, canClimb_456_532, canClimb_532_1, Bool.true_and]

private theorem actualVisits609 : eventVisits 609 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 214, 312, 312, 312, 312, 312, 312, 312, 472, 472, 527, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits609
private theorem actualStart609 : startFrames[609]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd609 : finalFrames[609]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid609 : forwardPathValid 609 = true := by
  rw [forwardPathValid, actualVisits609, actualStart609, actualEnd609]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_214, canClimb_214_312, canClimb_312_472, canClimb_472_527, canClimb_527_1, Bool.true_and]

private theorem actualVisits610 : eventVisits 610 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 215, 309, 309, 309, 309, 309, 309, 505, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits610
private theorem actualStart610 : startFrames[610]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd610 : finalFrames[610]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid610 : forwardPathValid 610 = true := by
  rw [forwardPathValid, actualVisits610, actualStart610, actualEnd610]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_215, canClimb_215_309, canClimb_309_505, canClimb_505_1, Bool.true_and]

private theorem actualVisits611 : eventVisits 611 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 216, 322, 322, 322, 322, 322, 322, 474, 474, 634, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits611
private theorem actualStart611 : startFrames[611]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd611 : finalFrames[611]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid611 : forwardPathValid 611 = true := by
  rw [forwardPathValid, actualVisits611, actualStart611, actualEnd611]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_216, canClimb_216_322, canClimb_322_474, canClimb_474_634, canClimb_634_1, Bool.true_and]

private theorem actualVisits612 : eventVisits 612 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 217, 306, 306, 306, 306, 306, 306, 306, 402, 402, 551, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits612
private theorem actualStart612 : startFrames[612]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd612 : finalFrames[612]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid612 : forwardPathValid 612 = true := by
  rw [forwardPathValid, actualVisits612, actualStart612, actualEnd612]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_217, canClimb_217_306, canClimb_306_402, canClimb_402_551, canClimb_551_1, Bool.true_and]

private theorem actualVisits613 : eventVisits 613 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 218, 305, 305, 305, 305, 305, 305, 305, 436, 436, 535, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits613
private theorem actualStart613 : startFrames[613]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd613 : finalFrames[613]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid613 : forwardPathValid 613 = true := by
  rw [forwardPathValid, actualVisits613, actualStart613, actualEnd613]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_218, canClimb_218_305, canClimb_305_436, canClimb_436_535, canClimb_535_1, Bool.true_and]

private theorem actualVisits614 : eventVisits 614 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 219, 316, 316, 316, 316, 316, 316, 316, 427, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits614
private theorem actualStart614 : startFrames[614]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd614 : finalFrames[614]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid614 : forwardPathValid 614 = true := by
  rw [forwardPathValid, actualVisits614, actualStart614, actualEnd614]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_219, canClimb_219_316, canClimb_316_427, canClimb_427_1, Bool.true_and]

private theorem actualVisits615 : eventVisits 615 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 220, 325, 325, 325, 325, 325, 325, 325, 461, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits615
private theorem actualStart615 : startFrames[615]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd615 : finalFrames[615]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid615 : forwardPathValid 615 = true := by
  rw [forwardPathValid, actualVisits615, actualStart615, actualEnd615]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_220, canClimb_220_325, canClimb_325_461, canClimb_461_1, Bool.true_and]

theorem forwardPathBlock076 (f : Nat) (hl : 608 ≤ f) (hu : f < 616) : forwardPathValid f = true := by
  have hs : f = 608 ∨ f = 609 ∨ f = 610 ∨ f = 611 ∨ f = 612 ∨ f = 613 ∨ f = 614 ∨ f = 615 := by omega
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact forwardPathValid608
  · exact forwardPathValid609
  · exact forwardPathValid610
  · exact forwardPathValid611
  · exact forwardPathValid612
  · exact forwardPathValid613
  · exact forwardPathValid614
  · exact forwardPathValid615

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

attribute [local irreducible] canClimb
private theorem actualVisits616 : eventVisits 616 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 221, 324, 324, 324, 324, 324, 324, 324, 460, 460, 549, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits616
private theorem actualStart616 : startFrames[616]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd616 : finalFrames[616]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid616 : forwardPathValid 616 = true := by
  rw [forwardPathValid, actualVisits616, actualStart616, actualEnd616]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_221, canClimb_221_324, canClimb_324_460, canClimb_460_549, canClimb_549_1, Bool.true_and]

private theorem actualVisits617 : eventVisits 617 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 222, 317, 317, 317, 317, 317, 317, 412, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits617
private theorem actualStart617 : startFrames[617]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd617 : finalFrames[617]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid617 : forwardPathValid 617 = true := by
  rw [forwardPathValid, actualVisits617, actualStart617, actualEnd617]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_222, canClimb_222_317, canClimb_317_412, canClimb_412_1, Bool.true_and]

private theorem actualVisits618 : eventVisits 618 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 223, 304, 304, 304, 304, 304, 304, 437, 437, 629, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits618
private theorem actualStart618 : startFrames[618]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd618 : finalFrames[618]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid618 : forwardPathValid 618 = true := by
  rw [forwardPathValid, actualVisits618, actualStart618, actualEnd618]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_223, canClimb_223_304, canClimb_304_437, canClimb_437_629, canClimb_629_1, Bool.true_and]

private theorem actualVisits619 : eventVisits 619 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 224, 321, 321, 321, 321, 321, 321, 321, 438, 438, 632, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits619
private theorem actualStart619 : startFrames[619]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd619 : finalFrames[619]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid619 : forwardPathValid 619 = true := by
  rw [forwardPathValid, actualVisits619, actualStart619, actualEnd619]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_224, canClimb_224_321, canClimb_321_438, canClimb_438_632, canClimb_632_1, Bool.true_and]

private theorem actualVisits620 : eventVisits 620 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 225, 314, 314, 314, 314, 314, 314, 468, 468, 553, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits620
private theorem actualStart620 : startFrames[620]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd620 : finalFrames[620]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid620 : forwardPathValid 620 = true := by
  rw [forwardPathValid, actualVisits620, actualStart620, actualEnd620]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_225, canClimb_225_314, canClimb_314_468, canClimb_468_553, canClimb_553_1, Bool.true_and]

private theorem actualVisits621 : eventVisits 621 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 226, 313, 313, 313, 313, 313, 313, 430, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits621
private theorem actualStart621 : startFrames[621]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd621 : finalFrames[621]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid621 : forwardPathValid 621 = true := by
  rw [forwardPathValid, actualVisits621, actualStart621, actualEnd621]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_226, canClimb_226_313, canClimb_313_430, canClimb_430_1, Bool.true_and]

private theorem actualVisits622 : eventVisits 622 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 227, 308, 308, 308, 308, 308, 478, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits622
private theorem actualStart622 : startFrames[622]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd622 : finalFrames[622]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid622 : forwardPathValid 622 = true := by
  rw [forwardPathValid, actualVisits622, actualStart622, actualEnd622]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_227, canClimb_227_308, canClimb_308_478, canClimb_478_1, Bool.true_and]

private theorem actualVisits623 : eventVisits 623 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 228, 319, 319, 319, 319, 319, 319, 495, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits623
private theorem actualStart623 : startFrames[623]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd623 : finalFrames[623]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid623 : forwardPathValid 623 = true := by
  rw [forwardPathValid, actualVisits623, actualStart623, actualEnd623]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_228, canClimb_228_319, canClimb_319_495, canClimb_495_1, Bool.true_and]

theorem forwardPathBlock077 (f : Nat) (hl : 616 ≤ f) (hu : f < 624) : forwardPathValid f = true := by
  have hs : f = 616 ∨ f = 617 ∨ f = 618 ∨ f = 619 ∨ f = 620 ∨ f = 621 ∨ f = 622 ∨ f = 623 := by omega
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact forwardPathValid616
  · exact forwardPathValid617
  · exact forwardPathValid618
  · exact forwardPathValid619
  · exact forwardPathValid620
  · exact forwardPathValid621
  · exact forwardPathValid622
  · exact forwardPathValid623

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

attribute [local irreducible] canClimb
private theorem actualVisits624 : eventVisits 624 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 229, 320, 320, 320, 320, 320, 320, 435, 435, 535, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits624
private theorem actualStart624 : startFrames[624]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd624 : finalFrames[624]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid624 : forwardPathValid 624 = true := by
  rw [forwardPathValid, actualVisits624, actualStart624, actualEnd624]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_229, canClimb_229_320, canClimb_320_435, canClimb_435_535, canClimb_535_1, Bool.true_and]

private theorem actualVisits625 : eventVisits 625 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 230, 306, 306, 306, 306, 306, 306, 306, 306, 306, 475, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits625
private theorem actualStart625 : startFrames[625]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd625 : finalFrames[625]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid625 : forwardPathValid 625 = true := by
  rw [forwardPathValid, actualVisits625, actualStart625, actualEnd625]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_230, canClimb_230_306, canClimb_306_475, canClimb_475_1, Bool.true_and]

private theorem actualVisits626 : eventVisits 626 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 231, 322, 322, 322, 322, 322, 322, 453, 453, 526, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits626
private theorem actualStart626 : startFrames[626]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd626 : finalFrames[626]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid626 : forwardPathValid 626 = true := by
  rw [forwardPathValid, actualVisits626, actualStart626, actualEnd626]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_231, canClimb_231_322, canClimb_322_453, canClimb_453_526, canClimb_526_1, Bool.true_and]

private theorem actualVisits627 : eventVisits 627 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 232, 309, 309, 309, 309, 309, 309, 309, 454, 454, 633, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits627
private theorem actualStart627 : startFrames[627]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd627 : finalFrames[627]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid627 : forwardPathValid 627 = true := by
  rw [forwardPathValid, actualVisits627, actualStart627, actualEnd627]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_232, canClimb_232_309, canClimb_309_454, canClimb_454_633, canClimb_633_1, Bool.true_and]

private theorem actualVisits628 : eventVisits 628 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 233, 312, 312, 312, 312, 312, 312, 312, 500, 500, 570, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits628
private theorem actualStart628 : startFrames[628]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd628 : finalFrames[628]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid628 : forwardPathValid 628 = true := by
  rw [forwardPathValid, actualVisits628, actualStart628, actualEnd628]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_233, canClimb_233_312, canClimb_312_500, canClimb_500_570, canClimb_570_1, Bool.true_and]

private theorem actualVisits629 : eventVisits 629 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 234, 323, 323, 323, 323, 323, 323, 471, 471, 628, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits629
private theorem actualStart629 : startFrames[629]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd629 : finalFrames[629]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid629 : forwardPathValid 629 = true := by
  rw [forwardPathValid, actualVisits629, actualStart629, actualEnd629]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_234, canClimb_234_323, canClimb_323_471, canClimb_471_628, canClimb_628_1, Bool.true_and]

private theorem actualVisits630 : eventVisits 630 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 235, 303, 303, 303, 303, 303, 303, 303, 303, 470, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits630
private theorem actualStart630 : startFrames[630]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd630 : finalFrames[630]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid630 : forwardPathValid 630 = true := by
  rw [forwardPathValid, actualVisits630, actualStart630, actualEnd630]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_235, canClimb_235_303, canClimb_303_470, canClimb_470_1, Bool.true_and]

private theorem actualVisits631 : eventVisits 631 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 236, 320, 320, 320, 320, 320, 320, 481, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits631
private theorem actualStart631 : startFrames[631]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd631 : finalFrames[631]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid631 : forwardPathValid 631 = true := by
  rw [forwardPathValid, actualVisits631, actualStart631, actualEnd631]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_236, canClimb_236_320, canClimb_320_481, canClimb_481_1, Bool.true_and]

theorem forwardPathBlock078 (f : Nat) (hl : 624 ≤ f) (hu : f < 632) : forwardPathValid f = true := by
  have hs : f = 624 ∨ f = 625 ∨ f = 626 ∨ f = 627 ∨ f = 628 ∨ f = 629 ∨ f = 630 ∨ f = 631 := by omega
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact forwardPathValid624
  · exact forwardPathValid625
  · exact forwardPathValid626
  · exact forwardPathValid627
  · exact forwardPathValid628
  · exact forwardPathValid629
  · exact forwardPathValid630
  · exact forwardPathValid631

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

attribute [local irreducible] canClimb
private theorem actualVisits632 : eventVisits 632 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 237, 314, 314, 314, 314, 314, 314, 480, 480, 545, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits632
private theorem actualStart632 : startFrames[632]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd632 : finalFrames[632]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid632 : forwardPathValid 632 = true := by
  rw [forwardPathValid, actualVisits632, actualStart632, actualEnd632]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_237, canClimb_237_314, canClimb_314_480, canClimb_480_545, canClimb_545_1, Bool.true_and]

private theorem actualVisits633 : eventVisits 633 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 238, 313, 313, 313, 313, 313, 313, 313, 479, 479, 545, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits633
private theorem actualStart633 : startFrames[633]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd633 : finalFrames[633]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid633 : forwardPathValid 633 = true := by
  rw [forwardPathValid, actualVisits633, actualStart633, actualEnd633]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_238, canClimb_238_313, canClimb_313_479, canClimb_479_545, canClimb_545_1, Bool.true_and]

private theorem actualVisits634 : eventVisits 634 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 239, 308, 308, 308, 308, 308, 466, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits634
private theorem actualStart634 : startFrames[634]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd634 : finalFrames[634]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid634 : forwardPathValid 634 = true := by
  rw [forwardPathValid, actualVisits634, actualStart634, actualEnd634]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_239, canClimb_239_308, canClimb_308_466, canClimb_466_1, Bool.true_and]

private theorem actualVisits635 : eventVisits 635 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 240, 319, 319, 319, 319, 319, 319, 319, 465, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits635
private theorem actualStart635 : startFrames[635]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd635 : finalFrames[635]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid635 : forwardPathValid 635 = true := by
  rw [forwardPathValid, actualVisits635, actualStart635, actualEnd635]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_240, canClimb_240_319, canClimb_319_465, canClimb_465_1, Bool.true_and]

private theorem actualVisits636 : eventVisits 636 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 241, 321, 321, 321, 321, 321, 321, 321, 476, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits636
private theorem actualStart636 : startFrames[636]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd636 : finalFrames[636]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid636 : forwardPathValid 636 = true := by
  rw [forwardPathValid, actualVisits636, actualStart636, actualEnd636]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_241, canClimb_241_321, canClimb_321_476, canClimb_476_1, Bool.true_and]

private theorem actualVisits637 : eventVisits 637 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 242, 304, 304, 304, 304, 304, 304, 487, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits637
private theorem actualStart637 : startFrames[637]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd637 : finalFrames[637]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid637 : forwardPathValid 637 = true := by
  rw [forwardPathValid, actualVisits637, actualStart637, actualEnd637]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_242, canClimb_242_304, canClimb_304_487, canClimb_487_1, Bool.true_and]

private theorem actualVisits638 : eventVisits 638 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 243, 316, 316, 316, 316, 316, 316, 486, 486, 543, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits638
private theorem actualStart638 : startFrames[638]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd638 : finalFrames[638]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid638 : forwardPathValid 638 = true := by
  rw [forwardPathValid, actualVisits638, actualStart638, actualEnd638]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_243, canClimb_243_316, canClimb_316_486, canClimb_486_543, canClimb_543_1, Bool.true_and]

private theorem actualVisits639 : eventVisits 639 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 244, 325, 325, 325, 325, 325, 325, 485, 485, 543, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits639
private theorem actualStart639 : startFrames[639]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd639 : finalFrames[639]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid639 : forwardPathValid 639 = true := by
  rw [forwardPathValid, actualVisits639, actualStart639, actualEnd639]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_244, canClimb_244_325, canClimb_325_485, canClimb_485_543, canClimb_543_1, Bool.true_and]

theorem forwardPathBlock079 (f : Nat) (hl : 632 ≤ f) (hu : f < 640) : forwardPathValid f = true := by
  have hs : f = 632 ∨ f = 633 ∨ f = 634 ∨ f = 635 ∨ f = 636 ∨ f = 637 ∨ f = 638 ∨ f = 639 := by omega
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact forwardPathValid632
  · exact forwardPathValid633
  · exact forwardPathValid634
  · exact forwardPathValid635
  · exact forwardPathValid636
  · exact forwardPathValid637
  · exact forwardPathValid638
  · exact forwardPathValid639

end CSL.Construction.PhysicalFramePaths


