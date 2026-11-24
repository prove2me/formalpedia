-- Prove2me | Definitions.Def_CSL_Generated_FiniteCircuit_FramePathChecks_Paths_Batch02
-- name    : CSL_Generated_FiniteCircuit_FramePathChecks_Paths_Batch02
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T15:28:39.115998+00:00
-- url     : https://prove2.me/theorems/d4623983-6830-46c0-97b3-9ba70e6f3715
-- title:
--   Coded sorting library: Generated / FiniteCircuit / FramePathChecks / Paths / Batch02
-- statement:
--   Module `CodedSorting.Generated.FiniteCircuit.FramePathChecks.Paths.Batch02` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   Generated physical-frame checks. Uncompiled until a build record exists.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Generated.FiniteCircuit.FramePathChecks.Paths.Batch02

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Generated_FiniteCircuit_FramePathChecks_Nesting_Batch00
import Definitions.Def_CSL_Generated_FiniteCircuit_FramePathChecks_Nesting_Batch01
import Definitions.Def_CSL_Generated_FiniteCircuit_FramePathChecks_Nesting_Batch02
import Definitions.Def_CSL_Generated_FiniteCircuit_FramePathChecks_Nesting_Batch03
import Definitions.Def_CSL_Generated_FiniteCircuit_FramePathChecks_Nesting_Batch04
import Definitions.Def_CSL_Generated_FiniteCircuit_FramePathChecks_Nesting_Batch05
import Definitions.Def_CSL_Generated_FiniteCircuit_FramePathChecks_Nesting_Batch06
import Definitions.Def_CSL_Generated_FiniteCircuit_FramePathChecks_VisitNumbers_Batch02
import Definitions.Def_CSL_Generated_FiniteCircuit_FramePathChecks_VisitNumbers_Bridge

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

attribute [local irreducible] canClimb
private theorem actualVisits256 : eventVisits 256 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 135, 135, 282, 282, 282, 282, 282, 282, 282, 334, 334, 571, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits256
private theorem actualStart256 : startFrames[256]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd256 : finalFrames[256]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid256 : forwardPathValid 256 = true := by
  rw [forwardPathValid, actualVisits256, actualStart256, actualEnd256]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_17, canClimb_17_135, canClimb_135_282, canClimb_282_334, canClimb_334_571, canClimb_571_1, Bool.true_and]

private theorem actualVisits257 : eventVisits 257 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 136, 399, 546, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits257
private theorem actualStart257 : startFrames[257]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd257 : finalFrames[257]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid257 : forwardPathValid 257 = true := by
  rw [forwardPathValid, actualVisits257, actualStart257, actualEnd257]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_17, canClimb_17_136, canClimb_136_399, canClimb_399_546, canClimb_546_1, Bool.true_and]

private theorem actualVisits258 : eventVisits 258 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 242, 242, 268, 268, 268, 268, 268, 268, 268, 268, 268, 268, 487, 487, 618, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits258
private theorem actualStart258 : startFrames[258]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd258 : finalFrames[258]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid258 : forwardPathValid 258 = true := by
  rw [forwardPathValid, actualVisits258, actualStart258, actualEnd258]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_18, canClimb_18_242, canClimb_242_268, canClimb_268_487, canClimb_487_618, canClimb_618_1, Bool.true_and]

private theorem actualVisits259 : eventVisits 259 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 244, 461, 624, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits259
private theorem actualStart259 : startFrames[259]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd259 : finalFrames[259]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid259 : forwardPathValid 259 = true := by
  rw [forwardPathValid, actualVisits259, actualStart259, actualEnd259]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_18, canClimb_18_244, canClimb_244_461, canClimb_461_624, canClimb_624_1, Bool.true_and]

private theorem actualVisits260 : eventVisits 260 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 19, 182, 182, 268, 268, 268, 268, 268, 268, 268, 268, 463, 463, 626, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits260
private theorem actualStart260 : startFrames[260]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd260 : finalFrames[260]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid260 : forwardPathValid 260 = true := by
  rw [forwardPathValid, actualVisits260, actualStart260, actualEnd260]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_19, canClimb_19_182, canClimb_182_268, canClimb_268_463, canClimb_463_626, canClimb_626_1, Bool.true_and]

private theorem actualVisits261 : eventVisits 261 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 19, 19, 280, 280, 280, 280, 280, 280, 280, 408, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits261
private theorem actualStart261 : startFrames[261]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd261 : finalFrames[261]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid261 : forwardPathValid 261 = true := by
  rw [forwardPathValid, actualVisits261, actualStart261, actualEnd261]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_19, canClimb_19_280, canClimb_280_408, canClimb_408_1, Bool.true_and]

private theorem actualVisits262 : eventVisits 262 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20, 245, 245, 299, 299, 299, 299, 299, 299, 299, 299, 484, 484, 618, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits262
private theorem actualStart262 : startFrames[262]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd262 : finalFrames[262]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid262 : forwardPathValid 262 = true := by
  rw [forwardPathValid, actualVisits262, actualStart262, actualEnd262]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_20, canClimb_20_245, canClimb_245_299, canClimb_299_484, canClimb_484_618, canClimb_618_1, Bool.true_and]

private theorem actualVisits263 : eventVisits 263 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20, 246, 246, 281, 281, 281, 281, 281, 281, 483, 483, 613, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits263
private theorem actualStart263 : startFrames[263]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd263 : finalFrames[263]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid263 : forwardPathValid 263 = true := by
  rw [forwardPathValid, actualVisits263, actualStart263, actualEnd263]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_20, canClimb_20_246, canClimb_246_281, canClimb_281_483, canClimb_483_613, canClimb_613_1, Bool.true_and]

theorem forwardPathBlock032 (f : Nat) (hl : 256 ≤ f) (hu : f < 264) : forwardPathValid f = true := by
  have hs : f = 256 ∨ f = 257 ∨ f = 258 ∨ f = 259 ∨ f = 260 ∨ f = 261 ∨ f = 262 ∨ f = 263 := by omega
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact forwardPathValid256
  · exact forwardPathValid257
  · exact forwardPathValid258
  · exact forwardPathValid259
  · exact forwardPathValid260
  · exact forwardPathValid261
  · exact forwardPathValid262
  · exact forwardPathValid263

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

attribute [local irreducible] canClimb
private theorem actualVisits264 : eventVisits 264 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 21, 153, 153, 293, 293, 293, 293, 293, 293, 360, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits264
private theorem actualStart264 : startFrames[264]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd264 : finalFrames[264]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid264 : forwardPathValid 264 = true := by
  rw [forwardPathValid, actualVisits264, actualStart264, actualEnd264]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_21, canClimb_21_153, canClimb_153_293, canClimb_293_360, canClimb_360_1, Bool.true_and]

private theorem actualVisits265 : eventVisits 265 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 21, 154, 154, 287, 287, 287, 287, 287, 287, 287, 287, 372, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits265
private theorem actualStart265 : startFrames[265]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd265 : finalFrames[265]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid265 : forwardPathValid 265 = true := by
  rw [forwardPathValid, actualVisits265, actualStart265, actualEnd265]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_21, canClimb_21_154, canClimb_154_287, canClimb_287_372, canClimb_372_1, Bool.true_and]

private theorem actualVisits266 : eventVisits 266 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 22, 236, 236, 270, 270, 270, 270, 270, 270, 469, 469, 625, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits266
private theorem actualStart266 : startFrames[266]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd266 : finalFrames[266]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid266 : forwardPathValid 266 = true := by
  rw [forwardPathValid, actualVisits266, actualStart266, actualEnd266]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_22, canClimb_22_236, canClimb_236_270, canClimb_270_469, canClimb_469_625, canClimb_625_1, Bool.true_and]

private theorem actualVisits267 : eventVisits 267 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 22, 239, 239, 297, 297, 297, 297, 297, 297, 478, 478, 539, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits267
private theorem actualStart267 : startFrames[267]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd267 : finalFrames[267]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid267 : forwardPathValid 267 = true := by
  rw [forwardPathValid, actualVisits267, actualStart267, actualEnd267]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_22, canClimb_22_239, canClimb_239_297, canClimb_297_478, canClimb_478_539, canClimb_539_1, Bool.true_and]

private theorem actualVisits268 : eventVisits 268 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 23, 164, 164, 270, 270, 270, 270, 270, 270, 403, 403, 627, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits268
private theorem actualStart268 : startFrames[268]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd268 : finalFrames[268]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid268 : forwardPathValid 268 = true := by
  rw [forwardPathValid, actualVisits268, actualStart268, actualEnd268]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_23, canClimb_23_164, canClimb_164_270, canClimb_270_403, canClimb_403_627, canClimb_627_1, Bool.true_and]

private theorem actualVisits269 : eventVisits 269 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 23, 166, 166, 295, 295, 295, 295, 295, 295, 295, 295, 401, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits269
private theorem actualStart269 : startFrames[269]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd269 : finalFrames[269]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid269 : forwardPathValid 269 = true := by
  rw [forwardPathValid, actualVisits269, actualStart269, actualEnd269]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_23, canClimb_23_166, canClimb_166_295, canClimb_295_401, canClimb_401_1, Bool.true_and]

private theorem actualVisits270 : eventVisits 270 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24, 184, 184, 287, 287, 287, 287, 287, 287, 287, 287, 418, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits270
private theorem actualStart270 : startFrames[270]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd270 : finalFrames[270]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid270 : forwardPathValid 270 = true := by
  rw [forwardPathValid, actualVisits270, actualStart270, actualEnd270]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_24, canClimb_24_184, canClimb_184_287, canClimb_287_418, canClimb_418_1, Bool.true_and]

private theorem actualVisits271 : eventVisits 271 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24, 24, 509, 509, 382, 544, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits271
private theorem actualStart271 : startFrames[271]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd271 : finalFrames[271]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid271 : forwardPathValid 271 = true := by
  rw [forwardPathValid, actualVisits271, actualStart271, actualEnd271]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_24, canClimb_24_509, canClimb_382_544, canClimb_509_382, canClimb_544_1, Bool.true_and]

theorem forwardPathBlock033 (f : Nat) (hl : 264 ≤ f) (hu : f < 272) : forwardPathValid f = true := by
  have hs : f = 264 ∨ f = 265 ∨ f = 266 ∨ f = 267 ∨ f = 268 ∨ f = 269 ∨ f = 270 ∨ f = 271 := by omega
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact forwardPathValid264
  · exact forwardPathValid265
  · exact forwardPathValid266
  · exact forwardPathValid267
  · exact forwardPathValid268
  · exact forwardPathValid269
  · exact forwardPathValid270
  · exact forwardPathValid271

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

attribute [local irreducible] canClimb
private theorem actualVisits272 : eventVisits 272 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 25, 134, 134, 270, 270, 270, 270, 270, 270, 270, 347, 347, 528, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits272
private theorem actualStart272 : startFrames[272]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd272 : finalFrames[272]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid272 : forwardPathValid 272 = true := by
  rw [forwardPathValid, actualVisits272, actualStart272, actualEnd272]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_25, canClimb_25_134, canClimb_134_270, canClimb_270_347, canClimb_347_528, canClimb_528_1, Bool.true_and]

private theorem actualVisits273 : eventVisits 273 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 25, 138, 401, 551, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits273
private theorem actualStart273 : startFrames[273]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd273 : finalFrames[273]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid273 : forwardPathValid 273 = true := by
  rw [forwardPathValid, actualVisits273, actualStart273, actualEnd273]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_25, canClimb_25_138, canClimb_138_401, canClimb_401_551, canClimb_551_1, Bool.true_and]

private theorem actualVisits274 : eventVisits 274 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 26, 218, 218, 268, 268, 268, 268, 268, 268, 268, 268, 385, 385, 614, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits274
private theorem actualStart274 : startFrames[274]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd274 : finalFrames[274]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid274 : forwardPathValid 274 = true := by
  rw [forwardPathValid, actualVisits274, actualStart274, actualEnd274]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_26, canClimb_26_218, canClimb_218_268, canClimb_268_385, canClimb_385_614, canClimb_614_1, Bool.true_and]

private theorem actualVisits275 : eventVisits 275 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 26, 219, 219, 281, 281, 281, 281, 281, 281, 462, 462, 626, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits275
private theorem actualStart275 : startFrames[275]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd275 : finalFrames[275]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid275 : forwardPathValid 275 = true := by
  rw [forwardPathValid, actualVisits275, actualStart275, actualEnd275]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_26, canClimb_26_219, canClimb_219_281, canClimb_281_462, canClimb_462_626, canClimb_626_1, Bool.true_and]

private theorem actualVisits276 : eventVisits 276 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 27, 224, 224, 270, 270, 270, 270, 270, 270, 481, 481, 620, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits276
private theorem actualStart276 : startFrames[276]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd276 : finalFrames[276]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid276 : forwardPathValid 276 = true := by
  rw [forwardPathValid, actualVisits276, actualStart276, actualEnd276]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_27, canClimb_27_224, canClimb_224_270, canClimb_270_481, canClimb_481_620, canClimb_620_1, Bool.true_and]

private theorem actualVisits277 : eventVisits 277 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 27, 225, 475, 628, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits277
private theorem actualStart277 : startFrames[277]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd277 : finalFrames[277]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid277 : forwardPathValid 277 = true := by
  rw [forwardPathValid, actualVisits277, actualStart277, actualEnd277]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_27, canClimb_27_225, canClimb_225_475, canClimb_475_628, canClimb_628_1, Bool.true_and]

private theorem actualVisits278 : eventVisits 278 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 28, 164, 372, 566, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits278
private theorem actualStart278 : startFrames[278]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd278 : finalFrames[278]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid278 : forwardPathValid 278 = true := by
  rw [forwardPathValid, actualVisits278, actualStart278, actualEnd278]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_28, canClimb_28_164, canClimb_164_372, canClimb_372_566, canClimb_566_1, Bool.true_and]

private theorem actualVisits279 : eventVisits 279 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 28, 167, 167, 296, 296, 296, 296, 296, 296, 296, 400, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits279
private theorem actualStart279 : startFrames[279]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd279 : finalFrames[279]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid279 : forwardPathValid 279 = true := by
  rw [forwardPathValid, actualVisits279, actualStart279, actualEnd279]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_28, canClimb_28_167, canClimb_167_296, canClimb_296_400, canClimb_400_1, Bool.true_and]

theorem forwardPathBlock034 (f : Nat) (hl : 272 ≤ f) (hu : f < 280) : forwardPathValid f = true := by
  have hs : f = 272 ∨ f = 273 ∨ f = 274 ∨ f = 275 ∨ f = 276 ∨ f = 277 ∨ f = 278 ∨ f = 279 := by omega
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact forwardPathValid272
  · exact forwardPathValid273
  · exact forwardPathValid274
  · exact forwardPathValid275
  · exact forwardPathValid276
  · exact forwardPathValid277
  · exact forwardPathValid278
  · exact forwardPathValid279

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

attribute [local irreducible] canClimb
private theorem actualVisits280 : eventVisits 280 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 29, 152, 152, 268, 268, 268, 268, 268, 268, 268, 268, 421, 421, 617, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits280
private theorem actualStart280 : startFrames[280]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd280 : finalFrames[280]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid280 : forwardPathValid 280 = true := by
  rw [forwardPathValid, actualVisits280, actualStart280, actualEnd280]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_29, canClimb_29_152, canClimb_152_268, canClimb_268_421, canClimb_421_617, canClimb_617_1, Bool.true_and]

private theorem actualVisits281 : eventVisits 281 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 29, 155, 155, 280, 280, 280, 280, 280, 280, 280, 280, 382, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits281
private theorem actualStart281 : startFrames[281]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd281 : finalFrames[281]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid281 : forwardPathValid 281 = true := by
  rw [forwardPathValid, actualVisits281, actualStart281, actualEnd281]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_29, canClimb_29_155, canClimb_155_280, canClimb_280_382, canClimb_382_1, Bool.true_and]

private theorem actualVisits282 : eventVisits 282 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 30, 227, 227, 294, 294, 294, 294, 294, 294, 504, 504, 603, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits282
private theorem actualStart282 : startFrames[282]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd282 : finalFrames[282]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid282 : forwardPathValid 282 = true := by
  rw [forwardPathValid, actualVisits282, actualStart282, actualEnd282]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_30, canClimb_30_227, canClimb_227_294, canClimb_294_504, canClimb_504_603, canClimb_603_1, Bool.true_and]

private theorem actualVisits283 : eventVisits 283 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 30, 228, 228, 284, 284, 284, 284, 284, 284, 465, 465, 623, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits283
private theorem actualStart283 : startFrames[283]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd283 : finalFrames[283]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid283 : forwardPathValid 283 = true := by
  rw [forwardPathValid, actualVisits283, actualStart283, actualEnd283]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_30, canClimb_30_228, canClimb_228_284, canClimb_284_465, canClimb_465_623, canClimb_623_1, Bool.true_and]

private theorem actualVisits284 : eventVisits 284 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 31, 218, 485, 613, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits284
private theorem actualStart284 : startFrames[284]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd284 : finalFrames[284]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid284 : forwardPathValid 284 = true := by
  rw [forwardPathValid, actualVisits284, actualStart284, actualEnd284]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_31, canClimb_31_218, canClimb_218_485, canClimb_485_613, canClimb_613_1, Bool.true_and]

private theorem actualVisits285 : eventVisits 285 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 31, 221, 221, 292, 292, 292, 292, 292, 292, 292, 407, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits285
private theorem actualStart285 : startFrames[285]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd285 : finalFrames[285]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid285 : forwardPathValid 285 = true := by
  rw [forwardPathValid, actualVisits285, actualStart285, actualEnd285]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_31, canClimb_31_221, canClimb_221_292, canClimb_292_407, canClimb_407_1, Bool.true_and]

private theorem actualVisits286 : eventVisits 286 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 32, 141, 141, 287, 287, 287, 287, 287, 287, 383, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits286
private theorem actualStart286 : startFrames[286]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd286 : finalFrames[286]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid286 : forwardPathValid 286 = true := by
  rw [forwardPathValid, actualVisits286, actualStart286, actualEnd286]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_32, canClimb_32_141, canClimb_141_287, canClimb_287_383, canClimb_383_1, Bool.true_and]

private theorem actualVisits287 : eventVisits 287 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 32, 142, 412, 576, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits287
private theorem actualStart287 : startFrames[287]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd287 : finalFrames[287]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid287 : forwardPathValid 287 = true := by
  rw [forwardPathValid, actualVisits287, actualStart287, actualEnd287]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_32, canClimb_32_142, canClimb_142_412, canClimb_412_576, canClimb_576_1, Bool.true_and]

theorem forwardPathBlock035 (f : Nat) (hl : 280 ≤ f) (hu : f < 288) : forwardPathValid f = true := by
  have hs : f = 280 ∨ f = 281 ∨ f = 282 ∨ f = 283 ∨ f = 284 ∨ f = 285 ∨ f = 286 ∨ f = 287 := by omega
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact forwardPathValid280
  · exact forwardPathValid281
  · exact forwardPathValid282
  · exact forwardPathValid283
  · exact forwardPathValid284
  · exact forwardPathValid285
  · exact forwardPathValid286
  · exact forwardPathValid287

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

attribute [local irreducible] canClimb
private theorem actualVisits288 : eventVisits 288 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 33, 254, 254, 274, 274, 274, 274, 274, 274, 499, 499, 606, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits288
private theorem actualStart288 : startFrames[288]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd288 : finalFrames[288]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid288 : forwardPathValid 288 = true := by
  rw [forwardPathValid, actualVisits288, actualStart288, actualEnd288]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_33, canClimb_33_254, canClimb_254_274, canClimb_274_499, canClimb_499_606, canClimb_606_1, Bool.true_and]

private theorem actualVisits289 : eventVisits 289 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 33, 255, 255, 293, 293, 293, 293, 293, 293, 498, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits289
private theorem actualStart289 : startFrames[289]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd289 : finalFrames[289]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid289 : forwardPathValid 289 = true := by
  rw [forwardPathValid, actualVisits289, actualStart289, actualEnd289]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_33, canClimb_33_255, canClimb_255_293, canClimb_293_498, canClimb_498_1, Bool.true_and]

private theorem actualVisits290 : eventVisits 290 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 34, 200, 501, 565, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits290
private theorem actualStart290 : startFrames[290]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd290 : finalFrames[290]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid290 : forwardPathValid 290 = true := by
  rw [forwardPathValid, actualVisits290, actualStart290, actualEnd290]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_34, canClimb_34_200, canClimb_200_501, canClimb_501_565, canClimb_565_1, Bool.true_and]

private theorem actualVisits291 : eventVisits 291 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 34, 201, 201, 297, 297, 297, 297, 297, 341, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits291
private theorem actualStart291 : startFrames[291]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd291 : finalFrames[291]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid291 : forwardPathValid 291 = true := by
  rw [forwardPathValid, actualVisits291, actualStart291, actualEnd291]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_34, canClimb_34_201, canClimb_201_297, canClimb_297_341, canClimb_341_1, Bool.true_and]

private theorem actualVisits292 : eventVisits 292 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 35, 186, 186, 295, 295, 295, 295, 295, 295, 295, 295, 426, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits292
private theorem actualStart292 : startFrames[292]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd292 : finalFrames[292]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid292 : forwardPathValid 292 = true := by
  rw [forwardPathValid, actualVisits292, actualStart292, actualEnd292]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_35, canClimb_35_186, canClimb_186_295, canClimb_295_426, canClimb_426_1, Bool.true_and]

private theorem actualVisits293 : eventVisits 293 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 35, 187, 509, 509, 380, 552, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits293
private theorem actualStart293 : startFrames[293]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd293 : finalFrames[293]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid293 : forwardPathValid 293 = true := by
  rw [forwardPathValid, actualVisits293, actualStart293, actualEnd293]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_35, canClimb_35_187, canClimb_187_509, canClimb_380_552, canClimb_509_380, canClimb_552_1, Bool.true_and]

private theorem actualVisits294 : eventVisits 294 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 36, 200, 200, 272, 272, 272, 272, 272, 272, 272, 427, 427, 602, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits294
private theorem actualStart294 : startFrames[294]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd294 : finalFrames[294]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid294 : forwardPathValid 294 = true := by
  rw [forwardPathValid, actualVisits294, actualStart294, actualEnd294]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_36, canClimb_36_200, canClimb_200_272, canClimb_272_427, canClimb_427_602, canClimb_602_1, Bool.true_and]

private theorem actualVisits295 : eventVisits 295 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 36, 203, 491, 630, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits295
private theorem actualStart295 : startFrames[295]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd295 : finalFrames[295]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid295 : forwardPathValid 295 = true := by
  rw [forwardPathValid, actualVisits295, actualStart295, actualEnd295]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_36, canClimb_36_203, canClimb_203_491, canClimb_491_630, canClimb_630_1, Bool.true_and]

theorem forwardPathBlock036 (f : Nat) (hl : 288 ≤ f) (hu : f < 296) : forwardPathValid f = true := by
  have hs : f = 288 ∨ f = 289 ∨ f = 290 ∨ f = 291 ∨ f = 292 ∨ f = 293 ∨ f = 294 ∨ f = 295 := by omega
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact forwardPathValid288
  · exact forwardPathValid289
  · exact forwardPathValid290
  · exact forwardPathValid291
  · exact forwardPathValid292
  · exact forwardPathValid293
  · exact forwardPathValid294
  · exact forwardPathValid295

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

attribute [local irreducible] canClimb
private theorem actualVisits296 : eventVisits 296 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 37, 158, 158, 272, 272, 272, 272, 272, 272, 272, 272, 391, 391, 517, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits296
private theorem actualStart296 : startFrames[296]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd296 : finalFrames[296]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid296 : forwardPathValid 296 = true := by
  rw [forwardPathValid, actualVisits296, actualStart296, actualEnd296]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_37, canClimb_37_158, canClimb_158_272, canClimb_272_391, canClimb_391_517, canClimb_517_1, Bool.true_and]

private theorem actualVisits297 : eventVisits 297 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 37, 37, 508, 427, 612, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits297
private theorem actualStart297 : startFrames[297]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd297 : finalFrames[297]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid297 : forwardPathValid 297 = true := by
  rw [forwardPathValid, actualVisits297, actualStart297, actualEnd297]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_37, canClimb_37_508, canClimb_427_612, canClimb_508_427, canClimb_612_1, Bool.true_and]

private theorem actualVisits298 : eventVisits 298 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 38, 170, 170, 274, 274, 274, 274, 274, 274, 409, 409, 605, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits298
private theorem actualStart298 : startFrames[298]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd298 : finalFrames[298]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid298 : forwardPathValid 298 = true := by
  rw [forwardPathValid, actualVisits298, actualStart298, actualEnd298]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_38, canClimb_38_170, canClimb_170_274, canClimb_274_409, canClimb_409_605, canClimb_605_1, Bool.true_and]

private theorem actualVisits299 : eventVisits 299 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 38, 171, 171, 280, 280, 280, 280, 280, 280, 280, 419, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits299
private theorem actualStart299 : startFrames[299]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd299 : finalFrames[299]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid299 : forwardPathValid 299 = true := by
  rw [forwardPathValid, actualVisits299, actualStart299, actualEnd299]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_38, canClimb_38_171, canClimb_171_280, canClimb_280_419, canClimb_419_1, Bool.true_and]

private theorem actualVisits300 : eventVisits 300 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 39, 257, 257, 286, 286, 286, 286, 286, 286, 286, 486, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits300
private theorem actualStart300 : startFrames[300]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd300 : finalFrames[300]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid300 : forwardPathValid 300 = true := by
  rw [forwardPathValid, actualVisits300, actualStart300, actualEnd300]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_39, canClimb_39_257, canClimb_257_286, canClimb_286_486, canClimb_486_1, Bool.true_and]

private theorem actualVisits301 : eventVisits 301 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 39, 258, 258, 298, 298, 298, 298, 298, 298, 495, 495, 556, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits301
private theorem actualStart301 : startFrames[301]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd301 : finalFrames[301]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid301 : forwardPathValid 301 = true := by
  rw [forwardPathValid, actualVisits301, actualStart301, actualEnd301]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_39, canClimb_39_258, canClimb_258_298, canClimb_298_495, canClimb_495_556, canClimb_556_1, Bool.true_and]

private theorem actualVisits302 : eventVisits 302 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 40, 185, 185, 272, 272, 272, 272, 272, 272, 272, 445, 445, 610, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits302
private theorem actualStart302 : startFrames[302]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd302 : finalFrames[302]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid302 : forwardPathValid 302 = true := by
  rw [forwardPathValid, actualVisits302, actualStart302, actualEnd302]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_40, canClimb_40_185, canClimb_185_272, canClimb_272_445, canClimb_445_610, canClimb_610_1, Bool.true_and]

private theorem actualVisits303 : eventVisits 303 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 40, 189, 189, 296, 296, 296, 296, 296, 296, 423, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits303
private theorem actualStart303 : startFrames[303]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd303 : finalFrames[303]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid303 : forwardPathValid 303 = true := by
  rw [forwardPathValid, actualVisits303, actualStart303, actualEnd303]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_40, canClimb_40_189, canClimb_189_296, canClimb_296_423, canClimb_423_1, Bool.true_and]

theorem forwardPathBlock037 (f : Nat) (hl : 296 ≤ f) (hu : f < 304) : forwardPathValid f = true := by
  have hs : f = 296 ∨ f = 297 ∨ f = 298 ∨ f = 299 ∨ f = 300 ∨ f = 301 ∨ f = 302 ∨ f = 303 := by omega
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact forwardPathValid296
  · exact forwardPathValid297
  · exact forwardPathValid298
  · exact forwardPathValid299
  · exact forwardPathValid300
  · exact forwardPathValid301
  · exact forwardPathValid302
  · exact forwardPathValid303

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

attribute [local irreducible] canClimb
private theorem actualVisits304 : eventVisits 304 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 41, 206, 206, 274, 274, 274, 274, 274, 274, 451, 451, 604, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits304
private theorem actualStart304 : startFrames[304]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd304 : finalFrames[304]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid304 : forwardPathValid 304 = true := by
  rw [forwardPathValid, actualVisits304, actualStart304, actualEnd304]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_41, canClimb_41_206, canClimb_206_274, canClimb_274_451, canClimb_451_604, canClimb_604_1, Bool.true_and]

private theorem actualVisits305 : eventVisits 305 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 41, 208, 208, 286, 286, 286, 286, 286, 286, 286, 351, 351, 594, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits305
private theorem actualStart305 : startFrames[305]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd305 : finalFrames[305]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid305 : forwardPathValid 305 = true := by
  rw [forwardPathValid, actualVisits305, actualStart305, actualEnd305]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_41, canClimb_41_208, canClimb_208_286, canClimb_286_351, canClimb_351_594, canClimb_594_1, Bool.true_and]

private theorem actualVisits306 : eventVisits 306 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 42, 261, 261, 294, 294, 294, 294, 294, 294, 479, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits306
private theorem actualStart306 : startFrames[306]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd306 : finalFrames[306]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid306 : forwardPathValid 306 = true := by
  rw [forwardPathValid, actualVisits306, actualStart306, actualEnd306]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_42, canClimb_42_261, canClimb_261_294, canClimb_294_479, canClimb_479_1, Bool.true_and]

private theorem actualVisits307 : eventVisits 307 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 42, 262, 441, 608, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits307
private theorem actualStart307 : startFrames[307]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd307 : finalFrames[307]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid307 : forwardPathValid 307 = true := by
  rw [forwardPathValid, actualVisits307, actualStart307, actualEnd307]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_42, canClimb_42_262, canClimb_262_441, canClimb_441_608, canClimb_608_1, Bool.true_and]

private theorem actualVisits308 : eventVisits 308 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 43, 140, 140, 274, 274, 274, 274, 274, 274, 274, 348, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits308
private theorem actualStart308 : startFrames[308]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd308 : finalFrames[308]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid308 : forwardPathValid 308 = true := by
  rw [forwardPathValid, actualVisits308, actualStart308, actualEnd308]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_43, canClimb_43_140, canClimb_140_274, canClimb_274_348, canClimb_348_1, Bool.true_and]

private theorem actualVisits309 : eventVisits 309 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 43, 144, 144, 280, 280, 280, 280, 280, 280, 280, 280, 369, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits309
private theorem actualStart309 : startFrames[309]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd309 : finalFrames[309]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid309 : forwardPathValid 309 = true := by
  rw [forwardPathValid, actualVisits309, actualStart309, actualEnd309]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_43, canClimb_43_144, canClimb_144_280, canClimb_280_369, canClimb_369_1, Bool.true_and]

private theorem actualVisits310 : eventVisits 310 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 44, 209, 209, 281, 281, 281, 281, 281, 281, 281, 281, 333, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits310
private theorem actualStart310 : startFrames[310]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd310 : finalFrames[310]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid310 : forwardPathValid 310 = true := by
  rw [forwardPathValid, actualVisits310, actualStart310, actualEnd310]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_44, canClimb_44_209, canClimb_209_281, canClimb_281_333, canClimb_333_1, Bool.true_and]

private theorem actualVisits311 : eventVisits 311 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 44, 210, 490, 533, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits311
private theorem actualStart311 : startFrames[311]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd311 : finalFrames[311]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid311 : forwardPathValid 311 = true := by
  rw [forwardPathValid, actualVisits311, actualStart311, actualEnd311]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_44, canClimb_44_210, canClimb_210_490, canClimb_490_533, canClimb_533_1, Bool.true_and]

theorem forwardPathBlock038 (f : Nat) (hl : 304 ≤ f) (hu : f < 312) : forwardPathValid f = true := by
  have hs : f = 304 ∨ f = 305 ∨ f = 306 ∨ f = 307 ∨ f = 308 ∨ f = 309 ∨ f = 310 ∨ f = 311 := by omega
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact forwardPathValid304
  · exact forwardPathValid305
  · exact forwardPathValid306
  · exact forwardPathValid307
  · exact forwardPathValid308
  · exact forwardPathValid309
  · exact forwardPathValid310
  · exact forwardPathValid311

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

attribute [local irreducible] canClimb
private theorem actualVisits312 : eventVisits 312 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 45, 160, 160, 283, 283, 283, 283, 283, 283, 283, 353, 353, 587, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits312
private theorem actualStart312 : startFrames[312]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd312 : finalFrames[312]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid312 : forwardPathValid 312 = true := by
  rw [forwardPathValid, actualVisits312, actualStart312, actualEnd312]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_45, canClimb_45_160, canClimb_160_283, canClimb_283_353, canClimb_353_587, canClimb_587_1, Bool.true_and]

private theorem actualVisits313 : eventVisits 313 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 45, 45, 295, 295, 295, 295, 295, 295, 364, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits313
private theorem actualStart313 : startFrames[313]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd313 : finalFrames[313]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid313 : forwardPathValid 313 = true := by
  rw [forwardPathValid, actualVisits313, actualStart313, actualEnd313]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_45, canClimb_45_295, canClimb_295_364, canClimb_364_1, Bool.true_and]

private theorem actualVisits314 : eventVisits 314 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 46, 173, 173, 299, 299, 299, 299, 299, 299, 461, 461, 554, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits314
private theorem actualStart314 : startFrames[314]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd314 : finalFrames[314]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid314 : forwardPathValid 314 = true := by
  rw [forwardPathValid, actualVisits314, actualStart314, actualEnd314]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_46, canClimb_46_173, canClimb_173_299, canClimb_299_461, canClimb_461_554, canClimb_554_1, Bool.true_and]

private theorem actualVisits315 : eventVisits 315 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 46, 174, 174, 287, 287, 287, 287, 287, 287, 287, 287, 405, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits315
private theorem actualStart315 : startFrames[315]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd315 : finalFrames[315]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid315 : forwardPathValid 315 = true := by
  rw [forwardPathValid, actualVisits315, actualStart315, actualEnd315]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_46, canClimb_46_174, canClimb_174_287, canClimb_287_405, canClimb_405_1, Bool.true_and]

private theorem actualVisits316 : eventVisits 316 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 47, 260, 260, 272, 272, 272, 272, 272, 272, 272, 272, 505, 505, 603, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits316
private theorem actualStart316 : startFrames[316]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd316 : finalFrames[316]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid316 : forwardPathValid 316 = true := by
  rw [forwardPathValid, actualVisits316, actualStart316, actualEnd316]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_47, canClimb_47_260, canClimb_260_272, canClimb_272_505, canClimb_505_603, canClimb_603_1, Bool.true_and]

private theorem actualVisits317 : eventVisits 317 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 47, 264, 264, 297, 297, 297, 297, 297, 297, 297, 297, 297, 501, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits317
private theorem actualStart317 : startFrames[317]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd317 : finalFrames[317]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid317 : forwardPathValid 317 = true := by
  rw [forwardPathValid, actualVisits317, actualStart317, actualEnd317]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_47, canClimb_47_264, canClimb_264_297, canClimb_297_501, canClimb_501_1, Bool.true_and]

private theorem actualVisits318 : eventVisits 318 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 48, 116, 116, 286, 286, 286, 286, 286, 286, 286, 449, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits318
private theorem actualStart318 : startFrames[318]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd318 : finalFrames[318]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid318 : forwardPathValid 318 = true := by
  rw [forwardPathValid, actualVisits318, actualStart318, actualEnd318]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_48, canClimb_48_116, canClimb_116_286, canClimb_286_449, canClimb_449_1, Bool.true_and]

private theorem actualVisits319 : eventVisits 319 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 48, 117, 506, 506, 506, 357, 586, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits319
private theorem actualStart319 : startFrames[319]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd319 : finalFrames[319]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid319 : forwardPathValid 319 = true := by
  rw [forwardPathValid, actualVisits319, actualStart319, actualEnd319]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_48, canClimb_48_117, canClimb_117_506, canClimb_357_586, canClimb_506_357, canClimb_586_1, Bool.true_and]

theorem forwardPathBlock039 (f : Nat) (hl : 312 ≤ f) (hu : f < 320) : forwardPathValid f = true := by
  have hs : f = 312 ∨ f = 313 ∨ f = 314 ∨ f = 315 ∨ f = 316 ∨ f = 317 ∨ f = 318 ∨ f = 319 := by omega
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact forwardPathValid312
  · exact forwardPathValid313
  · exact forwardPathValid314
  · exact forwardPathValid315
  · exact forwardPathValid316
  · exact forwardPathValid317
  · exact forwardPathValid318
  · exact forwardPathValid319

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

attribute [local irreducible] canClimb
private theorem actualVisits320 : eventVisits 320 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 49, 119, 119, 300, 300, 300, 300, 300, 300, 300, 300, 361, 361, 593, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits320
private theorem actualStart320 : startFrames[320]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd320 : finalFrames[320]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid320 : forwardPathValid 320 = true := by
  rw [forwardPathValid, actualVisits320, actualStart320, actualEnd320]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_49, canClimb_49_119, canClimb_119_300, canClimb_300_361, canClimb_361_593, canClimb_593_1, Bool.true_and]

private theorem actualVisits321 : eventVisits 321 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 49, 120, 120, 298, 298, 298, 298, 298, 298, 298, 298, 357, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits321
private theorem actualStart321 : startFrames[321]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd321 : finalFrames[321]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid321 : forwardPathValid 321 = true := by
  rw [forwardPathValid, actualVisits321, actualStart321, actualEnd321]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_49, canClimb_49_120, canClimb_120_298, canClimb_298_357, canClimb_357_1, Bool.true_and]

private theorem actualVisits322 : eventVisits 322 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 50, 122, 506, 506, 349, 536, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits322
private theorem actualStart322 : startFrames[322]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd322 : finalFrames[322]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid322 : forwardPathValid 322 = true := by
  rw [forwardPathValid, actualVisits322, actualStart322, actualEnd322]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_50, canClimb_50_122, canClimb_122_506, canClimb_349_536, canClimb_506_349, canClimb_536_1, Bool.true_and]

private theorem actualVisits323 : eventVisits 323 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 50, 123, 123, 292, 292, 292, 292, 292, 292, 292, 292, 339, 339, 572, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits323
private theorem actualStart323 : startFrames[323]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd323 : finalFrames[323]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid323 : forwardPathValid 323 = true := by
  rw [forwardPathValid, actualVisits323, actualStart323, actualEnd323]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_50, canClimb_50_123, canClimb_123_292, canClimb_292_339, canClimb_339_572, canClimb_572_1, Bool.true_and]

private theorem actualVisits324 : eventVisits 324 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 48, 48, 288, 288, 288, 288, 288, 288, 288, 288, 355, 355, 594, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits324
private theorem actualStart324 : startFrames[324]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd324 : finalFrames[324]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid324 : forwardPathValid 324 = true := by
  rw [forwardPathValid, actualVisits324, actualStart324, actualEnd324]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_48, canClimb_48_288, canClimb_288_355, canClimb_355_594, canClimb_594_1, Bool.true_and]

private theorem actualVisits325 : eventVisits 325 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 56, 56, 282, 282, 282, 282, 282, 282, 282, 282, 352, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits325
private theorem actualStart325 : startFrames[325]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd325 : finalFrames[325]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid325 : forwardPathValid 325 = true := by
  rw [forwardPathValid, actualVisits325, actualStart325, actualEnd325]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_56, canClimb_56_282, canClimb_282_352, canClimb_352_1, Bool.true_and]

private theorem actualVisits326 : eventVisits 326 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 51, 147, 147, 288, 288, 288, 288, 288, 288, 288, 337, 337, 581, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits326
private theorem actualStart326 : startFrames[326]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd326 : finalFrames[326]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid326 : forwardPathValid 326 = true := by
  rw [forwardPathValid, actualVisits326, actualStart326, actualEnd326]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_51, canClimb_51_147, canClimb_147_288, canClimb_288_337, canClimb_337_581, canClimb_581_1, Bool.true_and]

private theorem actualVisits327 : eventVisits 327 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 51, 148, 406, 561, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits327
private theorem actualStart327 : startFrames[327]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd327 : finalFrames[327]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid327 : forwardPathValid 327 = true := by
  rw [forwardPathValid, actualVisits327, actualStart327, actualEnd327]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_51, canClimb_51_148, canClimb_148_406, canClimb_406_561, canClimb_561_1, Bool.true_and]

theorem forwardPathBlock040 (f : Nat) (hl : 320 ≤ f) (hu : f < 328) : forwardPathValid f = true := by
  have hs : f = 320 ∨ f = 321 ∨ f = 322 ∨ f = 323 ∨ f = 324 ∨ f = 325 ∨ f = 326 ∨ f = 327 := by omega
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact forwardPathValid320
  · exact forwardPathValid321
  · exact forwardPathValid322
  · exact forwardPathValid323
  · exact forwardPathValid324
  · exact forwardPathValid325
  · exact forwardPathValid326
  · exact forwardPathValid327

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

attribute [local irreducible] canClimb
private theorem actualVisits328 : eventVisits 328 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 67, 67, 300, 300, 300, 300, 300, 300, 300, 300, 432, 432, 514, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits328
private theorem actualStart328 : startFrames[328]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd328 : finalFrames[328]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid328 : forwardPathValid 328 = true := by
  rw [forwardPathValid, actualVisits328, actualStart328, actualEnd328]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_67, canClimb_67_300, canClimb_300_432, canClimb_432_514, canClimb_514_1, Bool.true_and]

private theorem actualVisits329 : eventVisits 329 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 68, 68, 279, 279, 279, 279, 279, 279, 332, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits329
private theorem actualStart329 : startFrames[329]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd329 : finalFrames[329]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid329 : forwardPathValid 329 = true := by
  rw [forwardPathValid, actualVisits329, actualStart329, actualEnd329]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_68, canClimb_68_279, canClimb_279_332, canClimb_332_1, Bool.true_and]

private theorem actualVisits330 : eventVisits 330 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 52, 191, 191, 300, 300, 300, 300, 300, 300, 300, 455, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits330
private theorem actualStart330 : startFrames[330]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd330 : finalFrames[330]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid330 : forwardPathValid 330 = true := by
  rw [forwardPathValid, actualVisits330, actualStart330, actualEnd330]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_52, canClimb_52_191, canClimb_191_300, canClimb_300_455, canClimb_455_1, Bool.true_and]

private theorem actualVisits331 : eventVisits 331 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 52, 192, 192, 279, 279, 279, 279, 279, 279, 279, 279, 431, 431, 585, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits331
private theorem actualStart331 : startFrames[331]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd331 : finalFrames[331]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid331 : forwardPathValid 331 = true := by
  rw [forwardPathValid, actualVisits331, actualStart331, actualEnd331]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_52, canClimb_52_192, canClimb_192_279, canClimb_279_431, canClimb_431_585, canClimb_585_1, Bool.true_and]

private theorem actualVisits332 : eventVisits 332 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 53, 176, 374, 574, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits332
private theorem actualStart332 : startFrames[332]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd332 : finalFrames[332]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid332 : forwardPathValid 332 = true := by
  rw [forwardPathValid, actualVisits332, actualStart332, actualEnd332]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_53, canClimb_53_176, canClimb_176_374, canClimb_374_574, canClimb_574_1, Bool.true_and]

private theorem actualVisits333 : eventVisits 333 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 53, 177, 371, 600, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits333
private theorem actualStart333 : startFrames[333]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd333 : finalFrames[333]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid333 : forwardPathValid 333 = true := by
  rw [forwardPathValid, actualVisits333, actualStart333, actualEnd333]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_53, canClimb_53_177, canClimb_177_371, canClimb_371_600, canClimb_600_1, Bool.true_and]

private theorem actualVisits334 : eventVisits 334 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 52, 52, 276, 276, 276, 276, 276, 276, 276, 433, 433, 592, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits334
private theorem actualStart334 : startFrames[334]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd334 : finalFrames[334]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid334 : forwardPathValid 334 = true := by
  rw [forwardPathValid, actualVisits334, actualStart334, actualEnd334]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_52, canClimb_52_276, canClimb_276_433, canClimb_433_592, canClimb_592_1, Bool.true_and]

private theorem actualVisits335 : eventVisits 335 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 62, 62, 289, 289, 289, 289, 289, 289, 437, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits335
private theorem actualStart335 : startFrames[335]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd335 : finalFrames[335]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid335 : forwardPathValid 335 = true := by
  rw [forwardPathValid, actualVisits335, actualStart335, actualEnd335]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_62, canClimb_62_289, canClimb_289_437, canClimb_437_1, Bool.true_and]

theorem forwardPathBlock041 (f : Nat) (hl : 328 ≤ f) (hu : f < 336) : forwardPathValid f = true := by
  have hs : f = 328 ∨ f = 329 ∨ f = 330 ∨ f = 331 ∨ f = 332 ∨ f = 333 ∨ f = 334 ∨ f = 335 := by omega
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact forwardPathValid328
  · exact forwardPathValid329
  · exact forwardPathValid330
  · exact forwardPathValid331
  · exact forwardPathValid332
  · exact forwardPathValid333
  · exact forwardPathValid334
  · exact forwardPathValid335

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

attribute [local irreducible] canClimb
private theorem actualVisits336 : eventVisits 336 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 54, 122, 122, 294, 294, 294, 294, 294, 294, 294, 294, 358, 358, 586, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits336
private theorem actualStart336 : startFrames[336]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd336 : finalFrames[336]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid336 : forwardPathValid 336 = true := by
  rw [forwardPathValid, actualVisits336, actualStart336, actualEnd336]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_54, canClimb_54_122, canClimb_122_294, canClimb_294_358, canClimb_358_586, canClimb_586_1, Bool.true_and]

private theorem actualVisits337 : eventVisits 337 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 54, 124, 124, 290, 290, 290, 290, 290, 290, 290, 393, 393, 513, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits337
private theorem actualStart337 : startFrames[337]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd337 : finalFrames[337]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid337 : forwardPathValid 337 = true := by
  rw [forwardPathValid, actualVisits337, actualStart337, actualEnd337]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_54, canClimb_54_124, canClimb_124_290, canClimb_290_393, canClimb_393_513, canClimb_513_1, Bool.true_and]

private theorem actualVisits338 : eventVisits 338 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 55, 146, 146, 276, 276, 276, 276, 276, 276, 344, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits338
private theorem actualStart338 : startFrames[338]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd338 : finalFrames[338]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid338 : forwardPathValid 338 = true := by
  rw [forwardPathValid, actualVisits338, actualStart338, actualEnd338]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_55, canClimb_55_146, canClimb_146_276, canClimb_276_344, canClimb_344_1, Bool.true_and]

private theorem actualVisits339 : eventVisits 339 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 55, 150, 150, 278, 278, 278, 278, 278, 278, 278, 453, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits339
private theorem actualStart339 : startFrames[339]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd339 : finalFrames[339]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid339 : forwardPathValid 339 = true := by
  rw [forwardPathValid, actualVisits339, actualStart339, actualEnd339]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_55, canClimb_55_150, canClimb_150_278, canClimb_278_453, canClimb_453_1, Bool.true_and]

private theorem actualVisits340 : eventVisits 340 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 56, 116, 506, 506, 351, 515, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits340
private theorem actualStart340 : startFrames[340]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd340 : finalFrames[340]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid340 : forwardPathValid 340 = true := by
  rw [forwardPathValid, actualVisits340, actualStart340, actualEnd340]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_56, canClimb_56_116, canClimb_116_506, canClimb_351_515, canClimb_506_351, canClimb_515_1, Bool.true_and]

private theorem actualVisits341 : eventVisits 341 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 56, 118, 118, 278, 278, 278, 278, 278, 278, 278, 278, 350, 350, 587, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits341
private theorem actualStart341 : startFrames[341]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd341 : finalFrames[341]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid341 : forwardPathValid 341 = true := by
  rw [forwardPathValid, actualVisits341, actualStart341, actualEnd341]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_56, canClimb_56_118, canClimb_118_278, canClimb_278_350, canClimb_350_587, canClimb_587_1, Bool.true_and]

private theorem actualVisits342 : eventVisits 342 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 57, 176, 176, 276, 276, 276, 276, 276, 397, 397, 591, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits342
private theorem actualStart342 : startFrames[342]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd342 : finalFrames[342]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid342 : forwardPathValid 342 = true := by
  rw [forwardPathValid, actualVisits342, actualStart342, actualEnd342]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_57, canClimb_57_176, canClimb_176_276, canClimb_276_397, canClimb_397_591, canClimb_591_1, Bool.true_and]

private theorem actualVisits343 : eventVisits 343 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 57, 180, 180, 278, 278, 278, 278, 278, 278, 278, 411, 411, 576, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits343
private theorem actualStart343 : startFrames[343]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd343 : finalFrames[343]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid343 : forwardPathValid 343 = true := by
  rw [forwardPathValid, actualVisits343, actualStart343, actualEnd343]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_57, canClimb_57_180, canClimb_180_278, canClimb_278_411, canClimb_411_576, canClimb_576_1, Bool.true_and]

theorem forwardPathBlock042 (f : Nat) (hl : 336 ≤ f) (hu : f < 344) : forwardPathValid f = true := by
  have hs : f = 336 ∨ f = 337 ∨ f = 338 ∨ f = 339 ∨ f = 340 ∨ f = 341 ∨ f = 342 ∨ f = 343 := by omega
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact forwardPathValid336
  · exact forwardPathValid337
  · exact forwardPathValid338
  · exact forwardPathValid339
  · exact forwardPathValid340
  · exact forwardPathValid341
  · exact forwardPathValid342
  · exact forwardPathValid343

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

attribute [local irreducible] canClimb
private theorem actualVisits344 : eventVisits 344 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 58, 117, 117, 284, 284, 284, 284, 284, 284, 284, 284, 352, 352, 597, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits344
private theorem actualStart344 : startFrames[344]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd344 : finalFrames[344]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid344 : forwardPathValid 344 = true := by
  rw [forwardPathValid, actualVisits344, actualStart344, actualEnd344]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_58, canClimb_58_117, canClimb_117_284, canClimb_284_352, canClimb_352_597, canClimb_597_1, Bool.true_and]

private theorem actualVisits345 : eventVisits 345 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 58, 58, 280, 280, 280, 280, 280, 280, 280, 280, 333, 333, 579, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits345
private theorem actualStart345 : startFrames[345]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd345 : finalFrames[345]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid345 : forwardPathValid 345 = true := by
  rw [forwardPathValid, actualVisits345, actualStart345, actualEnd345]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_58, canClimb_58_280, canClimb_280_333, canClimb_333_579, canClimb_579_1, Bool.true_and]

private theorem actualVisits346 : eventVisits 346 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 59, 59, 276, 276, 276, 276, 276, 276, 276, 276, 415, 415, 596, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits346
private theorem actualStart346 : startFrames[346]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd346 : finalFrames[346]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid346 : forwardPathValid 346 = true := by
  rw [forwardPathValid, actualVisits346, actualStart346, actualEnd346]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_59, canClimb_59_276, canClimb_276_415, canClimb_415_596, canClimb_596_1, Bool.true_and]

private theorem actualVisits347 : eventVisits 347 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 59, 162, 162, 290, 290, 290, 290, 290, 290, 290, 356, 356, 588, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits347
private theorem actualStart347 : startFrames[347]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd347 : finalFrames[347]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid347 : forwardPathValid 347 = true := by
  rw [forwardPathValid, actualVisits347, actualStart347, actualEnd347]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_59, canClimb_59_162, canClimb_162_290, canClimb_290_356, canClimb_356_588, canClimb_588_1, Bool.true_and]

private theorem actualVisits348 : eventVisits 348 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 60, 121, 121, 296, 296, 296, 296, 296, 296, 296, 365, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits348
private theorem actualStart348 : startFrames[348]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd348 : finalFrames[348]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid348 : forwardPathValid 348 = true := by
  rw [forwardPathValid, actualVisits348, actualStart348, actualEnd348]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_60, canClimb_60_121, canClimb_121_296, canClimb_296_365, canClimb_365_1, Bool.true_and]

private theorem actualVisits349 : eventVisits 349 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 60, 123, 506, 506, 348, 511, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits349
private theorem actualStart349 : startFrames[349]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd349 : finalFrames[349]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid349 : forwardPathValid 349 = true := by
  rw [forwardPathValid, actualVisits349, actualStart349, actualEnd349]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_60, canClimb_60_123, canClimb_123_506, canClimb_348_511, canClimb_506_348, canClimb_511_1, Bool.true_and]

private theorem actualVisits350 : eventVisits 350 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 61, 149, 149, 301, 301, 301, 301, 301, 301, 301, 438, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits350
private theorem actualStart350 : startFrames[350]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd350 : finalFrames[350]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid350 : forwardPathValid 350 = true := by
  rw [forwardPathValid, actualVisits350, actualStart350, actualEnd350]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_61, canClimb_61_149, canClimb_149_301, canClimb_301_438, canClimb_438_1, Bool.true_and]

private theorem actualVisits351 : eventVisits 351 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 61, 151, 151, 267, 267, 267, 267, 267, 267, 267, 267, 326, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits351
private theorem actualStart351 : startFrames[351]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd351 : finalFrames[351]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid351 : forwardPathValid 351 = true := by
  rw [forwardPathValid, actualVisits351, actualStart351, actualEnd351]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_61, canClimb_61_151, canClimb_151_267, canClimb_267_326, canClimb_326_1, Bool.true_and]

theorem forwardPathBlock043 (f : Nat) (hl : 344 ≤ f) (hu : f < 352) : forwardPathValid f = true := by
  have hs : f = 344 ∨ f = 345 ∨ f = 346 ∨ f = 347 ∨ f = 348 ∨ f = 349 ∨ f = 350 ∨ f = 351 := by omega
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact forwardPathValid344
  · exact forwardPathValid345
  · exact forwardPathValid346
  · exact forwardPathValid347
  · exact forwardPathValid348
  · exact forwardPathValid349
  · exact forwardPathValid350
  · exact forwardPathValid351

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

attribute [local irreducible] canClimb
private theorem actualVisits352 : eventVisits 352 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 62, 191, 509, 509, 393, 590, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits352
private theorem actualStart352 : startFrames[352]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd352 : finalFrames[352]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid352 : forwardPathValid 352 = true := by
  rw [forwardPathValid, actualVisits352, actualStart352, actualEnd352]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_62, canClimb_62_191, canClimb_191_509, canClimb_393_590, canClimb_509_393, canClimb_590_1, Bool.true_and]

private theorem actualVisits353 : eventVisits 353 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 62, 193, 193, 267, 267, 267, 267, 267, 267, 428, 428, 575, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits353
private theorem actualStart353 : startFrames[353]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd353 : finalFrames[353]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid353 : forwardPathValid 353 = true := by
  rw [forwardPathValid, actualVisits353, actualStart353, actualEnd353]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_62, canClimb_62_193, canClimb_193_267, canClimb_267_428, canClimb_428_575, canClimb_575_1, Bool.true_and]

private theorem actualVisits354 : eventVisits 354 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 64, 64, 279, 279, 279, 279, 279, 355, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits354
private theorem actualStart354 : startFrames[354]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd354 : finalFrames[354]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid354 : forwardPathValid 354 = true := by
  rw [forwardPathValid, actualVisits354, actualStart354, actualEnd354]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_64, canClimb_64_279, canClimb_279_355, canClimb_355_1, Bool.true_and]

private theorem actualVisits355 : eventVisits 355 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 74, 74, 283, 283, 283, 283, 283, 283, 388, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits355
private theorem actualStart355 : startFrames[355]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd355 : finalFrames[355]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid355 : forwardPathValid 355 = true := by
  rw [forwardPathValid, actualVisits355, actualStart355, actualEnd355]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_74, canClimb_74_283, canClimb_283_388, canClimb_388_1, Bool.true_and]

private theorem actualVisits356 : eventVisits 356 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 63, 131, 131, 291, 291, 291, 291, 291, 291, 291, 291, 361, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits356
private theorem actualStart356 : startFrames[356]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd356 : finalFrames[356]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid356 : forwardPathValid 356 = true := by
  rw [forwardPathValid, actualVisits356, actualStart356, actualEnd356]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_63, canClimb_63_131, canClimb_131_291, canClimb_291_361, canClimb_361_1, Bool.true_and]

private theorem actualVisits357 : eventVisits 357 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 63, 132, 507, 341, 573, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits357
private theorem actualStart357 : startFrames[357]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd357 : finalFrames[357]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid357 : forwardPathValid 357 = true := by
  rw [forwardPathValid, actualVisits357, actualStart357, actualEnd357]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_63, canClimb_63_132, canClimb_132_507, canClimb_341_573, canClimb_507_341, canClimb_573_1, Bool.true_and]

private theorem actualVisits358 : eventVisits 358 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 64, 64, 507, 507, 340, 572, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits358
private theorem actualStart358 : startFrames[358]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd358 : finalFrames[358]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid358 : forwardPathValid 358 = true := by
  rw [forwardPathValid, actualVisits358, actualStart358, actualEnd358]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_64, canClimb_64_507, canClimb_340_572, canClimb_507_340, canClimb_572_1, Bool.true_and]

private theorem actualVisits359 : eventVisits 359 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 64, 128, 128, 282, 282, 282, 282, 282, 366, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits359
private theorem actualStart359 : startFrames[359]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd359 : finalFrames[359]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid359 : forwardPathValid 359 = true := by
  rw [forwardPathValid, actualVisits359, actualStart359, actualEnd359]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_64, canClimb_64_128, canClimb_128_282, canClimb_282_366, canClimb_366_1, Bool.true_and]

theorem forwardPathBlock044 (f : Nat) (hl : 352 ≤ f) (hu : f < 360) : forwardPathValid f = true := by
  have hs : f = 352 ∨ f = 353 ∨ f = 354 ∨ f = 355 ∨ f = 356 ∨ f = 357 ∨ f = 358 ∨ f = 359 := by omega
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact forwardPathValid352
  · exact forwardPathValid353
  · exact forwardPathValid354
  · exact forwardPathValid355
  · exact forwardPathValid356
  · exact forwardPathValid357
  · exact forwardPathValid358
  · exact forwardPathValid359

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

attribute [local irreducible] canClimb
private theorem actualVisits360 : eventVisits 360 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 65, 65, 507, 507, 331, 510, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits360
private theorem actualStart360 : startFrames[360]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd360 : finalFrames[360]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid360 : forwardPathValid 360 = true := by
  rw [forwardPathValid, actualVisits360, actualStart360, actualEnd360]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_65, canClimb_65_507, canClimb_331_510, canClimb_507_331, canClimb_510_1, Bool.true_and]

private theorem actualVisits361 : eventVisits 361 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 65, 133, 133, 292, 292, 292, 292, 292, 370, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits361
private theorem actualStart361 : startFrames[361]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd361 : finalFrames[361]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid361 : forwardPathValid 361 = true := by
  rw [forwardPathValid, actualVisits361, actualStart361, actualEnd361]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_65, canClimb_65_133, canClimb_133_292, canClimb_292_370, canClimb_370_1, Bool.true_and]

private theorem actualVisits362 : eventVisits 362 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 66, 177, 177, 288, 288, 288, 288, 288, 414, 414, 580, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits362
private theorem actualStart362 : startFrames[362]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd362 : finalFrames[362]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid362 : forwardPathValid 362 = true := by
  rw [forwardPathValid, actualVisits362, actualStart362, actualEnd362]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_66, canClimb_66_177, canClimb_177_288, canClimb_288_414, canClimb_414_580, canClimb_580_1, Bool.true_and]

private theorem actualVisits363 : eventVisits 363 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 66, 179, 179, 301, 301, 301, 301, 301, 301, 301, 376, 376, 574, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits363
private theorem actualStart363 : startFrames[363]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd363 : finalFrames[363]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid363 : forwardPathValid 363 = true := by
  rw [forwardPathValid, actualVisits363, actualStart363, actualEnd363]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_66, canClimb_66_179, canClimb_179_301, canClimb_301_376, canClimb_376_574, canClimb_574_1, Bool.true_and]

private theorem actualVisits364 : eventVisits 364 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 67, 161, 161, 289, 289, 289, 289, 289, 289, 289, 350, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits364
private theorem actualStart364 : startFrames[364]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd364 : finalFrames[364]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid364 : forwardPathValid 364 = true := by
  rw [forwardPathValid, actualVisits364, actualStart364, actualEnd364]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_67, canClimb_67_161, canClimb_161_289, canClimb_289_350, canClimb_350_1, Bool.true_and]

private theorem actualVisits365 : eventVisits 365 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 67, 163, 508, 432, 592, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits365
private theorem actualStart365 : startFrames[365]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd365 : finalFrames[365]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid365 : forwardPathValid 365 = true := by
  rw [forwardPathValid, actualVisits365, actualStart365, actualEnd365]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_67, canClimb_67_163, canClimb_163_508, canClimb_432_592, canClimb_508_432, canClimb_592_1, Bool.true_and]

private theorem actualVisits366 : eventVisits 366 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 63, 63, 293, 293, 293, 293, 293, 339, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits366
private theorem actualStart366 : startFrames[366]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd366 : finalFrames[366]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid366 : forwardPathValid 366 = true := by
  rw [forwardPathValid, actualVisits366, actualStart366, actualEnd366]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_63, canClimb_63_293, canClimb_293_339, canClimb_339_1, Bool.true_and]

private theorem actualVisits367 : eventVisits 367 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 65, 65, 294, 294, 294, 294, 294, 441, 441, 557, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits367
private theorem actualStart367 : startFrames[367]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd367 : finalFrames[367]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid367 : forwardPathValid 367 = true := by
  rw [forwardPathValid, actualVisits367, actualStart367, actualEnd367]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_65, canClimb_65_294, canClimb_294_441, canClimb_441_557, canClimb_557_1, Bool.true_and]

theorem forwardPathBlock045 (f : Nat) (hl : 360 ≤ f) (hu : f < 368) : forwardPathValid f = true := by
  have hs : f = 360 ∨ f = 361 ∨ f = 362 ∨ f = 363 ∨ f = 364 ∨ f = 365 ∨ f = 366 ∨ f = 367 := by omega
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact forwardPathValid360
  · exact forwardPathValid361
  · exact forwardPathValid362
  · exact forwardPathValid363
  · exact forwardPathValid364
  · exact forwardPathValid365
  · exact forwardPathValid366
  · exact forwardPathValid367

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

attribute [local irreducible] canClimb
private theorem actualVisits368 : eventVisits 368 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 68, 162, 508, 420, 518, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits368
private theorem actualStart368 : startFrames[368]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd368 : finalFrames[368]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid368 : forwardPathValid 368 = true := by
  rw [forwardPathValid, actualVisits368, actualStart368, actualEnd368]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_68, canClimb_68_162, canClimb_162_508, canClimb_420_518, canClimb_508_420, canClimb_518_1, Bool.true_and]

private theorem actualVisits369 : eventVisits 369 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 68, 163, 163, 267, 267, 267, 267, 267, 267, 392, 392, 582, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits369
private theorem actualStart369 : startFrames[369]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd369 : finalFrames[369]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid369 : forwardPathValid 369 = true := by
  rw [forwardPathValid, actualVisits369, actualStart369, actualEnd369]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_68, canClimb_68_163, canClimb_163_267, canClimb_267_392, canClimb_392_582, canClimb_582_1, Bool.true_and]

private theorem actualVisits370 : eventVisits 370 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 69, 69, 290, 290, 290, 290, 290, 290, 454, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits370
private theorem actualStart370 : startFrames[370]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd370 : finalFrames[370]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid370 : forwardPathValid 370 = true := by
  rw [forwardPathValid, actualVisits370, actualStart370, actualEnd370]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_69, canClimb_69_290, canClimb_290_454, canClimb_454_1, Bool.true_and]

private theorem actualVisits371 : eventVisits 371 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 69, 193, 509, 391, 599, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits371
private theorem actualStart371 : startFrames[371]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd371 : finalFrames[371]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid371 : forwardPathValid 371 = true := by
  rw [forwardPathValid, actualVisits371, actualStart371, actualEnd371]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_69, canClimb_69_193, canClimb_193_509, canClimb_391_599, canClimb_509_391, canClimb_599_1, Bool.true_and]

private theorem actualVisits372 : eventVisits 372 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 70, 132, 132, 295, 295, 295, 295, 295, 295, 295, 295, 340, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits372
private theorem actualStart372 : startFrames[372]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd372 : finalFrames[372]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid372 : forwardPathValid 372 = true := by
  rw [forwardPathValid, actualVisits372, actualStart372, actualEnd372]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_70, canClimb_70_132, canClimb_132_295, canClimb_295_340, canClimb_340_1, Bool.true_and]

private theorem actualVisits373 : eventVisits 373 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 70, 70, 290, 290, 290, 290, 290, 338, 338, 573, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits373
private theorem actualStart373 : startFrames[373]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd373 : finalFrames[373]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid373 : forwardPathValid 373 = true := by
  rw [forwardPathValid, actualVisits373, actualStart373, actualEnd373]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_70, canClimb_70_290, canClimb_290_338, canClimb_338_573, canClimb_573_1, Bool.true_and]

private theorem actualVisits374 : eventVisits 374 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 71, 71, 281, 281, 281, 281, 281, 281, 448, 448, 604, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits374
private theorem actualStart374 : startFrames[374]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd374 : finalFrames[374]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid374 : forwardPathValid 374 = true := by
  rw [forwardPathValid, actualVisits374, actualStart374, actualEnd374]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_71, canClimb_71_281, canClimb_281_448, canClimb_448_604, canClimb_604_1, Bool.true_and]

private theorem actualVisits375 : eventVisits 375 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 71, 130, 130, 278, 278, 278, 278, 278, 278, 278, 278, 332, 332, 571, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits375
private theorem actualStart375 : startFrames[375]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd375 : finalFrames[375]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid375 : forwardPathValid 375 = true := by
  rw [forwardPathValid, actualVisits375, actualStart375, actualEnd375]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_71, canClimb_71_130, canClimb_130_278, canClimb_278_332, canClimb_332_571, canClimb_571_1, Bool.true_and]

theorem forwardPathBlock046 (f : Nat) (hl : 368 ≤ f) (hu : f < 376) : forwardPathValid f = true := by
  have hs : f = 368 ∨ f = 369 ∨ f = 370 ∨ f = 371 ∨ f = 372 ∨ f = 373 ∨ f = 374 ∨ f = 375 := by omega
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact forwardPathValid368
  · exact forwardPathValid369
  · exact forwardPathValid370
  · exact forwardPathValid371
  · exact forwardPathValid372
  · exact forwardPathValid373
  · exact forwardPathValid374
  · exact forwardPathValid375

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

attribute [local irreducible] canClimb
private theorem actualVisits376 : eventVisits 376 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 72, 148, 148, 291, 291, 291, 291, 291, 291, 291, 435, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits376
private theorem actualStart376 : startFrames[376]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd376 : finalFrames[376]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid376 : forwardPathValid 376 = true := by
  rw [forwardPathValid, actualVisits376, actualStart376, actualEnd376]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_72, canClimb_72_148, canClimb_148_291, canClimb_291_435, canClimb_435_1, Bool.true_and]

private theorem actualVisits377 : eventVisits 377 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 72, 151, 408, 609, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits377
private theorem actualStart377 : startFrames[377]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd377 : finalFrames[377]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid377 : forwardPathValid 377 = true := by
  rw [forwardPathValid, actualVisits377, actualStart377, actualEnd377]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_72, canClimb_72_151, canClimb_151_408, canClimb_408_609, canClimb_609_1, Bool.true_and]

private theorem actualVisits378 : eventVisits 378 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 73, 178, 178, 291, 291, 291, 291, 291, 291, 291, 413, 413, 589, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits378
private theorem actualStart378 : startFrames[378]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd378 : finalFrames[378]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid378 : forwardPathValid 378 = true := by
  rw [forwardPathValid, actualVisits378, actualStart378, actualEnd378]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_73, canClimb_73_178, canClimb_178_291, canClimb_291_413, canClimb_413_589, canClimb_589_1, Bool.true_and]

private theorem actualVisits379 : eventVisits 379 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 73, 181, 181, 267, 267, 267, 267, 267, 267, 267, 267, 410, 410, 580, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits379
private theorem actualStart379 : startFrames[379]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd379 : finalFrames[379]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid379 : forwardPathValid 379 = true := by
  rw [forwardPathValid, actualVisits379, actualStart379, actualEnd379]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_73, canClimb_73_181, canClimb_181_267, canClimb_267_410, canClimb_410_580, canClimb_580_1, Bool.true_and]

private theorem actualVisits380 : eventVisits 380 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 74, 129, 129, 280, 280, 280, 280, 280, 280, 280, 280, 351, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits380
private theorem actualStart380 : startFrames[380]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd380 : finalFrames[380]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid380 : forwardPathValid 380 = true := by
  rw [forwardPathValid, actualVisits380, actualStart380, actualEnd380]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_74, canClimb_74_129, canClimb_129_280, canClimb_280_351, canClimb_351_1, Bool.true_and]

private theorem actualVisits381 : eventVisits 381 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 74, 130, 507, 507, 332, 512, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits381
private theorem actualStart381 : startFrames[381]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd381 : finalFrames[381]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid381 : forwardPathValid 381 = true := by
  rw [forwardPathValid, actualVisits381, actualStart381, actualEnd381]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_74, canClimb_74_130, canClimb_130_507, canClimb_332_512, canClimb_507_332, canClimb_512_1, Bool.true_and]

private theorem actualVisits382 : eventVisits 382 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 75, 261, 438, 538, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits382
private theorem actualStart382 : startFrames[382]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd382 : finalFrames[382]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid382 : forwardPathValid 382 = true := by
  rw [forwardPathValid, actualVisits382, actualStart382, actualEnd382]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_75, canClimb_75_261, canClimb_261_438, canClimb_438_538, canClimb_538_1, Bool.true_and]

private theorem actualVisits383 : eventVisits 383 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 75, 263, 263, 285, 285, 285, 285, 285, 285, 285, 285, 443, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits383
private theorem actualStart383 : startFrames[383]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd383 : finalFrames[383]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid383 : forwardPathValid 383 = true := by
  rw [forwardPathValid, actualVisits383, actualStart383, actualEnd383]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_75, canClimb_75_263, canClimb_263_285, canClimb_285_443, canClimb_443_1, Bool.true_and]

theorem forwardPathBlock047 (f : Nat) (hl : 376 ≤ f) (hu : f < 384) : forwardPathValid f = true := by
  have hs : f = 376 ∨ f = 377 ∨ f = 378 ∨ f = 379 ∨ f = 380 ∨ f = 381 ∨ f = 382 ∨ f = 383 := by omega
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact forwardPathValid376
  · exact forwardPathValid377
  · exact forwardPathValid378
  · exact forwardPathValid379
  · exact forwardPathValid380
  · exact forwardPathValid381
  · exact forwardPathValid382
  · exact forwardPathValid383

end CSL.Construction.PhysicalFramePaths


