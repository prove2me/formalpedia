-- Prove2me | Definitions.Def_CSL_Generated_FiniteCircuit_FramePathChecks_Paths_Batch03
-- name    : CSL_Generated_FiniteCircuit_FramePathChecks_Paths_Batch03
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T17:19:05.381802+00:00
-- url     : https://prove2.me/theorems/54597eee-3ab3-48ac-bc18-9eb10d711905
-- title:
--   Coded sorting library: Generated / FiniteCircuit / FramePathChecks / Paths / Batch03
-- statement:
--   Module `CodedSorting.Generated.FiniteCircuit.FramePathChecks.Paths.Batch03` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   Generated physical-frame checks. Uncompiled until a build record exists.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Generated.FiniteCircuit.FramePathChecks.Paths.Batch03

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Generated_FiniteCircuit_FramePathChecks_Nesting_Batch00
import Definitions.Def_CSL_Generated_FiniteCircuit_FramePathChecks_Nesting_Batch01
import Definitions.Def_CSL_Generated_FiniteCircuit_FramePathChecks_Nesting_Batch02
import Definitions.Def_CSL_Generated_FiniteCircuit_FramePathChecks_Nesting_Batch03
import Definitions.Def_CSL_Generated_FiniteCircuit_FramePathChecks_Nesting_Batch04
import Definitions.Def_CSL_Generated_FiniteCircuit_FramePathChecks_Nesting_Batch05
import Definitions.Def_CSL_Generated_FiniteCircuit_FramePathChecks_Nesting_Batch06
import Definitions.Def_CSL_Generated_FiniteCircuit_FramePathChecks_VisitNumbers_Batch03
import Definitions.Def_CSL_Generated_FiniteCircuit_FramePathChecks_VisitNumbers_Bridge

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

attribute [local irreducible] canClimb
private theorem actualVisits384 : eventVisits 384 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 76, 159, 159, 296, 296, 296, 296, 296, 296, 296, 390, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits384
private theorem actualStart384 : startFrames[384]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd384 : finalFrames[384]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid384 : forwardPathValid 384 = true := by
  rw [forwardPathValid, actualVisits384, actualStart384, actualEnd384]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_76, canClimb_76_159, canClimb_159_296, canClimb_296_390, canClimb_390_1, Bool.true_and]

private theorem actualVisits385 : eventVisits 385 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 76, 76, 508, 508, 428, 514, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits385
private theorem actualStart385 : startFrames[385]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd385 : finalFrames[385]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid385 : forwardPathValid 385 = true := by
  rw [forwardPathValid, actualVisits385, actualStart385, actualEnd385]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_76, canClimb_76_508, canClimb_428_514, canClimb_508_428, canClimb_514_1, Bool.true_and]

private theorem actualVisits386 : eventVisits 386 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 77, 141, 411, 589, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits386
private theorem actualStart386 : startFrames[386]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd386 : finalFrames[386]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid386 : forwardPathValid 386 = true := by
  rw [forwardPathValid, actualVisits386, actualStart386, actualEnd386]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_77, canClimb_77_141, canClimb_141_411, canClimb_411_589, canClimb_589_1, Bool.true_and]

private theorem actualVisits387 : eventVisits 387 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 77, 143, 143, 292, 292, 292, 292, 292, 357, 357, 516, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits387
private theorem actualStart387 : startFrames[387]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd387 : finalFrames[387]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid387 : forwardPathValid 387 = true := by
  rw [forwardPathValid, actualVisits387, actualStart387, actualEnd387]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_77, canClimb_77_143, canClimb_143_292, canClimb_292_357, canClimb_357_516, canClimb_516_1, Bool.true_and]

private theorem actualVisits388 : eventVisits 388 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 78, 207, 207, 298, 298, 298, 298, 298, 298, 298, 420, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits388
private theorem actualStart388 : startFrames[388]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd388 : finalFrames[388]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid388 : forwardPathValid 388 = true := by
  rw [forwardPathValid, actualVisits388, actualStart388, actualEnd388]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_78, canClimb_78_207, canClimb_207_298, canClimb_298_420, canClimb_420_1, Bool.true_and]

private theorem actualVisits389 : eventVisits 389 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 78, 211, 211, 269, 269, 269, 269, 269, 269, 404, 404, 561, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits389
private theorem actualStart389 : startFrames[389]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd389 : finalFrames[389]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid389 : forwardPathValid 389 = true := by
  rw [forwardPathValid, actualVisits389, actualStart389, actualEnd389]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_78, canClimb_78_211, canClimb_211_269, canClimb_269_404, canClimb_404_561, canClimb_561_1, Bool.true_and]

private theorem actualVisits390 : eventVisits 390 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 79, 188, 188, 284, 284, 284, 284, 284, 284, 284, 284, 424, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits390
private theorem actualStart390 : startFrames[390]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd390 : finalFrames[390]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid390 : forwardPathValid 390 = true := by
  rw [forwardPathValid, actualVisits390, actualStart390, actualEnd390]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_79, canClimb_79_188, canClimb_188_284, canClimb_284_424, canClimb_424_1, Bool.true_and]

private theorem actualVisits391 : eventVisits 391 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 79, 190, 190, 271, 271, 271, 271, 271, 271, 271, 271, 440, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits391
private theorem actualStart391 : startFrames[391]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd391 : finalFrames[391]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid391 : forwardPathValid 391 = true := by
  rw [forwardPathValid, actualVisits391, actualStart391, actualEnd391]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_79, canClimb_79_190, canClimb_190_271, canClimb_271_440, canClimb_440_1, Bool.true_and]

theorem forwardPathBlock048 (f : Nat) (hl : 384 ≤ f) (hu : f < 392) : forwardPathValid f = true := by
  have hs : f = 384 ∨ f = 385 ∨ f = 386 ∨ f = 387 ∨ f = 388 ∨ f = 389 ∨ f = 390 ∨ f = 391 := by omega
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact forwardPathValid384
  · exact forwardPathValid385
  · exact forwardPathValid386
  · exact forwardPathValid387
  · exact forwardPathValid388
  · exact forwardPathValid389
  · exact forwardPathValid390
  · exact forwardPathValid391

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

attribute [local irreducible] canClimb
private theorem actualVisits392 : eventVisits 392 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 80, 262, 262, 282, 282, 282, 282, 282, 282, 442, 442, 557, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits392
private theorem actualStart392 : startFrames[392]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd392 : finalFrames[392]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid392 : forwardPathValid 392 = true := by
  rw [forwardPathValid, actualVisits392, actualStart392, actualEnd392]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_80, canClimb_80_262, canClimb_262_282, canClimb_282_442, canClimb_442_557, canClimb_557_1, Bool.true_and]

private theorem actualVisits393 : eventVisits 393 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 80, 265, 265, 271, 271, 271, 271, 271, 271, 271, 271, 271, 271, 500, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits393
private theorem actualStart393 : startFrames[393]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd393 : finalFrames[393]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid393 : forwardPathValid 393 = true := by
  rw [forwardPathValid, actualVisits393, actualStart393, actualEnd393]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_80, canClimb_80_265, canClimb_265_271, canClimb_271_500, canClimb_500_1, Bool.true_and]

private theorem actualVisits394 : eventVisits 394 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 81, 208, 499, 611, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits394
private theorem actualStart394 : startFrames[394]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd394 : finalFrames[394]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid394 : forwardPathValid 394 = true := by
  rw [forwardPathValid, actualVisits394, actualStart394, actualEnd394]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_81, canClimb_81_208, canClimb_208_499, canClimb_499_611, canClimb_611_1, Bool.true_and]

private theorem actualVisits395 : eventVisits 395 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 81, 210, 210, 293, 293, 293, 293, 293, 293, 293, 417, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits395
private theorem actualStart395 : startFrames[395]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd395 : finalFrames[395]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid395 : forwardPathValid 395 = true := by
  rw [forwardPathValid, actualVisits395, actualStart395, actualEnd395]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_81, canClimb_81_210, canClimb_210_293, canClimb_293_417, canClimb_417_1, Bool.true_and]

private theorem actualVisits396 : eventVisits 396 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 82, 171, 364, 621, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits396
private theorem actualStart396 : startFrames[396]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd396 : finalFrames[396]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid396 : forwardPathValid 396 = true := by
  rw [forwardPathValid, actualVisits396, actualStart396, actualEnd396]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_82, canClimb_82_171, canClimb_171_364, canClimb_364_621, canClimb_621_1, Bool.true_and]

private theorem actualVisits397 : eventVisits 397 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 82, 175, 175, 269, 269, 269, 269, 269, 269, 446, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits397
private theorem actualStart397 : startFrames[397]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd397 : finalFrames[397]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid397 : forwardPathValid 397 = true := by
  rw [forwardPathValid, actualVisits397, actualStart397, actualEnd397]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_82, canClimb_82_175, canClimb_175_269, canClimb_269_446, canClimb_446_1, Bool.true_and]

private theorem actualVisits398 : eventVisits 398 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 83, 255, 449, 601, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits398
private theorem actualStart398 : startFrames[398]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd398 : finalFrames[398]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid398 : forwardPathValid 398 = true := by
  rw [forwardPathValid, actualVisits398, actualStart398, actualEnd398]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_83, canClimb_83_255, canClimb_255_449, canClimb_449_601, canClimb_601_1, Bool.true_and]

private theorem actualVisits399 : eventVisits 399 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 83, 259, 259, 269, 269, 269, 269, 269, 269, 269, 494, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits399
private theorem actualStart399 : startFrames[399]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd399 : finalFrames[399]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid399 : forwardPathValid 399 = true := by
  rw [forwardPathValid, actualVisits399, actualStart399, actualEnd399]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_83, canClimb_83_259, canClimb_259_269, canClimb_269_494, canClimb_494_1, Bool.true_and]

theorem forwardPathBlock049 (f : Nat) (hl : 392 ≤ f) (hu : f < 400) : forwardPathValid f = true := by
  have hs : f = 392 ∨ f = 393 ∨ f = 394 ∨ f = 395 ∨ f = 396 ∨ f = 397 ∨ f = 398 ∨ f = 399 := by omega
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact forwardPathValid392
  · exact forwardPathValid393
  · exact forwardPathValid394
  · exact forwardPathValid395
  · exact forwardPathValid396
  · exact forwardPathValid397
  · exact forwardPathValid398
  · exact forwardPathValid399

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

attribute [local irreducible] canClimb
private theorem actualVisits400 : eventVisits 400 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 37, 37, 284, 284, 284, 284, 284, 284, 284, 284, 335, 335, 579, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits400
private theorem actualStart400 : startFrames[400]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd400 : finalFrames[400]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid400 : forwardPathValid 400 = true := by
  rw [forwardPathValid, actualVisits400, actualStart400, actualEnd400]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_37, canClimb_37_284, canClimb_284_335, canClimb_335_579, canClimb_579_1, Bool.true_and]

private theorem actualVisits401 : eventVisits 401 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 76, 76, 271, 271, 271, 271, 271, 271, 271, 271, 422, 422, 563, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits401
private theorem actualStart401 : startFrames[401]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd401 : finalFrames[401]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid401 : forwardPathValid 401 = true := by
  rw [forwardPathValid, actualVisits401, actualStart401, actualEnd401]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_76, canClimb_76_271, canClimb_271_422, canClimb_422_563, canClimb_563_1, Bool.true_and]

private theorem actualVisits402 : eventVisits 402 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 84, 142, 142, 299, 299, 299, 299, 299, 299, 299, 299, 342, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits402
private theorem actualStart402 : startFrames[402]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd402 : finalFrames[402]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid402 : forwardPathValid 402 = true := by
  rw [forwardPathValid, actualVisits402, actualStart402, actualEnd402]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_84, canClimb_84_142, canClimb_142_299, canClimb_299_342, canClimb_342_1, Bool.true_and]

private theorem actualVisits403 : eventVisits 403 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 84, 145, 145, 269, 269, 269, 269, 269, 269, 269, 269, 327, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits403
private theorem actualStart403 : startFrames[403]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd403 : finalFrames[403]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid403 : forwardPathValid 403 = true := by
  rw [forwardPathValid, actualVisits403, actualStart403, actualEnd403]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_84, canClimb_84_145, canClimb_145_269, canClimb_269_327, canClimb_327_1, Bool.true_and]

private theorem actualVisits404 : eventVisits 404 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 85, 203, 203, 282, 282, 282, 282, 282, 282, 503, 503, 570, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits404
private theorem actualStart404 : startFrames[404]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd404 : finalFrames[404]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid404 : forwardPathValid 404 = true := by
  rw [forwardPathValid, actualVisits404, actualStart404, actualEnd404]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_85, canClimb_85_203, canClimb_203_282, canClimb_282_503, canClimb_503_570, canClimb_570_1, Bool.true_and]

private theorem actualVisits405 : eventVisits 405 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 85, 205, 205, 271, 271, 271, 271, 271, 271, 271, 271, 386, 386, 568, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits405
private theorem actualStart405 : startFrames[405]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd405 : finalFrames[405]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid405 : forwardPathValid 405 = true := by
  rw [forwardPathValid, actualVisits405, actualStart405, actualEnd405]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_85, canClimb_85_205, canClimb_205_271, canClimb_271_386, canClimb_386_568, canClimb_568_1, Bool.true_and]

private theorem actualVisits406 : eventVisits 406 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 86, 172, 172, 292, 292, 292, 292, 292, 292, 292, 460, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits406
private theorem actualStart406 : startFrames[406]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd406 : finalFrames[406]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid406 : forwardPathValid 406 = true := by
  rw [forwardPathValid, actualVisits406, actualStart406, actualEnd406]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_86, canClimb_86_172, canClimb_172_292, canClimb_292_460, canClimb_460_1, Bool.true_and]

private theorem actualVisits407 : eventVisits 407 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 86, 175, 376, 595, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits407
private theorem actualStart407 : startFrames[407]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd407 : finalFrames[407]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid407 : forwardPathValid 407 = true := by
  rw [forwardPathValid, actualVisits407, actualStart407, actualEnd407]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_86, canClimb_86_175, canClimb_175_376, canClimb_376_595, canClimb_595_1, Bool.true_and]

theorem forwardPathBlock050 (f : Nat) (hl : 400 ≤ f) (hu : f < 408) : forwardPathValid f = true := by
  have hs : f = 400 ∨ f = 401 ∨ f = 402 ∨ f = 403 ∨ f = 404 ∨ f = 405 ∨ f = 406 ∨ f = 407 := by omega
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact forwardPathValid400
  · exact forwardPathValid401
  · exact forwardPathValid402
  · exact forwardPathValid403
  · exact forwardPathValid404
  · exact forwardPathValid405
  · exact forwardPathValid406
  · exact forwardPathValid407

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

attribute [local irreducible] canClimb
private theorem actualVisits408 : eventVisits 408 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 87, 202, 202, 285, 285, 285, 285, 285, 285, 285, 285, 502, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits408
private theorem actualStart408 : startFrames[408]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd408 : finalFrames[408]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid408 : forwardPathValid 408 = true := by
  rw [forwardPathValid, actualVisits408, actualStart408, actualEnd408]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_87, canClimb_87_202, canClimb_202_285, canClimb_285_502, canClimb_502_1, Bool.true_and]

private theorem actualVisits409 : eventVisits 409 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 87, 204, 204, 294, 294, 294, 294, 294, 294, 294, 294, 340, 340, 583, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits409
private theorem actualStart409 : startFrames[409]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd409 : finalFrames[409]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid409 : forwardPathValid 409 = true := by
  rw [forwardPathValid, actualVisits409, actualStart409, actualEnd409]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_87, canClimb_87_204, canClimb_204_294, canClimb_294_340, canClimb_340_583, canClimb_583_1, Bool.true_and]

private theorem actualVisits410 : eventVisits 410 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 88, 256, 256, 281, 281, 281, 281, 281, 281, 281, 281, 497, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits410
private theorem actualStart410 : startFrames[410]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd410 : finalFrames[410]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid410 : forwardPathValid 410 = true := by
  rw [forwardPathValid, actualVisits410, actualStart410, actualEnd410]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_88, canClimb_88_256, canClimb_256_281, canClimb_281_497, canClimb_497_1, Bool.true_and]

private theorem actualVisits411 : eventVisits 411 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 88, 258, 439, 629, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits411
private theorem actualStart411 : startFrames[411]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd411 : finalFrames[411]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid411 : forwardPathValid 411 = true := by
  rw [forwardPathValid, actualVisits411, actualStart411, actualEnd411]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_88, canClimb_88_258, canClimb_258_439, canClimb_439_629, canClimb_629_1, Bool.true_and]

private theorem actualVisits412 : eventVisits 412 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 89, 187, 187, 283, 283, 283, 283, 283, 425, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits412
private theorem actualStart412 : startFrames[412]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd412 : finalFrames[412]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid412 : forwardPathValid 412 = true := by
  rw [forwardPathValid, actualVisits412, actualStart412, actualEnd412]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_89, canClimb_89_187, canClimb_187_283, canClimb_283_425, canClimb_425_1, Bool.true_and]

private theorem actualVisits413 : eventVisits 413 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 89, 190, 509, 509, 390, 517, 517, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits413
private theorem actualStart413 : startFrames[413]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd413 : finalFrames[413]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid413 : forwardPathValid 413 = true := by
  rw [forwardPathValid, actualVisits413, actualStart413, actualEnd413]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_89, canClimb_89_190, canClimb_190_509, canClimb_390_517, canClimb_509_390, canClimb_517_1, Bool.true_and]

private theorem actualVisits414 : eventVisits 414 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 90, 243, 243, 286, 286, 286, 286, 286, 286, 286, 496, 496, 611, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits414
private theorem actualStart414 : startFrames[414]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd414 : finalFrames[414]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid414 : forwardPathValid 414 = true := by
  rw [forwardPathValid, actualVisits414, actualStart414, actualEnd414]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_90, canClimb_90_243, canClimb_243_286, canClimb_286_496, canClimb_496_611, canClimb_611_1, Bool.true_and]

private theorem actualVisits415 : eventVisits 415 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 90, 245, 455, 631, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits415
private theorem actualStart415 : startFrames[415]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd415 : finalFrames[415]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid415 : forwardPathValid 415 = true := by
  rw [forwardPathValid, actualVisits415, actualStart415, actualEnd415]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_90, canClimb_90_245, canClimb_245_455, canClimb_455_631, canClimb_631_1, Bool.true_and]

theorem forwardPathBlock051 (f : Nat) (hl : 408 ≤ f) (hu : f < 416) : forwardPathValid f = true := by
  have hs : f = 408 ∨ f = 409 ∨ f = 410 ∨ f = 411 ∨ f = 412 ∨ f = 413 ∨ f = 414 ∨ f = 415 := by omega
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact forwardPathValid408
  · exact forwardPathValid409
  · exact forwardPathValid410
  · exact forwardPathValid411
  · exact forwardPathValid412
  · exact forwardPathValid413
  · exact forwardPathValid414
  · exact forwardPathValid415

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

attribute [local irreducible] canClimb
private theorem actualVisits416 : eventVisits 416 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 91, 153, 508, 426, 563, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits416
private theorem actualStart416 : startFrames[416]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd416 : finalFrames[416]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid416 : forwardPathValid 416 = true := by
  rw [forwardPathValid, actualVisits416, actualStart416, actualEnd416]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_91, canClimb_91_153, canClimb_153_508, canClimb_426_563, canClimb_508_426, canClimb_563_1, Bool.true_and]

private theorem actualVisits417 : eventVisits 417 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 91, 157, 157, 275, 275, 275, 275, 275, 275, 330, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits417
private theorem actualStart417 : startFrames[417]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd417 : finalFrames[417]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid417 : forwardPathValid 417 = true := by
  rw [forwardPathValid, actualVisits417, actualStart417, actualEnd417]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_91, canClimb_91_157, canClimb_157_275, canClimb_275_330, canClimb_330_1, Bool.true_and]

private theorem actualVisits418 : eventVisits 418 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 92, 237, 237, 284, 284, 284, 284, 284, 284, 480, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits418
private theorem actualStart418 : startFrames[418]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd418 : finalFrames[418]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid418 : forwardPathValid 418 = true := by
  rw [forwardPathValid, actualVisits418, actualStart418, actualEnd418]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_92, canClimb_92_237, canClimb_237_284, canClimb_284_480, canClimb_480_1, Bool.true_and]

private theorem actualVisits419 : eventVisits 419 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 92, 241, 241, 273, 273, 273, 273, 273, 273, 464, 464, 550, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits419
private theorem actualStart419 : startFrames[419]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd419 : finalFrames[419]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid419 : forwardPathValid 419 = true := by
  rw [forwardPathValid, actualVisits419, actualStart419, actualEnd419]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_92, canClimb_92_241, canClimb_241_273, canClimb_273_464, canClimb_464_550, canClimb_550_1, Bool.true_and]

private theorem actualVisits420 : eventVisits 420 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 93, 137, 137, 295, 295, 295, 295, 295, 295, 295, 295, 387, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits420
private theorem actualStart420 : startFrames[420]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd420 : finalFrames[420]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid420 : forwardPathValid 420 = true := by
  rw [forwardPathValid, actualVisits420, actualStart420, actualEnd420]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_93, canClimb_93_137, canClimb_137_295, canClimb_295_387, canClimb_387_1, Bool.true_and]

private theorem actualVisits421 : eventVisits 421 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 93, 139, 139, 273, 273, 273, 273, 273, 273, 273, 346, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits421
private theorem actualStart421 : startFrames[421]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd421 : finalFrames[421]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid421 : forwardPathValid 421 = true := by
  rw [forwardPathValid, actualVisits421, actualStart421, actualEnd421]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_93, canClimb_93_139, canClimb_139_273, canClimb_273_346, canClimb_346_1, Bool.true_and]

private theorem actualVisits422 : eventVisits 422 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 94, 183, 183, 298, 298, 298, 298, 298, 298, 298, 450, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits422
private theorem actualStart422 : startFrames[422]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd422 : finalFrames[422]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid422 : forwardPathValid 422 = true := by
  rw [forwardPathValid, actualVisits422, actualStart422, actualEnd422]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_94, canClimb_94_183, canClimb_183_298, canClimb_298_450, canClimb_450_1, Bool.true_and]

private theorem actualVisits423 : eventVisits 423 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 94, 94, 275, 275, 275, 275, 275, 458, 458, 554, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits423
private theorem actualStart423 : startFrames[423]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd423 : finalFrames[423]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid423 : forwardPathValid 423 = true := by
  rw [forwardPathValid, actualVisits423, actualStart423, actualEnd423]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_94, canClimb_94_275, canClimb_275_458, canClimb_458_554, canClimb_554_1, Bool.true_and]

theorem forwardPathBlock052 (f : Nat) (hl : 416 ≤ f) (hu : f < 424) : forwardPathValid f = true := by
  have hs : f = 416 ∨ f = 417 ∨ f = 418 ∨ f = 419 ∨ f = 420 ∨ f = 421 ∨ f = 422 ∨ f = 423 := by omega
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact forwardPathValid416
  · exact forwardPathValid417
  · exact forwardPathValid418
  · exact forwardPathValid419
  · exact forwardPathValid420
  · exact forwardPathValid421
  · exact forwardPathValid422
  · exact forwardPathValid423

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

attribute [local irreducible] canClimb
private theorem actualVisits424 : eventVisits 424 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 95, 244, 244, 292, 292, 292, 292, 292, 292, 292, 292, 485, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits424
private theorem actualStart424 : startFrames[424]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd424 : finalFrames[424]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid424 : forwardPathValid 424 = true := by
  rw [forwardPathValid, actualVisits424, actualStart424, actualEnd424]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_95, canClimb_95_244, canClimb_244_292, canClimb_292_485, canClimb_485_1, Bool.true_and]

private theorem actualVisits425 : eventVisits 425 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 95, 247, 247, 275, 275, 275, 275, 275, 275, 482, 482, 541, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits425
private theorem actualStart425 : startFrames[425]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd425 : finalFrames[425]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid425 : forwardPathValid 425 = true := by
  rw [forwardPathValid, actualVisits425, actualStart425, actualEnd425]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_95, canClimb_95_247, canClimb_247_275, canClimb_275_482, canClimb_482_541, canClimb_541_1, Bool.true_and]

private theorem actualVisits426 : eventVisits 426 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 96, 165, 165, 285, 285, 285, 285, 285, 285, 285, 285, 363, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits426
private theorem actualStart426 : startFrames[426]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd426 : finalFrames[426]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid426 : forwardPathValid 426 = true := by
  rw [forwardPathValid, actualVisits426, actualStart426, actualEnd426]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_96, canClimb_96_165, canClimb_165_285, canClimb_285_363, canClimb_363_1, Bool.true_and]

private theorem actualVisits427 : eventVisits 427 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 96, 169, 169, 273, 273, 273, 273, 273, 273, 398, 398, 546, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits427
private theorem actualStart427 : startFrames[427]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd427 : finalFrames[427]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid427 : forwardPathValid 427 = true := by
  rw [forwardPathValid, actualVisits427, actualStart427, actualEnd427]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_96, canClimb_96_169, canClimb_169_273, canClimb_273_398, canClimb_398_546, canClimb_546_1, Bool.true_and]

private theorem actualVisits428 : eventVisits 428 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 97, 238, 469, 623, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits428
private theorem actualStart428 : startFrames[428]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd428 : finalFrames[428]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid428 : forwardPathValid 428 = true := by
  rw [forwardPathValid, actualVisits428, actualStart428, actualEnd428]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_97, canClimb_97_238, canClimb_238_469, canClimb_469_623, canClimb_623_1, Bool.true_and]

private theorem actualVisits429 : eventVisits 429 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 97, 240, 240, 283, 283, 283, 283, 283, 477, 477, 615, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits429
private theorem actualStart429 : startFrames[429]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd429 : finalFrames[429]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid429 : forwardPathValid 429 = true := by
  rw [forwardPathValid, actualVisits429, actualStart429, actualEnd429]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_97, canClimb_97_240, canClimb_240_283, canClimb_283_477, canClimb_477_615, canClimb_615_1, Bool.true_and]

private theorem actualVisits430 : eventVisits 430 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 98, 136, 136, 296, 296, 296, 296, 296, 296, 341, 341, 577, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits430
private theorem actualStart430 : startFrames[430]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd430 : finalFrames[430]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid430 : forwardPathValid 430 = true := by
  rw [forwardPathValid, actualVisits430, actualStart430, actualEnd430]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_98, canClimb_98_136, canClimb_136_296, canClimb_296_341, canClimb_341_577, canClimb_577_1, Bool.true_and]

private theorem actualVisits431 : eventVisits 431 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 98, 138, 138, 285, 285, 285, 285, 285, 285, 285, 285, 402, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits431
private theorem actualStart431 : startFrames[431]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd431 : finalFrames[431]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid431 : forwardPathValid 431 = true := by
  rw [forwardPathValid, actualVisits431, actualStart431, actualEnd431]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_98, canClimb_98_138, canClimb_138_285, canClimb_285_402, canClimb_402_1, Bool.true_and]

theorem forwardPathBlock053 (f : Nat) (hl : 424 ≤ f) (hu : f < 432) : forwardPathValid f = true := by
  have hs : f = 424 ∨ f = 425 ∨ f = 426 ∨ f = 427 ∨ f = 428 ∨ f = 429 ∨ f = 430 ∨ f = 431 := by omega
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact forwardPathValid424
  · exact forwardPathValid425
  · exact forwardPathValid426
  · exact forwardPathValid427
  · exact forwardPathValid428
  · exact forwardPathValid429
  · exact forwardPathValid430
  · exact forwardPathValid431

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

attribute [local irreducible] canClimb
private theorem actualVisits432 : eventVisits 432 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 99, 156, 156, 298, 298, 298, 298, 298, 342, 342, 583, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits432
private theorem actualStart432 : startFrames[432]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd432 : finalFrames[432]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid432 : forwardPathValid 432 = true := by
  rw [forwardPathValid, actualVisits432, actualStart432, actualEnd432]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_99, canClimb_99_156, canClimb_156_298, canClimb_298_342, canClimb_342_583, canClimb_583_1, Bool.true_and]

private theorem actualVisits433 : eventVisits 433 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 99, 157, 508, 508, 418, 542, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits433
private theorem actualStart433 : startFrames[433]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd433 : finalFrames[433]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid433 : forwardPathValid 433 = true := by
  rw [forwardPathValid, actualVisits433, actualStart433, actualEnd433]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_99, canClimb_99_157, canClimb_157_508, canClimb_418_542, canClimb_508_418, canClimb_542_1, Bool.true_and]

private theorem actualVisits434 : eventVisits 434 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 100, 225, 225, 283, 283, 283, 283, 283, 468, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits434
private theorem actualStart434 : startFrames[434]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd434 : finalFrames[434]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid434 : forwardPathValid 434 = true := by
  rw [forwardPathValid, actualVisits434, actualStart434, actualEnd434]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_100, canClimb_100_225, canClimb_225_283, canClimb_283_468, canClimb_468_1, Bool.true_and]

private theorem actualVisits435 : eventVisits 435 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 100, 227, 478, 620, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits435
private theorem actualStart435 : startFrames[435]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd435 : finalFrames[435]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid435 : forwardPathValid 435 = true := by
  rw [forwardPathValid, actualVisits435, actualStart435, actualEnd435]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_100, canClimb_100_227, canClimb_227_478, canClimb_478_620, canClimb_620_1, Bool.true_and]

private theorem actualVisits436 : eventVisits 436 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 101, 221, 470, 527, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits436
private theorem actualStart436 : startFrames[436]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd436 : finalFrames[436]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid436 : forwardPathValid 436 = true := by
  rw [forwardPathValid, actualVisits436, actualStart436, actualEnd436]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_101, canClimb_101_221, canClimb_221_470, canClimb_470_527, canClimb_527_1, Bool.true_and]

private theorem actualVisits437 : eventVisits 437 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 101, 223, 223, 275, 275, 275, 275, 275, 275, 275, 416, 416, 547, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits437
private theorem actualStart437 : startFrames[437]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd437 : finalFrames[437]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid437 : forwardPathValid 437 = true := by
  rw [forwardPathValid, actualVisits437, actualStart437, actualEnd437]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_101, canClimb_101_223, canClimb_223_275, canClimb_275_416, canClimb_416_547, canClimb_547_1, Bool.true_and]

private theorem actualVisits438 : eventVisits 438 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 102, 226, 226, 297, 297, 297, 297, 297, 297, 297, 467, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits438
private theorem actualStart438 : startFrames[438]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd438 : finalFrames[438]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid438 : forwardPathValid 438 = true := by
  rw [forwardPathValid, actualVisits438, actualStart438, actualEnd438]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_102, canClimb_102_226, canClimb_226_297, canClimb_297_467, canClimb_467_1, Bool.true_and]

private theorem actualVisits439 : eventVisits 439 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 102, 229, 229, 273, 273, 273, 273, 273, 273, 476, 476, 539, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits439
private theorem actualStart439 : startFrames[439]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd439 : finalFrames[439]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid439 : forwardPathValid 439 = true := by
  rw [forwardPathValid, actualVisits439, actualStart439, actualEnd439]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_102, canClimb_102_229, canClimb_229_273, canClimb_273_476, canClimb_476_539, canClimb_539_1, Bool.true_and]

theorem forwardPathBlock054 (f : Nat) (hl : 432 ≤ f) (hu : f < 440) : forwardPathValid f = true := by
  have hs : f = 432 ∨ f = 433 ∨ f = 434 ∨ f = 435 ∨ f = 436 ∨ f = 437 ∨ f = 438 ∨ f = 439 := by omega
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact forwardPathValid432
  · exact forwardPathValid433
  · exact forwardPathValid434
  · exact forwardPathValid435
  · exact forwardPathValid436
  · exact forwardPathValid437
  · exact forwardPathValid438
  · exact forwardPathValid439

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

attribute [local irreducible] canClimb
private theorem actualVisits440 : eventVisits 440 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 103, 220, 220, 299, 299, 299, 299, 299, 299, 299, 406, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits440
private theorem actualStart440 : startFrames[440]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd440 : finalFrames[440]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid440 : forwardPathValid 440 = true := by
  rw [forwardPathValid, actualVisits440, actualStart440, actualEnd440]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_103, canClimb_103_220, canClimb_220_299, canClimb_299_406, canClimb_406_1, Bool.true_and]

private theorem actualVisits441 : eventVisits 441 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 103, 222, 222, 286, 286, 286, 286, 286, 286, 286, 459, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits441
private theorem actualStart441 : startFrames[441]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd441 : finalFrames[441]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid441 : forwardPathValid 441 = true := by
  rw [forwardPathValid, actualVisits441, actualStart441, actualEnd441]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_103, canClimb_103_222, canClimb_222_286, canClimb_286_459, canClimb_459_1, Bool.true_and]

private theorem actualVisits442 : eventVisits 442 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 104, 168, 168, 282, 282, 282, 282, 282, 282, 399, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits442
private theorem actualStart442 : startFrames[442]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd442 : finalFrames[442]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid442 : forwardPathValid 442 = true := by
  rw [forwardPathValid, actualVisits442, actualStart442, actualEnd442]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_104, canClimb_104_168, canClimb_168_282, canClimb_282_399, canClimb_399_1, Bool.true_and]

private theorem actualVisits443 : eventVisits 443 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 104, 169, 367, 621, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits443
private theorem actualStart443 : startFrames[443]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd443 : finalFrames[443]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid443 : forwardPathValid 443 = true := by
  rw [forwardPathValid, actualVisits443, actualStart443, actualEnd443]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_104, canClimb_104_169, canClimb_169_367, canClimb_367_621, canClimb_621_1, Bool.true_and]

private theorem actualVisits444 : eventVisits 444 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 79, 509, 392, 513, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits444
private theorem actualStart444 : startFrames[444]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd444 : finalFrames[444]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid444 : forwardPathValid 444 = true := by
  rw [forwardPathValid, actualVisits444, actualStart444, actualEnd444]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_79, canClimb_79_509, canClimb_392_513, canClimb_509_392, canClimb_513_1, Bool.true_and]

private theorem actualVisits445 : eventVisits 445 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24, 24, 293, 293, 293, 293, 293, 447, 447, 564, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits445
private theorem actualStart445 : startFrames[445]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd445 : finalFrames[445]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid445 : forwardPathValid 445 = true := by
  rw [forwardPathValid, actualVisits445, actualStart445, actualEnd445]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_24, canClimb_24_293, canClimb_293_447, canClimb_447_564, canClimb_564_1, Bool.true_and]

private theorem actualVisits446 : eventVisits 446 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 105, 231, 231, 288, 288, 288, 288, 288, 456, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits446
private theorem actualStart446 : startFrames[446]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd446 : finalFrames[446]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid446 : forwardPathValid 446 = true := by
  rw [forwardPathValid, actualVisits446, actualStart446, actualEnd446]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_105, canClimb_105_231, canClimb_231_288, canClimb_288_456, canClimb_456_1, Bool.true_and]

private theorem actualVisits447 : eventVisits 447 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 105, 235, 235, 277, 277, 277, 277, 277, 277, 470, 470, 529, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits447
private theorem actualStart447 : startFrames[447]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd447 : finalFrames[447]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid447 : forwardPathValid 447 = true := by
  rw [forwardPathValid, actualVisits447, actualStart447, actualEnd447]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_105, canClimb_105_235, canClimb_235_277, canClimb_277_470, canClimb_470_529, canClimb_529_1, Bool.true_and]

theorem forwardPathBlock055 (f : Nat) (hl : 440 ≤ f) (hu : f < 448) : forwardPathValid f = true := by
  have hs : f = 440 ∨ f = 441 ∨ f = 442 ∨ f = 443 ∨ f = 444 ∨ f = 445 ∨ f = 446 ∨ f = 447 := by omega
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact forwardPathValid440
  · exact forwardPathValid441
  · exact forwardPathValid442
  · exact forwardPathValid443
  · exact forwardPathValid444
  · exact forwardPathValid445
  · exact forwardPathValid446
  · exact forwardPathValid447

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

attribute [local irreducible] canClimb
private theorem actualVisits448 : eventVisits 448 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 106, 195, 195, 301, 301, 301, 301, 301, 301, 301, 301, 412, 412, 596, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits448
private theorem actualStart448 : startFrames[448]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd448 : finalFrames[448]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid448 : forwardPathValid 448 = true := by
  rw [forwardPathValid, actualVisits448, actualStart448, actualEnd448]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_106, canClimb_106_195, canClimb_195_301, canClimb_301_412, canClimb_412_596, canClimb_596_1, Bool.true_and]

private theorem actualVisits449 : eventVisits 449 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 106, 197, 197, 279, 279, 279, 279, 279, 279, 490, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits449
private theorem actualStart449 : startFrames[449]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd449 : finalFrames[449]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid449 : forwardPathValid 449 = true := by
  rw [forwardPathValid, actualVisits449, actualStart449, actualEnd449]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_106, canClimb_106_197, canClimb_197_279, canClimb_279_490, canClimb_490_1, Bool.true_and]

private theorem actualVisits450 : eventVisits 450 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 107, 249, 249, 301, 301, 301, 301, 301, 301, 301, 301, 492, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits450
private theorem actualStart450 : startFrames[450]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd450 : finalFrames[450]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid450 : forwardPathValid 450 = true := by
  rw [forwardPathValid, actualVisits450, actualStart450, actualEnd450]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_107, canClimb_107_249, canClimb_249_301, canClimb_301_492, canClimb_492_1, Bool.true_and]

private theorem actualVisits451 : eventVisits 451 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 107, 253, 447, 601, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits451
private theorem actualStart451 : startFrames[451]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd451 : finalFrames[451]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid451 : forwardPathValid 451 = true := by
  rw [forwardPathValid, actualVisits451, actualStart451, actualEnd451]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_107, canClimb_107_253, canClimb_253_447, canClimb_447_601, canClimb_601_1, Bool.true_and]

private theorem actualVisits452 : eventVisits 452 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 108, 213, 481, 615, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits452
private theorem actualStart452 : startFrames[452]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd452 : finalFrames[452]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid452 : forwardPathValid 452 = true := by
  rw [forwardPathValid, actualVisits452, actualStart452, actualEnd452]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_108, canClimb_108_213, canClimb_213_481, canClimb_481_615, canClimb_615_1, Bool.true_and]

private theorem actualVisits453 : eventVisits 453 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 108, 215, 215, 290, 290, 290, 290, 290, 290, 290, 429, 429, 585, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits453
private theorem actualStart453 : startFrames[453]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd453 : finalFrames[453]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid453 : forwardPathValid 453 = true := by
  rw [forwardPathValid, actualVisits453, actualStart453, actualEnd453]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_108, canClimb_108_215, canClimb_215_290, canClimb_290_429, canClimb_429_585, canClimb_585_1, Bool.true_and]

private theorem actualVisits454 : eventVisits 454 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 109, 196, 196, 289, 289, 289, 289, 289, 289, 289, 430, 430, 575, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits454
private theorem actualStart454 : startFrames[454]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd454 : finalFrames[454]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid454 : forwardPathValid 454 = true := by
  rw [forwardPathValid, actualVisits454, actualStart454, actualEnd454]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_109, canClimb_109_196, canClimb_196_289, canClimb_289_430, canClimb_430_575, canClimb_575_1, Bool.true_and]

private theorem actualVisits455 : eventVisits 455 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 109, 199, 199, 277, 277, 277, 277, 277, 277, 349, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits455
private theorem actualStart455 : startFrames[455]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd455 : finalFrames[455]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid455 : forwardPathValid 455 = true := by
  rw [forwardPathValid, actualVisits455, actualStart455, actualEnd455]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_109, canClimb_109_199, canClimb_199_277, canClimb_277_349, canClimb_349_1, Bool.true_and]

theorem forwardPathBlock056 (f : Nat) (hl : 448 ≤ f) (hu : f < 456) : forwardPathValid f = true := by
  have hs : f = 448 ∨ f = 449 ∨ f = 450 ∨ f = 451 ∨ f = 452 ∨ f = 453 ∨ f = 454 ∨ f = 455 := by omega
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact forwardPathValid448
  · exact forwardPathValid449
  · exact forwardPathValid450
  · exact forwardPathValid451
  · exact forwardPathValid452
  · exact forwardPathValid453
  · exact forwardPathValid454
  · exact forwardPathValid455

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

attribute [local irreducible] canClimb
private theorem actualVisits456 : eventVisits 456 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 110, 216, 216, 278, 278, 278, 278, 278, 278, 375, 375, 584, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits456
private theorem actualStart456 : startFrames[456]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd456 : finalFrames[456]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid456 : forwardPathValid 456 = true := by
  rw [forwardPathValid, actualVisits456, actualStart456, actualEnd456]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_110, canClimb_110_216, canClimb_216_278, canClimb_278_375, canClimb_375_584, canClimb_584_1, Bool.true_and]

private theorem actualVisits457 : eventVisits 457 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 110, 217, 217, 277, 277, 277, 277, 277, 277, 277, 452, 452, 526, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits457
private theorem actualStart457 : startFrames[457]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd457 : finalFrames[457]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid457 : forwardPathValid 457 = true := by
  rw [forwardPathValid, actualVisits457, actualStart457, actualEnd457]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_110, canClimb_110_217, canClimb_217_277, canClimb_277_452, canClimb_452_526, canClimb_526_1, Bool.true_and]

private theorem actualVisits458 : eventVisits 458 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 111, 232, 232, 300, 300, 300, 300, 300, 300, 300, 300, 473, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits458
private theorem actualStart458 : startFrames[458]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd458 : finalFrames[458]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid458 : forwardPathValid 458 = true := by
  rw [forwardPathValid, actualVisits458, actualStart458, actualEnd458]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_111, canClimb_111_232, canClimb_232_300, canClimb_300_473, canClimb_473_1, Bool.true_and]

private theorem actualVisits459 : eventVisits 459 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 111, 234, 458, 549, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits459
private theorem actualStart459 : startFrames[459]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd459 : finalFrames[459]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid459 : forwardPathValid 459 = true := by
  rw [forwardPathValid, actualVisits459, actualStart459, actualEnd459]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_111, canClimb_111_234, canClimb_234_458, canClimb_458_549, canClimb_549_1, Bool.true_and]

private theorem actualVisits460 : eventVisits 460 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 112, 252, 252, 291, 291, 291, 291, 291, 291, 291, 291, 489, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits460
private theorem actualStart460 : startFrames[460]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd460 : finalFrames[460]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid460 : forwardPathValid 460 = true := by
  rw [forwardPathValid, actualVisits460, actualStart460, actualEnd460]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_112, canClimb_112_252, canClimb_252_291, canClimb_291_489, canClimb_489_1, Bool.true_and]

private theorem actualVisits461 : eventVisits 461 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 112, 253, 253, 277, 277, 277, 277, 277, 277, 277, 488, 488, 537, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits461
private theorem actualStart461 : startFrames[461]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd461 : finalFrames[461]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid461 : forwardPathValid 461 = true := by
  rw [forwardPathValid, actualVisits461, actualStart461, actualEnd461]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_112, canClimb_112_253, canClimb_253_277, canClimb_277_488, canClimb_488_537, canClimb_537_1, Bool.true_and]

private theorem actualVisits462 : eventVisits 462 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 49, 506, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits462
private theorem actualStart462 : startFrames[462]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd462 : finalFrames[462]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid462 : forwardPathValid 462 = true := by
  rw [forwardPathValid, actualVisits462, actualStart462, actualEnd462]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_49, canClimb_49_506, canClimb_506_1, Bool.true_and]

private theorem actualVisits463 : eventVisits 463 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 54, 506, 506, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits463
private theorem actualStart463 : startFrames[463]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd463 : finalFrames[463]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid463 : forwardPathValid 463 = true := by
  rw [forwardPathValid, actualVisits463, actualStart463, actualEnd463]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_54, canClimb_54_506, canClimb_506_1, Bool.true_and]

theorem forwardPathBlock057 (f : Nat) (hl : 456 ≤ f) (hu : f < 464) : forwardPathValid f = true := by
  have hs : f = 456 ∨ f = 457 ∨ f = 458 ∨ f = 459 ∨ f = 460 ∨ f = 461 ∨ f = 462 ∨ f = 463 := by omega
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact forwardPathValid456
  · exact forwardPathValid457
  · exact forwardPathValid458
  · exact forwardPathValid459
  · exact forwardPathValid460
  · exact forwardPathValid461
  · exact forwardPathValid462
  · exact forwardPathValid463

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

attribute [local irreducible] canClimb
private theorem actualVisits464 : eventVisits 464 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 56, 506, 506, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits464
private theorem actualStart464 : startFrames[464]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd464 : finalFrames[464]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid464 : forwardPathValid 464 = true := by
  rw [forwardPathValid, actualVisits464, actualStart464, actualEnd464]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_56, canClimb_56_506, canClimb_506_1, Bool.true_and]

private theorem actualVisits465 : eventVisits 465 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 507, 507, 507, 507, 507, 507, 339, 577, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits465
private theorem actualStart465 : startFrames[465]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd465 : finalFrames[465]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid465 : forwardPathValid 465 = true := by
  rw [forwardPathValid, actualVisits465, actualStart465, actualEnd465]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_2, canClimb_2_507, canClimb_339_577, canClimb_507_339, canClimb_577_1, Bool.true_and]

private theorem actualVisits466 : eventVisits 466 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 21, 508, 508, 508, 508, 508, 508, 424, 612, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits466
private theorem actualStart466 : startFrames[466]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd466 : finalFrames[466]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid466 : forwardPathValid 466 = true := by
  rw [forwardPathValid, actualVisits466, actualStart466, actualEnd466]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_21, canClimb_21_508, canClimb_424_612, canClimb_508_424, canClimb_612_1, Bool.true_and]

private theorem actualVisits467 : eventVisits 467 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 29, 508, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits467
private theorem actualStart467 : startFrames[467]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd467 : finalFrames[467]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid467 : forwardPathValid 467 = true := by
  rw [forwardPathValid, actualVisits467, actualStart467, actualEnd467]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_29, canClimb_29_508, canClimb_508_1, Bool.true_and]

private theorem actualVisits468 : eventVisits 468 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 40, 509, 509, 509, 509, 509, 385, 622, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits468
private theorem actualStart468 : startFrames[468]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd468 : finalFrames[468]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid468 : forwardPathValid 468 = true := by
  rw [forwardPathValid, actualVisits468, actualStart468, actualEnd468]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_40, canClimb_40_509, canClimb_385_622, canClimb_509_385, canClimb_622_1, Bool.true_and]

private theorem actualVisits469 : eventVisits 469 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 52, 517, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits469
private theorem actualStart469 : startFrames[469]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd469 : finalFrames[469]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid469 : forwardPathValid 469 = true := by
  rw [forwardPathValid, actualVisits469, actualStart469, actualEnd469]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_52, canClimb_52_517, canClimb_517_1, Bool.true_and]

private theorem actualVisits470 : eventVisits 470 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 79, 79, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits470
private theorem actualStart470 : startFrames[470]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd470 : finalFrames[470]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid470 : forwardPathValid 470 = true := by
  rw [forwardPathValid, actualVisits470, actualStart470, actualEnd470]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_79, canClimb_79_1, Bool.true_and]

private theorem actualVisits471 : eventVisits 471 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 94, 509, 509, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits471
private theorem actualStart471 : startFrames[471]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd471 : finalFrames[471]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid471 : forwardPathValid 471 = true := by
  rw [forwardPathValid, actualVisits471, actualStart471, actualEnd471]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_94, canClimb_94_509, canClimb_509_1, Bool.true_and]

theorem forwardPathBlock058 (f : Nat) (hl : 464 ≤ f) (hu : f < 472) : forwardPathValid f = true := by
  have hs : f = 464 ∨ f = 465 ∨ f = 466 ∨ f = 467 ∨ f = 468 ∨ f = 469 ∨ f = 470 ∨ f = 471 := by omega
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact forwardPathValid464
  · exact forwardPathValid465
  · exact forwardPathValid466
  · exact forwardPathValid467
  · exact forwardPathValid468
  · exact forwardPathValid469
  · exact forwardPathValid470
  · exact forwardPathValid471

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

attribute [local irreducible] canClimb
private theorem actualVisits472 : eventVisits 472 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 328, 510, 510, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits472
private theorem actualStart472 : startFrames[472]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd472 : finalFrames[472]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid472 : forwardPathValid 472 = true := by
  rw [forwardPathValid, actualVisits472, actualStart472, actualEnd472]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_8, canClimb_8_328, canClimb_328_510, canClimb_510_1, Bool.true_and]

private theorem actualVisits473 : eventVisits 473 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 346, 511, 511, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits473
private theorem actualStart473 : startFrames[473]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd473 : finalFrames[473]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid473 : forwardPathValid 473 = true := by
  rw [forwardPathValid, actualVisits473, actualStart473, actualEnd473]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_13, canClimb_13_346, canClimb_346_511, canClimb_511_1, Bool.true_and]

private theorem actualVisits474 : eventVisits 474 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 58, 335, 512, 512, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits474
private theorem actualStart474 : startFrames[474]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd474 : finalFrames[474]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid474 : forwardPathValid 474 = true := by
  rw [forwardPathValid, actualVisits474, actualStart474, actualEnd474]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_58, canClimb_58_335, canClimb_335_512, canClimb_512_1, Bool.true_and]

private theorem actualVisits475 : eventVisits 475 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 59, 394, 513, 513, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits475
private theorem actualStart475 : startFrames[475]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd475 : finalFrames[475]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid475 : forwardPathValid 475 = true := by
  rw [forwardPathValid, actualVisits475, actualStart475, actualEnd475]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_59, canClimb_59_394, canClimb_394_513, canClimb_513_1, Bool.true_and]

private theorem actualVisits476 : eventVisits 476 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 69, 431, 514, 514, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits476
private theorem actualStart476 : startFrames[476]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd476 : finalFrames[476]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid476 : forwardPathValid 476 = true := by
  rw [forwardPathValid, actualVisits476, actualStart476, actualEnd476]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_69, canClimb_69_431, canClimb_431_514, canClimb_514_1, Bool.true_and]

private theorem actualVisits477 : eventVisits 477 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 71, 350, 515, 515, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits477
private theorem actualStart477 : startFrames[477]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd477 : finalFrames[477]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid477 : forwardPathValid 477 = true := by
  rw [forwardPathValid, actualVisits477, actualStart477, actualEnd477]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_71, canClimb_71_350, canClimb_350_515, canClimb_515_1, Bool.true_and]

private theorem actualVisits478 : eventVisits 478 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 70, 359, 516, 516, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits478
private theorem actualStart478 : startFrames[478]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd478 : finalFrames[478]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid478 : forwardPathValid 478 = true := by
  rw [forwardPathValid, actualVisits478, actualStart478, actualEnd478]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_70, canClimb_70_359, canClimb_359_516, canClimb_516_1, Bool.true_and]

private theorem actualVisits479 : eventVisits 479 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 45, 388, 517, 517, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits479
private theorem actualStart479 : startFrames[479]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd479 : finalFrames[479]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid479 : forwardPathValid 479 = true := by
  rw [forwardPathValid, actualVisits479, actualStart479, actualEnd479]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_45, canClimb_45_388, canClimb_388_517, canClimb_517_1, Bool.true_and]

theorem forwardPathBlock059 (f : Nat) (hl : 472 ≤ f) (hu : f < 480) : forwardPathValid f = true := by
  have hs : f = 472 ∨ f = 473 ∨ f = 474 ∨ f = 475 ∨ f = 476 ∨ f = 477 ∨ f = 478 ∨ f = 479 := by omega
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact forwardPathValid472
  · exact forwardPathValid473
  · exact forwardPathValid474
  · exact forwardPathValid475
  · exact forwardPathValid476
  · exact forwardPathValid477
  · exact forwardPathValid478
  · exact forwardPathValid479

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

attribute [local irreducible] canClimb
private theorem actualVisits480 : eventVisits 480 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 19, 421, 518, 518, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits480
private theorem actualStart480 : startFrames[480]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd480 : finalFrames[480]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid480 : forwardPathValid 480 = true := by
  rw [forwardPathValid, actualVisits480, actualStart480, actualEnd480]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_19, canClimb_19_421, canClimb_421_518, canClimb_518_1, Bool.true_and]

private theorem actualVisits481 : eventVisits 481 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 113, 277, 277, 277, 277, 277, 277, 277, 434, 434, 538, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits481
private theorem actualStart481 : startFrames[481]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd481 : finalFrames[481]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid481 : forwardPathValid 481 = true := by
  rw [forwardPathValid, actualVisits481, actualStart481, actualEnd481]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_113, canClimb_113_277, canClimb_277_434, canClimb_434_538, canClimb_538_1, Bool.true_and]

private theorem actualVisits482 : eventVisits 482 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 114, 275, 275, 275, 275, 275, 275, 275, 380, 380, 544, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits482
private theorem actualStart482 : startFrames[482]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd482 : finalFrames[482]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid482 : forwardPathValid 482 = true := by
  rw [forwardPathValid, actualVisits482, actualStart482, actualEnd482]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_114, canClimb_114_275, canClimb_275_380, canClimb_380_544, canClimb_544_1, Bool.true_and]

private theorem actualVisits483 : eventVisits 483 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 273, 273, 273, 273, 273, 273, 273, 273, 329, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits483
private theorem actualStart483 : startFrames[483]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd483 : finalFrames[483]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid483 : forwardPathValid 483 = true := by
  rw [forwardPathValid, actualVisits483, actualStart483, actualEnd483]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_7, canClimb_7_273, canClimb_273_329, canClimb_329_1, Bool.true_and]

private theorem actualVisits484 : eventVisits 484 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 115, 271, 271, 271, 271, 271, 271, 271, 271, 328, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits484
private theorem actualStart484 : startFrames[484]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd484 : finalFrames[484]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid484 : forwardPathValid 484 = true := by
  rw [forwardPathValid, actualVisits484, actualStart484, actualEnd484]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_115, canClimb_115_271, canClimb_271_328, canClimb_328_1, Bool.true_and]

private theorem actualVisits485 : eventVisits 485 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 269, 269, 269, 269, 269, 269, 269, 269, 345, 345, 536, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits485
private theorem actualStart485 : startFrames[485]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd485 : finalFrames[485]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid485 : forwardPathValid 485 = true := by
  rw [forwardPathValid, actualVisits485, actualStart485, actualEnd485]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_8, canClimb_8_269, canClimb_269_345, canClimb_345_536, canClimb_536_1, Bool.true_and]

private theorem actualVisits486 : eventVisits 486 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 11, 267, 267, 267, 267, 267, 267, 267, 267, 349, 349, 511, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits486
private theorem actualStart486 : startFrames[486]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd486 : finalFrames[486]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid486 : forwardPathValid 486 = true := by
  rw [forwardPathValid, actualVisits486, actualStart486, actualEnd486]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_11, canClimb_11_267, canClimb_267_349, canClimb_349_511, canClimb_511_1, Bool.true_and]

private theorem actualVisits487 : eventVisits 487 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 48, 289, 289, 289, 289, 289, 289, 289, 394, 394, 591, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits487
private theorem actualStart487 : startFrames[487]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd487 : finalFrames[487]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid487 : forwardPathValid 487 = true := by
  rw [forwardPathValid, actualVisits487, actualStart487, actualEnd487]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_48, canClimb_48_289, canClimb_289_394, canClimb_394_591, canClimb_591_1, Bool.true_and]

theorem forwardPathBlock060 (f : Nat) (hl : 480 ≤ f) (hu : f < 488) : forwardPathValid f = true := by
  have hs : f = 480 ∨ f = 481 ∨ f = 482 ∨ f = 483 ∨ f = 484 ∨ f = 485 ∨ f = 486 ∨ f = 487 := by omega
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact forwardPathValid480
  · exact forwardPathValid481
  · exact forwardPathValid482
  · exact forwardPathValid483
  · exact forwardPathValid484
  · exact forwardPathValid485
  · exact forwardPathValid486
  · exact forwardPathValid487

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

attribute [local irreducible] canClimb
private theorem actualVisits488 : eventVisits 488 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 116, 287, 287, 287, 287, 287, 287, 287, 287, 336, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits488
private theorem actualStart488 : startFrames[488]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd488 : finalFrames[488]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid488 : forwardPathValid 488 = true := by
  rw [forwardPathValid, actualVisits488, actualStart488, actualEnd488]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_116, canClimb_116_287, canClimb_287_336, canClimb_336_1, Bool.true_and]

private theorem actualVisits489 : eventVisits 489 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 117, 285, 285, 285, 285, 285, 285, 285, 285, 353, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits489
private theorem actualStart489 : startFrames[489]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd489 : finalFrames[489]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid489 : forwardPathValid 489 = true := by
  rw [forwardPathValid, actualVisits489, actualStart489, actualEnd489]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_117, canClimb_117_285, canClimb_285_353, canClimb_353_1, Bool.true_and]

private theorem actualVisits490 : eventVisits 490 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 56, 283, 283, 283, 283, 283, 283, 283, 283, 334, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits490
private theorem actualStart490 : startFrames[490]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd490 : finalFrames[490]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid490 : forwardPathValid 490 = true := by
  rw [forwardPathValid, actualVisits490, actualStart490, actualEnd490]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_56, canClimb_56_283, canClimb_283_334, canClimb_334_1, Bool.true_and]

private theorem actualVisits491 : eventVisits 491 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 58, 281, 281, 281, 281, 281, 281, 281, 281, 354, 354, 597, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits491
private theorem actualStart491 : startFrames[491]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd491 : finalFrames[491]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid491 : forwardPathValid 491 = true := by
  rw [forwardPathValid, actualVisits491, actualStart491, actualEnd491]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_58, canClimb_58_281, canClimb_281_354, canClimb_354_597, canClimb_597_1, Bool.true_and]

private theorem actualVisits492 : eventVisits 492 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 118, 279, 279, 279, 279, 279, 279, 279, 395, 395, 590, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits492
private theorem actualStart492 : startFrames[492]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd492 : finalFrames[492]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid492 : forwardPathValid 492 = true := by
  rw [forwardPathValid, actualVisits492, actualStart492, actualEnd492]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_118, canClimb_118_279, canClimb_279_395, canClimb_395_590, canClimb_590_1, Bool.true_and]

private theorem actualVisits493 : eventVisits 493 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 119, 301, 301, 301, 301, 301, 301, 301, 301, 343, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits493
private theorem actualStart493 : startFrames[493]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd493 : finalFrames[493]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid493 : forwardPathValid 493 = true := by
  rw [forwardPathValid, actualVisits493, actualStart493, actualEnd493]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_119, canClimb_119_301, canClimb_301_343, canClimb_343_1, Bool.true_and]

private theorem actualVisits494 : eventVisits 494 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 120, 299, 299, 299, 299, 299, 299, 299, 299, 360, 360, 593, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits494
private theorem actualStart494 : startFrames[494]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd494 : finalFrames[494]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid494 : forwardPathValid 494 = true := by
  rw [forwardPathValid, actualVisits494, actualStart494, actualEnd494]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_120, canClimb_120_299, canClimb_299_360, canClimb_360_593, canClimb_593_1, Bool.true_and]

private theorem actualVisits495 : eventVisits 495 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 121, 297, 297, 297, 297, 297, 297, 297, 297, 359, 359, 588, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits495
private theorem actualStart495 : startFrames[495]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd495 : finalFrames[495]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid495 : forwardPathValid 495 = true := by
  rw [forwardPathValid, actualVisits495, actualStart495, actualEnd495]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_121, canClimb_121_297, canClimb_297_359, canClimb_359_588, canClimb_588_1, Bool.true_and]

theorem forwardPathBlock061 (f : Nat) (hl : 488 ≤ f) (hu : f < 496) : forwardPathValid f = true := by
  have hs : f = 488 ∨ f = 489 ∨ f = 490 ∨ f = 491 ∨ f = 492 ∨ f = 493 ∨ f = 494 ∨ f = 495 := by omega
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact forwardPathValid488
  · exact forwardPathValid489
  · exact forwardPathValid490
  · exact forwardPathValid491
  · exact forwardPathValid492
  · exact forwardPathValid493
  · exact forwardPathValid494
  · exact forwardPathValid495

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

attribute [local irreducible] canClimb
private theorem actualVisits496 : eventVisits 496 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 122, 295, 295, 295, 295, 295, 295, 295, 295, 359, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits496
private theorem actualStart496 : startFrames[496]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd496 : finalFrames[496]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid496 : forwardPathValid 496 = true := by
  rw [forwardPathValid, actualVisits496, actualStart496, actualEnd496]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_122, canClimb_122_295, canClimb_295_359, canClimb_359_1, Bool.true_and]

private theorem actualVisits497 : eventVisits 497 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 123, 293, 293, 293, 293, 293, 293, 293, 384, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits497
private theorem actualStart497 : startFrames[497]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd497 : finalFrames[497]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid497 : forwardPathValid 497 = true := by
  rw [forwardPathValid, actualVisits497, actualStart497, actualEnd497]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_123, canClimb_123_293, canClimb_293_384, canClimb_384_1, Bool.true_and]

private theorem actualVisits498 : eventVisits 498 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 124, 291, 291, 291, 291, 291, 291, 291, 291, 338, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits498
private theorem actualStart498 : startFrames[498]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd498 : finalFrames[498]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid498 : forwardPathValid 498 = true := by
  rw [forwardPathValid, actualVisits498, actualStart498, actualEnd498]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_124, canClimb_124_291, canClimb_291_338, canClimb_338_1, Bool.true_and]

private theorem actualVisits499 : eventVisits 499 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 125, 277, 277, 277, 277, 277, 331, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits499
private theorem actualStart499 : startFrames[499]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd499 : finalFrames[499]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid499 : forwardPathValid 499 = true := by
  rw [forwardPathValid, actualVisits499, actualStart499, actualEnd499]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_125, canClimb_125_277, canClimb_277_331, canClimb_331_1, Bool.true_and]

private theorem actualVisits500 : eventVisits 500 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 126, 274, 274, 274, 274, 274, 373, 373, 607, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits500
private theorem actualStart500 : startFrames[500]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd500 : finalFrames[500]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid500 : forwardPathValid 500 = true := by
  rw [forwardPathValid, actualVisits500, actualStart500, actualEnd500]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_126, canClimb_126_274, canClimb_274_373, canClimb_373_607, canClimb_607_1, Bool.true_and]

private theorem actualVisits501 : eventVisits 501 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 272, 272, 272, 272, 272, 272, 272, 272, 329, 329, 531, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits501
private theorem actualStart501 : startFrames[501]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd501 : finalFrames[501]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid501 : forwardPathValid 501 = true := by
  rw [forwardPathValid, actualVisits501, actualStart501, actualEnd501]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_2, canClimb_2_272, canClimb_272_329, canClimb_329_531, canClimb_531_1, Bool.true_and]

private theorem actualVisits502 : eventVisits 502 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 127, 273, 273, 273, 273, 273, 362, 362, 540, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits502
private theorem actualStart502 : startFrames[502]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd502 : finalFrames[502]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid502 : forwardPathValid 502 = true := by
  rw [forwardPathValid, actualVisits502, actualStart502, actualEnd502]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_127, canClimb_127_273, canClimb_273_362, canClimb_362_540, canClimb_540_1, Bool.true_and]

private theorem actualVisits503 : eventVisits 503 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 275, 275, 275, 275, 275, 345, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits503
private theorem actualStart503 : startFrames[503]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd503 : finalFrames[503]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid503 : forwardPathValid 503 = true := by
  rw [forwardPathValid, actualVisits503, actualStart503, actualEnd503]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_5, canClimb_5_275, canClimb_275_345, canClimb_345_1, Bool.true_and]

theorem forwardPathBlock062 (f : Nat) (hl : 496 ≤ f) (hu : f < 504) : forwardPathValid f = true := by
  have hs : f = 496 ∨ f = 497 ∨ f = 498 ∨ f = 499 ∨ f = 500 ∨ f = 501 ∨ f = 502 ∨ f = 503 := by omega
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact forwardPathValid496
  · exact forwardPathValid497
  · exact forwardPathValid498
  · exact forwardPathValid499
  · exact forwardPathValid500
  · exact forwardPathValid501
  · exact forwardPathValid502
  · exact forwardPathValid503

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

attribute [local irreducible] canClimb
private theorem actualVisits504 : eventVisits 504 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 276, 276, 276, 276, 276, 331, 331, 534, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits504
private theorem actualStart504 : startFrames[504]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd504 : finalFrames[504]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid504 : forwardPathValid 504 = true := by
  rw [forwardPathValid, actualVisits504, actualStart504, actualEnd504]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_13, canClimb_13_276, canClimb_276_331, canClimb_331_534, canClimb_534_1, Bool.true_and]

private theorem actualVisits505 : eventVisits 505 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 64, 288, 288, 288, 288, 288, 288, 378, 378, 578, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits505
private theorem actualStart505 : startFrames[505]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd505 : finalFrames[505]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid505 : forwardPathValid 505 = true := by
  rw [forwardPathValid, actualVisits505, actualStart505, actualEnd505]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_64, canClimb_64_288, canClimb_288_378, canClimb_378_578, canClimb_578_1, Bool.true_and]

private theorem actualVisits506 : eventVisits 506 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 71, 287, 287, 287, 287, 287, 287, 287, 287, 354, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits506
private theorem actualStart506 : startFrames[506]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd506 : finalFrames[506]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid506 : forwardPathValid 506 = true := by
  rw [forwardPathValid, actualVisits506, actualStart506, actualEnd506]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_71, canClimb_71_287, canClimb_287_354, canClimb_354_1, Bool.true_and]

private theorem actualVisits507 : eventVisits 507 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 74, 285, 285, 285, 285, 285, 285, 285, 285, 335, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits507
private theorem actualStart507 : startFrames[507]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd507 : finalFrames[507]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid507 : forwardPathValid 507 = true := by
  rw [forwardPathValid, actualVisits507, actualStart507, actualEnd507]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_74, canClimb_74_285, canClimb_285_335, canClimb_335_1, Bool.true_and]

private theorem actualVisits508 : eventVisits 508 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 128, 284, 284, 284, 284, 284, 284, 389, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits508
private theorem actualStart508 : startFrames[508]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd508 : finalFrames[508]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid508 : forwardPathValid 508 = true := by
  rw [forwardPathValid, actualVisits508, actualStart508, actualEnd508]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_128, canClimb_128_284, canClimb_284_389, canClimb_389_1, Bool.true_and]

private theorem actualVisits509 : eventVisits 509 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 129, 286, 286, 286, 286, 286, 336, 336, 512, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits509
private theorem actualStart509 : startFrames[509]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd509 : finalFrames[509]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid509 : forwardPathValid 509 = true := by
  rw [forwardPathValid, actualVisits509, actualStart509, actualEnd509]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_129, canClimb_129_286, canClimb_286_336, canClimb_336_512, canClimb_512_1, Bool.true_and]

private theorem actualVisits510 : eventVisits 510 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 130, 289, 289, 289, 289, 289, 337, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits510
private theorem actualStart510 : startFrames[510]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd510 : finalFrames[510]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid510 : forwardPathValid 510 = true := by
  rw [forwardPathValid, actualVisits510, actualStart510, actualEnd510]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_130, canClimb_130_289, canClimb_289_337, canClimb_337_1, Bool.true_and]

private theorem actualVisits511 : eventVisits 511 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 131, 300, 300, 300, 300, 300, 300, 300, 300, 343, 343, 577, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits511
private theorem actualStart511 : startFrames[511]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd511 : finalFrames[511]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid511 : forwardPathValid 511 = true := by
  rw [forwardPathValid, actualVisits511, actualStart511, actualEnd511]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_131, canClimb_131_300, canClimb_300_343, canClimb_343_577, canClimb_577_1, Bool.true_and]

theorem forwardPathBlock063 (f : Nat) (hl : 504 ≤ f) (hu : f < 512) : forwardPathValid f = true := by
  have hs : f = 504 ∨ f = 505 ∨ f = 506 ∨ f = 507 ∨ f = 508 ∨ f = 509 ∨ f = 510 ∨ f = 511 := by omega
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact forwardPathValid504
  · exact forwardPathValid505
  · exact forwardPathValid506
  · exact forwardPathValid507
  · exact forwardPathValid508
  · exact forwardPathValid509
  · exact forwardPathValid510
  · exact forwardPathValid511

end CSL.Construction.PhysicalFramePaths


