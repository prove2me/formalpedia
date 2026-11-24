-- Prove2me | Definitions.Def_CSL_Generated_FiniteCircuit_FramePathChecks_Paths_Batch05
-- name    : CSL_Generated_FiniteCircuit_FramePathChecks_Paths_Batch05
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T15:49:23.344798+00:00
-- url     : https://prove2.me/theorems/b53b6e27-c35d-4e50-9ee6-e347519d05cf
-- title:
--   Coded sorting library: Generated / FiniteCircuit / FramePathChecks / Paths / Batch05
-- statement:
--   Module `CodedSorting.Generated.FiniteCircuit.FramePathChecks.Paths.Batch05` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   Generated physical-frame checks. Uncompiled until a build record exists.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Generated.FiniteCircuit.FramePathChecks.Paths.Batch05

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Generated_FiniteCircuit_FramePathChecks_Nesting_Batch00
import Definitions.Def_CSL_Generated_FiniteCircuit_FramePathChecks_Nesting_Batch03
import Definitions.Def_CSL_Generated_FiniteCircuit_FramePathChecks_Nesting_Batch04
import Definitions.Def_CSL_Generated_FiniteCircuit_FramePathChecks_Nesting_Batch05
import Definitions.Def_CSL_Generated_FiniteCircuit_FramePathChecks_Nesting_Batch06
import Definitions.Def_CSL_Generated_FiniteCircuit_FramePathChecks_VisitNumbers_Batch05
import Definitions.Def_CSL_Generated_FiniteCircuit_FramePathChecks_VisitNumbers_Bridge

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

attribute [local irreducible] canClimb
private theorem actualVisits640 : eventVisits 640 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 245, 324, 324, 324, 324, 324, 324, 484, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits640
private theorem actualStart640 : startFrames[640]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd640 : finalFrames[640]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid640 : forwardPathValid 640 = true := by
  rw [forwardPathValid, actualVisits640, actualStart640, actualEnd640]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_245, canClimb_245_324, canClimb_324_484, canClimb_484_1, Bool.true_and]

private theorem actualVisits641 : eventVisits 641 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 246, 317, 317, 317, 317, 317, 317, 317, 483, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits641
private theorem actualStart641 : startFrames[641]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd641 : finalFrames[641]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid641 : forwardPathValid 641 = true := by
  rw [forwardPathValid, actualVisits641, actualStart641, actualEnd641]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_246, canClimb_246_317, canClimb_317_483, canClimb_483_1, Bool.true_and]

private theorem actualVisits642 : eventVisits 642 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 247, 305, 305, 305, 305, 305, 305, 482, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits642
private theorem actualStart642 : startFrames[642]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd642 : finalFrames[642]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid642 : forwardPathValid 642 = true := by
  rw [forwardPathValid, actualVisits642, actualStart642, actualEnd642]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_247, canClimb_247_305, canClimb_305_482, canClimb_482_1, Bool.true_and]

private theorem actualVisits643 : eventVisits 643 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 248, 311, 311, 311, 311, 311, 311, 311, 311, 493, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits643
private theorem actualStart643 : startFrames[643]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd643 : finalFrames[643]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid643 : forwardPathValid 643 = true := by
  rw [forwardPathValid, actualVisits643, actualStart643, actualEnd643]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_248, canClimb_248_311, canClimb_311_493, canClimb_493_1, Bool.true_and]

private theorem actualVisits644 : eventVisits 644 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 249, 320, 320, 320, 320, 320, 320, 320, 492, 492, 635, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits644
private theorem actualStart644 : startFrames[644]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd644 : finalFrames[644]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid644 : forwardPathValid 644 = true := by
  rw [forwardPathValid, actualVisits644, actualStart644, actualEnd644]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_249, canClimb_249_320, canClimb_320_492, canClimb_492_635, canClimb_635_1, Bool.true_and]

private theorem actualVisits645 : eventVisits 645 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 250, 305, 305, 305, 305, 305, 305, 305, 491, 491, 537, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits645
private theorem actualStart645 : startFrames[645]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd645 : finalFrames[645]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid645 : forwardPathValid 645 = true := by
  rw [forwardPathValid, actualVisits645, actualStart645, actualEnd645]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_250, canClimb_250_305, canClimb_305_491, canClimb_491_537, canClimb_537_1, Bool.true_and]

private theorem actualVisits646 : eventVisits 646 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 251, 304, 304, 304, 304, 304, 304, 304, 490, 490, 635, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits646
private theorem actualStart646 : startFrames[646]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd646 : finalFrames[646]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid646 : forwardPathValid 646 = true := by
  rw [forwardPathValid, actualVisits646, actualStart646, actualEnd646]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_251, canClimb_251_304, canClimb_304_490, canClimb_490_635, canClimb_635_1, Bool.true_and]

private theorem actualVisits647 : eventVisits 647 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 252, 321, 321, 321, 321, 321, 321, 321, 489, 489, 533, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits647
private theorem actualStart647 : startFrames[647]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd647 : finalFrames[647]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid647 : forwardPathValid 647 = true := by
  rw [forwardPathValid, actualVisits647, actualStart647, actualEnd647]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_252, canClimb_252_321, canClimb_321_489, canClimb_489_533, canClimb_533_1, Bool.true_and]

theorem forwardPathBlock080 (f : Nat) (hl : 640 ≤ f) (hu : f < 648) : forwardPathValid f = true := by
  have hs : f = 640 ∨ f = 641 ∨ f = 642 ∨ f = 643 ∨ f = 644 ∨ f = 645 ∨ f = 646 ∨ f = 647 := by omega
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact forwardPathValid640
  · exact forwardPathValid641
  · exact forwardPathValid642
  · exact forwardPathValid643
  · exact forwardPathValid644
  · exact forwardPathValid645
  · exact forwardPathValid646
  · exact forwardPathValid647

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

attribute [local irreducible] canClimb
private theorem actualVisits648 : eventVisits 648 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 253, 310, 310, 310, 310, 310, 310, 310, 310, 488, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits648
private theorem actualStart648 : startFrames[648]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd648 : finalFrames[648]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid648 : forwardPathValid 648 = true := by
  rw [forwardPathValid, actualVisits648, actualStart648, actualEnd648]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_253, canClimb_253_310, canClimb_310_488, canClimb_488_1, Bool.true_and]

private theorem actualVisits649 : eventVisits 649 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 254, 323, 323, 323, 323, 323, 323, 499, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits649
private theorem actualStart649 : startFrames[649]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd649 : finalFrames[649]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid649 : forwardPathValid 649 = true := by
  rw [forwardPathValid, actualVisits649, actualStart649, actualEnd649]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_254, canClimb_254_323, canClimb_323_499, canClimb_499_1, Bool.true_and]

private theorem actualVisits650 : eventVisits 650 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 255, 314, 314, 314, 314, 314, 314, 314, 314, 314, 314, 498, 498, 562, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits650
private theorem actualStart650 : startFrames[650]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd650 : finalFrames[650]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid650 : forwardPathValid 650 = true := by
  rw [forwardPathValid, actualVisits650, actualStart650, actualEnd650]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_255, canClimb_255_314, canClimb_314_498, canClimb_498_562, canClimb_562_1, Bool.true_and]

private theorem actualVisits651 : eventVisits 651 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 256, 307, 307, 307, 307, 307, 497, 497, 606, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits651
private theorem actualStart651 : startFrames[651]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd651 : finalFrames[651]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid651 : forwardPathValid 651 = true := by
  rw [forwardPathValid, actualVisits651, actualStart651, actualEnd651]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_256, canClimb_256_307, canClimb_307_497, canClimb_497_606, canClimb_606_1, Bool.true_and]

private theorem actualVisits652 : eventVisits 652 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 257, 302, 302, 302, 302, 302, 496, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits652
private theorem actualStart652 : startFrames[652]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd652 : finalFrames[652]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid652 : forwardPathValid 652 = true := by
  rw [forwardPathValid, actualVisits652, actualStart652, actualEnd652]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_257, canClimb_257_302, canClimb_302_496, canClimb_496_1, Bool.true_and]

private theorem actualVisits653 : eventVisits 653 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 258, 319, 319, 319, 319, 319, 319, 477, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits653
private theorem actualStart653 : startFrames[653]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd653 : finalFrames[653]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid653 : forwardPathValid 653 = true := by
  rw [forwardPathValid, actualVisits653, actualStart653, actualEnd653]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_258, canClimb_258_319, canClimb_319_477, canClimb_477_1, Bool.true_and]

private theorem actualVisits654 : eventVisits 654 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 259, 322, 322, 322, 322, 322, 322, 322, 322, 494, 494, 556, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits654
private theorem actualStart654 : startFrames[654]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd654 : finalFrames[654]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid654 : forwardPathValid 654 = true := by
  rw [forwardPathValid, actualVisits654, actualStart654, actualEnd654]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_259, canClimb_259_322, canClimb_322_494, canClimb_494_556, canClimb_556_1, Bool.true_and]

private theorem actualVisits655 : eventVisits 655 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 260, 309, 309, 309, 309, 309, 309, 473, 473, 529, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits655
private theorem actualStart655 : startFrames[655]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd655 : finalFrames[655]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid655 : forwardPathValid 655 = true := by
  rw [forwardPathValid, actualVisits655, actualStart655, actualEnd655]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_260, canClimb_260_309, canClimb_309_473, canClimb_473_529, canClimb_529_1, Bool.true_and]

theorem forwardPathBlock081 (f : Nat) (hl : 648 ≤ f) (hu : f < 656) : forwardPathValid f = true := by
  have hs : f = 648 ∨ f = 649 ∨ f = 650 ∨ f = 651 ∨ f = 652 ∨ f = 653 ∨ f = 654 ∨ f = 655 := by omega
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact forwardPathValid648
  · exact forwardPathValid649
  · exact forwardPathValid650
  · exact forwardPathValid651
  · exact forwardPathValid652
  · exact forwardPathValid653
  · exact forwardPathValid654
  · exact forwardPathValid655

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

attribute [local irreducible] canClimb
private theorem actualVisits656 : eventVisits 656 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 261, 318, 318, 318, 318, 318, 318, 504, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits656
private theorem actualStart656 : startFrames[656]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd656 : finalFrames[656]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid656 : forwardPathValid 656 = true := by
  rw [forwardPathValid, actualVisits656, actualStart656, actualEnd656]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_261, canClimb_261_318, canClimb_318_504, canClimb_504_1, Bool.true_and]

private theorem actualVisits657 : eventVisits 657 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 262, 325, 325, 325, 325, 325, 325, 325, 325, 325, 503, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits657
private theorem actualStart657 : startFrames[657]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd657 : finalFrames[657]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid657 : forwardPathValid 657 = true := by
  rw [forwardPathValid, actualVisits657, actualStart657, actualEnd657]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_262, canClimb_262_325, canClimb_325_503, canClimb_503_1, Bool.true_and]

private theorem actualVisits658 : eventVisits 658 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 263, 324, 324, 324, 324, 324, 324, 324, 502, 502, 565, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits658
private theorem actualStart658 : startFrames[658]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd658 : finalFrames[658]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid658 : forwardPathValid 658 = true := by
  rw [forwardPathValid, actualVisits658, actualStart658, actualEnd658]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_263, canClimb_263_324, canClimb_324_502, canClimb_502_565, canClimb_565_1, Bool.true_and]

private theorem actualVisits659 : eventVisits 659 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 264, 315, 315, 315, 315, 315, 501, 501, 598, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits659
private theorem actualStart659 : startFrames[659]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd659 : finalFrames[659]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid659 : forwardPathValid 659 = true := by
  rw [forwardPathValid, actualVisits659, actualStart659, actualEnd659]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_264, canClimb_264_315, canClimb_315_501, canClimb_501_598, canClimb_598_1, Bool.true_and]

private theorem actualVisits660 : eventVisits 660 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 265, 312, 312, 312, 312, 312, 312, 312, 455, 455, 532, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits660
private theorem actualStart660 : startFrames[660]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd660 : finalFrames[660]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid660 : forwardPathValid 660 = true := by
  rw [forwardPathValid, actualVisits660, actualStart660, actualEnd660]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_265, canClimb_265_312, canClimb_312_455, canClimb_455_532, canClimb_532_1, Bool.true_and]

theorem forwardPathBlock082 (f : Nat) (hl : 656 ≤ f) (hu : f < 661) : forwardPathValid f = true := by
  have hs : f = 656 ∨ f = 657 ∨ f = 658 ∨ f = 659 ∨ f = 660 := by omega
  rcases hs with rfl | rfl | rfl | rfl | rfl
  · exact forwardPathValid656
  · exact forwardPathValid657
  · exact forwardPathValid658
  · exact forwardPathValid659
  · exact forwardPathValid660

end CSL.Construction.PhysicalFramePaths


