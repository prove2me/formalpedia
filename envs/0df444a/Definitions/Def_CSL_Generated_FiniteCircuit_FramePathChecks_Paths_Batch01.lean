-- Prove2me | Definitions.Def_CSL_Generated_FiniteCircuit_FramePathChecks_Paths_Batch01
-- name    : CSL_Generated_FiniteCircuit_FramePathChecks_Paths_Batch01
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T16:47:18.612419+00:00
-- url     : https://prove2.me/theorems/221b7c81-0b06-4a2f-869c-92ede5705ed4
-- title:
--   Coded sorting library: Generated / FiniteCircuit / FramePathChecks / Paths / Batch01
-- statement:
--   Module `CodedSorting.Generated.FiniteCircuit.FramePathChecks.Paths.Batch01` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   Generated physical-frame checks. Uncompiled until a build record exists.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Generated.FiniteCircuit.FramePathChecks.Paths.Batch01

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Generated_FiniteCircuit_FramePathChecks_Nesting_Batch00
import Definitions.Def_CSL_Generated_FiniteCircuit_FramePathChecks_Nesting_Batch01
import Definitions.Def_CSL_Generated_FiniteCircuit_FramePathChecks_Nesting_Batch02
import Definitions.Def_CSL_Generated_FiniteCircuit_FramePathChecks_Nesting_Batch03
import Definitions.Def_CSL_Generated_FiniteCircuit_FramePathChecks_Nesting_Batch04
import Definitions.Def_CSL_Generated_FiniteCircuit_FramePathChecks_Nesting_Batch05
import Definitions.Def_CSL_Generated_FiniteCircuit_FramePathChecks_Nesting_Batch06
import Definitions.Def_CSL_Generated_FiniteCircuit_FramePathChecks_VisitNumbers_Batch01
import Definitions.Def_CSL_Generated_FiniteCircuit_FramePathChecks_VisitNumbers_Bridge

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

attribute [local irreducible] canClimb
private theorem actualVisits128 : eventVisits 128 forwardEvents = [0, 0, 184, 542] := by
  rw [forward_visits_computed]
  exact computedForwardVisits128
private theorem actualStart128 : startFrames[128]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd128 : finalFrames[128]! = 542 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid128 : forwardPathValid 128 = true := by
  rw [forwardPathValid, actualVisits128, actualStart128, actualEnd128]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_184, canClimb_184_542, Bool.true_and]

private theorem actualVisits129 : eventVisits 129 forwardEvents = [0, 0, 247, 543] := by
  rw [forward_visits_computed]
  exact computedForwardVisits129
private theorem actualStart129 : startFrames[129]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd129 : finalFrames[129]! = 543 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid129 : forwardPathValid 129 = true := by
  rw [forwardPathValid, actualVisits129, actualStart129, actualEnd129]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_247, canClimb_247_543, Bool.true_and]

private theorem actualVisits130 : eventVisits 130 forwardEvents = [0, 0, 155, 544] := by
  rw [forward_visits_computed]
  exact computedForwardVisits130
private theorem actualStart130 : startFrames[130]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd130 : finalFrames[130]! = 544 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid130 : forwardPathValid 130 = true := by
  rw [forwardPathValid, actualVisits130, actualStart130, actualEnd130]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_155, canClimb_155_544, Bool.true_and]

private theorem actualVisits131 : eventVisits 131 forwardEvents = [0, 0, 241, 545] := by
  rw [forward_visits_computed]
  exact computedForwardVisits131
private theorem actualStart131 : startFrames[131]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd131 : finalFrames[131]! = 545 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid131 : forwardPathValid 131 = true := by
  rw [forwardPathValid, actualVisits131, actualStart131, actualEnd131]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_241, canClimb_241_545, Bool.true_and]

private theorem actualVisits132 : eventVisits 132 forwardEvents = [0, 0, 168, 546] := by
  rw [forward_visits_computed]
  exact computedForwardVisits132
private theorem actualStart132 : startFrames[132]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd132 : finalFrames[132]! = 546 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid132 : forwardPathValid 132 = true := by
  rw [forwardPathValid, actualVisits132, actualStart132, actualEnd132]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_168, canClimb_168_546, Bool.true_and]

private theorem actualVisits133 : eventVisits 133 forwardEvents = [0, 0, 547] := by
  rw [forward_visits_computed]
  exact computedForwardVisits133
private theorem actualStart133 : startFrames[133]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd133 : finalFrames[133]! = 547 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid133 : forwardPathValid 133 = true := by
  rw [forwardPathValid, actualVisits133, actualStart133, actualEnd133]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_547, Bool.true_and]

private theorem actualVisits134 : eventVisits 134 forwardEvents = [0, 0, 135, 548] := by
  rw [forward_visits_computed]
  exact computedForwardVisits134
private theorem actualStart134 : startFrames[134]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd134 : finalFrames[134]! = 548 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid134 : forwardPathValid 134 = true := by
  rw [forwardPathValid, actualVisits134, actualStart134, actualEnd134]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_135, canClimb_135_548, Bool.true_and]

private theorem actualVisits135 : eventVisits 135 forwardEvents = [0, 0, 222, 549] := by
  rw [forward_visits_computed]
  exact computedForwardVisits135
private theorem actualStart135 : startFrames[135]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd135 : finalFrames[135]! = 549 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid135 : forwardPathValid 135 = true := by
  rw [forwardPathValid, actualVisits135, actualStart135, actualEnd135]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_222, canClimb_222_549, Bool.true_and]

theorem forwardPathBlock016 (f : Nat) (hl : 128 ≤ f) (hu : f < 136) : forwardPathValid f = true := by
  have hs : f = 128 ∨ f = 129 ∨ f = 130 ∨ f = 131 ∨ f = 132 ∨ f = 133 ∨ f = 134 ∨ f = 135 := by omega
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact forwardPathValid128
  · exact forwardPathValid129
  · exact forwardPathValid130
  · exact forwardPathValid131
  · exact forwardPathValid132
  · exact forwardPathValid133
  · exact forwardPathValid134
  · exact forwardPathValid135

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

attribute [local irreducible] canClimb
private theorem actualVisits136 : eventVisits 136 forwardEvents = [0, 0, 229, 550] := by
  rw [forward_visits_computed]
  exact computedForwardVisits136
private theorem actualStart136 : startFrames[136]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd136 : finalFrames[136]! = 550 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid136 : forwardPathValid 136 = true := by
  rw [forwardPathValid, actualVisits136, actualStart136, actualEnd136]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_229, canClimb_229_550, Bool.true_and]

private theorem actualVisits137 : eventVisits 137 forwardEvents = [0, 0, 165, 551] := by
  rw [forward_visits_computed]
  exact computedForwardVisits137
private theorem actualStart137 : startFrames[137]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd137 : finalFrames[137]! = 551 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid137 : forwardPathValid 137 = true := by
  rw [forwardPathValid, actualVisits137, actualStart137, actualEnd137]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_165, canClimb_165_551, Bool.true_and]

private theorem actualVisits138 : eventVisits 138 forwardEvents = [0, 0, 154, 552] := by
  rw [forward_visits_computed]
  exact computedForwardVisits138
private theorem actualStart138 : startFrames[138]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd138 : finalFrames[138]! = 552 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid138 : forwardPathValid 138 = true := by
  rw [forwardPathValid, actualVisits138, actualStart138, actualEnd138]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_154, canClimb_154_552, Bool.true_and]

private theorem actualVisits139 : eventVisits 139 forwardEvents = [0, 0, 226, 553] := by
  rw [forward_visits_computed]
  exact computedForwardVisits139
private theorem actualStart139 : startFrames[139]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd139 : finalFrames[139]! = 553 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid139 : forwardPathValid 139 = true := by
  rw [forwardPathValid, actualVisits139, actualStart139, actualEnd139]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_226, canClimb_226_553, Bool.true_and]

private theorem actualVisits140 : eventVisits 140 forwardEvents = [0, 0, 223, 554] := by
  rw [forward_visits_computed]
  exact computedForwardVisits140
private theorem actualStart140 : startFrames[140]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd140 : finalFrames[140]! = 554 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid140 : forwardPathValid 140 = true := by
  rw [forwardPathValid, actualVisits140, actualStart140, actualEnd140]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_223, canClimb_223_554, Bool.true_and]

private theorem actualVisits141 : eventVisits 141 forwardEvents = [0, 0, 143, 555] := by
  rw [forward_visits_computed]
  exact computedForwardVisits141
private theorem actualStart141 : startFrames[141]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd141 : finalFrames[141]! = 555 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid141 : forwardPathValid 141 = true := by
  rw [forwardPathValid, actualVisits141, actualStart141, actualEnd141]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_143, canClimb_143_555, Bool.true_and]

private theorem actualVisits142 : eventVisits 142 forwardEvents = [0, 0, 257, 556] := by
  rw [forward_visits_computed]
  exact computedForwardVisits142
private theorem actualStart142 : startFrames[142]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd142 : finalFrames[142]! = 556 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid142 : forwardPathValid 142 = true := by
  rw [forwardPathValid, actualVisits142, actualStart142, actualEnd142]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_257, canClimb_257_556, Bool.true_and]

private theorem actualVisits143 : eventVisits 143 forwardEvents = [0, 0, 205, 557] := by
  rw [forward_visits_computed]
  exact computedForwardVisits143
private theorem actualStart143 : startFrames[143]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd143 : finalFrames[143]! = 557 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid143 : forwardPathValid 143 = true := by
  rw [forwardPathValid, actualVisits143, actualStart143, actualEnd143]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_205, canClimb_205_557, Bool.true_and]

theorem forwardPathBlock017 (f : Nat) (hl : 136 ≤ f) (hu : f < 144) : forwardPathValid f = true := by
  have hs : f = 136 ∨ f = 137 ∨ f = 138 ∨ f = 139 ∨ f = 140 ∨ f = 141 ∨ f = 142 ∨ f = 143 := by omega
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact forwardPathValid136
  · exact forwardPathValid137
  · exact forwardPathValid138
  · exact forwardPathValid139
  · exact forwardPathValid140
  · exact forwardPathValid141
  · exact forwardPathValid142
  · exact forwardPathValid143

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

attribute [local irreducible] canClimb
private theorem actualVisits144 : eventVisits 144 forwardEvents = [0, 0, 188, 558] := by
  rw [forward_visits_computed]
  exact computedForwardVisits144
private theorem actualStart144 : startFrames[144]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd144 : finalFrames[144]! = 558 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid144 : forwardPathValid 144 = true := by
  rw [forwardPathValid, actualVisits144, actualStart144, actualEnd144]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_188, canClimb_188_558, Bool.true_and]

private theorem actualVisits145 : eventVisits 145 forwardEvents = [0, 0, 202, 559] := by
  rw [forward_visits_computed]
  exact computedForwardVisits145
private theorem actualStart145 : startFrames[145]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd145 : finalFrames[145]! = 559 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid145 : forwardPathValid 145 = true := by
  rw [forwardPathValid, actualVisits145, actualStart145, actualEnd145]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_202, canClimb_202_559, Bool.true_and]

private theorem actualVisits146 : eventVisits 146 forwardEvents = [0, 0, 160, 560] := by
  rw [forward_visits_computed]
  exact computedForwardVisits146
private theorem actualStart146 : startFrames[146]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd146 : finalFrames[146]! = 560 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid146 : forwardPathValid 146 = true := by
  rw [forwardPathValid, actualVisits146, actualStart146, actualEnd146]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_160, canClimb_160_560, Bool.true_and]

private theorem actualVisits147 : eventVisits 147 forwardEvents = [0, 0, 173, 561] := by
  rw [forward_visits_computed]
  exact computedForwardVisits147
private theorem actualStart147 : startFrames[147]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd147 : finalFrames[147]! = 561 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid147 : forwardPathValid 147 = true := by
  rw [forwardPathValid, actualVisits147, actualStart147, actualEnd147]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_173, canClimb_173_561, Bool.true_and]

private theorem actualVisits148 : eventVisits 148 forwardEvents = [0, 0, 259, 562] := by
  rw [forward_visits_computed]
  exact computedForwardVisits148
private theorem actualStart148 : startFrames[148]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd148 : finalFrames[148]! = 562 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid148 : forwardPathValid 148 = true := by
  rw [forwardPathValid, actualVisits148, actualStart148, actualEnd148]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_259, canClimb_259_562, Bool.true_and]

private theorem actualVisits149 : eventVisits 149 forwardEvents = [0, 0, 186, 563] := by
  rw [forward_visits_computed]
  exact computedForwardVisits149
private theorem actualStart149 : startFrames[149]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd149 : finalFrames[149]! = 563 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid149 : forwardPathValid 149 = true := by
  rw [forwardPathValid, actualVisits149, actualStart149, actualEnd149]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_186, canClimb_186_563, Bool.true_and]

private theorem actualVisits150 : eventVisits 150 forwardEvents = [0, 0, 211, 564] := by
  rw [forward_visits_computed]
  exact computedForwardVisits150
private theorem actualStart150 : startFrames[150]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd150 : finalFrames[150]! = 564 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid150 : forwardPathValid 150 = true := by
  rw [forwardPathValid, actualVisits150, actualStart150, actualEnd150]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_211, canClimb_211_564, Bool.true_and]

private theorem actualVisits151 : eventVisits 151 forwardEvents = [0, 0, 263, 565] := by
  rw [forward_visits_computed]
  exact computedForwardVisits151
private theorem actualStart151 : startFrames[151]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd151 : finalFrames[151]! = 565 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid151 : forwardPathValid 151 = true := by
  rw [forwardPathValid, actualVisits151, actualStart151, actualEnd151]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_263, canClimb_263_565, Bool.true_and]

theorem forwardPathBlock018 (f : Nat) (hl : 144 ≤ f) (hu : f < 152) : forwardPathValid f = true := by
  have hs : f = 144 ∨ f = 145 ∨ f = 146 ∨ f = 147 ∨ f = 148 ∨ f = 149 ∨ f = 150 ∨ f = 151 := by omega
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact forwardPathValid144
  · exact forwardPathValid145
  · exact forwardPathValid146
  · exact forwardPathValid147
  · exact forwardPathValid148
  · exact forwardPathValid149
  · exact forwardPathValid150
  · exact forwardPathValid151

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

attribute [local irreducible] canClimb
private theorem actualVisits152 : eventVisits 152 forwardEvents = [0, 0, 145, 566] := by
  rw [forward_visits_computed]
  exact computedForwardVisits152
private theorem actualStart152 : startFrames[152]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd152 : finalFrames[152]! = 566 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid152 : forwardPathValid 152 = true := by
  rw [forwardPathValid, actualVisits152, actualStart152, actualEnd152]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_145, canClimb_145_566, Bool.true_and]

private theorem actualVisits153 : eventVisits 153 forwardEvents = [0, 0, 207, 567] := by
  rw [forward_visits_computed]
  exact computedForwardVisits153
private theorem actualStart153 : startFrames[153]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd153 : finalFrames[153]! = 567 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid153 : forwardPathValid 153 = true := by
  rw [forwardPathValid, actualVisits153, actualStart153, actualEnd153]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_207, canClimb_207_567, Bool.true_and]

private theorem actualVisits154 : eventVisits 154 forwardEvents = [0, 0, 159, 568] := by
  rw [forward_visits_computed]
  exact computedForwardVisits154
private theorem actualStart154 : startFrames[154]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd154 : finalFrames[154]! = 568 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid154 : forwardPathValid 154 = true := by
  rw [forwardPathValid, actualVisits154, actualStart154, actualEnd154]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_159, canClimb_159_568, Bool.true_and]

private theorem actualVisits155 : eventVisits 155 forwardEvents = [0, 0, 172, 569] := by
  rw [forward_visits_computed]
  exact computedForwardVisits155
private theorem actualStart155 : startFrames[155]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd155 : finalFrames[155]! = 569 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid155 : forwardPathValid 155 = true := by
  rw [forwardPathValid, actualVisits155, actualStart155, actualEnd155]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_172, canClimb_172_569, Bool.true_and]

private theorem actualVisits156 : eventVisits 156 forwardEvents = [0, 0, 265, 570] := by
  rw [forward_visits_computed]
  exact computedForwardVisits156
private theorem actualStart156 : startFrames[156]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd156 : finalFrames[156]! = 570 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid156 : forwardPathValid 156 = true := by
  rw [forwardPathValid, actualVisits156, actualStart156, actualEnd156]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_265, canClimb_265_570, Bool.true_and]

private theorem actualVisits157 : eventVisits 157 forwardEvents = [0, 0, 571] := by
  rw [forward_visits_computed]
  exact computedForwardVisits157
private theorem actualStart157 : startFrames[157]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd157 : finalFrames[157]! = 571 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid157 : forwardPathValid 157 = true := by
  rw [forwardPathValid, actualVisits157, actualStart157, actualEnd157]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_571, Bool.true_and]

private theorem actualVisits158 : eventVisits 158 forwardEvents = [0, 0, 124, 572] := by
  rw [forward_visits_computed]
  exact computedForwardVisits158
private theorem actualStart158 : startFrames[158]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd158 : finalFrames[158]! = 572 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid158 : forwardPathValid 158 = true := by
  rw [forwardPathValid, actualVisits158, actualStart158, actualEnd158]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_124, canClimb_124_572, Bool.true_and]

private theorem actualVisits159 : eventVisits 159 forwardEvents = [0, 0, 121, 573] := by
  rw [forward_visits_computed]
  exact computedForwardVisits159
private theorem actualStart159 : startFrames[159]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd159 : finalFrames[159]! = 573 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid159 : forwardPathValid 159 = true := by
  rw [forwardPathValid, actualVisits159, actualStart159, actualEnd159]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_121, canClimb_121_573, Bool.true_and]

theorem forwardPathBlock019 (f : Nat) (hl : 152 ≤ f) (hu : f < 160) : forwardPathValid f = true := by
  have hs : f = 152 ∨ f = 153 ∨ f = 154 ∨ f = 155 ∨ f = 156 ∨ f = 157 ∨ f = 158 ∨ f = 159 := by omega
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact forwardPathValid152
  · exact forwardPathValid153
  · exact forwardPathValid154
  · exact forwardPathValid155
  · exact forwardPathValid156
  · exact forwardPathValid157
  · exact forwardPathValid158
  · exact forwardPathValid159

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

attribute [local irreducible] canClimb
private theorem actualVisits160 : eventVisits 160 forwardEvents = [0, 0, 149, 574] := by
  rw [forward_visits_computed]
  exact computedForwardVisits160
private theorem actualStart160 : startFrames[160]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd160 : finalFrames[160]! = 574 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid160 : forwardPathValid 160 = true := by
  rw [forwardPathValid, actualVisits160, actualStart160, actualEnd160]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_149, canClimb_149_574, Bool.true_and]

private theorem actualVisits161 : eventVisits 161 forwardEvents = [0, 0, 62, 575] := by
  rw [forward_visits_computed]
  exact computedForwardVisits161
private theorem actualStart161 : startFrames[161]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd161 : finalFrames[161]! = 575 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid161 : forwardPathValid 161 = true := by
  rw [forwardPathValid, actualVisits161, actualStart161, actualEnd161]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_62, canClimb_62_575, Bool.true_and]

private theorem actualVisits162 : eventVisits 162 forwardEvents = [0, 0, 181, 576] := by
  rw [forward_visits_computed]
  exact computedForwardVisits162
private theorem actualStart162 : startFrames[162]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd162 : finalFrames[162]! = 576 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid162 : forwardPathValid 162 = true := by
  rw [forwardPathValid, actualVisits162, actualStart162, actualEnd162]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_181, canClimb_181_576, Bool.true_and]

private theorem actualVisits163 : eventVisits 163 forwardEvents = [0, 0, 119, 577] := by
  rw [forward_visits_computed]
  exact computedForwardVisits163
private theorem actualStart163 : startFrames[163]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd163 : finalFrames[163]! = 577 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid163 : forwardPathValid 163 = true := by
  rw [forwardPathValid, actualVisits163, actualStart163, actualEnd163]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_119, canClimb_119_577, Bool.true_and]

private theorem actualVisits164 : eventVisits 164 forwardEvents = [0, 0, 147, 578] := by
  rw [forward_visits_computed]
  exact computedForwardVisits164
private theorem actualStart164 : startFrames[164]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd164 : finalFrames[164]! = 578 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid164 : forwardPathValid 164 = true := by
  rw [forwardPathValid, actualVisits164, actualStart164, actualEnd164]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_147, canClimb_147_578, Bool.true_and]

private theorem actualVisits165 : eventVisits 165 forwardEvents = [0, 0, 48, 579] := by
  rw [forward_visits_computed]
  exact computedForwardVisits165
private theorem actualStart165 : startFrames[165]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd165 : finalFrames[165]! = 579 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid165 : forwardPathValid 165 = true := by
  rw [forwardPathValid, actualVisits165, actualStart165, actualEnd165]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_48, canClimb_48_579, Bool.true_and]

private theorem actualVisits166 : eventVisits 166 forwardEvents = [0, 0, 178, 580] := by
  rw [forward_visits_computed]
  exact computedForwardVisits166
private theorem actualStart166 : startFrames[166]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd166 : finalFrames[166]! = 580 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid166 : forwardPathValid 166 = true := by
  rw [forwardPathValid, actualVisits166, actualStart166, actualEnd166]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_178, canClimb_178_580, Bool.true_and]

private theorem actualVisits167 : eventVisits 167 forwardEvents = [0, 0, 56, 581] := by
  rw [forward_visits_computed]
  exact computedForwardVisits167
private theorem actualStart167 : startFrames[167]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd167 : finalFrames[167]! = 581 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid167 : forwardPathValid 167 = true := by
  rw [forwardPathValid, actualVisits167, actualStart167, actualEnd167]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_56, canClimb_56_581, Bool.true_and]

theorem forwardPathBlock020 (f : Nat) (hl : 160 ≤ f) (hu : f < 168) : forwardPathValid f = true := by
  have hs : f = 160 ∨ f = 161 ∨ f = 162 ∨ f = 163 ∨ f = 164 ∨ f = 165 ∨ f = 166 ∨ f = 167 := by omega
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact forwardPathValid160
  · exact forwardPathValid161
  · exact forwardPathValid162
  · exact forwardPathValid163
  · exact forwardPathValid164
  · exact forwardPathValid165
  · exact forwardPathValid166
  · exact forwardPathValid167

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

attribute [local irreducible] canClimb
private theorem actualVisits168 : eventVisits 168 forwardEvents = [0, 0, 67, 582] := by
  rw [forward_visits_computed]
  exact computedForwardVisits168
private theorem actualStart168 : startFrames[168]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd168 : finalFrames[168]! = 582 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid168 : forwardPathValid 168 = true := by
  rw [forwardPathValid, actualVisits168, actualStart168, actualEnd168]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_67, canClimb_67_582, Bool.true_and]

private theorem actualVisits169 : eventVisits 169 forwardEvents = [0, 0, 120, 583] := by
  rw [forward_visits_computed]
  exact computedForwardVisits169
private theorem actualStart169 : startFrames[169]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd169 : finalFrames[169]! = 583 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid169 : forwardPathValid 169 = true := by
  rw [forwardPathValid, actualVisits169, actualStart169, actualEnd169]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_120, canClimb_120_583, Bool.true_and]

private theorem actualVisits170 : eventVisits 170 forwardEvents = [0, 0, 150, 584] := by
  rw [forward_visits_computed]
  exact computedForwardVisits170
private theorem actualStart170 : startFrames[170]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd170 : finalFrames[170]! = 584 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid170 : forwardPathValid 170 = true := by
  rw [forwardPathValid, actualVisits170, actualStart170, actualEnd170]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_150, canClimb_150_584, Bool.true_and]

private theorem actualVisits171 : eventVisits 171 forwardEvents = [0, 0, 585] := by
  rw [forward_visits_computed]
  exact computedForwardVisits171
private theorem actualStart171 : startFrames[171]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd171 : finalFrames[171]! = 585 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid171 : forwardPathValid 171 = true := by
  rw [forwardPathValid, actualVisits171, actualStart171, actualEnd171]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_585, Bool.true_and]

private theorem actualVisits172 : eventVisits 172 forwardEvents = [0, 0, 586] := by
  rw [forward_visits_computed]
  exact computedForwardVisits172
private theorem actualStart172 : startFrames[172]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd172 : finalFrames[172]! = 586 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid172 : forwardPathValid 172 = true := by
  rw [forwardPathValid, actualVisits172, actualStart172, actualEnd172]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_586, Bool.true_and]

private theorem actualVisits173 : eventVisits 173 forwardEvents = [0, 0, 74, 587] := by
  rw [forward_visits_computed]
  exact computedForwardVisits173
private theorem actualStart173 : startFrames[173]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd173 : finalFrames[173]! = 587 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid173 : forwardPathValid 173 = true := by
  rw [forwardPathValid, actualVisits173, actualStart173, actualEnd173]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_74, canClimb_74_587, Bool.true_and]

private theorem actualVisits174 : eventVisits 174 forwardEvents = [0, 0, 63, 588] := by
  rw [forward_visits_computed]
  exact computedForwardVisits174
private theorem actualStart174 : startFrames[174]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd174 : finalFrames[174]! = 588 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid174 : forwardPathValid 174 = true := by
  rw [forwardPathValid, actualVisits174, actualStart174, actualEnd174]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_63, canClimb_63_588, Bool.true_and]

private theorem actualVisits175 : eventVisits 175 forwardEvents = [0, 0, 180, 589] := by
  rw [forward_visits_computed]
  exact computedForwardVisits175
private theorem actualStart175 : startFrames[175]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd175 : finalFrames[175]! = 589 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid175 : forwardPathValid 175 = true := by
  rw [forwardPathValid, actualVisits175, actualStart175, actualEnd175]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_180, canClimb_180_589, Bool.true_and]

theorem forwardPathBlock021 (f : Nat) (hl : 168 ≤ f) (hu : f < 176) : forwardPathValid f = true := by
  have hs : f = 168 ∨ f = 169 ∨ f = 170 ∨ f = 171 ∨ f = 172 ∨ f = 173 ∨ f = 174 ∨ f = 175 := by omega
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact forwardPathValid168
  · exact forwardPathValid169
  · exact forwardPathValid170
  · exact forwardPathValid171
  · exact forwardPathValid172
  · exact forwardPathValid173
  · exact forwardPathValid174
  · exact forwardPathValid175

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

attribute [local irreducible] canClimb
private theorem actualVisits176 : eventVisits 176 forwardEvents = [0, 0, 68, 590] := by
  rw [forward_visits_computed]
  exact computedForwardVisits176
private theorem actualStart176 : startFrames[176]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd176 : finalFrames[176]! = 590 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid176 : forwardPathValid 176 = true := by
  rw [forwardPathValid, actualVisits176, actualStart176, actualEnd176]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_68, canClimb_68_590, Bool.true_and]

private theorem actualVisits177 : eventVisits 177 forwardEvents = [0, 0, 591] := by
  rw [forward_visits_computed]
  exact computedForwardVisits177
private theorem actualStart177 : startFrames[177]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd177 : finalFrames[177]! = 591 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid177 : forwardPathValid 177 = true := by
  rw [forwardPathValid, actualVisits177, actualStart177, actualEnd177]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_591, Bool.true_and]

private theorem actualVisits178 : eventVisits 178 forwardEvents = [0, 0, 52, 592] := by
  rw [forward_visits_computed]
  exact computedForwardVisits178
private theorem actualStart178 : startFrames[178]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd178 : finalFrames[178]! = 592 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid178 : forwardPathValid 178 = true := by
  rw [forwardPathValid, actualVisits178, actualStart178, actualEnd178]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_52, canClimb_52_592, Bool.true_and]

private theorem actualVisits179 : eventVisits 179 forwardEvents = [0, 0, 131, 593] := by
  rw [forward_visits_computed]
  exact computedForwardVisits179
private theorem actualStart179 : startFrames[179]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd179 : finalFrames[179]! = 593 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid179 : forwardPathValid 179 = true := by
  rw [forwardPathValid, actualVisits179, actualStart179, actualEnd179]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_131, canClimb_131_593, Bool.true_and]

private theorem actualVisits180 : eventVisits 180 forwardEvents = [0, 0, 129, 594] := by
  rw [forward_visits_computed]
  exact computedForwardVisits180
private theorem actualStart180 : startFrames[180]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd180 : finalFrames[180]! = 594 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid180 : forwardPathValid 180 = true := by
  rw [forwardPathValid, actualVisits180, actualStart180, actualEnd180]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_129, canClimb_129_594, Bool.true_and]

private theorem actualVisits181 : eventVisits 181 forwardEvents = [0, 0, 146, 595] := by
  rw [forward_visits_computed]
  exact computedForwardVisits181
private theorem actualStart181 : startFrames[181]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd181 : finalFrames[181]! = 595 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid181 : forwardPathValid 181 = true := by
  rw [forwardPathValid, actualVisits181, actualStart181, actualEnd181]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_146, canClimb_146_595, Bool.true_and]

private theorem actualVisits182 : eventVisits 182 forwardEvents = [0, 0, 179, 596] := by
  rw [forward_visits_computed]
  exact computedForwardVisits182
private theorem actualStart182 : startFrames[182]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd182 : finalFrames[182]! = 596 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid182 : forwardPathValid 182 = true := by
  rw [forwardPathValid, actualVisits182, actualStart182, actualEnd182]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_179, canClimb_179_596, Bool.true_and]

private theorem actualVisits183 : eventVisits 183 forwardEvents = [0, 0, 597] := by
  rw [forward_visits_computed]
  exact computedForwardVisits183
private theorem actualStart183 : startFrames[183]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd183 : finalFrames[183]! = 597 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid183 : forwardPathValid 183 = true := by
  rw [forwardPathValid, actualVisits183, actualStart183, actualEnd183]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_597, Bool.true_and]

theorem forwardPathBlock022 (f : Nat) (hl : 176 ≤ f) (hu : f < 184) : forwardPathValid f = true := by
  have hs : f = 176 ∨ f = 177 ∨ f = 178 ∨ f = 179 ∨ f = 180 ∨ f = 181 ∨ f = 182 ∨ f = 183 := by omega
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact forwardPathValid176
  · exact forwardPathValid177
  · exact forwardPathValid178
  · exact forwardPathValid179
  · exact forwardPathValid180
  · exact forwardPathValid181
  · exact forwardPathValid182
  · exact forwardPathValid183

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

attribute [local irreducible] canClimb
private theorem actualVisits184 : eventVisits 184 forwardEvents = [0, 0, 264, 598] := by
  rw [forward_visits_computed]
  exact computedForwardVisits184
private theorem actualStart184 : startFrames[184]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd184 : finalFrames[184]! = 598 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid184 : forwardPathValid 184 = true := by
  rw [forwardPathValid, actualVisits184, actualStart184, actualEnd184]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_264, canClimb_264_598, Bool.true_and]

private theorem actualVisits185 : eventVisits 185 forwardEvents = [0, 0, 599] := by
  rw [forward_visits_computed]
  exact computedForwardVisits185
private theorem actualStart185 : startFrames[185]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd185 : finalFrames[185]! = 599 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid185 : forwardPathValid 185 = true := by
  rw [forwardPathValid, actualVisits185, actualStart185, actualEnd185]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_599, Bool.true_and]

private theorem actualVisits186 : eventVisits 186 forwardEvents = [0, 0, 144, 600] := by
  rw [forward_visits_computed]
  exact computedForwardVisits186
private theorem actualStart186 : startFrames[186]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd186 : finalFrames[186]! = 600 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid186 : forwardPathValid 186 = true := by
  rw [forwardPathValid, actualVisits186, actualStart186, actualEnd186]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_144, canClimb_144_600, Bool.true_and]

private theorem actualVisits187 : eventVisits 187 forwardEvents = [0, 0, 206, 601] := by
  rw [forward_visits_computed]
  exact computedForwardVisits187
private theorem actualStart187 : startFrames[187]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd187 : finalFrames[187]! = 601 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid187 : forwardPathValid 187 = true := by
  rw [forwardPathValid, actualVisits187, actualStart187, actualEnd187]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_206, canClimb_206_601, Bool.true_and]

private theorem actualVisits188 : eventVisits 188 forwardEvents = [0, 0, 189, 602] := by
  rw [forward_visits_computed]
  exact computedForwardVisits188
private theorem actualStart188 : startFrames[188]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd188 : finalFrames[188]! = 602 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid188 : forwardPathValid 188 = true := by
  rw [forwardPathValid, actualVisits188, actualStart188, actualEnd188]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_189, canClimb_189_602, Bool.true_and]

private theorem actualVisits189 : eventVisits 189 forwardEvents = [0, 0, 260, 603] := by
  rw [forward_visits_computed]
  exact computedForwardVisits189
private theorem actualStart189 : startFrames[189]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd189 : finalFrames[189]! = 603 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid189 : forwardPathValid 189 = true := by
  rw [forwardPathValid, actualVisits189, actualStart189, actualEnd189]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_260, canClimb_260_603, Bool.true_and]

private theorem actualVisits190 : eventVisits 190 forwardEvents = [0, 0, 209, 604] := by
  rw [forward_visits_computed]
  exact computedForwardVisits190
private theorem actualStart190 : startFrames[190]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd190 : finalFrames[190]! = 604 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid190 : forwardPathValid 190 = true := by
  rw [forwardPathValid, actualVisits190, actualStart190, actualEnd190]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_209, canClimb_209_604, Bool.true_and]

private theorem actualVisits191 : eventVisits 191 forwardEvents = [0, 0, 174, 605] := by
  rw [forward_visits_computed]
  exact computedForwardVisits191
private theorem actualStart191 : startFrames[191]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd191 : finalFrames[191]! = 605 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid191 : forwardPathValid 191 = true := by
  rw [forwardPathValid, actualVisits191, actualStart191, actualEnd191]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_174, canClimb_174_605, Bool.true_and]

theorem forwardPathBlock023 (f : Nat) (hl : 184 ≤ f) (hu : f < 192) : forwardPathValid f = true := by
  have hs : f = 184 ∨ f = 185 ∨ f = 186 ∨ f = 187 ∨ f = 188 ∨ f = 189 ∨ f = 190 ∨ f = 191 := by omega
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact forwardPathValid184
  · exact forwardPathValid185
  · exact forwardPathValid186
  · exact forwardPathValid187
  · exact forwardPathValid188
  · exact forwardPathValid189
  · exact forwardPathValid190
  · exact forwardPathValid191

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

attribute [local irreducible] canClimb
private theorem actualVisits192 : eventVisits 192 forwardEvents = [0, 0, 256, 606] := by
  rw [forward_visits_computed]
  exact computedForwardVisits192
private theorem actualStart192 : startFrames[192]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd192 : finalFrames[192]! = 606 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid192 : forwardPathValid 192 = true := by
  rw [forwardPathValid, actualVisits192, actualStart192, actualEnd192]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_256, canClimb_256_606, Bool.true_and]

private theorem actualVisits193 : eventVisits 193 forwardEvents = [0, 0, 140, 607] := by
  rw [forward_visits_computed]
  exact computedForwardVisits193
private theorem actualStart193 : startFrames[193]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd193 : finalFrames[193]! = 607 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid193 : forwardPathValid 193 = true := by
  rw [forwardPathValid, actualVisits193, actualStart193, actualEnd193]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_140, canClimb_140_607, Bool.true_and]

private theorem actualVisits194 : eventVisits 194 forwardEvents = [0, 0, 204, 608] := by
  rw [forward_visits_computed]
  exact computedForwardVisits194
private theorem actualStart194 : startFrames[194]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd194 : finalFrames[194]! = 608 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid194 : forwardPathValid 194 = true := by
  rw [forwardPathValid, actualVisits194, actualStart194, actualEnd194]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_204, canClimb_204_608, Bool.true_and]

private theorem actualVisits195 : eventVisits 195 forwardEvents = [0, 0, 170, 609] := by
  rw [forward_visits_computed]
  exact computedForwardVisits195
private theorem actualStart195 : startFrames[195]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd195 : finalFrames[195]! = 609 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid195 : forwardPathValid 195 = true := by
  rw [forwardPathValid, actualVisits195, actualStart195, actualEnd195]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_170, canClimb_170_609, Bool.true_and]

private theorem actualVisits196 : eventVisits 196 forwardEvents = [0, 0, 201, 610] := by
  rw [forward_visits_computed]
  exact computedForwardVisits196
private theorem actualStart196 : startFrames[196]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd196 : finalFrames[196]! = 610 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid196 : forwardPathValid 196 = true := by
  rw [forwardPathValid, actualVisits196, actualStart196, actualEnd196]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_201, canClimb_201_610, Bool.true_and]

private theorem actualVisits197 : eventVisits 197 forwardEvents = [0, 0, 254, 611] := by
  rw [forward_visits_computed]
  exact computedForwardVisits197
private theorem actualStart197 : startFrames[197]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd197 : finalFrames[197]! = 611 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid197 : forwardPathValid 197 = true := by
  rw [forwardPathValid, actualVisits197, actualStart197, actualEnd197]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_254, canClimb_254_611, Bool.true_and]

private theorem actualVisits198 : eventVisits 198 forwardEvents = [0, 0, 185, 612] := by
  rw [forward_visits_computed]
  exact computedForwardVisits198
private theorem actualStart198 : startFrames[198]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd198 : finalFrames[198]! = 612 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid198 : forwardPathValid 198 = true := by
  rw [forwardPathValid, actualVisits198, actualStart198, actualEnd198]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_185, canClimb_185_612, Bool.true_and]

private theorem actualVisits199 : eventVisits 199 forwardEvents = [0, 0, 242, 613] := by
  rw [forward_visits_computed]
  exact computedForwardVisits199
private theorem actualStart199 : startFrames[199]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd199 : finalFrames[199]! = 613 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid199 : forwardPathValid 199 = true := by
  rw [forwardPathValid, actualVisits199, actualStart199, actualEnd199]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_242, canClimb_242_613, Bool.true_and]

theorem forwardPathBlock024 (f : Nat) (hl : 192 ≤ f) (hu : f < 200) : forwardPathValid f = true := by
  have hs : f = 192 ∨ f = 193 ∨ f = 194 ∨ f = 195 ∨ f = 196 ∨ f = 197 ∨ f = 198 ∨ f = 199 := by omega
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact forwardPathValid192
  · exact forwardPathValid193
  · exact forwardPathValid194
  · exact forwardPathValid195
  · exact forwardPathValid196
  · exact forwardPathValid197
  · exact forwardPathValid198
  · exact forwardPathValid199

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

attribute [local irreducible] canClimb
private theorem actualVisits200 : eventVisits 200 forwardEvents = [0, 0, 156, 614] := by
  rw [forward_visits_computed]
  exact computedForwardVisits200
private theorem actualStart200 : startFrames[200]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd200 : finalFrames[200]! = 614 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid200 : forwardPathValid 200 = true := by
  rw [forwardPathValid, actualVisits200, actualStart200, actualEnd200]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_156, canClimb_156_614, Bool.true_and]

private theorem actualVisits201 : eventVisits 201 forwardEvents = [0, 0, 240, 615] := by
  rw [forward_visits_computed]
  exact computedForwardVisits201
private theorem actualStart201 : startFrames[201]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd201 : finalFrames[201]! = 615 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid201 : forwardPathValid 201 = true := by
  rw [forwardPathValid, actualVisits201, actualStart201, actualEnd201]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_240, canClimb_240_615, Bool.true_and]

private theorem actualVisits202 : eventVisits 202 forwardEvents = [0, 0, 134, 616] := by
  rw [forward_visits_computed]
  exact computedForwardVisits202
private theorem actualStart202 : startFrames[202]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd202 : finalFrames[202]! = 616 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid202 : forwardPathValid 202 = true := by
  rw [forwardPathValid, actualVisits202, actualStart202, actualEnd202]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_134, canClimb_134_616, Bool.true_and]

private theorem actualVisits203 : eventVisits 203 forwardEvents = [0, 0, 182, 617] := by
  rw [forward_visits_computed]
  exact computedForwardVisits203
private theorem actualStart203 : startFrames[203]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd203 : finalFrames[203]! = 617 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid203 : forwardPathValid 203 = true := by
  rw [forwardPathValid, actualVisits203, actualStart203, actualEnd203]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_182, canClimb_182_617, Bool.true_and]

private theorem actualVisits204 : eventVisits 204 forwardEvents = [0, 0, 243, 618] := by
  rw [forward_visits_computed]
  exact computedForwardVisits204
private theorem actualStart204 : startFrames[204]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd204 : finalFrames[204]! = 618 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid204 : forwardPathValid 204 = true := by
  rw [forwardPathValid, actualVisits204, actualStart204, actualEnd204]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_243, canClimb_243_618, Bool.true_and]

private theorem actualVisits205 : eventVisits 205 forwardEvents = [0, 0, 166, 619] := by
  rw [forward_visits_computed]
  exact computedForwardVisits205
private theorem actualStart205 : startFrames[205]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd205 : finalFrames[205]! = 619 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid205 : forwardPathValid 205 = true := by
  rw [forwardPathValid, actualVisits205, actualStart205, actualEnd205]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_166, canClimb_166_619, Bool.true_and]

private theorem actualVisits206 : eventVisits 206 forwardEvents = [0, 0, 236, 620] := by
  rw [forward_visits_computed]
  exact computedForwardVisits206
private theorem actualStart206 : startFrames[206]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd206 : finalFrames[206]! = 620 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid206 : forwardPathValid 206 = true := by
  rw [forwardPathValid, actualVisits206, actualStart206, actualEnd206]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_236, canClimb_236_620, Bool.true_and]

private theorem actualVisits207 : eventVisits 207 forwardEvents = [0, 0, 137, 621] := by
  rw [forward_visits_computed]
  exact computedForwardVisits207
private theorem actualStart207 : startFrames[207]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd207 : finalFrames[207]! = 621 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid207 : forwardPathValid 207 = true := by
  rw [forwardPathValid, actualVisits207, actualStart207, actualEnd207]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_137, canClimb_137_621, Bool.true_and]

theorem forwardPathBlock025 (f : Nat) (hl : 200 ≤ f) (hu : f < 208) : forwardPathValid f = true := by
  have hs : f = 200 ∨ f = 201 ∨ f = 202 ∨ f = 203 ∨ f = 204 ∨ f = 205 ∨ f = 206 ∨ f = 207 := by omega
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact forwardPathValid200
  · exact forwardPathValid201
  · exact forwardPathValid202
  · exact forwardPathValid203
  · exact forwardPathValid204
  · exact forwardPathValid205
  · exact forwardPathValid206
  · exact forwardPathValid207

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

attribute [local irreducible] canClimb
private theorem actualVisits208 : eventVisits 208 forwardEvents = [0, 0, 152, 622] := by
  rw [forward_visits_computed]
  exact computedForwardVisits208
private theorem actualStart208 : startFrames[208]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd208 : finalFrames[208]! = 622 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid208 : forwardPathValid 208 = true := by
  rw [forwardPathValid, actualVisits208, actualStart208, actualEnd208]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_152, canClimb_152_622, Bool.true_and]

private theorem actualVisits209 : eventVisits 209 forwardEvents = [0, 0, 228, 623] := by
  rw [forward_visits_computed]
  exact computedForwardVisits209
private theorem actualStart209 : startFrames[209]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd209 : finalFrames[209]! = 623 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid209 : forwardPathValid 209 = true := by
  rw [forwardPathValid, actualVisits209, actualStart209, actualEnd209]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_228, canClimb_228_623, Bool.true_and]

private theorem actualVisits210 : eventVisits 210 forwardEvents = [0, 0, 220, 624] := by
  rw [forward_visits_computed]
  exact computedForwardVisits210
private theorem actualStart210 : startFrames[210]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd210 : finalFrames[210]! = 624 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid210 : forwardPathValid 210 = true := by
  rw [forwardPathValid, actualVisits210, actualStart210, actualEnd210]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_220, canClimb_220_624, Bool.true_and]

private theorem actualVisits211 : eventVisits 211 forwardEvents = [0, 0, 224, 625] := by
  rw [forward_visits_computed]
  exact computedForwardVisits211
private theorem actualStart211 : startFrames[211]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd211 : finalFrames[211]! = 625 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid211 : forwardPathValid 211 = true := by
  rw [forwardPathValid, actualVisits211, actualStart211, actualEnd211]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_224, canClimb_224_625, Bool.true_and]

private theorem actualVisits212 : eventVisits 212 forwardEvents = [0, 0, 219, 626] := by
  rw [forward_visits_computed]
  exact computedForwardVisits212
private theorem actualStart212 : startFrames[212]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd212 : finalFrames[212]! = 626 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid212 : forwardPathValid 212 = true := by
  rw [forwardPathValid, actualVisits212, actualStart212, actualEnd212]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_219, canClimb_219_626, Bool.true_and]

private theorem actualVisits213 : eventVisits 213 forwardEvents = [0, 0, 167, 627] := by
  rw [forward_visits_computed]
  exact computedForwardVisits213
private theorem actualStart213 : startFrames[213]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd213 : finalFrames[213]! = 627 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid213 : forwardPathValid 213 = true := by
  rw [forwardPathValid, actualVisits213, actualStart213, actualEnd213]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_167, canClimb_167_627, Bool.true_and]

private theorem actualVisits214 : eventVisits 214 forwardEvents = [0, 0, 230, 628] := by
  rw [forward_visits_computed]
  exact computedForwardVisits214
private theorem actualStart214 : startFrames[214]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd214 : finalFrames[214]! = 628 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid214 : forwardPathValid 214 = true := by
  rw [forwardPathValid, actualVisits214, actualStart214, actualEnd214]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_230, canClimb_230_628, Bool.true_and]

private theorem actualVisits215 : eventVisits 215 forwardEvents = [0, 0, 194, 629] := by
  rw [forward_visits_computed]
  exact computedForwardVisits215
private theorem actualStart215 : startFrames[215]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd215 : finalFrames[215]! = 629 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid215 : forwardPathValid 215 = true := by
  rw [forwardPathValid, actualVisits215, actualStart215, actualEnd215]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_194, canClimb_194_629, Bool.true_and]

theorem forwardPathBlock026 (f : Nat) (hl : 208 ≤ f) (hu : f < 216) : forwardPathValid f = true := by
  have hs : f = 208 ∨ f = 209 ∨ f = 210 ∨ f = 211 ∨ f = 212 ∨ f = 213 ∨ f = 214 ∨ f = 215 := by omega
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact forwardPathValid208
  · exact forwardPathValid209
  · exact forwardPathValid210
  · exact forwardPathValid211
  · exact forwardPathValid212
  · exact forwardPathValid213
  · exact forwardPathValid214
  · exact forwardPathValid215

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

attribute [local irreducible] canClimb
private theorem actualVisits216 : eventVisits 216 forwardEvents = [0, 0, 250, 630] := by
  rw [forward_visits_computed]
  exact computedForwardVisits216
private theorem actualStart216 : startFrames[216]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd216 : finalFrames[216]! = 630 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid216 : forwardPathValid 216 = true := by
  rw [forwardPathValid, actualVisits216, actualStart216, actualEnd216]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_250, canClimb_250_630, Bool.true_and]

private theorem actualVisits217 : eventVisits 217 forwardEvents = [0, 0, 212, 631] := by
  rw [forward_visits_computed]
  exact computedForwardVisits217
private theorem actualStart217 : startFrames[217]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd217 : finalFrames[217]! = 631 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid217 : forwardPathValid 217 = true := by
  rw [forwardPathValid, actualVisits217, actualStart217, actualEnd217]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_212, canClimb_212_631, Bool.true_and]

private theorem actualVisits218 : eventVisits 218 forwardEvents = [0, 0, 195, 632] := by
  rw [forward_visits_computed]
  exact computedForwardVisits218
private theorem actualStart218 : startFrames[218]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd218 : finalFrames[218]! = 632 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid218 : forwardPathValid 218 = true := by
  rw [forwardPathValid, actualVisits218, actualStart218, actualEnd218]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_195, canClimb_195_632, Bool.true_and]

private theorem actualVisits219 : eventVisits 219 forwardEvents = [0, 0, 215, 633] := by
  rw [forward_visits_computed]
  exact computedForwardVisits219
private theorem actualStart219 : startFrames[219]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd219 : finalFrames[219]! = 633 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid219 : forwardPathValid 219 = true := by
  rw [forwardPathValid, actualVisits219, actualStart219, actualEnd219]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_215, canClimb_215_633, Bool.true_and]

private theorem actualVisits220 : eventVisits 220 forwardEvents = [0, 0, 231, 634] := by
  rw [forward_visits_computed]
  exact computedForwardVisits220
private theorem actualStart220 : startFrames[220]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd220 : finalFrames[220]! = 634 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid220 : forwardPathValid 220 = true := by
  rw [forwardPathValid, actualVisits220, actualStart220, actualEnd220]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_231, canClimb_231_634, Bool.true_and]

private theorem actualVisits221 : eventVisits 221 forwardEvents = [0, 0, 251, 635] := by
  rw [forward_visits_computed]
  exact computedForwardVisits221
private theorem actualStart221 : startFrames[221]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd221 : finalFrames[221]! = 635 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid221 : forwardPathValid 221 = true := by
  rw [forwardPathValid, actualVisits221, actualStart221, actualEnd221]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_251, canClimb_251_635, Bool.true_and]

private theorem actualVisits222 : eventVisits 222 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 125, 125, 267, 267, 267, 267, 267, 267, 374, 374, 578, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits222
private theorem actualStart222 : startFrames[222]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd222 : finalFrames[222]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid222 : forwardPathValid 222 = true := by
  rw [forwardPathValid, actualVisits222, actualStart222, actualEnd222]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_2, canClimb_2_125, canClimb_125_267, canClimb_267_374, canClimb_374_578, canClimb_578_1, Bool.true_and]

private theorem actualVisits223 : eventVisits 223 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 126, 126, 268, 268, 268, 268, 268, 268, 268, 268, 348, 348, 528, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits223
private theorem actualStart223 : startFrames[223]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd223 : finalFrames[223]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid223 : forwardPathValid 223 = true := by
  rw [forwardPathValid, actualVisits223, actualStart223, actualEnd223]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_2, canClimb_2_126, canClimb_126_268, canClimb_268_348, canClimb_348_528, canClimb_528_1, Bool.true_and]

theorem forwardPathBlock027 (f : Nat) (hl : 216 ≤ f) (hu : f < 224) : forwardPathValid f = true := by
  have hs : f = 216 ∨ f = 217 ∨ f = 218 ∨ f = 219 ∨ f = 220 ∨ f = 221 ∨ f = 222 ∨ f = 223 := by omega
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact forwardPathValid216
  · exact forwardPathValid217
  · exact forwardPathValid218
  · exact forwardPathValid219
  · exact forwardPathValid220
  · exact forwardPathValid221
  · exact forwardPathValid222
  · exact forwardPathValid223

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

attribute [local irreducible] canClimb
private theorem actualVisits224 : eventVisits 224 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 213, 213, 288, 288, 288, 288, 288, 474, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits224
private theorem actualStart224 : startFrames[224]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd224 : finalFrames[224]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid224 : forwardPathValid 224 = true := by
  rw [forwardPathValid, actualVisits224, actualStart224, actualEnd224]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_3, canClimb_3_213, canClimb_213_288, canClimb_288_474, canClimb_474_1, Bool.true_and]

private theorem actualVisits225 : eventVisits 225 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 214, 214, 300, 300, 300, 300, 300, 300, 300, 396, 396, 582, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits225
private theorem actualStart225 : startFrames[225]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd225 : finalFrames[225]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid225 : forwardPathValid 225 = true := by
  rw [forwardPathValid, actualVisits225, actualStart225, actualEnd225]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_3, canClimb_3_214, canClimb_214_300, canClimb_300_396, canClimb_396_582, canClimb_582_1, Bool.true_and]

private theorem actualVisits226 : eventVisits 226 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 230, 230, 266, 266, 266, 266, 266, 266, 266, 266, 475, 475, 634, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits226
private theorem actualStart226 : startFrames[226]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd226 : finalFrames[226]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid226 : forwardPathValid 226 = true := by
  rw [forwardPathValid, actualVisits226, actualStart226, actualEnd226]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_4, canClimb_4_230, canClimb_230_266, canClimb_266_475, canClimb_475_634, canClimb_634_1, Bool.true_and]

private theorem actualVisits227 : eventVisits 227 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 232, 456, 633, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits227
private theorem actualStart227 : startFrames[227]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd227 : finalFrames[227]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid227 : forwardPathValid 227 = true := by
  rw [forwardPathValid, actualVisits227, actualStart227, actualEnd227]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_4, canClimb_4_232, canClimb_232_456, canClimb_456_633, canClimb_633_1, Bool.true_and]

private theorem actualVisits228 : eventVisits 228 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 125, 507, 330, 531, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits228
private theorem actualStart228 : startFrames[228]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd228 : finalFrames[228]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid228 : forwardPathValid 228 = true := by
  rw [forwardPathValid, actualVisits228, actualStart228, actualEnd228]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_5, canClimb_5_125, canClimb_125_507, canClimb_330_531, canClimb_507_330, canClimb_531_1, Bool.true_and]

private theorem actualVisits229 : eventVisits 229 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 5, 336, 581, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits229
private theorem actualStart229 : startFrames[229]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd229 : finalFrames[229]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid229 : forwardPathValid 229 = true := by
  rw [forwardPathValid, actualVisits229, actualStart229, actualEnd229]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_5, canClimb_5_336, canClimb_336_581, canClimb_581_1, Bool.true_and]

private theorem actualVisits230 : eventVisits 230 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 233, 233, 290, 290, 290, 290, 290, 290, 290, 290, 472, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits230
private theorem actualStart230 : startFrames[230]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd230 : finalFrames[230]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid230 : forwardPathValid 230 = true := by
  rw [forwardPathValid, actualVisits230, actualStart230, actualEnd230]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_6, canClimb_6_233, canClimb_233_290, canClimb_290_472, canClimb_472_1, Bool.true_and]

private theorem actualVisits231 : eventVisits 231 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 234, 234, 278, 278, 278, 278, 278, 278, 278, 278, 471, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits231
private theorem actualStart231 : startFrames[231]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd231 : finalFrames[231]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid231 : forwardPathValid 231 = true := by
  rw [forwardPathValid, actualVisits231, actualStart231, actualEnd231]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_6, canClimb_6_234, canClimb_234_278, canClimb_278_471, canClimb_471_1, Bool.true_and]

theorem forwardPathBlock028 (f : Nat) (hl : 224 ≤ f) (hu : f < 232) : forwardPathValid f = true := by
  have hs : f = 224 ∨ f = 225 ∨ f = 226 ∨ f = 227 ∨ f = 228 ∨ f = 229 ∨ f = 230 ∨ f = 231 := by omega
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact forwardPathValid224
  · exact forwardPathValid225
  · exact forwardPathValid226
  · exact forwardPathValid227
  · exact forwardPathValid228
  · exact forwardPathValid229
  · exact forwardPathValid230
  · exact forwardPathValid231

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

attribute [local irreducible] canClimb
private theorem actualVisits232 : eventVisits 232 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 113, 113, 276, 276, 276, 276, 276, 276, 276, 379, 379, 595, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits232
private theorem actualStart232 : startFrames[232]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd232 : finalFrames[232]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid232 : forwardPathValid 232 = true := by
  rw [forwardPathValid, actualVisits232, actualStart232, actualEnd232]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_7, canClimb_7_113, canClimb_113_276, canClimb_276_379, canClimb_379_595, canClimb_595_1, Bool.true_and]

private theorem actualVisits233 : eventVisits 233 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 7, 506, 506, 506, 352, 515, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits233
private theorem actualStart233 : startFrames[233]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd233 : finalFrames[233]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid233 : forwardPathValid 233 = true := by
  rw [forwardPathValid, actualVisits233, actualStart233, actualEnd233]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_7, canClimb_7_506, canClimb_352_515, canClimb_506_352, canClimb_515_1, Bool.true_and]

private theorem actualVisits234 : eventVisits 234 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 115, 115, 270, 270, 270, 270, 270, 270, 270, 270, 328, 328, 530, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits234
private theorem actualStart234 : startFrames[234]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd234 : finalFrames[234]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid234 : forwardPathValid 234 = true := by
  rw [forwardPathValid, actualVisits234, actualStart234, actualEnd234]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_8, canClimb_8_115, canClimb_115_270, canClimb_270_328, canClimb_328_530, canClimb_530_1, Bool.true_and]

private theorem actualVisits235 : eventVisits 235 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 8, 268, 268, 268, 268, 268, 268, 268, 268, 327, 327, 534, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits235
private theorem actualStart235 : startFrames[235]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd235 : finalFrames[235]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid235 : forwardPathValid 235 = true := by
  rw [forwardPathValid, actualVisits235, actualStart235, actualEnd235]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_8, canClimb_8_268, canClimb_268_327, canClimb_327_534, canClimb_534_1, Bool.true_and]

private theorem actualVisits236 : eventVisits 236 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 212, 212, 266, 266, 266, 266, 266, 266, 266, 266, 457, 457, 631, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits236
private theorem actualStart236 : startFrames[236]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd236 : finalFrames[236]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid236 : forwardPathValid 236 = true := by
  rw [forwardPathValid, actualVisits236, actualStart236, actualEnd236]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_9, canClimb_9_212, canClimb_212_266, canClimb_266_457, canClimb_457_631, canClimb_631_1, Bool.true_and]

private theorem actualVisits237 : eventVisits 237 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 216, 483, 541, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits237
private theorem actualStart237 : startFrames[237]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd237 : finalFrames[237]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid237 : forwardPathValid 237 = true := by
  rw [forwardPathValid, actualVisits237, actualStart237, actualEnd237]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_9, canClimb_9_216, canClimb_216_483, canClimb_483_541, canClimb_541_1, Bool.true_and]

private theorem actualVisits238 : eventVisits 238 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 248, 248, 266, 266, 266, 266, 266, 266, 266, 266, 493, 493, 630, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits238
private theorem actualStart238 : startFrames[238]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd238 : finalFrames[238]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid238 : forwardPathValid 238 = true := by
  rw [forwardPathValid, actualVisits238, actualStart238, actualEnd238]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_10, canClimb_10_248, canClimb_248_266, canClimb_266_493, canClimb_493_630, canClimb_630_1, Bool.true_and]

private theorem actualVisits239 : eventVisits 239 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 250, 250, 289, 289, 289, 289, 289, 289, 289, 289, 491, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits239
private theorem actualStart239 : startFrames[239]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd239 : finalFrames[239]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid239 : forwardPathValid 239 = true := by
  rw [forwardPathValid, actualVisits239, actualStart239, actualEnd239]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_10, canClimb_10_250, canClimb_250_289, canClimb_289_491, canClimb_491_1, Bool.true_and]

theorem forwardPathBlock029 (f : Nat) (hl : 232 ≤ f) (hu : f < 240) : forwardPathValid f = true := by
  have hs : f = 232 ∨ f = 233 ∨ f = 234 ∨ f = 235 ∨ f = 236 ∨ f = 237 ∨ f = 238 ∨ f = 239 := by omega
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact forwardPathValid232
  · exact forwardPathValid233
  · exact forwardPathValid234
  · exact forwardPathValid235
  · exact forwardPathValid236
  · exact forwardPathValid237
  · exact forwardPathValid238
  · exact forwardPathValid239

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

attribute [local irreducible] canClimb
private theorem actualVisits240 : eventVisits 240 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 11, 114, 114, 274, 274, 274, 274, 274, 274, 274, 274, 330, 330, 510, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits240
private theorem actualStart240 : startFrames[240]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd240 : finalFrames[240]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid240 : forwardPathValid 240 = true := by
  rw [forwardPathValid, actualVisits240, actualStart240, actualEnd240]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_11, canClimb_11_114, canClimb_114_274, canClimb_274_330, canClimb_330_510, canClimb_510_1, Bool.true_and]

private theorem actualVisits241 : eventVisits 241 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 11, 115, 506, 506, 361, 516, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits241
private theorem actualStart241 : startFrames[241]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd241 : finalFrames[241]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid241 : forwardPathValid 241 = true := by
  rw [forwardPathValid, actualVisits241, actualStart241, actualEnd241]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_11, canClimb_11_115, canClimb_115_506, canClimb_361_516, canClimb_506_361, canClimb_516_1, Bool.true_and]

private theorem actualVisits242 : eventVisits 242 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 7, 272, 272, 272, 272, 272, 272, 272, 272, 347, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits242
private theorem actualStart242 : startFrames[242]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd242 : finalFrames[242]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid242 : forwardPathValid 242 = true := by
  rw [forwardPathValid, actualVisits242, actualStart242, actualEnd242]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_7, canClimb_7_272, canClimb_272_347, canClimb_347_1, Bool.true_and]

private theorem actualVisits243 : eventVisits 243 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 11, 11, 266, 266, 266, 266, 266, 266, 266, 266, 344, 344, 525, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits243
private theorem actualStart243 : startFrames[243]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd243 : finalFrames[243]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid243 : forwardPathValid 243 = true := by
  rw [forwardPathValid, actualVisits243, actualStart243, actualEnd243]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_11, canClimb_11_266, canClimb_266_344, canClimb_344_525, canClimb_525_1, Bool.true_and]

private theorem actualVisits244 : eventVisits 244 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12, 194, 194, 266, 266, 266, 266, 266, 266, 266, 266, 439, 439, 632, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits244
private theorem actualStart244 : startFrames[244]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd244 : finalFrames[244]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid244 : forwardPathValid 244 = true := by
  rw [forwardPathValid, actualVisits244, actualStart244, actualEnd244]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_12, canClimb_12_194, canClimb_194_266, canClimb_266_439, canClimb_439_632, canClimb_632_1, Bool.true_and]

private theorem actualVisits245 : eventVisits 245 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12, 196, 497, 562, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits245
private theorem actualStart245 : startFrames[245]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd245 : finalFrames[245]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid245 : forwardPathValid 245 = true := by
  rw [forwardPathValid, actualVisits245, actualStart245, actualEnd245]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_12, canClimb_12_196, canClimb_196_497, canClimb_497_562, canClimb_562_1, Bool.true_and]

private theorem actualVisits246 : eventVisits 246 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 127, 127, 271, 271, 271, 271, 271, 271, 271, 271, 346, 346, 525, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits246
private theorem actualStart246 : startFrames[246]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd246 : finalFrames[246]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid246 : forwardPathValid 246 = true := by
  rw [forwardPathValid, actualVisits246, actualStart246, actualEnd246]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_13, canClimb_13_127, canClimb_127_271, canClimb_271_346, canClimb_346_525, canClimb_525_1, Bool.true_and]

private theorem actualVisits247 : eventVisits 247 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 13, 266, 266, 266, 266, 266, 266, 266, 266, 326, 326, 530, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits247
private theorem actualStart247 : startFrames[247]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd247 : finalFrames[247]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid247 : forwardPathValid 247 = true := by
  rw [forwardPathValid, actualVisits247, actualStart247, actualEnd247]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_13, canClimb_13_266, canClimb_266_326, canClimb_326_530, canClimb_530_1, Bool.true_and]

theorem forwardPathBlock030 (f : Nat) (hl : 240 ≤ f) (hu : f < 248) : forwardPathValid f = true := by
  have hs : f = 240 ∨ f = 241 ∨ f = 242 ∨ f = 243 ∨ f = 244 ∨ f = 245 ∨ f = 246 ∨ f = 247 := by omega
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact forwardPathValid240
  · exact forwardPathValid241
  · exact forwardPathValid242
  · exact forwardPathValid243
  · exact forwardPathValid244
  · exact forwardPathValid245
  · exact forwardPathValid246
  · exact forwardPathValid247

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

attribute [local irreducible] canClimb
private theorem actualVisits248 : eventVisits 248 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 248, 444, 610, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits248
private theorem actualStart248 : startFrames[248]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd248 : finalFrames[248]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid248 : forwardPathValid 248 = true := by
  rw [forwardPathValid, actualVisits248, actualStart248, actualEnd248]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_14, canClimb_14_248, canClimb_248_444, canClimb_444_610, canClimb_610_1, Bool.true_and]

private theorem actualVisits249 : eventVisits 249 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 251, 251, 279, 279, 279, 279, 279, 279, 436, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits249
private theorem actualStart249 : startFrames[249]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd249 : finalFrames[249]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid249 : forwardPathValid 249 = true := by
  rw [forwardPathValid, actualVisits249, actualStart249, actualEnd249]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_14, canClimb_14_251, canClimb_251_279, canClimb_279_436, canClimb_436_1, Bool.true_and]

private theorem actualVisits250 : eventVisits 250 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 15, 197, 505, 598, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits250
private theorem actualStart250 : startFrames[250]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd250 : finalFrames[250]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid250 : forwardPathValid 250 = true := by
  rw [forwardPathValid, actualVisits250, actualStart250, actualEnd250]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_15, canClimb_15_197, canClimb_197_505, canClimb_505_598, canClimb_598_1, Bool.true_and]

private theorem actualVisits251 : eventVisits 251 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 15, 198, 198, 291, 291, 291, 291, 291, 291, 291, 291, 377, 377, 584, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits251
private theorem actualStart251 : startFrames[251]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd251 : finalFrames[251]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid251 : forwardPathValid 251 = true := by
  rw [forwardPathValid, actualVisits251, actualStart251, actualEnd251]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_15, canClimb_15_198, canClimb_198_291, canClimb_291_377, canClimb_377_584, canClimb_584_1, Bool.true_and]

private theorem actualVisits252 : eventVisits 252 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 270, 270, 270, 270, 270, 367, 367, 616, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits252
private theorem actualStart252 : startFrames[252]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd252 : finalFrames[252]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid252 : forwardPathValid 252 = true := by
  rw [forwardPathValid, actualVisits252, actualStart252, actualEnd252]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_2, canClimb_2_270, canClimb_270_367, canClimb_367_616, canClimb_616_1, Bool.true_and]

private theorem actualVisits253 : eventVisits 253 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 5, 269, 269, 269, 269, 269, 368, 368, 555, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits253
private theorem actualStart253 : startFrames[253]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd253 : finalFrames[253]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid253 : forwardPathValid 253 = true := by
  rw [forwardPathValid, actualVisits253, actualStart253, actualEnd253]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_5, canClimb_5_269, canClimb_269_368, canClimb_368_555, canClimb_555_1, Bool.true_and]

private theorem actualVisits254 : eventVisits 254 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 237, 465, 550, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits254
private theorem actualStart254 : startFrames[254]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd254 : finalFrames[254]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid254 : forwardPathValid 254 = true := by
  rw [forwardPathValid, actualVisits254, actualStart254, actualEnd254]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_16, canClimb_16_237, canClimb_237_465, canClimb_465_550, canClimb_550_1, Bool.true_and]

private theorem actualVisits255 : eventVisits 255 forwardEvents = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 238, 238, 294, 294, 294, 294, 294, 294, 294, 466, 466, 625, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  rw [forward_visits_computed]
  exact computedForwardVisits255
private theorem actualStart255 : startFrames[255]! = 0 := by
  rw [startFrames_lookup]
  rfl
private theorem actualEnd255 : finalFrames[255]! = 1 := by
  rw [finalFrames_lookup]
  rfl
theorem forwardPathValid255 : forwardPathValid 255 = true := by
  rw [forwardPathValid, actualVisits255, actualStart255, actualEnd255]
  simp only [List.cons_append, List.nil_append, climbPath, canClimb_self,
    canClimb_0_16, canClimb_16_238, canClimb_238_294, canClimb_294_466, canClimb_466_625, canClimb_625_1, Bool.true_and]

theorem forwardPathBlock031 (f : Nat) (hl : 248 ≤ f) (hu : f < 256) : forwardPathValid f = true := by
  have hs : f = 248 ∨ f = 249 ∨ f = 250 ∨ f = 251 ∨ f = 252 ∨ f = 253 ∨ f = 254 ∨ f = 255 := by omega
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact forwardPathValid248
  · exact forwardPathValid249
  · exact forwardPathValid250
  · exact forwardPathValid251
  · exact forwardPathValid252
  · exact forwardPathValid253
  · exact forwardPathValid254
  · exact forwardPathValid255

end CSL.Construction.PhysicalFramePaths


