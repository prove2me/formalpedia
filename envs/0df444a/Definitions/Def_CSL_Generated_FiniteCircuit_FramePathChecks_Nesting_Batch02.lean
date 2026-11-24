-- Prove2me | Definitions.Def_CSL_Generated_FiniteCircuit_FramePathChecks_Nesting_Batch02
-- name    : CSL_Generated_FiniteCircuit_FramePathChecks_Nesting_Batch02
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T13:58:20.592337+00:00
-- url     : https://prove2.me/theorems/4f37b147-fb0b-4532-9dfb-390ad30bd11a
-- title:
--   Coded sorting library: Generated / FiniteCircuit / FramePathChecks / Nesting / Batch02
-- statement:
--   Module `CodedSorting.Generated.FiniteCircuit.FramePathChecks.Nesting.Batch02` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   Generated physical-frame checks. Uncompiled until a build record exists.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Generated.FiniteCircuit.FramePathChecks.Nesting.Batch02

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Generated_FiniteCircuit_FramePathChecks_Entries_Batch01
import Definitions.Def_CSL_Generated_FiniteCircuit_FramePathChecks_Entries_Batch02
import Definitions.Def_CSL_Generated_FiniteCircuit_FramePathChecks_Entries_Batch03
import Definitions.Def_CSL_Generated_FiniteCircuit_FramePathChecks_Entries_Batch04

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem canClimb_139_302 : canClimb 139 302 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup139, nestingLookup302]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq139 nestingEntries_eq302]
  decide

theorem canClimb_139_519 : canClimb 139 519 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup139, nestingLookup519]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq139 nestingEntries_eq519]
  decide

theorem canClimb_139_540 : canClimb 139 540 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup139, nestingLookup540]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq139 nestingEntries_eq540]
  decide

theorem canClimb_140_274 : canClimb 140 274 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup140, nestingLookup274]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq140 nestingEntries_eq274]
  decide

theorem canClimb_140_313 : canClimb 140 313 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup140, nestingLookup313]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq140 nestingEntries_eq313]
  decide

theorem canClimb_140_519 : canClimb 140 519 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup140, nestingLookup519]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq140 nestingEntries_eq519]
  decide

theorem canClimb_140_607 : canClimb 140 607 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup140, nestingLookup607]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq140 nestingEntries_eq607]
  decide

theorem canClimb_141_287 : canClimb 141 287 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup141, nestingLookup287]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq141 nestingEntries_eq287]
  decide

theorem canClimb_141_312 : canClimb 141 312 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup141, nestingLookup312]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq141 nestingEntries_eq312]
  decide

theorem canClimb_141_411 : canClimb 141 411 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup141, nestingLookup411]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq141 nestingEntries_eq411]
  decide

theorem canClimb_142_299 : canClimb 142 299 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup142, nestingLookup299]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq142 nestingEntries_eq299]
  decide

theorem canClimb_142_311 : canClimb 142 311 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup142, nestingLookup311]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq142 nestingEntries_eq311]
  decide

theorem canClimb_142_412 : canClimb 142 412 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup142, nestingLookup412]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq142 nestingEntries_eq412]
  decide

theorem canClimb_143_292 : canClimb 143 292 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup143, nestingLookup292]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq143 nestingEntries_eq292]
  decide

theorem canClimb_143_310 : canClimb 143 310 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup143, nestingLookup310]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq143 nestingEntries_eq310]
  decide

theorem canClimb_143_519 : canClimb 143 519 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup143, nestingLookup519]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq143 nestingEntries_eq519]
  decide

theorem canClimb_143_555 : canClimb 143 555 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup143, nestingLookup555]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq143 nestingEntries_eq555]
  decide

theorem canClimb_144_280 : canClimb 144 280 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup144, nestingLookup280]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq144 nestingEntries_eq280]
  decide

theorem canClimb_144_309 : canClimb 144 309 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup144, nestingLookup309]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq144 nestingEntries_eq309]
  decide

theorem canClimb_144_519 : canClimb 144 519 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup144, nestingLookup519]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq144 nestingEntries_eq519]
  decide

theorem canClimb_144_600 : canClimb 144 600 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup144, nestingLookup600]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq144 nestingEntries_eq600]
  decide

theorem canClimb_145_269 : canClimb 145 269 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup145, nestingLookup269]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq145 nestingEntries_eq269]
  decide

theorem canClimb_145_308 : canClimb 145 308 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup145, nestingLookup308]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq145 nestingEntries_eq308]
  decide

theorem canClimb_145_519 : canClimb 145 519 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup145, nestingLookup519]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq145 nestingEntries_eq519]
  decide

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem canClimb_145_566 : canClimb 145 566 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup145, nestingLookup566]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq145 nestingEntries_eq566]
  decide

theorem canClimb_146_276 : canClimb 146 276 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup146, nestingLookup276]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq146 nestingEntries_eq276]
  decide

theorem canClimb_146_319 : canClimb 146 319 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup146, nestingLookup319]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq146 nestingEntries_eq319]
  decide

theorem canClimb_146_519 : canClimb 146 519 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup146, nestingLookup519]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq146 nestingEntries_eq519]
  decide

theorem canClimb_146_595 : canClimb 146 595 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup146, nestingLookup595]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq146 nestingEntries_eq595]
  decide

theorem canClimb_147_288 : canClimb 147 288 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup147, nestingLookup288]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq147 nestingEntries_eq288]
  decide

theorem canClimb_147_318 : canClimb 147 318 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup147, nestingLookup318]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq147 nestingEntries_eq318]
  decide

theorem canClimb_147_519 : canClimb 147 519 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup147, nestingLookup519]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq147 nestingEntries_eq519]
  decide

theorem canClimb_147_578 : canClimb 147 578 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup147, nestingLookup578]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq147 nestingEntries_eq578]
  decide

theorem canClimb_148_291 : canClimb 148 291 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup148, nestingLookup291]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq148 nestingEntries_eq291]
  decide

theorem canClimb_148_317 : canClimb 148 317 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup148, nestingLookup317]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq148 nestingEntries_eq317]
  decide

theorem canClimb_148_406 : canClimb 148 406 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup148, nestingLookup406]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq148 nestingEntries_eq406]
  decide

theorem canClimb_149_301 : canClimb 149 301 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup149, nestingLookup301]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq149 nestingEntries_eq301]
  decide

theorem canClimb_149_316 : canClimb 149 316 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup149, nestingLookup316]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq149 nestingEntries_eq316]
  decide

theorem canClimb_149_519 : canClimb 149 519 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup149, nestingLookup519]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq149 nestingEntries_eq519]
  decide

theorem canClimb_149_574 : canClimb 149 574 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup149, nestingLookup574]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq149 nestingEntries_eq574]
  decide

theorem canClimb_150_278 : canClimb 150 278 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup150, nestingLookup278]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq150 nestingEntries_eq278]
  decide

theorem canClimb_150_315 : canClimb 150 315 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup150, nestingLookup315]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq150 nestingEntries_eq315]
  decide

theorem canClimb_150_519 : canClimb 150 519 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup150, nestingLookup519]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq150 nestingEntries_eq519]
  decide

theorem canClimb_150_584 : canClimb 150 584 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup150, nestingLookup584]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq150 nestingEntries_eq584]
  decide

theorem canClimb_151_267 : canClimb 151 267 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup151, nestingLookup267]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq151 nestingEntries_eq267]
  decide

theorem canClimb_151_314 : canClimb 151 314 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup151, nestingLookup314]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq151 nestingEntries_eq314]
  decide

theorem canClimb_151_408 : canClimb 151 408 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup151, nestingLookup408]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq151 nestingEntries_eq408]
  decide

theorem canClimb_152_268 : canClimb 152 268 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup152, nestingLookup268]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq152 nestingEntries_eq268]
  decide

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem canClimb_152_315 : canClimb 152 315 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup152, nestingLookup315]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq152 nestingEntries_eq315]
  decide

theorem canClimb_152_508 : canClimb 152 508 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup152, nestingLookup508]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq152 nestingEntries_eq508]
  decide

theorem canClimb_152_622 : canClimb 152 622 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup152, nestingLookup622]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq152 nestingEntries_eq622]
  decide

theorem canClimb_153_293 : canClimb 153 293 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup153, nestingLookup293]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq153 nestingEntries_eq293]
  decide

theorem canClimb_153_306 : canClimb 153 306 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup153, nestingLookup306]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq153 nestingEntries_eq306]
  decide

theorem canClimb_153_508 : canClimb 153 508 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup153, nestingLookup508]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq153 nestingEntries_eq508]
  decide

theorem canClimb_154_287 : canClimb 154 287 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup154, nestingLookup287]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq154 nestingEntries_eq287]
  decide

theorem canClimb_154_321 : canClimb 154 321 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup154, nestingLookup321]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq154 nestingEntries_eq321]
  decide

theorem canClimb_154_508 : canClimb 154 508 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup154, nestingLookup508]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq154 nestingEntries_eq508]
  decide

theorem canClimb_154_552 : canClimb 154 552 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup154, nestingLookup552]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq154 nestingEntries_eq552]
  decide

theorem canClimb_155_280 : canClimb 155 280 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup155, nestingLookup280]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq155 nestingEntries_eq280]
  decide

theorem canClimb_155_320 : canClimb 155 320 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup155, nestingLookup320]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq155 nestingEntries_eq320]
  decide

theorem canClimb_155_508 : canClimb 155 508 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup155, nestingLookup508]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq155 nestingEntries_eq508]
  decide

theorem canClimb_155_544 : canClimb 155 544 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup155, nestingLookup544]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq155 nestingEntries_eq544]
  decide

theorem canClimb_156_298 : canClimb 156 298 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup156, nestingLookup298]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq156 nestingEntries_eq298]
  decide

theorem canClimb_156_303 : canClimb 156 303 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup156, nestingLookup303]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq156 nestingEntries_eq303]
  decide

theorem canClimb_156_508 : canClimb 156 508 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup156, nestingLookup508]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq156 nestingEntries_eq508]
  decide

theorem canClimb_156_614 : canClimb 156 614 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup156, nestingLookup614]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq156 nestingEntries_eq614]
  decide

theorem canClimb_157_275 : canClimb 157 275 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup157, nestingLookup275]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq157 nestingEntries_eq275]
  decide

theorem canClimb_157_318 : canClimb 157 318 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup157, nestingLookup318]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq157 nestingEntries_eq318]
  decide

theorem canClimb_157_508 : canClimb 157 508 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup157, nestingLookup508]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq157 nestingEntries_eq508]
  decide

theorem canClimb_158_272 : canClimb 158 272 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup158, nestingLookup272]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq158 nestingEntries_eq272]
  decide

theorem canClimb_158_317 : canClimb 158 317 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup158, nestingLookup317]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq158 nestingEntries_eq317]
  decide

theorem canClimb_158_508 : canClimb 158 508 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup158, nestingLookup508]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq158 nestingEntries_eq508]
  decide

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem canClimb_159_296 : canClimb 159 296 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup159, nestingLookup296]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq159 nestingEntries_eq296]
  decide

theorem canClimb_159_323 : canClimb 159 323 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup159, nestingLookup323]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq159 nestingEntries_eq323]
  decide

theorem canClimb_159_508 : canClimb 159 508 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup159, nestingLookup508]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq159 nestingEntries_eq508]
  decide

theorem canClimb_159_568 : canClimb 159 568 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup159, nestingLookup568]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq159 nestingEntries_eq568]
  decide

theorem canClimb_160_283 : canClimb 160 283 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup160, nestingLookup283]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq160 nestingEntries_eq283]
  decide

theorem canClimb_160_311 : canClimb 160 311 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup160, nestingLookup311]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq160 nestingEntries_eq311]
  decide

theorem canClimb_160_508 : canClimb 160 508 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup160, nestingLookup508]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq160 nestingEntries_eq508]
  decide

theorem canClimb_160_560 : canClimb 160 560 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup160, nestingLookup560]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq160 nestingEntries_eq560]
  decide

theorem canClimb_161_289 : canClimb 161 289 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup161, nestingLookup289]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq161 nestingEntries_eq289]
  decide

theorem canClimb_161_308 : canClimb 161 308 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup161, nestingLookup308]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq161 nestingEntries_eq308]
  decide

theorem canClimb_161_508 : canClimb 161 508 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup161, nestingLookup508]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq161 nestingEntries_eq508]
  decide

theorem canClimb_162_290 : canClimb 162 290 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup162, nestingLookup290]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq162 nestingEntries_eq290]
  decide

theorem canClimb_162_307 : canClimb 162 307 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup162, nestingLookup307]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq162 nestingEntries_eq307]
  decide

theorem canClimb_162_508 : canClimb 162 508 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup162, nestingLookup508]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq162 nestingEntries_eq508]
  decide

theorem canClimb_163_267 : canClimb 163 267 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup163, nestingLookup267]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq163 nestingEntries_eq267]
  decide

theorem canClimb_163_324 : canClimb 163 324 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup163, nestingLookup324]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq163 nestingEntries_eq324]
  decide

theorem canClimb_163_508 : canClimb 163 508 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup163, nestingLookup508]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq163 nestingEntries_eq508]
  decide

theorem canClimb_164_270 : canClimb 164 270 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup164, nestingLookup270]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq164 nestingEntries_eq270]
  decide

theorem canClimb_164_302 : canClimb 164 302 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup164, nestingLookup302]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq164 nestingEntries_eq302]
  decide

theorem canClimb_164_372 : canClimb 164 372 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup164, nestingLookup372]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq164 nestingEntries_eq372]
  decide

theorem canClimb_165_285 : canClimb 165 285 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup165, nestingLookup285]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq165 nestingEntries_eq285]
  decide

theorem canClimb_165_306 : canClimb 165 306 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup165, nestingLookup306]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq165 nestingEntries_eq306]
  decide

theorem canClimb_165_520 : canClimb 165 520 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup165, nestingLookup520]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq165 nestingEntries_eq520]
  decide

theorem canClimb_165_551 : canClimb 165 551 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup165, nestingLookup551]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq165 nestingEntries_eq551]
  decide

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem canClimb_166_295 : canClimb 166 295 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup166, nestingLookup295]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq166 nestingEntries_eq295]
  decide

theorem canClimb_166_305 : canClimb 166 305 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup166, nestingLookup305]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq166 nestingEntries_eq305]
  decide

theorem canClimb_166_520 : canClimb 166 520 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup166, nestingLookup520]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq166 nestingEntries_eq520]
  decide

theorem canClimb_166_619 : canClimb 166 619 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup166, nestingLookup619]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq166 nestingEntries_eq619]
  decide

theorem canClimb_167_296 : canClimb 167 296 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup167, nestingLookup296]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq167 nestingEntries_eq296]
  decide

theorem canClimb_167_304 : canClimb 167 304 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup167, nestingLookup304]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq167 nestingEntries_eq304]
  decide

theorem canClimb_167_520 : canClimb 167 520 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup167, nestingLookup520]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq167 nestingEntries_eq520]
  decide

theorem canClimb_167_627 : canClimb 167 627 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup167, nestingLookup627]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq167 nestingEntries_eq627]
  decide

theorem canClimb_168_282 : canClimb 168 282 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup168, nestingLookup282]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq168 nestingEntries_eq282]
  decide

theorem canClimb_168_303 : canClimb 168 303 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup168, nestingLookup303]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq168 nestingEntries_eq303]
  decide

theorem canClimb_168_520 : canClimb 168 520 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup168, nestingLookup520]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq168 nestingEntries_eq520]
  decide

theorem canClimb_168_546 : canClimb 168 546 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup168, nestingLookup546]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq168 nestingEntries_eq546]
  decide

theorem canClimb_169_273 : canClimb 169 273 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup169, nestingLookup273]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq169 nestingEntries_eq273]
  decide

theorem canClimb_169_307 : canClimb 169 307 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup169, nestingLookup307]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq169 nestingEntries_eq307]
  decide

theorem canClimb_169_367 : canClimb 169 367 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup169, nestingLookup367]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq169 nestingEntries_eq367]
  decide

theorem canClimb_170_274 : canClimb 170 274 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup170, nestingLookup274]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq170 nestingEntries_eq274]
  decide

theorem canClimb_170_308 : canClimb 170 308 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup170, nestingLookup308]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq170 nestingEntries_eq308]
  decide

theorem canClimb_170_520 : canClimb 170 520 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup170, nestingLookup520]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq170 nestingEntries_eq520]
  decide

theorem canClimb_170_609 : canClimb 170 609 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup170, nestingLookup609]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq170 nestingEntries_eq609]
  decide

theorem canClimb_171_280 : canClimb 171 280 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup171, nestingLookup280]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq171 nestingEntries_eq280]
  decide

theorem canClimb_171_312 : canClimb 171 312 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup171, nestingLookup312]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq171 nestingEntries_eq312]
  decide

theorem canClimb_171_364 : canClimb 171 364 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup171, nestingLookup364]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq171 nestingEntries_eq364]
  decide

theorem canClimb_172_292 : canClimb 172 292 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup172, nestingLookup292]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq172 nestingEntries_eq292]
  decide

theorem canClimb_172_311 : canClimb 172 311 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup172, nestingLookup311]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq172 nestingEntries_eq311]
  decide

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem canClimb_172_520 : canClimb 172 520 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup172, nestingLookup520]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq172 nestingEntries_eq520]
  decide

theorem canClimb_172_569 : canClimb 172 569 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup172, nestingLookup569]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq172 nestingEntries_eq569]
  decide

theorem canClimb_173_299 : canClimb 173 299 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup173, nestingLookup299]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq173 nestingEntries_eq299]
  decide

theorem canClimb_173_310 : canClimb 173 310 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup173, nestingLookup310]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq173 nestingEntries_eq310]
  decide

theorem canClimb_173_520 : canClimb 173 520 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup173, nestingLookup520]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq173 nestingEntries_eq520]
  decide

theorem canClimb_173_561 : canClimb 173 561 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup173, nestingLookup561]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq173 nestingEntries_eq561]
  decide

theorem canClimb_174_287 : canClimb 174 287 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup174, nestingLookup287]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq174 nestingEntries_eq287]
  decide

theorem canClimb_174_309 : canClimb 174 309 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup174, nestingLookup309]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq174 nestingEntries_eq309]
  decide

theorem canClimb_174_520 : canClimb 174 520 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup174, nestingLookup520]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq174 nestingEntries_eq520]
  decide

theorem canClimb_174_605 : canClimb 174 605 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup174, nestingLookup605]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq174 nestingEntries_eq605]
  decide

theorem canClimb_175_269 : canClimb 175 269 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup175, nestingLookup269]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq175 nestingEntries_eq269]
  decide

theorem canClimb_175_313 : canClimb 175 313 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup175, nestingLookup313]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq175 nestingEntries_eq313]
  decide

theorem canClimb_175_376 : canClimb 175 376 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup175, nestingLookup376]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq175 nestingEntries_eq376]
  decide

theorem canClimb_176_276 : canClimb 176 276 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup176, nestingLookup276]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq176 nestingEntries_eq276]
  decide

theorem canClimb_176_314 : canClimb 176 314 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup176, nestingLookup314]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq176 nestingEntries_eq314]
  decide

theorem canClimb_176_374 : canClimb 176 374 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup176, nestingLookup374]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq176 nestingEntries_eq374]
  decide

theorem canClimb_177_288 : canClimb 177 288 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup177, nestingLookup288]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq177 nestingEntries_eq288]
  decide

theorem canClimb_177_315 : canClimb 177 315 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup177, nestingLookup315]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq177 nestingEntries_eq315]
  decide

theorem canClimb_177_371 : canClimb 177 371 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup177, nestingLookup371]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq177 nestingEntries_eq371]
  decide

theorem canClimb_178_291 : canClimb 178 291 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup178, nestingLookup291]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq178 nestingEntries_eq291]
  decide

theorem canClimb_178_316 : canClimb 178 316 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup178, nestingLookup316]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq178 nestingEntries_eq316]
  decide

theorem canClimb_178_520 : canClimb 178 520 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup178, nestingLookup520]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq178 nestingEntries_eq520]
  decide

theorem canClimb_178_580 : canClimb 178 580 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup178, nestingLookup580]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq178 nestingEntries_eq580]
  decide

theorem canClimb_179_301 : canClimb 179 301 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup179, nestingLookup301]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq179 nestingEntries_eq301]
  decide

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem canClimb_179_317 : canClimb 179 317 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup179, nestingLookup317]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq179 nestingEntries_eq317]
  decide

theorem canClimb_179_520 : canClimb 179 520 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup179, nestingLookup520]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq179 nestingEntries_eq520]
  decide

theorem canClimb_179_596 : canClimb 179 596 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup179, nestingLookup596]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq179 nestingEntries_eq596]
  decide

theorem canClimb_180_278 : canClimb 180 278 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup180, nestingLookup278]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq180 nestingEntries_eq278]
  decide

theorem canClimb_180_318 : canClimb 180 318 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup180, nestingLookup318]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq180 nestingEntries_eq318]
  decide

theorem canClimb_180_520 : canClimb 180 520 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup180, nestingLookup520]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq180 nestingEntries_eq520]
  decide

theorem canClimb_180_589 : canClimb 180 589 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup180, nestingLookup589]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq180 nestingEntries_eq589]
  decide

theorem canClimb_181_267 : canClimb 181 267 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup181, nestingLookup267]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq181 nestingEntries_eq267]
  decide

theorem canClimb_181_319 : canClimb 181 319 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup181, nestingLookup319]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq181 nestingEntries_eq319]
  decide

theorem canClimb_181_520 : canClimb 181 520 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup181, nestingLookup520]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq181 nestingEntries_eq520]
  decide

theorem canClimb_181_576 : canClimb 181 576 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup181, nestingLookup576]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq181 nestingEntries_eq576]
  decide

theorem canClimb_182_268 : canClimb 182 268 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup182, nestingLookup268]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq182 nestingEntries_eq268]
  decide

theorem canClimb_182_318 : canClimb 182 318 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup182, nestingLookup318]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq182 nestingEntries_eq318]
  decide

theorem canClimb_182_509 : canClimb 182 509 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup182, nestingLookup509]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq182 nestingEntries_eq509]
  decide

theorem canClimb_182_617 : canClimb 182 617 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup182, nestingLookup617]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq182 nestingEntries_eq617]
  decide

theorem canClimb_183_298 : canClimb 183 298 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup183, nestingLookup298]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq183 nestingEntries_eq298]
  decide

theorem canClimb_183_306 : canClimb 183 306 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup183, nestingLookup306]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq183 nestingEntries_eq306]
  decide

theorem canClimb_183_509 : canClimb 183 509 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup183, nestingLookup509]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq183 nestingEntries_eq509]
  decide

theorem canClimb_184_287 : canClimb 184 287 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup184, nestingLookup287]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq184 nestingEntries_eq287]
  decide

theorem canClimb_184_320 : canClimb 184 320 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup184, nestingLookup320]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq184 nestingEntries_eq320]
  decide

theorem canClimb_184_509 : canClimb 184 509 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup184, nestingLookup509]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq184 nestingEntries_eq509]
  decide

theorem canClimb_184_542 : canClimb 184 542 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup184, nestingLookup542]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq184 nestingEntries_eq542]
  decide

theorem canClimb_185_272 : canClimb 185 272 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup185, nestingLookup272]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq185 nestingEntries_eq272]
  decide

theorem canClimb_185_316 : canClimb 185 316 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup185, nestingLookup316]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq185 nestingEntries_eq316]
  decide

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem canClimb_185_509 : canClimb 185 509 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup185, nestingLookup509]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq185 nestingEntries_eq509]
  decide

theorem canClimb_185_612 : canClimb 185 612 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup185, nestingLookup612]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq185 nestingEntries_eq612]
  decide

theorem canClimb_186_295 : canClimb 186 295 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup186, nestingLookup295]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq186 nestingEntries_eq295]
  decide

theorem canClimb_186_323 : canClimb 186 323 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup186, nestingLookup323]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq186 nestingEntries_eq323]
  decide

theorem canClimb_186_509 : canClimb 186 509 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup186, nestingLookup509]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq186 nestingEntries_eq509]
  decide

theorem canClimb_186_563 : canClimb 186 563 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup186, nestingLookup563]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq186 nestingEntries_eq563]
  decide

theorem canClimb_187_283 : canClimb 187 283 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup187, nestingLookup283]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq187 nestingEntries_eq283]
  decide

theorem canClimb_187_310 : canClimb 187 310 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup187, nestingLookup310]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq187 nestingEntries_eq310]
  decide

theorem canClimb_187_509 : canClimb 187 509 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup187, nestingLookup509]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq187 nestingEntries_eq509]
  decide

theorem canClimb_188_284 : canClimb 188 284 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup188, nestingLookup284]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq188 nestingEntries_eq284]
  decide

theorem canClimb_188_311 : canClimb 188 311 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup188, nestingLookup311]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq188 nestingEntries_eq311]
  decide

theorem canClimb_188_509 : canClimb 188 509 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup188, nestingLookup509]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq188 nestingEntries_eq509]
  decide

theorem canClimb_188_558 : canClimb 188 558 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup188, nestingLookup558]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq188 nestingEntries_eq558]
  decide

theorem canClimb_189_296 : canClimb 189 296 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup189, nestingLookup296]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq189 nestingEntries_eq296]
  decide

theorem canClimb_189_322 : canClimb 189 322 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup189, nestingLookup322]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq189 nestingEntries_eq322]
  decide

theorem canClimb_189_509 : canClimb 189 509 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup189, nestingLookup509]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq189 nestingEntries_eq509]
  decide

theorem canClimb_189_602 : canClimb 189 602 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup189, nestingLookup602]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq189 nestingEntries_eq602]
  decide

theorem canClimb_190_271 : canClimb 190 271 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup190, nestingLookup271]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq190 nestingEntries_eq271]
  decide

theorem canClimb_190_317 : canClimb 190 317 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup190, nestingLookup317]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq190 nestingEntries_eq317]
  decide

theorem canClimb_190_509 : canClimb 190 509 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup190, nestingLookup509]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq190 nestingEntries_eq509]
  decide

theorem canClimb_191_300 : canClimb 191 300 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup191, nestingLookup300]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq191 nestingEntries_eq300]
  decide

theorem canClimb_191_307 : canClimb 191 307 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup191, nestingLookup307]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq191 nestingEntries_eq307]
  decide

theorem canClimb_191_509 : canClimb 191 509 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup191, nestingLookup509]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq191 nestingEntries_eq509]
  decide

theorem canClimb_192_279 : canClimb 192 279 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup192, nestingLookup279]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq192 nestingEntries_eq279]
  decide

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem canClimb_192_308 : canClimb 192 308 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup192, nestingLookup308]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq192 nestingEntries_eq308]
  decide

theorem canClimb_192_509 : canClimb 192 509 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup192, nestingLookup509]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq192 nestingEntries_eq509]
  decide

theorem canClimb_193_267 : canClimb 193 267 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup193, nestingLookup267]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq193 nestingEntries_eq267]
  decide

theorem canClimb_193_325 : canClimb 193 325 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup193, nestingLookup325]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq193 nestingEntries_eq325]
  decide

theorem canClimb_193_509 : canClimb 193 509 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup193, nestingLookup509]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq193 nestingEntries_eq509]
  decide

theorem canClimb_194_266 : canClimb 194 266 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup194, nestingLookup266]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq194 nestingEntries_eq266]
  decide

theorem canClimb_194_310 : canClimb 194 310 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup194, nestingLookup310]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq194 nestingEntries_eq310]
  decide

theorem canClimb_194_521 : canClimb 194 521 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup194, nestingLookup521]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq194 nestingEntries_eq521]
  decide

theorem canClimb_194_629 : canClimb 194 629 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup194, nestingLookup629]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq194 nestingEntries_eq629]
  decide

theorem canClimb_195_301 : canClimb 195 301 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup195, nestingLookup301]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq195 nestingEntries_eq301]
  decide

theorem canClimb_195_321 : canClimb 195 321 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup195, nestingLookup321]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq195 nestingEntries_eq321]
  decide

theorem canClimb_195_521 : canClimb 195 521 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup195, nestingLookup521]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq195 nestingEntries_eq521]
  decide

theorem canClimb_195_632 : canClimb 195 632 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup195, nestingLookup632]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq195 nestingEntries_eq632]
  decide

theorem canClimb_196_289 : canClimb 196 289 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup196, nestingLookup289]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq196 nestingEntries_eq289]
  decide

theorem canClimb_196_304 : canClimb 196 304 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup196, nestingLookup304]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq196 nestingEntries_eq304]
  decide

theorem canClimb_196_497 : canClimb 196 497 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup196, nestingLookup497]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq196 nestingEntries_eq497]
  decide

theorem canClimb_197_279 : canClimb 197 279 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup197, nestingLookup279]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq197 nestingEntries_eq279]
  decide

theorem canClimb_197_305 : canClimb 197 305 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup197, nestingLookup305]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq197 nestingEntries_eq305]
  decide

theorem canClimb_197_505 : canClimb 197 505 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup197, nestingLookup505]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq197 nestingEntries_eq505]
  decide

theorem canClimb_198_291 : canClimb 198 291 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup198, nestingLookup291]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq198 nestingEntries_eq291]
  decide

theorem canClimb_198_320 : canClimb 198 320 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup198, nestingLookup320]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq198 nestingEntries_eq320]
  decide

theorem canClimb_198_521 : canClimb 198 521 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup198, nestingLookup521]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq198 nestingEntries_eq521]
  decide

theorem canClimb_198_535 : canClimb 198 535 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup198, nestingLookup535]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq198 nestingEntries_eq535]
  decide

theorem canClimb_199_277 : canClimb 199 277 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup199, nestingLookup277]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq199 nestingEntries_eq277]
  decide

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem canClimb_199_311 : canClimb 199 311 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup199, nestingLookup311]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq199 nestingEntries_eq311]
  decide

theorem canClimb_199_521 : canClimb 199 521 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup199, nestingLookup521]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq199 nestingEntries_eq521]
  decide

theorem canClimb_199_538 : canClimb 199 538 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup199, nestingLookup538]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq199 nestingEntries_eq538]
  decide

theorem canClimb_200_272 : canClimb 200 272 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup200, nestingLookup272]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq200 nestingEntries_eq272]
  decide

theorem canClimb_200_312 : canClimb 200 312 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup200, nestingLookup312]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq200 nestingEntries_eq312]
  decide

theorem canClimb_200_501 : canClimb 200 501 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup200, nestingLookup501]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq200 nestingEntries_eq501]
  decide

theorem canClimb_201_297 : canClimb 201 297 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup201, nestingLookup297]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq201 nestingEntries_eq297]
  decide

theorem canClimb_201_318 : canClimb 201 318 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup201, nestingLookup318]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq201 nestingEntries_eq318]
  decide

theorem canClimb_201_521 : canClimb 201 521 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup201, nestingLookup521]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq201 nestingEntries_eq521]
  decide

theorem canClimb_201_610 : canClimb 201 610 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup201, nestingLookup610]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq201 nestingEntries_eq610]
  decide

theorem canClimb_202_285 : canClimb 202 285 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup202, nestingLookup285]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq202 nestingEntries_eq285]
  decide

theorem canClimb_202_325 : canClimb 202 325 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup202, nestingLookup325]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq202 nestingEntries_eq325]
  decide

theorem canClimb_202_521 : canClimb 202 521 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup202, nestingLookup521]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq202 nestingEntries_eq521]
  decide

theorem canClimb_202_559 : canClimb 202 559 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup202, nestingLookup559]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq202 nestingEntries_eq559]
  decide

theorem canClimb_203_282 : canClimb 203 282 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup203, nestingLookup282]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq203 nestingEntries_eq282]
  decide

theorem canClimb_203_324 : canClimb 203 324 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup203, nestingLookup324]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq203 nestingEntries_eq324]
  decide

theorem canClimb_203_491 : canClimb 203 491 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup203, nestingLookup491]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq203 nestingEntries_eq491]
  decide

theorem canClimb_204_294 : canClimb 204 294 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup204, nestingLookup294]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq204 nestingEntries_eq294]
  decide

theorem canClimb_204_315 : canClimb 204 315 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup204, nestingLookup315]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq204 nestingEntries_eq315]
  decide

theorem canClimb_204_521 : canClimb 204 521 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup204, nestingLookup521]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq204 nestingEntries_eq521]
  decide

theorem canClimb_204_608 : canClimb 204 608 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup204, nestingLookup608]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq204 nestingEntries_eq608]
  decide

theorem canClimb_205_271 : canClimb 205 271 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup205, nestingLookup271]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq205 nestingEntries_eq271]
  decide

theorem canClimb_205_309 : canClimb 205 309 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup205, nestingLookup309]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq205 nestingEntries_eq309]
  decide

theorem canClimb_205_521 : canClimb 205 521 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup205, nestingLookup521]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq205 nestingEntries_eq521]
  decide

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem canClimb_205_557 : canClimb 205 557 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup205, nestingLookup557]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq205 nestingEntries_eq557]
  decide

theorem canClimb_206_274 : canClimb 206 274 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup206, nestingLookup274]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq206 nestingEntries_eq274]
  decide

theorem canClimb_206_322 : canClimb 206 322 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup206, nestingLookup322]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq206 nestingEntries_eq322]
  decide

theorem canClimb_206_521 : canClimb 206 521 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup206, nestingLookup521]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq206 nestingEntries_eq521]
  decide

theorem canClimb_206_601 : canClimb 206 601 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup206, nestingLookup601]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq206 nestingEntries_eq601]
  decide

theorem canClimb_207_298 : canClimb 207 298 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup207, nestingLookup298]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq207 nestingEntries_eq298]
  decide

theorem canClimb_207_314 : canClimb 207 314 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup207, nestingLookup314]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq207 nestingEntries_eq314]
  decide

theorem canClimb_207_521 : canClimb 207 521 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup207, nestingLookup521]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq207 nestingEntries_eq521]
  decide

theorem canClimb_207_567 : canClimb 207 567 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup207, nestingLookup567]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq207 nestingEntries_eq567]
  decide

theorem canClimb_208_286 : canClimb 208 286 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup208, nestingLookup286]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq208 nestingEntries_eq286]
  decide

theorem canClimb_208_307 : canClimb 208 307 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup208, nestingLookup307]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq208 nestingEntries_eq307]
  decide

theorem canClimb_208_499 : canClimb 208 499 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup208, nestingLookup499]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq208 nestingEntries_eq499]
  decide

theorem canClimb_209_281 : canClimb 209 281 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup209, nestingLookup281]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq209 nestingEntries_eq281]
  decide

theorem canClimb_209_302 : canClimb 209 302 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup209, nestingLookup302]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq209 nestingEntries_eq302]
  decide

theorem canClimb_209_521 : canClimb 209 521 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup209, nestingLookup521]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq209 nestingEntries_eq521]
  decide

theorem canClimb_209_604 : canClimb 209 604 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup209, nestingLookup604]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq209 nestingEntries_eq604]
  decide

theorem canClimb_210_293 : canClimb 210 293 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup210, nestingLookup293]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq210 nestingEntries_eq293]
  decide

theorem canClimb_210_319 : canClimb 210 319 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup210, nestingLookup319]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq210 nestingEntries_eq319]
  decide

theorem canClimb_210_490 : canClimb 210 490 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup210, nestingLookup490]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq210 nestingEntries_eq490]
  decide

theorem canClimb_211_269 : canClimb 211 269 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup211, nestingLookup269]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq211 nestingEntries_eq269]
  decide

theorem canClimb_211_323 : canClimb 211 323 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup211, nestingLookup323]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq211 nestingEntries_eq323]
  decide

theorem canClimb_211_521 : canClimb 211 521 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup211, nestingLookup521]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq211 nestingEntries_eq521]
  decide

theorem canClimb_211_564 : canClimb 211 564 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup211, nestingLookup564]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq211 nestingEntries_eq564]
  decide

theorem canClimb_212_266 : canClimb 212 266 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup212, nestingLookup266]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq212 nestingEntries_eq266]
  decide

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem canClimb_212_303 : canClimb 212 303 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup212, nestingLookup303]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq212 nestingEntries_eq303]
  decide

theorem canClimb_212_522 : canClimb 212 522 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup212, nestingLookup522]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq212 nestingEntries_eq522]
  decide

theorem canClimb_212_631 : canClimb 212 631 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup212, nestingLookup631]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq212 nestingEntries_eq631]
  decide

theorem canClimb_213_288 : canClimb 213 288 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup213, nestingLookup288]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq213 nestingEntries_eq288]
  decide

theorem canClimb_213_323 : canClimb 213 323 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup213, nestingLookup323]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq213 nestingEntries_eq323]
  decide

theorem canClimb_213_481 : canClimb 213 481 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup213, nestingLookup481]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq213 nestingEntries_eq481]
  decide

theorem canClimb_214_300 : canClimb 214 300 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup214, nestingLookup300]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq214 nestingEntries_eq300]
  decide

theorem canClimb_214_312 : canClimb 214 312 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup214, nestingLookup312]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq214 nestingEntries_eq312]
  decide

theorem canClimb_214_522 : canClimb 214 522 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup214, nestingLookup522]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq214 nestingEntries_eq522]
  decide

theorem canClimb_214_532 : canClimb 214 532 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup214, nestingLookup532]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq214 nestingEntries_eq532]
  decide

theorem canClimb_215_290 : canClimb 215 290 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup215, nestingLookup290]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq215 nestingEntries_eq290]
  decide

theorem canClimb_215_309 : canClimb 215 309 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup215, nestingLookup309]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq215 nestingEntries_eq309]
  decide

theorem canClimb_215_522 : canClimb 215 522 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup215, nestingLookup522]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq215 nestingEntries_eq522]
  decide

theorem canClimb_215_633 : canClimb 215 633 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup215, nestingLookup633]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq215 nestingEntries_eq633]
  decide

theorem canClimb_216_278 : canClimb 216 278 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup216, nestingLookup278]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq216 nestingEntries_eq278]
  decide

theorem canClimb_216_322 : canClimb 216 322 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup216, nestingLookup322]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq216 nestingEntries_eq322]
  decide

theorem canClimb_216_483 : canClimb 216 483 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup216, nestingLookup483]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq216 nestingEntries_eq483]
  decide

theorem canClimb_217_277 : canClimb 217 277 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup217, nestingLookup277]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq217 nestingEntries_eq277]
  decide

theorem canClimb_217_306 : canClimb 217 306 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup217, nestingLookup306]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq217 nestingEntries_eq306]
  decide

theorem canClimb_217_522 : canClimb 217 522 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup217, nestingLookup522]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq217 nestingEntries_eq522]
  decide

theorem canClimb_217_526 : canClimb 217 526 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup217, nestingLookup526]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq217 nestingEntries_eq526]
  decide

theorem canClimb_218_268 : canClimb 218 268 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup218, nestingLookup268]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq218 nestingEntries_eq268]
  decide

theorem canClimb_218_305 : canClimb 218 305 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup218, nestingLookup305]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq218 nestingEntries_eq305]
  decide

theorem canClimb_218_485 : canClimb 218 485 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup218, nestingLookup485]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq218 nestingEntries_eq485]
  decide

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem canClimb_219_281 : canClimb 219 281 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup219, nestingLookup281]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq219 nestingEntries_eq281]
  decide

theorem canClimb_219_316 : canClimb 219 316 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup219, nestingLookup316]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq219 nestingEntries_eq316]
  decide

theorem canClimb_219_522 : canClimb 219 522 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup219, nestingLookup522]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq219 nestingEntries_eq522]
  decide

theorem canClimb_219_626 : canClimb 219 626 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup219, nestingLookup626]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq219 nestingEntries_eq626]
  decide

theorem canClimb_220_299 : canClimb 220 299 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup220, nestingLookup299]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq220 nestingEntries_eq299]
  decide

theorem canClimb_220_325 : canClimb 220 325 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup220, nestingLookup325]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq220 nestingEntries_eq325]
  decide

theorem canClimb_220_522 : canClimb 220 522 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup220, nestingLookup522]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq220 nestingEntries_eq522]
  decide

theorem canClimb_220_624 : canClimb 220 624 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup220, nestingLookup624]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq220 nestingEntries_eq624]
  decide

theorem canClimb_221_292 : canClimb 221 292 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup221, nestingLookup292]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq221 nestingEntries_eq292]
  decide

theorem canClimb_221_324 : canClimb 221 324 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup221, nestingLookup324]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq221 nestingEntries_eq324]
  decide

theorem canClimb_221_470 : canClimb 221 470 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup221, nestingLookup470]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq221 nestingEntries_eq470]
  decide

theorem canClimb_222_286 : canClimb 222 286 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup222, nestingLookup286]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq222 nestingEntries_eq286]
  decide

theorem canClimb_222_317 : canClimb 222 317 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup222, nestingLookup317]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq222 nestingEntries_eq317]
  decide

theorem canClimb_222_522 : canClimb 222 522 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup222, nestingLookup522]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq222 nestingEntries_eq522]
  decide

theorem canClimb_222_549 : canClimb 222 549 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup222, nestingLookup549]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq222 nestingEntries_eq549]
  decide

theorem canClimb_223_275 : canClimb 223 275 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup223, nestingLookup275]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq223 nestingEntries_eq275]
  decide

theorem canClimb_223_304 : canClimb 223 304 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup223, nestingLookup304]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq223 nestingEntries_eq304]
  decide

theorem canClimb_223_522 : canClimb 223 522 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup223, nestingLookup522]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq223 nestingEntries_eq522]
  decide

theorem canClimb_223_554 : canClimb 223 554 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup223, nestingLookup554]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq223 nestingEntries_eq554]
  decide

theorem canClimb_224_270 : canClimb 224 270 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup224, nestingLookup270]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq224 nestingEntries_eq270]
  decide

theorem canClimb_224_321 : canClimb 224 321 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup224, nestingLookup321]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq224 nestingEntries_eq321]
  decide

theorem canClimb_224_522 : canClimb 224 522 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup224, nestingLookup522]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq224 nestingEntries_eq522]
  decide

theorem canClimb_224_625 : canClimb 224 625 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup224, nestingLookup625]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq224 nestingEntries_eq625]
  decide

theorem canClimb_225_283 : canClimb 225 283 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup225, nestingLookup283]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq225 nestingEntries_eq283]
  decide

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem canClimb_225_314 : canClimb 225 314 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup225, nestingLookup314]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq225 nestingEntries_eq314]
  decide

theorem canClimb_225_475 : canClimb 225 475 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup225, nestingLookup475]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq225 nestingEntries_eq475]
  decide

theorem canClimb_226_297 : canClimb 226 297 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup226, nestingLookup297]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq226 nestingEntries_eq297]
  decide

theorem canClimb_226_313 : canClimb 226 313 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup226, nestingLookup313]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq226 nestingEntries_eq313]
  decide

theorem canClimb_226_522 : canClimb 226 522 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup226, nestingLookup522]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq226 nestingEntries_eq522]
  decide

theorem canClimb_226_553 : canClimb 226 553 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup226, nestingLookup553]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq226 nestingEntries_eq553]
  decide

theorem canClimb_227_294 : canClimb 227 294 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup227, nestingLookup294]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq227 nestingEntries_eq294]
  decide

theorem canClimb_227_308 : canClimb 227 308 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup227, nestingLookup308]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq227 nestingEntries_eq308]
  decide

theorem canClimb_227_478 : canClimb 227 478 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup227, nestingLookup478]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq227 nestingEntries_eq478]
  decide

theorem canClimb_228_284 : canClimb 228 284 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup228, nestingLookup284]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq228 nestingEntries_eq284]
  decide

theorem canClimb_228_319 : canClimb 228 319 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup228, nestingLookup319]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq228 nestingEntries_eq319]
  decide

theorem canClimb_228_522 : canClimb 228 522 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup228, nestingLookup522]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq228 nestingEntries_eq522]
  decide

theorem canClimb_228_623 : canClimb 228 623 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup228, nestingLookup623]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq228 nestingEntries_eq623]
  decide

theorem canClimb_229_273 : canClimb 229 273 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup229, nestingLookup273]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq229 nestingEntries_eq273]
  decide

theorem canClimb_229_320 : canClimb 229 320 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup229, nestingLookup320]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq229 nestingEntries_eq320]
  decide

theorem canClimb_229_522 : canClimb 229 522 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup229, nestingLookup522]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq229 nestingEntries_eq522]
  decide

theorem canClimb_229_550 : canClimb 229 550 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup229, nestingLookup550]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq229 nestingEntries_eq550]
  decide

theorem canClimb_230_266 : canClimb 230 266 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup230, nestingLookup266]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq230 nestingEntries_eq266]
  decide

theorem canClimb_230_306 : canClimb 230 306 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup230, nestingLookup306]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq230 nestingEntries_eq306]
  decide

theorem canClimb_230_523 : canClimb 230 523 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup230, nestingLookup523]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq230 nestingEntries_eq523]
  decide

theorem canClimb_230_628 : canClimb 230 628 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup230, nestingLookup628]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq230 nestingEntries_eq628]
  decide

theorem canClimb_231_288 : canClimb 231 288 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup231, nestingLookup288]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq231 nestingEntries_eq288]
  decide

theorem canClimb_231_322 : canClimb 231 322 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup231, nestingLookup322]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq231 nestingEntries_eq322]
  decide

theorem canClimb_231_523 : canClimb 231 523 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup231, nestingLookup523]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq231 nestingEntries_eq523]
  decide

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem canClimb_231_634 : canClimb 231 634 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup231, nestingLookup634]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq231 nestingEntries_eq634]
  decide

theorem canClimb_232_300 : canClimb 232 300 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup232, nestingLookup300]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq232 nestingEntries_eq300]
  decide

theorem canClimb_232_309 : canClimb 232 309 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup232, nestingLookup309]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq232 nestingEntries_eq309]
  decide

theorem canClimb_232_456 : canClimb 232 456 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup232, nestingLookup456]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq232 nestingEntries_eq456]
  decide

theorem canClimb_233_290 : canClimb 233 290 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup233, nestingLookup290]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq233 nestingEntries_eq290]
  decide

theorem canClimb_233_312 : canClimb 233 312 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup233, nestingLookup312]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq233 nestingEntries_eq312]
  decide

theorem canClimb_233_523 : canClimb 233 523 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup233, nestingLookup523]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq233 nestingEntries_eq523]
  decide

theorem canClimb_233_527 : canClimb 233 527 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup233, nestingLookup527]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq233 nestingEntries_eq527]
  decide

theorem canClimb_234_278 : canClimb 234 278 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup234, nestingLookup278]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq234 nestingEntries_eq278]
  decide

theorem canClimb_234_323 : canClimb 234 323 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup234, nestingLookup323]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq234 nestingEntries_eq323]
  decide

theorem canClimb_234_458 : canClimb 234 458 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup234, nestingLookup458]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq234 nestingEntries_eq458]
  decide

theorem canClimb_235_277 : canClimb 235 277 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup235, nestingLookup277]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq235 nestingEntries_eq277]
  decide

theorem canClimb_235_303 : canClimb 235 303 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup235, nestingLookup303]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq235 nestingEntries_eq303]
  decide

theorem canClimb_235_523 : canClimb 235 523 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup235, nestingLookup523]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq235 nestingEntries_eq523]
  decide

theorem canClimb_235_529 : canClimb 235 529 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup235, nestingLookup529]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq235 nestingEntries_eq529]
  decide

theorem canClimb_236_270 : canClimb 236 270 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup236, nestingLookup270]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq236 nestingEntries_eq270]
  decide

theorem canClimb_236_320 : canClimb 236 320 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup236, nestingLookup320]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq236 nestingEntries_eq320]
  decide

theorem canClimb_236_523 : canClimb 236 523 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup236, nestingLookup523]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq236 nestingEntries_eq523]
  decide

theorem canClimb_236_620 : canClimb 236 620 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup236, nestingLookup620]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq236 nestingEntries_eq620]
  decide

theorem canClimb_237_284 : canClimb 237 284 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup237, nestingLookup284]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq237 nestingEntries_eq284]
  decide

theorem canClimb_237_314 : canClimb 237 314 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup237, nestingLookup314]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq237 nestingEntries_eq314]
  decide

theorem canClimb_237_465 : canClimb 237 465 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup237, nestingLookup465]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq237 nestingEntries_eq465]
  decide

theorem canClimb_238_294 : canClimb 238 294 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup238, nestingLookup294]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq238 nestingEntries_eq294]
  decide

theorem canClimb_238_313 : canClimb 238 313 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup238, nestingLookup313]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq238 nestingEntries_eq313]
  decide

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem canClimb_238_469 : canClimb 238 469 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup238, nestingLookup469]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq238 nestingEntries_eq469]
  decide

theorem canClimb_239_297 : canClimb 239 297 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup239, nestingLookup297]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq239 nestingEntries_eq297]
  decide

theorem canClimb_239_308 : canClimb 239 308 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup239, nestingLookup308]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq239 nestingEntries_eq308]
  decide

theorem canClimb_239_523 : canClimb 239 523 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup239, nestingLookup523]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq239 nestingEntries_eq523]
  decide

theorem canClimb_239_539 : canClimb 239 539 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup239, nestingLookup539]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq239 nestingEntries_eq539]
  decide

theorem canClimb_240_283 : canClimb 240 283 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup240, nestingLookup283]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq240 nestingEntries_eq283]
  decide

theorem canClimb_240_319 : canClimb 240 319 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup240, nestingLookup319]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq240 nestingEntries_eq319]
  decide

theorem canClimb_240_523 : canClimb 240 523 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup240, nestingLookup523]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq240 nestingEntries_eq523]
  decide

theorem canClimb_240_615 : canClimb 240 615 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup240, nestingLookup615]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq240 nestingEntries_eq615]
  decide

theorem canClimb_241_273 : canClimb 241 273 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup241, nestingLookup273]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq241 nestingEntries_eq273]
  decide

theorem canClimb_241_321 : canClimb 241 321 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup241, nestingLookup321]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq241 nestingEntries_eq321]
  decide

theorem canClimb_241_523 : canClimb 241 523 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup241, nestingLookup523]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq241 nestingEntries_eq523]
  decide

theorem canClimb_241_545 : canClimb 241 545 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup241, nestingLookup545]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq241 nestingEntries_eq545]
  decide

theorem canClimb_242_268 : canClimb 242 268 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup242, nestingLookup268]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq242 nestingEntries_eq268]
  decide

theorem canClimb_242_304 : canClimb 242 304 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup242, nestingLookup304]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq242 nestingEntries_eq304]
  decide

theorem canClimb_242_523 : canClimb 242 523 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup242, nestingLookup523]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq242 nestingEntries_eq523]
  decide

theorem canClimb_242_613 : canClimb 242 613 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup242, nestingLookup613]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq242 nestingEntries_eq613]
  decide

theorem canClimb_243_286 : canClimb 243 286 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup243, nestingLookup286]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq243 nestingEntries_eq286]
  decide

theorem canClimb_243_316 : canClimb 243 316 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup243, nestingLookup316]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq243 nestingEntries_eq316]
  decide

theorem canClimb_243_523 : canClimb 243 523 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup243, nestingLookup523]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq243 nestingEntries_eq523]
  decide

theorem canClimb_243_618 : canClimb 243 618 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup243, nestingLookup618]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq243 nestingEntries_eq618]
  decide

theorem canClimb_244_292 : canClimb 244 292 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup244, nestingLookup292]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq244 nestingEntries_eq292]
  decide

theorem canClimb_244_325 : canClimb 244 325 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup244, nestingLookup325]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq244 nestingEntries_eq325]
  decide

theorem canClimb_244_461 : canClimb 244 461 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup244, nestingLookup461]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq244 nestingEntries_eq461]
  decide

end CSL.Construction.PhysicalFramePaths


