-- Prove2me | Definitions.Def_CSL_Generated_FiniteCircuit_FramePathChecks_Nesting_Batch01
-- name    : CSL_Generated_FiniteCircuit_FramePathChecks_Nesting_Batch01
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T14:30:35.820385+00:00
-- url     : https://prove2.me/theorems/ff409008-e114-4043-81e7-8bc2b5b1b774
-- title:
--   Coded sorting library: Generated / FiniteCircuit / FramePathChecks / Nesting / Batch01
-- statement:
--   Module `CodedSorting.Generated.FiniteCircuit.FramePathChecks.Nesting.Batch01` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   Generated physical-frame checks. Uncompiled until a build record exists.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Generated.FiniteCircuit.FramePathChecks.Nesting.Batch01

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
theorem canClimb_32_141 : canClimb 32 141 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup032, nestingLookup141]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq032 nestingEntries_eq141]
  decide

theorem canClimb_32_142 : canClimb 32 142 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup032, nestingLookup142]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq032 nestingEntries_eq142]
  decide

theorem canClimb_33_254 : canClimb 33 254 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup033, nestingLookup254]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq033 nestingEntries_eq254]
  decide

theorem canClimb_33_255 : canClimb 33 255 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup033, nestingLookup255]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq033 nestingEntries_eq255]
  decide

theorem canClimb_33_256 : canClimb 33 256 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup033, nestingLookup256]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq033 nestingEntries_eq256]
  decide

theorem canClimb_34_200 : canClimb 34 200 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup034, nestingLookup200]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq034 nestingEntries_eq200]
  decide

theorem canClimb_34_201 : canClimb 34 201 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup034, nestingLookup201]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq034 nestingEntries_eq201]
  decide

theorem canClimb_34_202 : canClimb 34 202 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup034, nestingLookup202]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq034 nestingEntries_eq202]
  decide

theorem canClimb_35_185 : canClimb 35 185 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup035, nestingLookup185]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq035 nestingEntries_eq185]
  decide

theorem canClimb_35_186 : canClimb 35 186 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup035, nestingLookup186]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq035 nestingEntries_eq186]
  decide

theorem canClimb_35_187 : canClimb 35 187 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup035, nestingLookup187]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq035 nestingEntries_eq187]
  decide

theorem canClimb_36_200 : canClimb 36 200 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup036, nestingLookup200]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq036 nestingEntries_eq200]
  decide

theorem canClimb_36_203 : canClimb 36 203 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup036, nestingLookup203]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq036 nestingEntries_eq203]
  decide

theorem canClimb_36_204 : canClimb 36 204 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup036, nestingLookup204]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq036 nestingEntries_eq204]
  decide

theorem canClimb_37_158 : canClimb 37 158 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup037, nestingLookup158]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq037 nestingEntries_eq158]
  decide

theorem canClimb_37_159 : canClimb 37 159 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup037, nestingLookup159]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq037 nestingEntries_eq159]
  decide

theorem canClimb_37_284 : canClimb 37 284 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup037, nestingLookup284]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq037 nestingEntries_eq284]
  decide

theorem canClimb_37_310 : canClimb 37 310 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup037, nestingLookup310]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq037 nestingEntries_eq310]
  decide

theorem canClimb_37_508 : canClimb 37 508 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup037, nestingLookup508]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq037 nestingEntries_eq508]
  decide

theorem canClimb_38_170 : canClimb 38 170 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup038, nestingLookup170]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq038 nestingEntries_eq170]
  decide

theorem canClimb_38_171 : canClimb 38 171 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup038, nestingLookup171]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq038 nestingEntries_eq171]
  decide

theorem canClimb_38_172 : canClimb 38 172 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup038, nestingLookup172]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq038 nestingEntries_eq172]
  decide

theorem canClimb_39_254 : canClimb 39 254 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup039, nestingLookup254]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq039 nestingEntries_eq254]
  decide

theorem canClimb_39_257 : canClimb 39 257 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup039, nestingLookup257]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq039 nestingEntries_eq257]
  decide

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem canClimb_39_258 : canClimb 39 258 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup039, nestingLookup258]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq039 nestingEntries_eq258]
  decide

theorem canClimb_40_185 : canClimb 40 185 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup040, nestingLookup185]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq040 nestingEntries_eq185]
  decide

theorem canClimb_40_188 : canClimb 40 188 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup040, nestingLookup188]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq040 nestingEntries_eq188]
  decide

theorem canClimb_40_189 : canClimb 40 189 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup040, nestingLookup189]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq040 nestingEntries_eq189]
  decide

theorem canClimb_40_509 : canClimb 40 509 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup040, nestingLookup509]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq040 nestingEntries_eq509]
  decide

theorem canClimb_41_206 : canClimb 41 206 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup041, nestingLookup206]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq041 nestingEntries_eq206]
  decide

theorem canClimb_41_207 : canClimb 41 207 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup041, nestingLookup207]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq041 nestingEntries_eq207]
  decide

theorem canClimb_41_208 : canClimb 41 208 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup041, nestingLookup208]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq041 nestingEntries_eq208]
  decide

theorem canClimb_42_260 : canClimb 42 260 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup042, nestingLookup260]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq042 nestingEntries_eq260]
  decide

theorem canClimb_42_261 : canClimb 42 261 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup042, nestingLookup261]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq042 nestingEntries_eq261]
  decide

theorem canClimb_42_262 : canClimb 42 262 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup042, nestingLookup262]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq042 nestingEntries_eq262]
  decide

theorem canClimb_43_140 : canClimb 43 140 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup043, nestingLookup140]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq043 nestingEntries_eq140]
  decide

theorem canClimb_43_143 : canClimb 43 143 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup043, nestingLookup143]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq043 nestingEntries_eq143]
  decide

theorem canClimb_43_144 : canClimb 43 144 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup043, nestingLookup144]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq043 nestingEntries_eq144]
  decide

theorem canClimb_44_206 : canClimb 44 206 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup044, nestingLookup206]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq044 nestingEntries_eq206]
  decide

theorem canClimb_44_209 : canClimb 44 209 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup044, nestingLookup209]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq044 nestingEntries_eq209]
  decide

theorem canClimb_44_210 : canClimb 44 210 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup044, nestingLookup210]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq044 nestingEntries_eq210]
  decide

theorem canClimb_45_158 : canClimb 45 158 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup045, nestingLookup158]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq045 nestingEntries_eq158]
  decide

theorem canClimb_45_160 : canClimb 45 160 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup045, nestingLookup160]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq045 nestingEntries_eq160]
  decide

theorem canClimb_45_295 : canClimb 45 295 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup045, nestingLookup295]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq045 nestingEntries_eq295]
  decide

theorem canClimb_45_322 : canClimb 45 322 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup045, nestingLookup322]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq045 nestingEntries_eq322]
  decide

theorem canClimb_45_388 : canClimb 45 388 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup045, nestingLookup388]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq045 nestingEntries_eq388]
  decide

theorem canClimb_46_170 : canClimb 46 170 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup046, nestingLookup170]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq046 nestingEntries_eq170]
  decide

theorem canClimb_46_173 : canClimb 46 173 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup046, nestingLookup173]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq046 nestingEntries_eq173]
  decide

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem canClimb_46_174 : canClimb 46 174 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup046, nestingLookup174]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq046 nestingEntries_eq174]
  decide

theorem canClimb_47_260 : canClimb 47 260 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup047, nestingLookup260]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq047 nestingEntries_eq260]
  decide

theorem canClimb_47_263 : canClimb 47 263 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup047, nestingLookup263]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq047 nestingEntries_eq263]
  decide

theorem canClimb_47_264 : canClimb 47 264 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup047, nestingLookup264]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq047 nestingEntries_eq264]
  decide

theorem canClimb_48_116 : canClimb 48 116 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup048, nestingLookup116]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq048 nestingEntries_eq116]
  decide

theorem canClimb_48_117 : canClimb 48 117 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup048, nestingLookup117]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq048 nestingEntries_eq117]
  decide

theorem canClimb_48_288 : canClimb 48 288 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup048, nestingLookup288]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq048 nestingEntries_eq288]
  decide

theorem canClimb_48_289 : canClimb 48 289 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup048, nestingLookup289]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq048 nestingEntries_eq289]
  decide

theorem canClimb_48_506 : canClimb 48 506 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup048, nestingLookup506]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq048 nestingEntries_eq506]
  decide

theorem canClimb_48_579 : canClimb 48 579 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup048, nestingLookup579]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq048 nestingEntries_eq579]
  decide

theorem canClimb_49_119 : canClimb 49 119 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup049, nestingLookup119]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq049 nestingEntries_eq119]
  decide

theorem canClimb_49_120 : canClimb 49 120 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup049, nestingLookup120]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq049 nestingEntries_eq120]
  decide

theorem canClimb_49_121 : canClimb 49 121 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup049, nestingLookup121]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq049 nestingEntries_eq121]
  decide

theorem canClimb_49_506 : canClimb 49 506 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup049, nestingLookup506]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq049 nestingEntries_eq506]
  decide

theorem canClimb_50_119 : canClimb 50 119 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup050, nestingLookup119]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq050 nestingEntries_eq119]
  decide

theorem canClimb_50_122 : canClimb 50 122 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup050, nestingLookup122]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq050 nestingEntries_eq122]
  decide

theorem canClimb_50_123 : canClimb 50 123 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup050, nestingLookup123]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq050 nestingEntries_eq123]
  decide

theorem canClimb_51_146 : canClimb 51 146 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup051, nestingLookup146]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq051 nestingEntries_eq146]
  decide

theorem canClimb_51_147 : canClimb 51 147 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup051, nestingLookup147]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq051 nestingEntries_eq147]
  decide

theorem canClimb_51_148 : canClimb 51 148 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup051, nestingLookup148]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq051 nestingEntries_eq148]
  decide

theorem canClimb_52_191 : canClimb 52 191 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup052, nestingLookup191]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq052 nestingEntries_eq191]
  decide

theorem canClimb_52_192 : canClimb 52 192 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup052, nestingLookup192]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq052 nestingEntries_eq192]
  decide

theorem canClimb_52_276 : canClimb 52 276 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup052, nestingLookup276]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq052 nestingEntries_eq276]
  decide

theorem canClimb_52_324 : canClimb 52 324 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup052, nestingLookup324]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq052 nestingEntries_eq324]
  decide

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem canClimb_52_509 : canClimb 52 509 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup052, nestingLookup509]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq052 nestingEntries_eq509]
  decide

theorem canClimb_52_517 : canClimb 52 517 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup052, nestingLookup517]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq052 nestingEntries_eq517]
  decide

theorem canClimb_52_592 : canClimb 52 592 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup052, nestingLookup592]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq052 nestingEntries_eq592]
  decide

theorem canClimb_53_176 : canClimb 53 176 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup053, nestingLookup176]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq053 nestingEntries_eq176]
  decide

theorem canClimb_53_177 : canClimb 53 177 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup053, nestingLookup177]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq053 nestingEntries_eq177]
  decide

theorem canClimb_53_178 : canClimb 53 178 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup053, nestingLookup178]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq053 nestingEntries_eq178]
  decide

theorem canClimb_54_120 : canClimb 54 120 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup054, nestingLookup120]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq054 nestingEntries_eq120]
  decide

theorem canClimb_54_122 : canClimb 54 122 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup054, nestingLookup122]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq054 nestingEntries_eq122]
  decide

theorem canClimb_54_124 : canClimb 54 124 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup054, nestingLookup124]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq054 nestingEntries_eq124]
  decide

theorem canClimb_54_506 : canClimb 54 506 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup054, nestingLookup506]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq054 nestingEntries_eq506]
  decide

theorem canClimb_55_146 : canClimb 55 146 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup055, nestingLookup146]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq055 nestingEntries_eq146]
  decide

theorem canClimb_55_149 : canClimb 55 149 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup055, nestingLookup149]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq055 nestingEntries_eq149]
  decide

theorem canClimb_55_150 : canClimb 55 150 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup055, nestingLookup150]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq055 nestingEntries_eq150]
  decide

theorem canClimb_56_116 : canClimb 56 116 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup056, nestingLookup116]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq056 nestingEntries_eq116]
  decide

theorem canClimb_56_118 : canClimb 56 118 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup056, nestingLookup118]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq056 nestingEntries_eq118]
  decide

theorem canClimb_56_282 : canClimb 56 282 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup056, nestingLookup282]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq056 nestingEntries_eq282]
  decide

theorem canClimb_56_283 : canClimb 56 283 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup056, nestingLookup283]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq056 nestingEntries_eq283]
  decide

theorem canClimb_56_506 : canClimb 56 506 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup056, nestingLookup506]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq056 nestingEntries_eq506]
  decide

theorem canClimb_56_581 : canClimb 56 581 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup056, nestingLookup581]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq056 nestingEntries_eq581]
  decide

theorem canClimb_57_176 : canClimb 57 176 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup057, nestingLookup176]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq057 nestingEntries_eq176]
  decide

theorem canClimb_57_179 : canClimb 57 179 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup057, nestingLookup179]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq057 nestingEntries_eq179]
  decide

theorem canClimb_57_180 : canClimb 57 180 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup057, nestingLookup180]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq057 nestingEntries_eq180]
  decide

theorem canClimb_58_117 : canClimb 58 117 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup058, nestingLookup117]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq058 nestingEntries_eq117]
  decide

theorem canClimb_58_118 : canClimb 58 118 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup058, nestingLookup118]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq058 nestingEntries_eq118]
  decide

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem canClimb_58_280 : canClimb 58 280 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup058, nestingLookup280]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq058 nestingEntries_eq280]
  decide

theorem canClimb_58_281 : canClimb 58 281 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup058, nestingLookup281]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq058 nestingEntries_eq281]
  decide

theorem canClimb_58_335 : canClimb 58 335 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup058, nestingLookup335]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq058 nestingEntries_eq335]
  decide

theorem canClimb_59_161 : canClimb 59 161 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup059, nestingLookup161]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq059 nestingEntries_eq161]
  decide

theorem canClimb_59_162 : canClimb 59 162 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup059, nestingLookup162]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq059 nestingEntries_eq162]
  decide

theorem canClimb_59_276 : canClimb 59 276 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup059, nestingLookup276]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq059 nestingEntries_eq276]
  decide

theorem canClimb_59_325 : canClimb 59 325 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup059, nestingLookup325]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq059 nestingEntries_eq325]
  decide

theorem canClimb_59_394 : canClimb 59 394 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup059, nestingLookup394]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq059 nestingEntries_eq394]
  decide

theorem canClimb_60_121 : canClimb 60 121 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup060, nestingLookup121]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq060 nestingEntries_eq121]
  decide

theorem canClimb_60_123 : canClimb 60 123 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup060, nestingLookup123]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq060 nestingEntries_eq123]
  decide

theorem canClimb_60_124 : canClimb 60 124 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup060, nestingLookup124]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq060 nestingEntries_eq124]
  decide

theorem canClimb_61_147 : canClimb 61 147 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup061, nestingLookup147]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq061 nestingEntries_eq147]
  decide

theorem canClimb_61_149 : canClimb 61 149 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup061, nestingLookup149]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq061 nestingEntries_eq149]
  decide

theorem canClimb_61_151 : canClimb 61 151 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup061, nestingLookup151]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq061 nestingEntries_eq151]
  decide

theorem canClimb_62_191 : canClimb 62 191 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup062, nestingLookup191]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq062 nestingEntries_eq191]
  decide

theorem canClimb_62_193 : canClimb 62 193 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup062, nestingLookup193]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq062 nestingEntries_eq193]
  decide

theorem canClimb_62_289 : canClimb 62 289 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup062, nestingLookup289]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq062 nestingEntries_eq289]
  decide

theorem canClimb_62_313 : canClimb 62 313 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup062, nestingLookup313]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq062 nestingEntries_eq313]
  decide

theorem canClimb_62_509 : canClimb 62 509 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup062, nestingLookup509]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq062 nestingEntries_eq509]
  decide

theorem canClimb_62_575 : canClimb 62 575 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup062, nestingLookup575]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq062 nestingEntries_eq575]
  decide

theorem canClimb_63_131 : canClimb 63 131 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup063, nestingLookup131]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq063 nestingEntries_eq131]
  decide

theorem canClimb_63_132 : canClimb 63 132 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup063, nestingLookup132]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq063 nestingEntries_eq132]
  decide

theorem canClimb_63_293 : canClimb 63 293 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup063, nestingLookup293]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq063 nestingEntries_eq293]
  decide

theorem canClimb_63_299 : canClimb 63 299 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup063, nestingLookup299]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq063 nestingEntries_eq299]
  decide

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem canClimb_63_507 : canClimb 63 507 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup063, nestingLookup507]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq063 nestingEntries_eq507]
  decide

theorem canClimb_63_588 : canClimb 63 588 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup063, nestingLookup588]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq063 nestingEntries_eq588]
  decide

theorem canClimb_64_128 : canClimb 64 128 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup064, nestingLookup128]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq064 nestingEntries_eq128]
  decide

theorem canClimb_64_129 : canClimb 64 129 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup064, nestingLookup129]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq064 nestingEntries_eq129]
  decide

theorem canClimb_64_279 : canClimb 64 279 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup064, nestingLookup279]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq064 nestingEntries_eq279]
  decide

theorem canClimb_64_288 : canClimb 64 288 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup064, nestingLookup288]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq064 nestingEntries_eq288]
  decide

theorem canClimb_64_507 : canClimb 64 507 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup064, nestingLookup507]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq064 nestingEntries_eq507]
  decide

theorem canClimb_65_131 : canClimb 65 131 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup065, nestingLookup131]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq065 nestingEntries_eq131]
  decide

theorem canClimb_65_133 : canClimb 65 133 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup065, nestingLookup133]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq065 nestingEntries_eq133]
  decide

theorem canClimb_65_294 : canClimb 65 294 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup065, nestingLookup294]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq065 nestingEntries_eq294]
  decide

theorem canClimb_65_296 : canClimb 65 296 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup065, nestingLookup296]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq065 nestingEntries_eq296]
  decide

theorem canClimb_65_507 : canClimb 65 507 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup065, nestingLookup507]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq065 nestingEntries_eq507]
  decide

theorem canClimb_66_177 : canClimb 66 177 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup066, nestingLookup177]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq066 nestingEntries_eq177]
  decide

theorem canClimb_66_179 : canClimb 66 179 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup066, nestingLookup179]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq066 nestingEntries_eq179]
  decide

theorem canClimb_66_181 : canClimb 66 181 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup066, nestingLookup181]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq066 nestingEntries_eq181]
  decide

theorem canClimb_67_161 : canClimb 67 161 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup067, nestingLookup161]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq067 nestingEntries_eq161]
  decide

theorem canClimb_67_163 : canClimb 67 163 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup067, nestingLookup163]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq067 nestingEntries_eq163]
  decide

theorem canClimb_67_300 : canClimb 67 300 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup067, nestingLookup300]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq067 nestingEntries_eq300]
  decide

theorem canClimb_67_302 : canClimb 67 302 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup067, nestingLookup302]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq067 nestingEntries_eq302]
  decide

theorem canClimb_67_508 : canClimb 67 508 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup067, nestingLookup508]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq067 nestingEntries_eq508]
  decide

theorem canClimb_67_582 : canClimb 67 582 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup067, nestingLookup582]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq067 nestingEntries_eq582]
  decide

theorem canClimb_68_162 : canClimb 68 162 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup068, nestingLookup162]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq068 nestingEntries_eq162]
  decide

theorem canClimb_68_163 : canClimb 68 163 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup068, nestingLookup163]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq068 nestingEntries_eq163]
  decide

theorem canClimb_68_279 : canClimb 68 279 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup068, nestingLookup279]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq068 nestingEntries_eq279]
  decide

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem canClimb_68_313 : canClimb 68 313 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup068, nestingLookup313]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq068 nestingEntries_eq313]
  decide

theorem canClimb_68_508 : canClimb 68 508 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup068, nestingLookup508]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq068 nestingEntries_eq508]
  decide

theorem canClimb_68_590 : canClimb 68 590 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup068, nestingLookup590]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq068 nestingEntries_eq590]
  decide

theorem canClimb_69_192 : canClimb 69 192 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup069, nestingLookup192]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq069 nestingEntries_eq192]
  decide

theorem canClimb_69_193 : canClimb 69 193 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup069, nestingLookup193]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq069 nestingEntries_eq193]
  decide

theorem canClimb_69_290 : canClimb 69 290 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup069, nestingLookup290]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq069 nestingEntries_eq290]
  decide

theorem canClimb_69_302 : canClimb 69 302 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup069, nestingLookup302]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq069 nestingEntries_eq302]
  decide

theorem canClimb_69_431 : canClimb 69 431 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup069, nestingLookup431]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq069 nestingEntries_eq431]
  decide

theorem canClimb_70_132 : canClimb 70 132 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup070, nestingLookup132]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq070 nestingEntries_eq132]
  decide

theorem canClimb_70_133 : canClimb 70 133 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup070, nestingLookup133]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq070 nestingEntries_eq133]
  decide

theorem canClimb_70_290 : canClimb 70 290 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup070, nestingLookup290]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq070 nestingEntries_eq290]
  decide

theorem canClimb_70_301 : canClimb 70 301 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup070, nestingLookup301]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq070 nestingEntries_eq301]
  decide

theorem canClimb_70_359 : canClimb 70 359 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup070, nestingLookup359]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq070 nestingEntries_eq359]
  decide

theorem canClimb_71_128 : canClimb 71 128 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup071, nestingLookup128]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq071 nestingEntries_eq128]
  decide

theorem canClimb_71_130 : canClimb 71 130 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup071, nestingLookup130]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq071 nestingEntries_eq130]
  decide

theorem canClimb_71_281 : canClimb 71 281 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup071, nestingLookup281]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq071 nestingEntries_eq281]
  decide

theorem canClimb_71_287 : canClimb 71 287 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup071, nestingLookup287]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq071 nestingEntries_eq287]
  decide

theorem canClimb_71_350 : canClimb 71 350 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup071, nestingLookup350]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq071 nestingEntries_eq350]
  decide

theorem canClimb_72_148 : canClimb 72 148 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup072, nestingLookup148]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq072 nestingEntries_eq148]
  decide

theorem canClimb_72_150 : canClimb 72 150 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup072, nestingLookup150]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq072 nestingEntries_eq150]
  decide

theorem canClimb_72_151 : canClimb 72 151 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup072, nestingLookup151]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq072 nestingEntries_eq151]
  decide

theorem canClimb_73_178 : canClimb 73 178 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup073, nestingLookup178]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq073 nestingEntries_eq178]
  decide

theorem canClimb_73_180 : canClimb 73 180 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup073, nestingLookup180]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq073 nestingEntries_eq180]
  decide

theorem canClimb_73_181 : canClimb 73 181 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup073, nestingLookup181]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq073 nestingEntries_eq181]
  decide

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem canClimb_74_129 : canClimb 74 129 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup074, nestingLookup129]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq074 nestingEntries_eq129]
  decide

theorem canClimb_74_130 : canClimb 74 130 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup074, nestingLookup130]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq074 nestingEntries_eq130]
  decide

theorem canClimb_74_283 : canClimb 74 283 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup074, nestingLookup283]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq074 nestingEntries_eq283]
  decide

theorem canClimb_74_285 : canClimb 74 285 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup074, nestingLookup285]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq074 nestingEntries_eq285]
  decide

theorem canClimb_74_507 : canClimb 74 507 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup074, nestingLookup507]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq074 nestingEntries_eq507]
  decide

theorem canClimb_74_587 : canClimb 74 587 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup074, nestingLookup587]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq074 nestingEntries_eq587]
  decide

theorem canClimb_75_261 : canClimb 75 261 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup075, nestingLookup261]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq075 nestingEntries_eq261]
  decide

theorem canClimb_75_263 : canClimb 75 263 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup075, nestingLookup263]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq075 nestingEntries_eq263]
  decide

theorem canClimb_75_265 : canClimb 75 265 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup075, nestingLookup265]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq075 nestingEntries_eq265]
  decide

theorem canClimb_76_159 : canClimb 76 159 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup076, nestingLookup159]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq076 nestingEntries_eq159]
  decide

theorem canClimb_76_160 : canClimb 76 160 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup076, nestingLookup160]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq076 nestingEntries_eq160]
  decide

theorem canClimb_76_271 : canClimb 76 271 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup076, nestingLookup271]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq076 nestingEntries_eq271]
  decide

theorem canClimb_76_316 : canClimb 76 316 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup076, nestingLookup316]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq076 nestingEntries_eq316]
  decide

theorem canClimb_76_508 : canClimb 76 508 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup076, nestingLookup508]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq076 nestingEntries_eq508]
  decide

theorem canClimb_77_141 : canClimb 77 141 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup077, nestingLookup141]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq077 nestingEntries_eq141]
  decide

theorem canClimb_77_143 : canClimb 77 143 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup077, nestingLookup143]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq077 nestingEntries_eq143]
  decide

theorem canClimb_77_145 : canClimb 77 145 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup077, nestingLookup145]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq077 nestingEntries_eq145]
  decide

theorem canClimb_78_207 : canClimb 78 207 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup078, nestingLookup207]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq078 nestingEntries_eq207]
  decide

theorem canClimb_78_209 : canClimb 78 209 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup078, nestingLookup209]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq078 nestingEntries_eq209]
  decide

theorem canClimb_78_211 : canClimb 78 211 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup078, nestingLookup211]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq078 nestingEntries_eq211]
  decide

theorem canClimb_79_1 : canClimb 79 1 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup079, nestingLookup001]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq079 nestingIdentity_entries]
  rw [nestingIdentity_denominator, functionNestedCheck_identity]
  decide

theorem canClimb_79_186 : canClimb 79 186 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup079, nestingLookup186]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq079 nestingEntries_eq186]
  decide

theorem canClimb_79_188 : canClimb 79 188 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup079, nestingLookup188]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq079 nestingEntries_eq188]
  decide

theorem canClimb_79_190 : canClimb 79 190 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup079, nestingLookup190]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq079 nestingEntries_eq190]
  decide

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem canClimb_79_509 : canClimb 79 509 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup079, nestingLookup509]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq079 nestingEntries_eq509]
  decide

theorem canClimb_80_262 : canClimb 80 262 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup080, nestingLookup262]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq080 nestingEntries_eq262]
  decide

theorem canClimb_80_264 : canClimb 80 264 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup080, nestingLookup264]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq080 nestingEntries_eq264]
  decide

theorem canClimb_80_265 : canClimb 80 265 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup080, nestingLookup265]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq080 nestingEntries_eq265]
  decide

theorem canClimb_81_208 : canClimb 81 208 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup081, nestingLookup208]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq081 nestingEntries_eq208]
  decide

theorem canClimb_81_210 : canClimb 81 210 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup081, nestingLookup210]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq081 nestingEntries_eq210]
  decide

theorem canClimb_81_211 : canClimb 81 211 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup081, nestingLookup211]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq081 nestingEntries_eq211]
  decide

theorem canClimb_82_171 : canClimb 82 171 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup082, nestingLookup171]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq082 nestingEntries_eq171]
  decide

theorem canClimb_82_173 : canClimb 82 173 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup082, nestingLookup173]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq082 nestingEntries_eq173]
  decide

theorem canClimb_82_175 : canClimb 82 175 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup082, nestingLookup175]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq082 nestingEntries_eq175]
  decide

theorem canClimb_83_255 : canClimb 83 255 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup083, nestingLookup255]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq083 nestingEntries_eq255]
  decide

theorem canClimb_83_257 : canClimb 83 257 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup083, nestingLookup257]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq083 nestingEntries_eq257]
  decide

theorem canClimb_83_259 : canClimb 83 259 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup083, nestingLookup259]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq083 nestingEntries_eq259]
  decide

theorem canClimb_84_142 : canClimb 84 142 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup084, nestingLookup142]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq084 nestingEntries_eq142]
  decide

theorem canClimb_84_144 : canClimb 84 144 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup084, nestingLookup144]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq084 nestingEntries_eq144]
  decide

theorem canClimb_84_145 : canClimb 84 145 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup084, nestingLookup145]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq084 nestingEntries_eq145]
  decide

theorem canClimb_85_201 : canClimb 85 201 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup085, nestingLookup201]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq085 nestingEntries_eq201]
  decide

theorem canClimb_85_203 : canClimb 85 203 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup085, nestingLookup203]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq085 nestingEntries_eq203]
  decide

theorem canClimb_85_205 : canClimb 85 205 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup085, nestingLookup205]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq085 nestingEntries_eq205]
  decide

theorem canClimb_86_172 : canClimb 86 172 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup086, nestingLookup172]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq086 nestingEntries_eq172]
  decide

theorem canClimb_86_174 : canClimb 86 174 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup086, nestingLookup174]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq086 nestingEntries_eq174]
  decide

theorem canClimb_86_175 : canClimb 86 175 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup086, nestingLookup175]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq086 nestingEntries_eq175]
  decide

theorem canClimb_87_202 : canClimb 87 202 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup087, nestingLookup202]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq087 nestingEntries_eq202]
  decide

theorem canClimb_87_204 : canClimb 87 204 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup087, nestingLookup204]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq087 nestingEntries_eq204]
  decide

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem canClimb_87_205 : canClimb 87 205 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup087, nestingLookup205]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq087 nestingEntries_eq205]
  decide

theorem canClimb_88_256 : canClimb 88 256 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup088, nestingLookup256]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq088 nestingEntries_eq256]
  decide

theorem canClimb_88_258 : canClimb 88 258 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup088, nestingLookup258]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq088 nestingEntries_eq258]
  decide

theorem canClimb_88_259 : canClimb 88 259 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup088, nestingLookup259]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq088 nestingEntries_eq259]
  decide

theorem canClimb_89_187 : canClimb 89 187 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup089, nestingLookup187]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq089 nestingEntries_eq187]
  decide

theorem canClimb_89_189 : canClimb 89 189 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup089, nestingLookup189]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq089 nestingEntries_eq189]
  decide

theorem canClimb_89_190 : canClimb 89 190 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup089, nestingLookup190]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq089 nestingEntries_eq190]
  decide

theorem canClimb_90_243 : canClimb 90 243 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup090, nestingLookup243]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq090 nestingEntries_eq243]
  decide

theorem canClimb_90_245 : canClimb 90 245 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup090, nestingLookup245]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq090 nestingEntries_eq245]
  decide

theorem canClimb_90_247 : canClimb 90 247 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup090, nestingLookup247]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq090 nestingEntries_eq247]
  decide

theorem canClimb_91_153 : canClimb 91 153 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup091, nestingLookup153]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq091 nestingEntries_eq153]
  decide

theorem canClimb_91_155 : canClimb 91 155 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup091, nestingLookup155]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq091 nestingEntries_eq155]
  decide

theorem canClimb_91_157 : canClimb 91 157 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup091, nestingLookup157]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq091 nestingEntries_eq157]
  decide

theorem canClimb_92_237 : canClimb 92 237 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup092, nestingLookup237]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq092 nestingEntries_eq237]
  decide

theorem canClimb_92_239 : canClimb 92 239 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup092, nestingLookup239]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq092 nestingEntries_eq239]
  decide

theorem canClimb_92_241 : canClimb 92 241 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup092, nestingLookup241]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq092 nestingEntries_eq241]
  decide

theorem canClimb_93_135 : canClimb 93 135 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup093, nestingLookup135]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq093 nestingEntries_eq135]
  decide

theorem canClimb_93_137 : canClimb 93 137 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup093, nestingLookup137]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq093 nestingEntries_eq137]
  decide

theorem canClimb_93_139 : canClimb 93 139 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup093, nestingLookup139]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq093 nestingEntries_eq139]
  decide

theorem canClimb_94_183 : canClimb 94 183 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup094, nestingLookup183]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq094 nestingEntries_eq183]
  decide

theorem canClimb_94_184 : canClimb 94 184 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup094, nestingLookup184]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq094 nestingEntries_eq184]
  decide

theorem canClimb_94_275 : canClimb 94 275 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup094, nestingLookup275]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq094 nestingEntries_eq275]
  decide

theorem canClimb_94_315 : canClimb 94 315 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup094, nestingLookup315]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq094 nestingEntries_eq315]
  decide

theorem canClimb_94_509 : canClimb 94 509 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup094, nestingLookup509]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq094 nestingEntries_eq509]
  decide

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem canClimb_95_244 : canClimb 95 244 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup095, nestingLookup244]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq095 nestingEntries_eq244]
  decide

theorem canClimb_95_246 : canClimb 95 246 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup095, nestingLookup246]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq095 nestingEntries_eq246]
  decide

theorem canClimb_95_247 : canClimb 95 247 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup095, nestingLookup247]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq095 nestingEntries_eq247]
  decide

theorem canClimb_96_165 : canClimb 96 165 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup096, nestingLookup165]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq096 nestingEntries_eq165]
  decide

theorem canClimb_96_167 : canClimb 96 167 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup096, nestingLookup167]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq096 nestingEntries_eq167]
  decide

theorem canClimb_96_169 : canClimb 96 169 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup096, nestingLookup169]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq096 nestingEntries_eq169]
  decide

theorem canClimb_97_238 : canClimb 97 238 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup097, nestingLookup238]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq097 nestingEntries_eq238]
  decide

theorem canClimb_97_240 : canClimb 97 240 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup097, nestingLookup240]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq097 nestingEntries_eq240]
  decide

theorem canClimb_97_241 : canClimb 97 241 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup097, nestingLookup241]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq097 nestingEntries_eq241]
  decide

theorem canClimb_98_136 : canClimb 98 136 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup098, nestingLookup136]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq098 nestingEntries_eq136]
  decide

theorem canClimb_98_138 : canClimb 98 138 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup098, nestingLookup138]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq098 nestingEntries_eq138]
  decide

theorem canClimb_98_139 : canClimb 98 139 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup098, nestingLookup139]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq098 nestingEntries_eq139]
  decide

theorem canClimb_99_154 : canClimb 99 154 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup099, nestingLookup154]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq099 nestingEntries_eq154]
  decide

theorem canClimb_99_156 : canClimb 99 156 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup099, nestingLookup156]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq099 nestingEntries_eq156]
  decide

theorem canClimb_99_157 : canClimb 99 157 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup099, nestingLookup157]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq099 nestingEntries_eq157]
  decide

theorem canClimb_100_225 : canClimb 100 225 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup100, nestingLookup225]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq100 nestingEntries_eq225]
  decide

theorem canClimb_100_227 : canClimb 100 227 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup100, nestingLookup227]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq100 nestingEntries_eq227]
  decide

theorem canClimb_100_229 : canClimb 100 229 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup100, nestingLookup229]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq100 nestingEntries_eq229]
  decide

theorem canClimb_101_219 : canClimb 101 219 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup101, nestingLookup219]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq101 nestingEntries_eq219]
  decide

theorem canClimb_101_221 : canClimb 101 221 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup101, nestingLookup221]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq101 nestingEntries_eq221]
  decide

theorem canClimb_101_223 : canClimb 101 223 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup101, nestingLookup223]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq101 nestingEntries_eq223]
  decide

theorem canClimb_102_226 : canClimb 102 226 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup102, nestingLookup226]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq102 nestingEntries_eq226]
  decide

theorem canClimb_102_228 : canClimb 102 228 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup102, nestingLookup228]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq102 nestingEntries_eq228]
  decide

theorem canClimb_102_229 : canClimb 102 229 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup102, nestingLookup229]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq102 nestingEntries_eq229]
  decide

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem canClimb_103_220 : canClimb 103 220 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup103, nestingLookup220]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq103 nestingEntries_eq220]
  decide

theorem canClimb_103_222 : canClimb 103 222 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup103, nestingLookup222]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq103 nestingEntries_eq222]
  decide

theorem canClimb_103_223 : canClimb 103 223 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup103, nestingLookup223]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq103 nestingEntries_eq223]
  decide

theorem canClimb_104_166 : canClimb 104 166 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup104, nestingLookup166]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq104 nestingEntries_eq166]
  decide

theorem canClimb_104_168 : canClimb 104 168 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup104, nestingLookup168]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq104 nestingEntries_eq168]
  decide

theorem canClimb_104_169 : canClimb 104 169 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup104, nestingLookup169]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq104 nestingEntries_eq169]
  decide

theorem canClimb_105_231 : canClimb 105 231 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup105, nestingLookup231]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq105 nestingEntries_eq231]
  decide

theorem canClimb_105_233 : canClimb 105 233 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup105, nestingLookup233]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq105 nestingEntries_eq233]
  decide

theorem canClimb_105_235 : canClimb 105 235 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup105, nestingLookup235]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq105 nestingEntries_eq235]
  decide

theorem canClimb_106_195 : canClimb 106 195 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup106, nestingLookup195]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq106 nestingEntries_eq195]
  decide

theorem canClimb_106_197 : canClimb 106 197 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup106, nestingLookup197]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq106 nestingEntries_eq197]
  decide

theorem canClimb_106_199 : canClimb 106 199 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup106, nestingLookup199]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq106 nestingEntries_eq199]
  decide

theorem canClimb_107_249 : canClimb 107 249 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup107, nestingLookup249]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq107 nestingEntries_eq249]
  decide

theorem canClimb_107_251 : canClimb 107 251 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup107, nestingLookup251]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq107 nestingEntries_eq251]
  decide

theorem canClimb_107_253 : canClimb 107 253 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup107, nestingLookup253]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq107 nestingEntries_eq253]
  decide

theorem canClimb_108_213 : canClimb 108 213 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup108, nestingLookup213]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq108 nestingEntries_eq213]
  decide

theorem canClimb_108_215 : canClimb 108 215 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup108, nestingLookup215]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq108 nestingEntries_eq215]
  decide

theorem canClimb_108_217 : canClimb 108 217 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup108, nestingLookup217]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq108 nestingEntries_eq217]
  decide

theorem canClimb_109_196 : canClimb 109 196 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup109, nestingLookup196]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq109 nestingEntries_eq196]
  decide

theorem canClimb_109_198 : canClimb 109 198 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup109, nestingLookup198]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq109 nestingEntries_eq198]
  decide

theorem canClimb_109_199 : canClimb 109 199 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup109, nestingLookup199]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq109 nestingEntries_eq199]
  decide

theorem canClimb_110_214 : canClimb 110 214 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup110, nestingLookup214]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq110 nestingEntries_eq214]
  decide

theorem canClimb_110_216 : canClimb 110 216 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup110, nestingLookup216]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq110 nestingEntries_eq216]
  decide

theorem canClimb_110_217 : canClimb 110 217 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup110, nestingLookup217]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq110 nestingEntries_eq217]
  decide

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem canClimb_111_232 : canClimb 111 232 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup111, nestingLookup232]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq111 nestingEntries_eq232]
  decide

theorem canClimb_111_234 : canClimb 111 234 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup111, nestingLookup234]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq111 nestingEntries_eq234]
  decide

theorem canClimb_111_235 : canClimb 111 235 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup111, nestingLookup235]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq111 nestingEntries_eq235]
  decide

theorem canClimb_112_250 : canClimb 112 250 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup112, nestingLookup250]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq112 nestingEntries_eq250]
  decide

theorem canClimb_112_252 : canClimb 112 252 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup112, nestingLookup252]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq112 nestingEntries_eq252]
  decide

theorem canClimb_112_253 : canClimb 112 253 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup112, nestingLookup253]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq112 nestingEntries_eq253]
  decide

theorem canClimb_113_276 : canClimb 113 276 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup113, nestingLookup276]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq113 nestingEntries_eq276]
  decide

theorem canClimb_113_277 : canClimb 113 277 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup113, nestingLookup277]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq113 nestingEntries_eq277]
  decide

theorem canClimb_113_506 : canClimb 113 506 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup113, nestingLookup506]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq113 nestingEntries_eq506]
  decide

theorem canClimb_114_274 : canClimb 114 274 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup114, nestingLookup274]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq114 nestingEntries_eq274]
  decide

theorem canClimb_114_275 : canClimb 114 275 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup114, nestingLookup275]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq114 nestingEntries_eq275]
  decide

theorem canClimb_114_506 : canClimb 114 506 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup114, nestingLookup506]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq114 nestingEntries_eq506]
  decide

theorem canClimb_114_531 : canClimb 114 531 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup114, nestingLookup531]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq114 nestingEntries_eq531]
  decide

theorem canClimb_115_270 : canClimb 115 270 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup115, nestingLookup270]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq115 nestingEntries_eq270]
  decide

theorem canClimb_115_271 : canClimb 115 271 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup115, nestingLookup271]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq115 nestingEntries_eq271]
  decide

theorem canClimb_115_506 : canClimb 115 506 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup115, nestingLookup506]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq115 nestingEntries_eq506]
  decide

theorem canClimb_116_286 : canClimb 116 286 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup116, nestingLookup286]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq116 nestingEntries_eq286]
  decide

theorem canClimb_116_287 : canClimb 116 287 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup116, nestingLookup287]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq116 nestingEntries_eq287]
  decide

theorem canClimb_116_506 : canClimb 116 506 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup116, nestingLookup506]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq116 nestingEntries_eq506]
  decide

theorem canClimb_117_284 : canClimb 117 284 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup117, nestingLookup284]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq117 nestingEntries_eq284]
  decide

theorem canClimb_117_285 : canClimb 117 285 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup117, nestingLookup285]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq117 nestingEntries_eq285]
  decide

theorem canClimb_117_506 : canClimb 117 506 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup117, nestingLookup506]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq117 nestingEntries_eq506]
  decide

theorem canClimb_118_278 : canClimb 118 278 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup118, nestingLookup278]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq118 nestingEntries_eq278]
  decide

theorem canClimb_118_279 : canClimb 118 279 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup118, nestingLookup279]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq118 nestingEntries_eq279]
  decide

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem canClimb_118_506 : canClimb 118 506 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup118, nestingLookup506]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq118 nestingEntries_eq506]
  decide

theorem canClimb_119_300 : canClimb 119 300 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup119, nestingLookup300]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq119 nestingEntries_eq300]
  decide

theorem canClimb_119_301 : canClimb 119 301 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup119, nestingLookup301]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq119 nestingEntries_eq301]
  decide

theorem canClimb_119_506 : canClimb 119 506 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup119, nestingLookup506]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq119 nestingEntries_eq506]
  decide

theorem canClimb_119_577 : canClimb 119 577 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup119, nestingLookup577]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq119 nestingEntries_eq577]
  decide

theorem canClimb_120_298 : canClimb 120 298 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup120, nestingLookup298]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq120 nestingEntries_eq298]
  decide

theorem canClimb_120_299 : canClimb 120 299 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup120, nestingLookup299]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq120 nestingEntries_eq299]
  decide

theorem canClimb_120_506 : canClimb 120 506 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup120, nestingLookup506]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq120 nestingEntries_eq506]
  decide

theorem canClimb_120_583 : canClimb 120 583 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup120, nestingLookup583]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq120 nestingEntries_eq583]
  decide

theorem canClimb_121_296 : canClimb 121 296 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup121, nestingLookup296]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq121 nestingEntries_eq296]
  decide

theorem canClimb_121_297 : canClimb 121 297 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup121, nestingLookup297]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq121 nestingEntries_eq297]
  decide

theorem canClimb_121_506 : canClimb 121 506 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup121, nestingLookup506]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq121 nestingEntries_eq506]
  decide

theorem canClimb_121_573 : canClimb 121 573 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup121, nestingLookup573]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq121 nestingEntries_eq573]
  decide

theorem canClimb_122_294 : canClimb 122 294 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup122, nestingLookup294]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq122 nestingEntries_eq294]
  decide

theorem canClimb_122_295 : canClimb 122 295 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup122, nestingLookup295]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq122 nestingEntries_eq295]
  decide

theorem canClimb_122_506 : canClimb 122 506 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup122, nestingLookup506]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq122 nestingEntries_eq506]
  decide

theorem canClimb_123_292 : canClimb 123 292 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup123, nestingLookup292]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq123 nestingEntries_eq292]
  decide

theorem canClimb_123_293 : canClimb 123 293 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup123, nestingLookup293]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq123 nestingEntries_eq293]
  decide

theorem canClimb_123_506 : canClimb 123 506 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup123, nestingLookup506]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq123 nestingEntries_eq506]
  decide

theorem canClimb_124_290 : canClimb 124 290 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup124, nestingLookup290]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq124 nestingEntries_eq290]
  decide

theorem canClimb_124_291 : canClimb 124 291 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup124, nestingLookup291]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq124 nestingEntries_eq291]
  decide

theorem canClimb_124_506 : canClimb 124 506 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup124, nestingLookup506]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq124 nestingEntries_eq506]
  decide

theorem canClimb_124_572 : canClimb 124 572 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup124, nestingLookup572]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq124 nestingEntries_eq572]
  decide

theorem canClimb_125_267 : canClimb 125 267 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup125, nestingLookup267]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq125 nestingEntries_eq267]
  decide

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem canClimb_125_277 : canClimb 125 277 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup125, nestingLookup277]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq125 nestingEntries_eq277]
  decide

theorem canClimb_125_507 : canClimb 125 507 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup125, nestingLookup507]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq125 nestingEntries_eq507]
  decide

theorem canClimb_126_268 : canClimb 126 268 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup126, nestingLookup268]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq126 nestingEntries_eq268]
  decide

theorem canClimb_126_274 : canClimb 126 274 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup126, nestingLookup274]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq126 nestingEntries_eq274]
  decide

theorem canClimb_126_507 : canClimb 126 507 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup126, nestingLookup507]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq126 nestingEntries_eq507]
  decide

theorem canClimb_127_271 : canClimb 127 271 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup127, nestingLookup271]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq127 nestingEntries_eq271]
  decide

theorem canClimb_127_273 : canClimb 127 273 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup127, nestingLookup273]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq127 nestingEntries_eq273]
  decide

theorem canClimb_127_507 : canClimb 127 507 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup127, nestingLookup507]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq127 nestingEntries_eq507]
  decide

theorem canClimb_127_525 : canClimb 127 525 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup127, nestingLookup525]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq127 nestingEntries_eq525]
  decide

theorem canClimb_128_282 : canClimb 128 282 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup128, nestingLookup282]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq128 nestingEntries_eq282]
  decide

theorem canClimb_128_284 : canClimb 128 284 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup128, nestingLookup284]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq128 nestingEntries_eq284]
  decide

theorem canClimb_128_507 : canClimb 128 507 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup128, nestingLookup507]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq128 nestingEntries_eq507]
  decide

theorem canClimb_129_280 : canClimb 129 280 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup129, nestingLookup280]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq129 nestingEntries_eq280]
  decide

theorem canClimb_129_286 : canClimb 129 286 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup129, nestingLookup286]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq129 nestingEntries_eq286]
  decide

theorem canClimb_129_507 : canClimb 129 507 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup129, nestingLookup507]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq129 nestingEntries_eq507]
  decide

theorem canClimb_129_594 : canClimb 129 594 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup129, nestingLookup594]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq129 nestingEntries_eq594]
  decide

theorem canClimb_130_278 : canClimb 130 278 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup130, nestingLookup278]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq130 nestingEntries_eq278]
  decide

theorem canClimb_130_289 : canClimb 130 289 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup130, nestingLookup289]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq130 nestingEntries_eq289]
  decide

theorem canClimb_130_507 : canClimb 130 507 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup130, nestingLookup507]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq130 nestingEntries_eq507]
  decide

theorem canClimb_131_291 : canClimb 131 291 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup131, nestingLookup291]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq131 nestingEntries_eq291]
  decide

theorem canClimb_131_300 : canClimb 131 300 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup131, nestingLookup300]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq131 nestingEntries_eq300]
  decide

theorem canClimb_131_507 : canClimb 131 507 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup131, nestingLookup507]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq131 nestingEntries_eq507]
  decide

theorem canClimb_131_593 : canClimb 131 593 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup131, nestingLookup593]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq131 nestingEntries_eq593]
  decide

theorem canClimb_132_295 : canClimb 132 295 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup132, nestingLookup295]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq132 nestingEntries_eq295]
  decide

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem canClimb_132_297 : canClimb 132 297 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup132, nestingLookup297]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq132 nestingEntries_eq297]
  decide

theorem canClimb_132_507 : canClimb 132 507 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup132, nestingLookup507]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq132 nestingEntries_eq507]
  decide

theorem canClimb_133_292 : canClimb 133 292 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup133, nestingLookup292]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq133 nestingEntries_eq292]
  decide

theorem canClimb_133_298 : canClimb 133 298 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup133, nestingLookup298]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq133 nestingEntries_eq298]
  decide

theorem canClimb_133_507 : canClimb 133 507 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup133, nestingLookup507]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq133 nestingEntries_eq507]
  decide

theorem canClimb_134_270 : canClimb 134 270 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup134, nestingLookup270]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq134 nestingEntries_eq270]
  decide

theorem canClimb_134_307 : canClimb 134 307 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup134, nestingLookup307]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq134 nestingEntries_eq307]
  decide

theorem canClimb_134_519 : canClimb 134 519 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup134, nestingLookup519]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq134 nestingEntries_eq519]
  decide

theorem canClimb_134_616 : canClimb 134 616 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup134, nestingLookup616]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq134 nestingEntries_eq616]
  decide

theorem canClimb_135_282 : canClimb 135 282 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup135, nestingLookup282]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq135 nestingEntries_eq282]
  decide

theorem canClimb_135_306 : canClimb 135 306 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup135, nestingLookup306]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq135 nestingEntries_eq306]
  decide

theorem canClimb_135_519 : canClimb 135 519 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup135, nestingLookup519]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq135 nestingEntries_eq519]
  decide

theorem canClimb_135_548 : canClimb 135 548 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup135, nestingLookup548]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq135 nestingEntries_eq548]
  decide

theorem canClimb_136_296 : canClimb 136 296 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup136, nestingLookup296]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq136 nestingEntries_eq296]
  decide

theorem canClimb_136_305 : canClimb 136 305 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup136, nestingLookup305]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq136 nestingEntries_eq305]
  decide

theorem canClimb_136_399 : canClimb 136 399 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup136, nestingLookup399]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq136 nestingEntries_eq399]
  decide

theorem canClimb_137_295 : canClimb 137 295 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup137, nestingLookup295]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq137 nestingEntries_eq295]
  decide

theorem canClimb_137_304 : canClimb 137 304 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup137, nestingLookup304]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq137 nestingEntries_eq304]
  decide

theorem canClimb_137_519 : canClimb 137 519 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup137, nestingLookup519]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq137 nestingEntries_eq519]
  decide

theorem canClimb_137_621 : canClimb 137 621 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup137, nestingLookup621]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq137 nestingEntries_eq621]
  decide

theorem canClimb_138_285 : canClimb 138 285 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup138, nestingLookup285]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq138 nestingEntries_eq285]
  decide

theorem canClimb_138_303 : canClimb 138 303 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup138, nestingLookup303]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq138 nestingEntries_eq303]
  decide

theorem canClimb_138_401 : canClimb 138 401 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup138, nestingLookup401]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq138 nestingEntries_eq401]
  decide

theorem canClimb_139_273 : canClimb 139 273 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup139, nestingLookup273]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq139 nestingEntries_eq273]
  decide

end CSL.Construction.PhysicalFramePaths


