-- Prove2me | Definitions.Def_CSL_Generated_FiniteCircuit_FramePathChecks_Nesting_Batch03
-- name    : CSL_Generated_FiniteCircuit_FramePathChecks_Nesting_Batch03
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T14:02:04.427444+00:00
-- url     : https://prove2.me/theorems/2780b9c2-d151-4a7f-b1de-980344ad75c4
-- title:
--   Coded sorting library: Generated / FiniteCircuit / FramePathChecks / Nesting / Batch03
-- statement:
--   Module `CodedSorting.Generated.FiniteCircuit.FramePathChecks.Nesting.Batch03` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   Generated physical-frame checks. Uncompiled until a build record exists.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Generated.FiniteCircuit.FramePathChecks.Nesting.Batch03

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
theorem canClimb_245_299 : canClimb 245 299 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup245, nestingLookup299]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq245 nestingEntries_eq299]
  decide

theorem canClimb_245_324 : canClimb 245 324 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup245, nestingLookup324]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq245 nestingEntries_eq324]
  decide

theorem canClimb_245_455 : canClimb 245 455 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup245, nestingLookup455]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq245 nestingEntries_eq455]
  decide

theorem canClimb_246_281 : canClimb 246 281 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup246, nestingLookup281]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq246 nestingEntries_eq281]
  decide

theorem canClimb_246_317 : canClimb 246 317 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup246, nestingLookup317]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq246 nestingEntries_eq317]
  decide

theorem canClimb_246_523 : canClimb 246 523 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup246, nestingLookup523]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq246 nestingEntries_eq523]
  decide

theorem canClimb_246_541 : canClimb 246 541 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup246, nestingLookup541]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq246 nestingEntries_eq541]
  decide

theorem canClimb_247_275 : canClimb 247 275 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup247, nestingLookup275]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq247 nestingEntries_eq275]
  decide

theorem canClimb_247_305 : canClimb 247 305 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup247, nestingLookup305]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq247 nestingEntries_eq305]
  decide

theorem canClimb_247_523 : canClimb 247 523 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup247, nestingLookup523]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq247 nestingEntries_eq523]
  decide

theorem canClimb_247_543 : canClimb 247 543 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup247, nestingLookup543]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq247 nestingEntries_eq543]
  decide

theorem canClimb_248_266 : canClimb 248 266 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup248, nestingLookup266]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq248 nestingEntries_eq266]
  decide

theorem canClimb_248_311 : canClimb 248 311 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup248, nestingLookup311]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq248 nestingEntries_eq311]
  decide

theorem canClimb_248_444 : canClimb 248 444 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup248, nestingLookup444]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq248 nestingEntries_eq444]
  decide

theorem canClimb_249_301 : canClimb 249 301 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup249, nestingLookup301]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq249 nestingEntries_eq301]
  decide

theorem canClimb_249_320 : canClimb 249 320 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup249, nestingLookup320]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq249 nestingEntries_eq320]
  decide

theorem canClimb_249_524 : canClimb 249 524 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup249, nestingLookup524]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq249 nestingEntries_eq524]
  decide

theorem canClimb_249_537 : canClimb 249 537 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup249, nestingLookup537]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq249 nestingEntries_eq537]
  decide

theorem canClimb_250_289 : canClimb 250 289 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup250, nestingLookup289]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq250 nestingEntries_eq289]
  decide

theorem canClimb_250_305 : canClimb 250 305 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup250, nestingLookup305]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq250 nestingEntries_eq305]
  decide

theorem canClimb_250_524 : canClimb 250 524 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup250, nestingLookup524]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq250 nestingEntries_eq524]
  decide

theorem canClimb_250_630 : canClimb 250 630 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup250, nestingLookup630]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq250 nestingEntries_eq630]
  decide

theorem canClimb_251_279 : canClimb 251 279 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup251, nestingLookup279]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq251 nestingEntries_eq279]
  decide

theorem canClimb_251_304 : canClimb 251 304 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup251, nestingLookup304]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq251 nestingEntries_eq304]
  decide

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem canClimb_251_524 : canClimb 251 524 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup251, nestingLookup524]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq251 nestingEntries_eq524]
  decide

theorem canClimb_251_635 : canClimb 251 635 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup251, nestingLookup635]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq251 nestingEntries_eq635]
  decide

theorem canClimb_252_291 : canClimb 252 291 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup252, nestingLookup291]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq252 nestingEntries_eq291]
  decide

theorem canClimb_252_321 : canClimb 252 321 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup252, nestingLookup321]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq252 nestingEntries_eq321]
  decide

theorem canClimb_252_524 : canClimb 252 524 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup252, nestingLookup524]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq252 nestingEntries_eq524]
  decide

theorem canClimb_252_533 : canClimb 252 533 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup252, nestingLookup533]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq252 nestingEntries_eq533]
  decide

theorem canClimb_253_277 : canClimb 253 277 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup253, nestingLookup277]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq253 nestingEntries_eq277]
  decide

theorem canClimb_253_310 : canClimb 253 310 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup253, nestingLookup310]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq253 nestingEntries_eq310]
  decide

theorem canClimb_253_447 : canClimb 253 447 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup253, nestingLookup447]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq253 nestingEntries_eq447]
  decide

theorem canClimb_254_274 : canClimb 254 274 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup254, nestingLookup274]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq254 nestingEntries_eq274]
  decide

theorem canClimb_254_323 : canClimb 254 323 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup254, nestingLookup323]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq254 nestingEntries_eq323]
  decide

theorem canClimb_254_524 : canClimb 254 524 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup254, nestingLookup524]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq254 nestingEntries_eq524]
  decide

theorem canClimb_254_611 : canClimb 254 611 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup254, nestingLookup611]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq254 nestingEntries_eq611]
  decide

theorem canClimb_255_293 : canClimb 255 293 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup255, nestingLookup293]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq255 nestingEntries_eq293]
  decide

theorem canClimb_255_314 : canClimb 255 314 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup255, nestingLookup314]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq255 nestingEntries_eq314]
  decide

theorem canClimb_255_449 : canClimb 255 449 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup255, nestingLookup449]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq255 nestingEntries_eq449]
  decide

theorem canClimb_256_281 : canClimb 256 281 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup256, nestingLookup281]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq256 nestingEntries_eq281]
  decide

theorem canClimb_256_307 : canClimb 256 307 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup256, nestingLookup307]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq256 nestingEntries_eq307]
  decide

theorem canClimb_256_524 : canClimb 256 524 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup256, nestingLookup524]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq256 nestingEntries_eq524]
  decide

theorem canClimb_256_606 : canClimb 256 606 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup256, nestingLookup606]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq256 nestingEntries_eq606]
  decide

theorem canClimb_257_286 : canClimb 257 286 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup257, nestingLookup286]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq257 nestingEntries_eq286]
  decide

theorem canClimb_257_302 : canClimb 257 302 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup257, nestingLookup302]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq257 nestingEntries_eq302]
  decide

theorem canClimb_257_524 : canClimb 257 524 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup257, nestingLookup524]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq257 nestingEntries_eq524]
  decide

theorem canClimb_257_556 : canClimb 257 556 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup257, nestingLookup556]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq257 nestingEntries_eq556]
  decide

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem canClimb_258_298 : canClimb 258 298 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup258, nestingLookup298]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq258 nestingEntries_eq298]
  decide

theorem canClimb_258_319 : canClimb 258 319 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup258, nestingLookup319]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq258 nestingEntries_eq319]
  decide

theorem canClimb_258_439 : canClimb 258 439 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup258, nestingLookup439]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq258 nestingEntries_eq439]
  decide

theorem canClimb_259_269 : canClimb 259 269 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup259, nestingLookup269]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq259 nestingEntries_eq269]
  decide

theorem canClimb_259_322 : canClimb 259 322 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup259, nestingLookup322]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq259 nestingEntries_eq322]
  decide

theorem canClimb_259_524 : canClimb 259 524 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup259, nestingLookup524]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq259 nestingEntries_eq524]
  decide

theorem canClimb_259_562 : canClimb 259 562 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup259, nestingLookup562]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq259 nestingEntries_eq562]
  decide

theorem canClimb_260_272 : canClimb 260 272 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup260, nestingLookup272]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq260 nestingEntries_eq272]
  decide

theorem canClimb_260_309 : canClimb 260 309 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup260, nestingLookup309]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq260 nestingEntries_eq309]
  decide

theorem canClimb_260_524 : canClimb 260 524 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup260, nestingLookup524]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq260 nestingEntries_eq524]
  decide

theorem canClimb_260_603 : canClimb 260 603 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup260, nestingLookup603]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq260 nestingEntries_eq603]
  decide

theorem canClimb_261_294 : canClimb 261 294 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup261, nestingLookup294]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq261 nestingEntries_eq294]
  decide

theorem canClimb_261_318 : canClimb 261 318 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup261, nestingLookup318]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq261 nestingEntries_eq318]
  decide

theorem canClimb_261_438 : canClimb 261 438 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup261, nestingLookup438]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq261 nestingEntries_eq438]
  decide

theorem canClimb_262_282 : canClimb 262 282 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup262, nestingLookup282]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq262 nestingEntries_eq282]
  decide

theorem canClimb_262_325 : canClimb 262 325 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup262, nestingLookup325]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq262 nestingEntries_eq325]
  decide

theorem canClimb_262_441 : canClimb 262 441 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup262, nestingLookup441]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq262 nestingEntries_eq441]
  decide

theorem canClimb_263_285 : canClimb 263 285 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup263, nestingLookup285]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq263 nestingEntries_eq285]
  decide

theorem canClimb_263_324 : canClimb 263 324 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup263, nestingLookup324]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq263 nestingEntries_eq324]
  decide

theorem canClimb_263_524 : canClimb 263 524 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup263, nestingLookup524]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq263 nestingEntries_eq524]
  decide

theorem canClimb_263_565 : canClimb 263 565 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup263, nestingLookup565]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq263 nestingEntries_eq565]
  decide

theorem canClimb_264_297 : canClimb 264 297 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup264, nestingLookup297]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq264 nestingEntries_eq297]
  decide

theorem canClimb_264_315 : canClimb 264 315 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup264, nestingLookup315]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq264 nestingEntries_eq315]
  decide

theorem canClimb_264_524 : canClimb 264 524 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup264, nestingLookup524]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq264 nestingEntries_eq524]
  decide

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem canClimb_264_598 : canClimb 264 598 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup264, nestingLookup598]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq264 nestingEntries_eq598]
  decide

theorem canClimb_265_271 : canClimb 265 271 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup265, nestingLookup271]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq265 nestingEntries_eq271]
  decide

theorem canClimb_265_312 : canClimb 265 312 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup265, nestingLookup312]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq265 nestingEntries_eq312]
  decide

theorem canClimb_265_524 : canClimb 265 524 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup265, nestingLookup524]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq265 nestingEntries_eq524]
  decide

theorem canClimb_265_570 : canClimb 265 570 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup265, nestingLookup570]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq265 nestingEntries_eq570]
  decide

theorem canClimb_266_326 : canClimb 266 326 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup266, nestingLookup326]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq266 nestingEntries_eq326]
  decide

theorem canClimb_266_344 : canClimb 266 344 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup266, nestingLookup344]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq266 nestingEntries_eq344]
  decide

theorem canClimb_266_439 : canClimb 266 439 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup266, nestingLookup439]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq266 nestingEntries_eq439]
  decide

theorem canClimb_266_457 : canClimb 266 457 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup266, nestingLookup457]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq266 nestingEntries_eq457]
  decide

theorem canClimb_266_475 : canClimb 266 475 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup266, nestingLookup475]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq266 nestingEntries_eq475]
  decide

theorem canClimb_266_493 : canClimb 266 493 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup266, nestingLookup493]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq266 nestingEntries_eq493]
  decide

theorem canClimb_267_326 : canClimb 267 326 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup267, nestingLookup326]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq267 nestingEntries_eq326]
  decide

theorem canClimb_267_349 : canClimb 267 349 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup267, nestingLookup349]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq267 nestingEntries_eq349]
  decide

theorem canClimb_267_374 : canClimb 267 374 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup267, nestingLookup374]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq267 nestingEntries_eq374]
  decide

theorem canClimb_267_392 : canClimb 267 392 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup267, nestingLookup392]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq267 nestingEntries_eq392]
  decide

theorem canClimb_267_410 : canClimb 267 410 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup267, nestingLookup410]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq267 nestingEntries_eq410]
  decide

theorem canClimb_267_428 : canClimb 267 428 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup267, nestingLookup428]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq267 nestingEntries_eq428]
  decide

theorem canClimb_268_327 : canClimb 268 327 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup268, nestingLookup327]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq268 nestingEntries_eq327]
  decide

theorem canClimb_268_348 : canClimb 268 348 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup268, nestingLookup348]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq268 nestingEntries_eq348]
  decide

theorem canClimb_268_385 : canClimb 268 385 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup268, nestingLookup385]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq268 nestingEntries_eq385]
  decide

theorem canClimb_268_421 : canClimb 268 421 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup268, nestingLookup421]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq268 nestingEntries_eq421]
  decide

theorem canClimb_268_463 : canClimb 268 463 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup268, nestingLookup463]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq268 nestingEntries_eq463]
  decide

theorem canClimb_268_487 : canClimb 268 487 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup268, nestingLookup487]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq268 nestingEntries_eq487]
  decide

theorem canClimb_269_327 : canClimb 269 327 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup269, nestingLookup327]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq269 nestingEntries_eq327]
  decide

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem canClimb_269_345 : canClimb 269 345 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup269, nestingLookup345]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq269 nestingEntries_eq345]
  decide

theorem canClimb_269_368 : canClimb 269 368 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup269, nestingLookup368]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq269 nestingEntries_eq368]
  decide

theorem canClimb_269_404 : canClimb 269 404 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup269, nestingLookup404]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq269 nestingEntries_eq404]
  decide

theorem canClimb_269_446 : canClimb 269 446 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup269, nestingLookup446]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq269 nestingEntries_eq446]
  decide

theorem canClimb_269_494 : canClimb 269 494 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup269, nestingLookup494]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq269 nestingEntries_eq494]
  decide

theorem canClimb_270_328 : canClimb 270 328 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup270, nestingLookup328]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq270 nestingEntries_eq328]
  decide

theorem canClimb_270_347 : canClimb 270 347 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup270, nestingLookup347]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq270 nestingEntries_eq347]
  decide

theorem canClimb_270_367 : canClimb 270 367 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup270, nestingLookup367]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq270 nestingEntries_eq367]
  decide

theorem canClimb_270_403 : canClimb 270 403 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup270, nestingLookup403]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq270 nestingEntries_eq403]
  decide

theorem canClimb_270_469 : canClimb 270 469 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup270, nestingLookup469]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq270 nestingEntries_eq469]
  decide

theorem canClimb_270_481 : canClimb 270 481 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup270, nestingLookup481]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq270 nestingEntries_eq481]
  decide

theorem canClimb_271_328 : canClimb 271 328 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup271, nestingLookup328]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq271 nestingEntries_eq328]
  decide

theorem canClimb_271_346 : canClimb 271 346 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup271, nestingLookup346]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq271 nestingEntries_eq346]
  decide

theorem canClimb_271_386 : canClimb 271 386 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup271, nestingLookup386]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq271 nestingEntries_eq386]
  decide

theorem canClimb_271_422 : canClimb 271 422 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup271, nestingLookup422]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq271 nestingEntries_eq422]
  decide

theorem canClimb_271_440 : canClimb 271 440 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup271, nestingLookup440]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq271 nestingEntries_eq440]
  decide

theorem canClimb_271_500 : canClimb 271 500 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup271, nestingLookup500]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq271 nestingEntries_eq500]
  decide

theorem canClimb_272_329 : canClimb 272 329 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup272, nestingLookup329]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq272 nestingEntries_eq329]
  decide

theorem canClimb_272_347 : canClimb 272 347 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup272, nestingLookup347]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq272 nestingEntries_eq347]
  decide

theorem canClimb_272_391 : canClimb 272 391 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup272, nestingLookup391]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq272 nestingEntries_eq391]
  decide

theorem canClimb_272_427 : canClimb 272 427 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup272, nestingLookup427]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq272 nestingEntries_eq427]
  decide

theorem canClimb_272_445 : canClimb 272 445 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup272, nestingLookup445]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq272 nestingEntries_eq445]
  decide

theorem canClimb_272_505 : canClimb 272 505 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup272, nestingLookup505]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq272 nestingEntries_eq505]
  decide

theorem canClimb_273_329 : canClimb 273 329 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup273, nestingLookup329]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq273 nestingEntries_eq329]
  decide

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem canClimb_273_346 : canClimb 273 346 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup273, nestingLookup346]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq273 nestingEntries_eq346]
  decide

theorem canClimb_273_362 : canClimb 273 362 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup273, nestingLookup362]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq273 nestingEntries_eq362]
  decide

theorem canClimb_273_398 : canClimb 273 398 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup273, nestingLookup398]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq273 nestingEntries_eq398]
  decide

theorem canClimb_273_464 : canClimb 273 464 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup273, nestingLookup464]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq273 nestingEntries_eq464]
  decide

theorem canClimb_273_476 : canClimb 273 476 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup273, nestingLookup476]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq273 nestingEntries_eq476]
  decide

theorem canClimb_274_330 : canClimb 274 330 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup274, nestingLookup330]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq274 nestingEntries_eq330]
  decide

theorem canClimb_274_348 : canClimb 274 348 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup274, nestingLookup348]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq274 nestingEntries_eq348]
  decide

theorem canClimb_274_373 : canClimb 274 373 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup274, nestingLookup373]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq274 nestingEntries_eq373]
  decide

theorem canClimb_274_409 : canClimb 274 409 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup274, nestingLookup409]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq274 nestingEntries_eq409]
  decide

theorem canClimb_274_451 : canClimb 274 451 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup274, nestingLookup451]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq274 nestingEntries_eq451]
  decide

theorem canClimb_274_499 : canClimb 274 499 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup274, nestingLookup499]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq274 nestingEntries_eq499]
  decide

theorem canClimb_275_330 : canClimb 275 330 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup275, nestingLookup330]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq275 nestingEntries_eq330]
  decide

theorem canClimb_275_345 : canClimb 275 345 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup275, nestingLookup345]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq275 nestingEntries_eq345]
  decide

theorem canClimb_275_380 : canClimb 275 380 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup275, nestingLookup380]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq275 nestingEntries_eq380]
  decide

theorem canClimb_275_416 : canClimb 275 416 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup275, nestingLookup416]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq275 nestingEntries_eq416]
  decide

theorem canClimb_275_458 : canClimb 275 458 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup275, nestingLookup458]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq275 nestingEntries_eq458]
  decide

theorem canClimb_275_482 : canClimb 275 482 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup275, nestingLookup482]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq275 nestingEntries_eq482]
  decide

theorem canClimb_276_331 : canClimb 276 331 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup276, nestingLookup331]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq276 nestingEntries_eq331]
  decide

theorem canClimb_276_344 : canClimb 276 344 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup276, nestingLookup344]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq276 nestingEntries_eq344]
  decide

theorem canClimb_276_379 : canClimb 276 379 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup276, nestingLookup379]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq276 nestingEntries_eq379]
  decide

theorem canClimb_276_397 : canClimb 276 397 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup276, nestingLookup397]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq276 nestingEntries_eq397]
  decide

theorem canClimb_276_415 : canClimb 276 415 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup276, nestingLookup415]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq276 nestingEntries_eq415]
  decide

theorem canClimb_276_433 : canClimb 276 433 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup276, nestingLookup433]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq276 nestingEntries_eq433]
  decide

theorem canClimb_277_331 : canClimb 277 331 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup277, nestingLookup331]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq277 nestingEntries_eq331]
  decide

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem canClimb_277_349 : canClimb 277 349 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup277, nestingLookup349]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq277 nestingEntries_eq349]
  decide

theorem canClimb_277_434 : canClimb 277 434 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup277, nestingLookup434]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq277 nestingEntries_eq434]
  decide

theorem canClimb_277_452 : canClimb 277 452 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup277, nestingLookup452]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq277 nestingEntries_eq452]
  decide

theorem canClimb_277_470 : canClimb 277 470 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup277, nestingLookup470]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq277 nestingEntries_eq470]
  decide

theorem canClimb_277_488 : canClimb 277 488 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup277, nestingLookup488]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq277 nestingEntries_eq488]
  decide

theorem canClimb_278_332 : canClimb 278 332 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup278, nestingLookup332]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq278 nestingEntries_eq332]
  decide

theorem canClimb_278_350 : canClimb 278 350 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup278, nestingLookup350]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq278 nestingEntries_eq350]
  decide

theorem canClimb_278_375 : canClimb 278 375 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup278, nestingLookup375]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq278 nestingEntries_eq375]
  decide

theorem canClimb_278_411 : canClimb 278 411 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup278, nestingLookup411]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq278 nestingEntries_eq411]
  decide

theorem canClimb_278_453 : canClimb 278 453 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup278, nestingLookup453]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq278 nestingEntries_eq453]
  decide

theorem canClimb_278_471 : canClimb 278 471 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup278, nestingLookup471]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq278 nestingEntries_eq471]
  decide

theorem canClimb_279_332 : canClimb 279 332 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup279, nestingLookup332]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq279 nestingEntries_eq332]
  decide

theorem canClimb_279_355 : canClimb 279 355 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup279, nestingLookup355]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq279 nestingEntries_eq355]
  decide

theorem canClimb_279_395 : canClimb 279 395 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup279, nestingLookup395]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq279 nestingEntries_eq395]
  decide

theorem canClimb_279_431 : canClimb 279 431 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup279, nestingLookup431]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq279 nestingEntries_eq431]
  decide

theorem canClimb_279_436 : canClimb 279 436 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup279, nestingLookup436]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq279 nestingEntries_eq436]
  decide

theorem canClimb_279_490 : canClimb 279 490 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup279, nestingLookup490]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq279 nestingEntries_eq490]
  decide

theorem canClimb_280_333 : canClimb 280 333 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup280, nestingLookup333]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq280 nestingEntries_eq333]
  decide

theorem canClimb_280_351 : canClimb 280 351 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup280, nestingLookup351]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq280 nestingEntries_eq351]
  decide

theorem canClimb_280_369 : canClimb 280 369 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup280, nestingLookup369]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq280 nestingEntries_eq369]
  decide

theorem canClimb_280_382 : canClimb 280 382 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup280, nestingLookup382]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq280 nestingEntries_eq382]
  decide

theorem canClimb_280_408 : canClimb 280 408 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup280, nestingLookup408]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq280 nestingEntries_eq408]
  decide

theorem canClimb_280_419 : canClimb 280 419 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup280, nestingLookup419]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq280 nestingEntries_eq419]
  decide

theorem canClimb_281_333 : canClimb 281 333 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup281, nestingLookup333]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq281 nestingEntries_eq333]
  decide

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem canClimb_281_354 : canClimb 281 354 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup281, nestingLookup354]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq281 nestingEntries_eq354]
  decide

theorem canClimb_281_448 : canClimb 281 448 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup281, nestingLookup448]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq281 nestingEntries_eq448]
  decide

theorem canClimb_281_462 : canClimb 281 462 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup281, nestingLookup462]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq281 nestingEntries_eq462]
  decide

theorem canClimb_281_483 : canClimb 281 483 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup281, nestingLookup483]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq281 nestingEntries_eq483]
  decide

theorem canClimb_281_497 : canClimb 281 497 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup281, nestingLookup497]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq281 nestingEntries_eq497]
  decide

theorem canClimb_282_334 : canClimb 282 334 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup282, nestingLookup334]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq282 nestingEntries_eq334]
  decide

theorem canClimb_282_352 : canClimb 282 352 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup282, nestingLookup352]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq282 nestingEntries_eq352]
  decide

theorem canClimb_282_366 : canClimb 282 366 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup282, nestingLookup366]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq282 nestingEntries_eq366]
  decide

theorem canClimb_282_399 : canClimb 282 399 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup282, nestingLookup399]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq282 nestingEntries_eq399]
  decide

theorem canClimb_282_442 : canClimb 282 442 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup282, nestingLookup442]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq282 nestingEntries_eq442]
  decide

theorem canClimb_282_503 : canClimb 282 503 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup282, nestingLookup503]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq282 nestingEntries_eq503]
  decide

theorem canClimb_283_334 : canClimb 283 334 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup283, nestingLookup334]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq283 nestingEntries_eq334]
  decide

theorem canClimb_283_353 : canClimb 283 353 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup283, nestingLookup353]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq283 nestingEntries_eq353]
  decide

theorem canClimb_283_388 : canClimb 283 388 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup283, nestingLookup388]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq283 nestingEntries_eq388]
  decide

theorem canClimb_283_425 : canClimb 283 425 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup283, nestingLookup425]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq283 nestingEntries_eq425]
  decide

theorem canClimb_283_468 : canClimb 283 468 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup283, nestingLookup468]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq283 nestingEntries_eq468]
  decide

theorem canClimb_283_477 : canClimb 283 477 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup283, nestingLookup477]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq283 nestingEntries_eq477]
  decide

theorem canClimb_284_335 : canClimb 284 335 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup284, nestingLookup335]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq284 nestingEntries_eq335]
  decide

theorem canClimb_284_352 : canClimb 284 352 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup284, nestingLookup352]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq284 nestingEntries_eq352]
  decide

theorem canClimb_284_389 : canClimb 284 389 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup284, nestingLookup389]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq284 nestingEntries_eq389]
  decide

theorem canClimb_284_424 : canClimb 284 424 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup284, nestingLookup424]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq284 nestingEntries_eq424]
  decide

theorem canClimb_284_465 : canClimb 284 465 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup284, nestingLookup465]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq284 nestingEntries_eq465]
  decide

theorem canClimb_284_480 : canClimb 284 480 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup284, nestingLookup480]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq284 nestingEntries_eq480]
  decide

theorem canClimb_285_335 : canClimb 285 335 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup285, nestingLookup335]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq285 nestingEntries_eq335]
  decide

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem canClimb_285_353 : canClimb 285 353 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup285, nestingLookup353]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq285 nestingEntries_eq353]
  decide

theorem canClimb_285_363 : canClimb 285 363 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup285, nestingLookup363]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq285 nestingEntries_eq363]
  decide

theorem canClimb_285_402 : canClimb 285 402 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup285, nestingLookup402]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq285 nestingEntries_eq402]
  decide

theorem canClimb_285_443 : canClimb 285 443 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup285, nestingLookup443]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq285 nestingEntries_eq443]
  decide

theorem canClimb_285_502 : canClimb 285 502 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup285, nestingLookup502]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq285 nestingEntries_eq502]
  decide

theorem canClimb_286_336 : canClimb 286 336 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup286, nestingLookup336]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq286 nestingEntries_eq336]
  decide

theorem canClimb_286_351 : canClimb 286 351 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup286, nestingLookup351]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq286 nestingEntries_eq351]
  decide

theorem canClimb_286_449 : canClimb 286 449 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup286, nestingLookup449]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq286 nestingEntries_eq449]
  decide

theorem canClimb_286_459 : canClimb 286 459 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup286, nestingLookup459]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq286 nestingEntries_eq459]
  decide

theorem canClimb_286_486 : canClimb 286 486 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup286, nestingLookup486]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq286 nestingEntries_eq486]
  decide

theorem canClimb_286_496 : canClimb 286 496 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup286, nestingLookup496]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq286 nestingEntries_eq496]
  decide

theorem canClimb_287_336 : canClimb 287 336 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup287, nestingLookup336]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq287 nestingEntries_eq336]
  decide

theorem canClimb_287_354 : canClimb 287 354 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup287, nestingLookup354]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq287 nestingEntries_eq354]
  decide

theorem canClimb_287_372 : canClimb 287 372 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup287, nestingLookup372]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq287 nestingEntries_eq372]
  decide

theorem canClimb_287_383 : canClimb 287 383 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup287, nestingLookup383]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq287 nestingEntries_eq383]
  decide

theorem canClimb_287_405 : canClimb 287 405 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup287, nestingLookup405]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq287 nestingEntries_eq405]
  decide

theorem canClimb_287_418 : canClimb 287 418 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup287, nestingLookup418]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq287 nestingEntries_eq418]
  decide

theorem canClimb_288_337 : canClimb 288 337 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup288, nestingLookup337]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq288 nestingEntries_eq337]
  decide

theorem canClimb_288_355 : canClimb 288 355 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup288, nestingLookup355]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq288 nestingEntries_eq355]
  decide

theorem canClimb_288_378 : canClimb 288 378 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup288, nestingLookup378]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq288 nestingEntries_eq378]
  decide

theorem canClimb_288_414 : canClimb 288 414 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup288, nestingLookup414]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq288 nestingEntries_eq414]
  decide

theorem canClimb_288_456 : canClimb 288 456 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup288, nestingLookup456]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq288 nestingEntries_eq456]
  decide

theorem canClimb_288_474 : canClimb 288 474 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup288, nestingLookup474]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq288 nestingEntries_eq474]
  decide

theorem canClimb_289_337 : canClimb 289 337 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup289, nestingLookup337]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq289 nestingEntries_eq337]
  decide

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem canClimb_289_350 : canClimb 289 350 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup289, nestingLookup350]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq289 nestingEntries_eq350]
  decide

theorem canClimb_289_394 : canClimb 289 394 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup289, nestingLookup394]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq289 nestingEntries_eq394]
  decide

theorem canClimb_289_430 : canClimb 289 430 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup289, nestingLookup430]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq289 nestingEntries_eq430]
  decide

theorem canClimb_289_437 : canClimb 289 437 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup289, nestingLookup437]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq289 nestingEntries_eq437]
  decide

theorem canClimb_289_491 : canClimb 289 491 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup289, nestingLookup491]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq289 nestingEntries_eq491]
  decide

theorem canClimb_290_338 : canClimb 290 338 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup290, nestingLookup338]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq290 nestingEntries_eq338]
  decide

theorem canClimb_290_356 : canClimb 290 356 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup290, nestingLookup356]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq290 nestingEntries_eq356]
  decide

theorem canClimb_290_393 : canClimb 290 393 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup290, nestingLookup393]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq290 nestingEntries_eq393]
  decide

theorem canClimb_290_429 : canClimb 290 429 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup290, nestingLookup429]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq290 nestingEntries_eq429]
  decide

theorem canClimb_290_454 : canClimb 290 454 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup290, nestingLookup454]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq290 nestingEntries_eq454]
  decide

theorem canClimb_290_472 : canClimb 290 472 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup290, nestingLookup472]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq290 nestingEntries_eq472]
  decide

theorem canClimb_291_338 : canClimb 291 338 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup291, nestingLookup338]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq291 nestingEntries_eq338]
  decide

theorem canClimb_291_361 : canClimb 291 361 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup291, nestingLookup361]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq291 nestingEntries_eq361]
  decide

theorem canClimb_291_377 : canClimb 291 377 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup291, nestingLookup377]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq291 nestingEntries_eq377]
  decide

theorem canClimb_291_413 : canClimb 291 413 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup291, nestingLookup413]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq291 nestingEntries_eq413]
  decide

theorem canClimb_291_435 : canClimb 291 435 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup291, nestingLookup435]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq291 nestingEntries_eq435]
  decide

theorem canClimb_291_489 : canClimb 291 489 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup291, nestingLookup489]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq291 nestingEntries_eq489]
  decide

theorem canClimb_292_339 : canClimb 292 339 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup292, nestingLookup339]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq292 nestingEntries_eq339]
  decide

theorem canClimb_292_357 : canClimb 292 357 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup292, nestingLookup357]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq292 nestingEntries_eq357]
  decide

theorem canClimb_292_370 : canClimb 292 370 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup292, nestingLookup370]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq292 nestingEntries_eq370]
  decide

theorem canClimb_292_407 : canClimb 292 407 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup292, nestingLookup407]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq292 nestingEntries_eq407]
  decide

theorem canClimb_292_460 : canClimb 292 460 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup292, nestingLookup460]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq292 nestingEntries_eq460]
  decide

theorem canClimb_292_485 : canClimb 292 485 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup292, nestingLookup485]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq292 nestingEntries_eq485]
  decide

theorem canClimb_293_339 : canClimb 293 339 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup293, nestingLookup339]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq293 nestingEntries_eq339]
  decide

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem canClimb_293_360 : canClimb 293 360 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup293, nestingLookup360]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq293 nestingEntries_eq360]
  decide

theorem canClimb_293_384 : canClimb 293 384 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup293, nestingLookup384]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq293 nestingEntries_eq384]
  decide

theorem canClimb_293_417 : canClimb 293 417 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup293, nestingLookup417]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq293 nestingEntries_eq417]
  decide

theorem canClimb_293_447 : canClimb 293 447 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup293, nestingLookup447]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq293 nestingEntries_eq447]
  decide

theorem canClimb_293_498 : canClimb 293 498 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup293, nestingLookup498]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq293 nestingEntries_eq498]
  decide

theorem canClimb_294_340 : canClimb 294 340 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup294, nestingLookup340]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq294 nestingEntries_eq340]
  decide

theorem canClimb_294_358 : canClimb 294 358 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup294, nestingLookup358]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq294 nestingEntries_eq358]
  decide

theorem canClimb_294_441 : canClimb 294 441 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup294, nestingLookup441]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq294 nestingEntries_eq441]
  decide

theorem canClimb_294_466 : canClimb 294 466 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup294, nestingLookup466]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq294 nestingEntries_eq466]
  decide

theorem canClimb_294_479 : canClimb 294 479 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup294, nestingLookup479]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq294 nestingEntries_eq479]
  decide

theorem canClimb_294_504 : canClimb 294 504 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup294, nestingLookup504]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq294 nestingEntries_eq504]
  decide

theorem canClimb_295_340 : canClimb 295 340 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup295, nestingLookup340]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq295 nestingEntries_eq340]
  decide

theorem canClimb_295_359 : canClimb 295 359 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup295, nestingLookup359]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq295 nestingEntries_eq359]
  decide

theorem canClimb_295_364 : canClimb 295 364 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup295, nestingLookup364]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq295 nestingEntries_eq364]
  decide

theorem canClimb_295_387 : canClimb 295 387 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup295, nestingLookup387]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq295 nestingEntries_eq387]
  decide

theorem canClimb_295_401 : canClimb 295 401 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup295, nestingLookup401]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq295 nestingEntries_eq401]
  decide

theorem canClimb_295_426 : canClimb 295 426 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup295, nestingLookup426]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq295 nestingEntries_eq426]
  decide

theorem canClimb_296_341 : canClimb 296 341 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup296, nestingLookup341]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq296 nestingEntries_eq341]
  decide

theorem canClimb_296_358 : canClimb 296 358 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup296, nestingLookup358]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq296 nestingEntries_eq358]
  decide

theorem canClimb_296_365 : canClimb 296 365 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup296, nestingLookup365]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq296 nestingEntries_eq365]
  decide

theorem canClimb_296_390 : canClimb 296 390 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup296, nestingLookup390]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq296 nestingEntries_eq390]
  decide

theorem canClimb_296_400 : canClimb 296 400 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup296, nestingLookup400]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq296 nestingEntries_eq400]
  decide

theorem canClimb_296_423 : canClimb 296 423 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup296, nestingLookup423]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq296 nestingEntries_eq423]
  decide

theorem canClimb_297_341 : canClimb 297 341 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup297, nestingLookup341]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq297 nestingEntries_eq341]
  decide

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem canClimb_297_359 : canClimb 297 359 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup297, nestingLookup359]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq297 nestingEntries_eq359]
  decide

theorem canClimb_297_444 : canClimb 297 444 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup297, nestingLookup444]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq297 nestingEntries_eq444]
  decide

theorem canClimb_297_467 : canClimb 297 467 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup297, nestingLookup467]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq297 nestingEntries_eq467]
  decide

theorem canClimb_297_478 : canClimb 297 478 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup297, nestingLookup478]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq297 nestingEntries_eq478]
  decide

theorem canClimb_297_501 : canClimb 297 501 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup297, nestingLookup501]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq297 nestingEntries_eq501]
  decide

theorem canClimb_298_342 : canClimb 298 342 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup298, nestingLookup342]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq298 nestingEntries_eq342]
  decide

theorem canClimb_298_357 : canClimb 298 357 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup298, nestingLookup357]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq298 nestingEntries_eq357]
  decide

theorem canClimb_298_381 : canClimb 298 381 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup298, nestingLookup381]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq298 nestingEntries_eq381]
  decide

theorem canClimb_298_420 : canClimb 298 420 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup298, nestingLookup420]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq298 nestingEntries_eq420]
  decide

theorem canClimb_298_450 : canClimb 298 450 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup298, nestingLookup450]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq298 nestingEntries_eq450]
  decide

theorem canClimb_298_495 : canClimb 298 495 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup298, nestingLookup495]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq298 nestingEntries_eq495]
  decide

theorem canClimb_299_342 : canClimb 299 342 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup299, nestingLookup342]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq299 nestingEntries_eq342]
  decide

theorem canClimb_299_360 : canClimb 299 360 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup299, nestingLookup360]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq299 nestingEntries_eq360]
  decide

theorem canClimb_299_371 : canClimb 299 371 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup299, nestingLookup371]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq299 nestingEntries_eq371]
  decide

theorem canClimb_299_406 : canClimb 299 406 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup299, nestingLookup406]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq299 nestingEntries_eq406]
  decide

theorem canClimb_299_461 : canClimb 299 461 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup299, nestingLookup461]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq299 nestingEntries_eq461]
  decide

theorem canClimb_299_484 : canClimb 299 484 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup299, nestingLookup484]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq299 nestingEntries_eq484]
  decide

theorem canClimb_300_343 : canClimb 300 343 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup300, nestingLookup343]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq300 nestingEntries_eq343]
  decide

theorem canClimb_300_361 : canClimb 300 361 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup300, nestingLookup361]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq300 nestingEntries_eq361]
  decide

theorem canClimb_300_396 : canClimb 300 396 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup300, nestingLookup396]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq300 nestingEntries_eq396]
  decide

theorem canClimb_300_432 : canClimb 300 432 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup300, nestingLookup432]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq300 nestingEntries_eq432]
  decide

theorem canClimb_300_455 : canClimb 300 455 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup300, nestingLookup455]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq300 nestingEntries_eq455]
  decide

theorem canClimb_300_473 : canClimb 300 473 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup300, nestingLookup473]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq300 nestingEntries_eq473]
  decide

theorem canClimb_301_343 : canClimb 301 343 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup301, nestingLookup343]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq301 nestingEntries_eq343]
  decide

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem canClimb_301_356 : canClimb 301 356 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup301, nestingLookup356]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq301 nestingEntries_eq356]
  decide

theorem canClimb_301_376 : canClimb 301 376 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup301, nestingLookup376]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq301 nestingEntries_eq376]
  decide

theorem canClimb_301_412 : canClimb 301 412 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup301, nestingLookup412]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq301 nestingEntries_eq412]
  decide

theorem canClimb_301_438 : canClimb 301 438 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup301, nestingLookup438]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq301 nestingEntries_eq438]
  decide

theorem canClimb_301_492 : canClimb 301 492 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup301, nestingLookup492]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq301 nestingEntries_eq492]
  decide

theorem canClimb_302_362 : canClimb 302 362 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup302, nestingLookup362]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq302 nestingEntries_eq362]
  decide

theorem canClimb_302_396 : canClimb 302 396 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup302, nestingLookup396]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq302 nestingEntries_eq396]
  decide

theorem canClimb_302_403 : canClimb 302 403 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup302, nestingLookup403]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq302 nestingEntries_eq403]
  decide

theorem canClimb_302_429 : canClimb 302 429 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup302, nestingLookup429]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq302 nestingEntries_eq429]
  decide

theorem canClimb_302_448 : canClimb 302 448 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup302, nestingLookup448]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq302 nestingEntries_eq448]
  decide

theorem canClimb_302_496 : canClimb 302 496 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup302, nestingLookup496]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq302 nestingEntries_eq496]
  decide

theorem canClimb_303_363 : canClimb 303 363 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup303, nestingLookup363]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq303 nestingEntries_eq363]
  decide

theorem canClimb_303_381 : canClimb 303 381 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup303, nestingLookup381]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq303 nestingEntries_eq381]
  decide

theorem canClimb_303_399 : canClimb 303 399 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup303, nestingLookup399]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq303 nestingEntries_eq399]
  decide

theorem canClimb_303_417 : canClimb 303 417 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup303, nestingLookup417]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq303 nestingEntries_eq417]
  decide

theorem canClimb_303_457 : canClimb 303 457 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup303, nestingLookup457]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq303 nestingEntries_eq457]
  decide

theorem canClimb_303_470 : canClimb 303 470 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup303, nestingLookup470]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq303 nestingEntries_eq470]
  decide

theorem canClimb_304_364 : canClimb 304 364 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup304, nestingLookup364]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq304 nestingEntries_eq364]
  decide

theorem canClimb_304_400 : canClimb 304 400 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup304, nestingLookup400]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq304 nestingEntries_eq400]
  decide

theorem canClimb_304_437 : canClimb 304 437 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup304, nestingLookup437]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq304 nestingEntries_eq437]
  decide

theorem canClimb_304_458 : canClimb 304 458 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup304, nestingLookup458]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq304 nestingEntries_eq458]
  decide

theorem canClimb_304_487 : canClimb 304 487 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup304, nestingLookup487]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq304 nestingEntries_eq487]
  decide

theorem canClimb_304_490 : canClimb 304 490 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup304, nestingLookup490]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq304 nestingEntries_eq490]
  decide

theorem canClimb_305_365 : canClimb 305 365 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup305, nestingLookup365]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq305 nestingEntries_eq365]
  decide

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem canClimb_305_401 : canClimb 305 401 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup305, nestingLookup401]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq305 nestingEntries_eq401]
  decide

theorem canClimb_305_436 : canClimb 305 436 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup305, nestingLookup436]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq305 nestingEntries_eq436]
  decide

theorem canClimb_305_463 : canClimb 305 463 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup305, nestingLookup463]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq305 nestingEntries_eq463]
  decide

theorem canClimb_305_482 : canClimb 305 482 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup305, nestingLookup482]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq305 nestingEntries_eq482]
  decide

theorem canClimb_305_491 : canClimb 305 491 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup305, nestingLookup491]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq305 nestingEntries_eq491]
  decide

theorem canClimb_306_366 : canClimb 306 366 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup306, nestingLookup366]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq306 nestingEntries_eq366]
  decide

theorem canClimb_306_384 : canClimb 306 384 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup306, nestingLookup384]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq306 nestingEntries_eq384]
  decide

theorem canClimb_306_402 : canClimb 306 402 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup306, nestingLookup402]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq306 nestingEntries_eq402]
  decide

theorem canClimb_306_420 : canClimb 306 420 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup306, nestingLookup420]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq306 nestingEntries_eq420]
  decide

theorem canClimb_306_452 : canClimb 306 452 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup306, nestingLookup452]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq306 nestingEntries_eq452]
  decide

theorem canClimb_306_475 : canClimb 306 475 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup306, nestingLookup475]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq306 nestingEntries_eq475]
  decide

theorem canClimb_307_367 : canClimb 307 367 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup307, nestingLookup367]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq307 nestingEntries_eq367]
  decide

theorem canClimb_307_393 : canClimb 307 393 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup307, nestingLookup393]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq307 nestingEntries_eq393]
  decide

theorem canClimb_307_398 : canClimb 307 398 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup307, nestingLookup398]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq307 nestingEntries_eq398]
  decide

theorem canClimb_307_432 : canClimb 307 432 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup307, nestingLookup432]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq307 nestingEntries_eq432]
  decide

theorem canClimb_307_449 : canClimb 307 449 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup307, nestingLookup449]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq307 nestingEntries_eq449]
  decide

theorem canClimb_307_497 : canClimb 307 497 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup307, nestingLookup497]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq307 nestingEntries_eq497]
  decide

theorem canClimb_308_368 : canClimb 308 368 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup308, nestingLookup368]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq308 nestingEntries_eq368]
  decide

theorem canClimb_308_394 : canClimb 308 394 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup308, nestingLookup394]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq308 nestingEntries_eq394]
  decide

theorem canClimb_308_409 : canClimb 308 409 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup308, nestingLookup409]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq308 nestingEntries_eq409]
  decide

theorem canClimb_308_431 : canClimb 308 431 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup308, nestingLookup431]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq308 nestingEntries_eq431]
  decide

theorem canClimb_308_466 : canClimb 308 466 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup308, nestingLookup466]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq308 nestingEntries_eq466]
  decide

theorem canClimb_308_478 : canClimb 308 478 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup308, nestingLookup478]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq308 nestingEntries_eq478]
  decide

theorem canClimb_309_369 : canClimb 309 369 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup309, nestingLookup369]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq309 nestingEntries_eq369]
  decide

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem canClimb_309_405 : canClimb 309 405 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup309, nestingLookup405]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq309 nestingEntries_eq405]
  decide

theorem canClimb_309_440 : canClimb 309 440 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup309, nestingLookup440]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq309 nestingEntries_eq440]
  decide

theorem canClimb_309_454 : canClimb 309 454 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup309, nestingLookup454]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq309 nestingEntries_eq454]
  decide

theorem canClimb_309_473 : canClimb 309 473 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup309, nestingLookup473]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq309 nestingEntries_eq473]
  decide

theorem canClimb_309_505 : canClimb 309 505 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup309, nestingLookup505]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq309 nestingEntries_eq505]
  decide

theorem canClimb_310_370 : canClimb 310 370 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup310, nestingLookup370]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq310 nestingEntries_eq370]
  decide

theorem canClimb_310_389 : canClimb 310 389 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup310, nestingLookup389]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq310 nestingEntries_eq389]
  decide

theorem canClimb_310_406 : canClimb 310 406 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup310, nestingLookup406]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq310 nestingEntries_eq406]
  decide

theorem canClimb_310_425 : canClimb 310 425 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup310, nestingLookup425]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq310 nestingEntries_eq425]
  decide

theorem canClimb_310_439 : canClimb 310 439 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup310, nestingLookup439]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq310 nestingEntries_eq439]
  decide

theorem canClimb_310_488 : canClimb 310 488 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup310, nestingLookup488]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq310 nestingEntries_eq488]
  decide

theorem canClimb_311_371 : canClimb 311 371 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup311, nestingLookup371]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq311 nestingEntries_eq371]
  decide

theorem canClimb_311_388 : canClimb 311 388 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup311, nestingLookup388]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq311 nestingEntries_eq388]
  decide

theorem canClimb_311_407 : canClimb 311 407 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup311, nestingLookup407]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq311 nestingEntries_eq407]
  decide

theorem canClimb_311_424 : canClimb 311 424 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup311, nestingLookup424]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq311 nestingEntries_eq424]
  decide

theorem canClimb_311_434 : canClimb 311 434 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup311, nestingLookup434]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq311 nestingEntries_eq434]
  decide

theorem canClimb_311_493 : canClimb 311 493 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup311, nestingLookup493]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq311 nestingEntries_eq493]
  decide

theorem canClimb_312_372 : canClimb 312 372 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup312, nestingLookup372]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq312 nestingEntries_eq372]
  decide

theorem canClimb_312_408 : canClimb 312 408 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup312, nestingLookup408]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq312 nestingEntries_eq408]
  decide

theorem canClimb_312_445 : canClimb 312 445 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup312, nestingLookup445]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq312 nestingEntries_eq445]
  decide

theorem canClimb_312_455 : canClimb 312 455 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup312, nestingLookup455]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq312 nestingEntries_eq455]
  decide

theorem canClimb_312_472 : canClimb 312 472 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup312, nestingLookup472]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq312 nestingEntries_eq472]
  decide

theorem canClimb_312_500 : canClimb 312 500 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup312, nestingLookup500]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq312 nestingEntries_eq500]
  decide

theorem canClimb_313_373 : canClimb 313 373 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup313, nestingLookup373]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq313 nestingEntries_eq373]
  decide

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem canClimb_313_395 : canClimb 313 395 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup313, nestingLookup395]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq313 nestingEntries_eq395]
  decide

theorem canClimb_313_404 : canClimb 313 404 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup313, nestingLookup404]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq313 nestingEntries_eq404]
  decide

theorem canClimb_313_430 : canClimb 313 430 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup313, nestingLookup430]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq313 nestingEntries_eq430]
  decide

theorem canClimb_313_467 : canClimb 313 467 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup313, nestingLookup467]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq313 nestingEntries_eq467]
  decide

theorem canClimb_313_479 : canClimb 313 479 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup313, nestingLookup479]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq313 nestingEntries_eq479]
  decide

theorem canClimb_314_374 : canClimb 314 374 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup314, nestingLookup374]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq314 nestingEntries_eq374]
  decide

theorem canClimb_314_415 : canClimb 314 415 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup314, nestingLookup415]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq314 nestingEntries_eq415]
  decide

theorem canClimb_314_450 : canClimb 314 450 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup314, nestingLookup450]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq314 nestingEntries_eq450]
  decide

theorem canClimb_314_468 : canClimb 314 468 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup314, nestingLookup468]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq314 nestingEntries_eq468]
  decide

theorem canClimb_314_480 : canClimb 314 480 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup314, nestingLookup480]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq314 nestingEntries_eq480]
  decide

theorem canClimb_314_498 : canClimb 314 498 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup314, nestingLookup498]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq314 nestingEntries_eq498]
  decide

theorem canClimb_315_375 : canClimb 315 375 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup315, nestingLookup375]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq315 nestingEntries_eq375]
  decide

theorem canClimb_315_385 : canClimb 315 385 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup315, nestingLookup385]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq315 nestingEntries_eq385]
  decide

theorem canClimb_315_414 : canClimb 315 414 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup315, nestingLookup414]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq315 nestingEntries_eq414]
  decide

theorem canClimb_315_416 : canClimb 315 416 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup315, nestingLookup416]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq315 nestingEntries_eq416]
  decide

theorem canClimb_315_441 : canClimb 315 441 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup315, nestingLookup441]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq315 nestingEntries_eq441]
  decide

theorem canClimb_315_501 : canClimb 315 501 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup315, nestingLookup501]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq315 nestingEntries_eq501]
  decide

theorem canClimb_316_376 : canClimb 316 376 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup316, nestingLookup376]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq316 nestingEntries_eq376]
  decide

theorem canClimb_316_386 : canClimb 316 386 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup316, nestingLookup386]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq316 nestingEntries_eq386]
  decide

theorem canClimb_316_413 : canClimb 316 413 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup316, nestingLookup413]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq316 nestingEntries_eq413]
  decide

theorem canClimb_316_427 : canClimb 316 427 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup316, nestingLookup427]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq316 nestingEntries_eq427]
  decide

theorem canClimb_316_462 : canClimb 316 462 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup316, nestingLookup462]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq316 nestingEntries_eq462]
  decide

theorem canClimb_316_486 : canClimb 316 486 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup316, nestingLookup486]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq316 nestingEntries_eq486]
  decide

theorem canClimb_317_377 : canClimb 317 377 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup317, nestingLookup377]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq317 nestingEntries_eq377]
  decide

end CSL.Construction.PhysicalFramePaths


