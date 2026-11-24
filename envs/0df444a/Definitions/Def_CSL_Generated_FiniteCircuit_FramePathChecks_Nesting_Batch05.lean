-- Prove2me | Definitions.Def_CSL_Generated_FiniteCircuit_FramePathChecks_Nesting_Batch05
-- name    : CSL_Generated_FiniteCircuit_FramePathChecks_Nesting_Batch05
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T14:10:10.063772+00:00
-- url     : https://prove2.me/theorems/514e0e2f-e3e1-418f-8102-37a939baa6b2
-- title:
--   Coded sorting library: Generated / FiniteCircuit / FramePathChecks / Nesting / Batch05
-- statement:
--   Module `CodedSorting.Generated.FiniteCircuit.FramePathChecks.Nesting.Batch05` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   Generated physical-frame checks. Uncompiled until a build record exists.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Generated.FiniteCircuit.FramePathChecks.Nesting.Batch05

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Generated_FiniteCircuit_FramePathChecks_Entries_Batch00
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
theorem canClimb_436_535 : canClimb 436 535 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup436, nestingLookup535]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq436 nestingEntries_eq535]
  decide

theorem canClimb_436_632 : canClimb 436 632 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup436, nestingLookup632]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq436 nestingEntries_eq632]
  decide

theorem canClimb_437_1 : canClimb 437 1 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup437, nestingLookup001]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq437 nestingIdentity_entries]
  rw [nestingIdentity_denominator, functionNestedCheck_identity]
  decide

theorem canClimb_437_538 : canClimb 437 538 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup437, nestingLookup538]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq437 nestingEntries_eq538]
  decide

theorem canClimb_437_629 : canClimb 437 629 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup437, nestingLookup629]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq437 nestingEntries_eq629]
  decide

theorem canClimb_438_1 : canClimb 438 1 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup438, nestingLookup001]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq438 nestingIdentity_entries]
  rw [nestingIdentity_denominator, functionNestedCheck_identity]
  decide

theorem canClimb_438_538 : canClimb 438 538 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup438, nestingLookup538]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq438 nestingEntries_eq538]
  decide

theorem canClimb_438_632 : canClimb 438 632 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup438, nestingLookup632]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq438 nestingEntries_eq632]
  decide

theorem canClimb_439_1 : canClimb 439 1 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup439, nestingLookup001]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq439 nestingIdentity_entries]
  rw [nestingIdentity_denominator, functionNestedCheck_identity]
  decide

theorem canClimb_439_629 : canClimb 439 629 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup439, nestingLookup629]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq439 nestingEntries_eq629]
  decide

theorem canClimb_439_632 : canClimb 439 632 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup439, nestingLookup632]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq439 nestingEntries_eq632]
  decide

theorem canClimb_440_1 : canClimb 440 1 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup440, nestingLookup001]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq440 nestingIdentity_entries]
  rw [nestingIdentity_denominator, functionNestedCheck_identity]
  decide

theorem canClimb_440_557 : canClimb 440 557 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup440, nestingLookup557]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq440 nestingEntries_eq557]
  decide

theorem canClimb_440_559 : canClimb 440 559 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup440, nestingLookup559]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq440 nestingEntries_eq559]
  decide

theorem canClimb_441_1 : canClimb 441 1 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup441, nestingLookup001]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq441 nestingIdentity_entries]
  rw [nestingIdentity_denominator, functionNestedCheck_identity]
  decide

theorem canClimb_441_557 : canClimb 441 557 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup441, nestingLookup557]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq441 nestingEntries_eq557]
  decide

theorem canClimb_441_608 : canClimb 441 608 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup441, nestingLookup608]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq441 nestingEntries_eq608]
  decide

theorem canClimb_442_1 : canClimb 442 1 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup442, nestingLookup001]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq442 nestingIdentity_entries]
  rw [nestingIdentity_denominator, functionNestedCheck_identity]
  decide

theorem canClimb_442_557 : canClimb 442 557 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup442, nestingLookup557]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq442 nestingEntries_eq557]
  decide

theorem canClimb_442_610 : canClimb 442 610 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup442, nestingLookup610]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq442 nestingEntries_eq610]
  decide

theorem canClimb_443_1 : canClimb 443 1 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup443, nestingLookup001]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq443 nestingIdentity_entries]
  rw [nestingIdentity_denominator, functionNestedCheck_identity]
  decide

theorem canClimb_443_559 : canClimb 443 559 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup443, nestingLookup559]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq443 nestingEntries_eq559]
  decide

theorem canClimb_443_608 : canClimb 443 608 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup443, nestingLookup608]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq443 nestingEntries_eq608]
  decide

theorem canClimb_444_1 : canClimb 444 1 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup444, nestingLookup001]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq444 nestingIdentity_entries]
  rw [nestingIdentity_denominator, functionNestedCheck_identity]
  decide

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem canClimb_444_559 : canClimb 444 559 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup444, nestingLookup559]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq444 nestingEntries_eq559]
  decide

theorem canClimb_444_610 : canClimb 444 610 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup444, nestingLookup610]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq444 nestingEntries_eq610]
  decide

theorem canClimb_445_1 : canClimb 445 1 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup445, nestingLookup001]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq445 nestingIdentity_entries]
  rw [nestingIdentity_denominator, functionNestedCheck_identity]
  decide

theorem canClimb_445_608 : canClimb 445 608 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup445, nestingLookup608]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq445 nestingEntries_eq608]
  decide

theorem canClimb_445_610 : canClimb 445 610 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup445, nestingLookup610]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq445 nestingEntries_eq610]
  decide

theorem canClimb_446_1 : canClimb 446 1 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup446, nestingLookup001]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq446 nestingIdentity_entries]
  rw [nestingIdentity_denominator, functionNestedCheck_identity]
  decide

theorem canClimb_446_564 : canClimb 446 564 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup446, nestingLookup564]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq446 nestingEntries_eq564]
  decide

theorem canClimb_446_567 : canClimb 446 567 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup446, nestingLookup567]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq446 nestingEntries_eq567]
  decide

theorem canClimb_447_1 : canClimb 447 1 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup447, nestingLookup001]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq447 nestingIdentity_entries]
  rw [nestingIdentity_denominator, functionNestedCheck_identity]
  decide

theorem canClimb_447_564 : canClimb 447 564 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup447, nestingLookup564]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq447 nestingEntries_eq564]
  decide

theorem canClimb_447_601 : canClimb 447 601 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup447, nestingLookup601]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq447 nestingEntries_eq601]
  decide

theorem canClimb_448_1 : canClimb 448 1 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup448, nestingLookup001]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq448 nestingIdentity_entries]
  rw [nestingIdentity_denominator, functionNestedCheck_identity]
  decide

theorem canClimb_448_564 : canClimb 448 564 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup448, nestingLookup564]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq448 nestingEntries_eq564]
  decide

theorem canClimb_448_604 : canClimb 448 604 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup448, nestingLookup604]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq448 nestingEntries_eq604]
  decide

theorem canClimb_449_1 : canClimb 449 1 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup449, nestingLookup001]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq449 nestingIdentity_entries]
  rw [nestingIdentity_denominator, functionNestedCheck_identity]
  decide

theorem canClimb_449_567 : canClimb 449 567 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup449, nestingLookup567]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq449 nestingEntries_eq567]
  decide

theorem canClimb_449_601 : canClimb 449 601 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup449, nestingLookup601]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq449 nestingEntries_eq601]
  decide

theorem canClimb_450_1 : canClimb 450 1 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup450, nestingLookup001]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq450 nestingIdentity_entries]
  rw [nestingIdentity_denominator, functionNestedCheck_identity]
  decide

theorem canClimb_450_567 : canClimb 450 567 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup450, nestingLookup567]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq450 nestingEntries_eq567]
  decide

theorem canClimb_450_604 : canClimb 450 604 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup450, nestingLookup604]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq450 nestingEntries_eq604]
  decide

theorem canClimb_451_1 : canClimb 451 1 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup451, nestingLookup001]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq451 nestingIdentity_entries]
  rw [nestingIdentity_denominator, functionNestedCheck_identity]
  decide

theorem canClimb_451_601 : canClimb 451 601 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup451, nestingLookup601]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq451 nestingEntries_eq601]
  decide

theorem canClimb_451_604 : canClimb 451 604 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup451, nestingLookup604]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq451 nestingEntries_eq604]
  decide

theorem canClimb_452_1 : canClimb 452 1 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup452, nestingLookup001]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq452 nestingIdentity_entries]
  rw [nestingIdentity_denominator, functionNestedCheck_identity]
  decide

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem canClimb_452_526 : canClimb 452 526 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup452, nestingLookup526]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq452 nestingEntries_eq526]
  decide

theorem canClimb_452_532 : canClimb 452 532 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup452, nestingLookup532]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq452 nestingEntries_eq532]
  decide

theorem canClimb_453_1 : canClimb 453 1 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup453, nestingLookup001]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq453 nestingIdentity_entries]
  rw [nestingIdentity_denominator, functionNestedCheck_identity]
  decide

theorem canClimb_453_526 : canClimb 453 526 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup453, nestingLookup526]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq453 nestingEntries_eq526]
  decide

theorem canClimb_453_631 : canClimb 453 631 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup453, nestingLookup631]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq453 nestingEntries_eq631]
  decide

theorem canClimb_454_1 : canClimb 454 1 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup454, nestingLookup001]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq454 nestingIdentity_entries]
  rw [nestingIdentity_denominator, functionNestedCheck_identity]
  decide

theorem canClimb_454_526 : canClimb 454 526 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup454, nestingLookup526]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq454 nestingEntries_eq526]
  decide

theorem canClimb_454_633 : canClimb 454 633 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup454, nestingLookup633]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq454 nestingEntries_eq633]
  decide

theorem canClimb_455_1 : canClimb 455 1 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup455, nestingLookup001]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq455 nestingIdentity_entries]
  rw [nestingIdentity_denominator, functionNestedCheck_identity]
  decide

theorem canClimb_455_532 : canClimb 455 532 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup455, nestingLookup532]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq455 nestingEntries_eq532]
  decide

theorem canClimb_455_631 : canClimb 455 631 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup455, nestingLookup631]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq455 nestingEntries_eq631]
  decide

theorem canClimb_456_1 : canClimb 456 1 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup456, nestingLookup001]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq456 nestingIdentity_entries]
  rw [nestingIdentity_denominator, functionNestedCheck_identity]
  decide

theorem canClimb_456_532 : canClimb 456 532 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup456, nestingLookup532]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq456 nestingEntries_eq532]
  decide

theorem canClimb_456_633 : canClimb 456 633 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup456, nestingLookup633]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq456 nestingEntries_eq633]
  decide

theorem canClimb_457_1 : canClimb 457 1 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup457, nestingLookup001]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq457 nestingIdentity_entries]
  rw [nestingIdentity_denominator, functionNestedCheck_identity]
  decide

theorem canClimb_457_631 : canClimb 457 631 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup457, nestingLookup631]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq457 nestingEntries_eq631]
  decide

theorem canClimb_457_633 : canClimb 457 633 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup457, nestingLookup633]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq457 nestingEntries_eq633]
  decide

theorem canClimb_458_1 : canClimb 458 1 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup458, nestingLookup001]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq458 nestingIdentity_entries]
  rw [nestingIdentity_denominator, functionNestedCheck_identity]
  decide

theorem canClimb_458_549 : canClimb 458 549 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup458, nestingLookup549]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq458 nestingEntries_eq549]
  decide

theorem canClimb_458_554 : canClimb 458 554 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup458, nestingLookup554]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq458 nestingEntries_eq554]
  decide

theorem canClimb_459_1 : canClimb 459 1 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup459, nestingLookup001]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq459 nestingIdentity_entries]
  rw [nestingIdentity_denominator, functionNestedCheck_identity]
  decide

theorem canClimb_459_549 : canClimb 459 549 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup459, nestingLookup549]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq459 nestingEntries_eq549]
  decide

theorem canClimb_459_624 : canClimb 459 624 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup459, nestingLookup624]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq459 nestingEntries_eq624]
  decide

theorem canClimb_460_1 : canClimb 460 1 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup460, nestingLookup001]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq460 nestingIdentity_entries]
  rw [nestingIdentity_denominator, functionNestedCheck_identity]
  decide

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem canClimb_460_549 : canClimb 460 549 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup460, nestingLookup549]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq460 nestingEntries_eq549]
  decide

theorem canClimb_460_626 : canClimb 460 626 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup460, nestingLookup626]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq460 nestingEntries_eq626]
  decide

theorem canClimb_461_1 : canClimb 461 1 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup461, nestingLookup001]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq461 nestingIdentity_entries]
  rw [nestingIdentity_denominator, functionNestedCheck_identity]
  decide

theorem canClimb_461_554 : canClimb 461 554 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup461, nestingLookup554]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq461 nestingEntries_eq554]
  decide

theorem canClimb_461_624 : canClimb 461 624 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup461, nestingLookup624]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq461 nestingEntries_eq624]
  decide

theorem canClimb_462_1 : canClimb 462 1 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup462, nestingLookup001]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq462 nestingIdentity_entries]
  rw [nestingIdentity_denominator, functionNestedCheck_identity]
  decide

theorem canClimb_462_554 : canClimb 462 554 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup462, nestingLookup554]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq462 nestingEntries_eq554]
  decide

theorem canClimb_462_626 : canClimb 462 626 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup462, nestingLookup626]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq462 nestingEntries_eq626]
  decide

theorem canClimb_463_1 : canClimb 463 1 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup463, nestingLookup001]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq463 nestingIdentity_entries]
  rw [nestingIdentity_denominator, functionNestedCheck_identity]
  decide

theorem canClimb_463_624 : canClimb 463 624 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup463, nestingLookup624]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq463 nestingEntries_eq624]
  decide

theorem canClimb_463_626 : canClimb 463 626 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup463, nestingLookup626]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq463 nestingEntries_eq626]
  decide

theorem canClimb_464_1 : canClimb 464 1 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup464, nestingLookup001]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq464 nestingIdentity_entries]
  rw [nestingIdentity_denominator, functionNestedCheck_identity]
  decide

theorem canClimb_464_550 : canClimb 464 550 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup464, nestingLookup550]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq464 nestingEntries_eq550]
  decide

theorem canClimb_464_553 : canClimb 464 553 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup464, nestingLookup553]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq464 nestingEntries_eq553]
  decide

theorem canClimb_465_1 : canClimb 465 1 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup465, nestingLookup001]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq465 nestingIdentity_entries]
  rw [nestingIdentity_denominator, functionNestedCheck_identity]
  decide

theorem canClimb_465_550 : canClimb 465 550 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup465, nestingLookup550]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq465 nestingEntries_eq550]
  decide

theorem canClimb_465_623 : canClimb 465 623 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup465, nestingLookup623]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq465 nestingEntries_eq623]
  decide

theorem canClimb_466_1 : canClimb 466 1 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup466, nestingLookup001]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq466 nestingIdentity_entries]
  rw [nestingIdentity_denominator, functionNestedCheck_identity]
  decide

theorem canClimb_466_550 : canClimb 466 550 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup466, nestingLookup550]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq466 nestingEntries_eq550]
  decide

theorem canClimb_466_625 : canClimb 466 625 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup466, nestingLookup625]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq466 nestingEntries_eq625]
  decide

theorem canClimb_467_1 : canClimb 467 1 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup467, nestingLookup001]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq467 nestingIdentity_entries]
  rw [nestingIdentity_denominator, functionNestedCheck_identity]
  decide

theorem canClimb_467_553 : canClimb 467 553 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup467, nestingLookup553]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq467 nestingEntries_eq553]
  decide

theorem canClimb_467_623 : canClimb 467 623 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup467, nestingLookup623]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq467 nestingEntries_eq623]
  decide

theorem canClimb_468_1 : canClimb 468 1 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup468, nestingLookup001]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq468 nestingIdentity_entries]
  rw [nestingIdentity_denominator, functionNestedCheck_identity]
  decide

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem canClimb_468_553 : canClimb 468 553 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup468, nestingLookup553]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq468 nestingEntries_eq553]
  decide

theorem canClimb_468_625 : canClimb 468 625 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup468, nestingLookup625]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq468 nestingEntries_eq625]
  decide

theorem canClimb_469_1 : canClimb 469 1 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup469, nestingLookup001]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq469 nestingIdentity_entries]
  rw [nestingIdentity_denominator, functionNestedCheck_identity]
  decide

theorem canClimb_469_623 : canClimb 469 623 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup469, nestingLookup623]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq469 nestingEntries_eq623]
  decide

theorem canClimb_469_625 : canClimb 469 625 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup469, nestingLookup625]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq469 nestingEntries_eq625]
  decide

theorem canClimb_470_1 : canClimb 470 1 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup470, nestingLookup001]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq470 nestingIdentity_entries]
  rw [nestingIdentity_denominator, functionNestedCheck_identity]
  decide

theorem canClimb_470_527 : canClimb 470 527 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup470, nestingLookup527]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq470 nestingEntries_eq527]
  decide

theorem canClimb_470_529 : canClimb 470 529 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup470, nestingLookup529]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq470 nestingEntries_eq529]
  decide

theorem canClimb_471_1 : canClimb 471 1 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup471, nestingLookup001]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq471 nestingIdentity_entries]
  rw [nestingIdentity_denominator, functionNestedCheck_identity]
  decide

theorem canClimb_471_527 : canClimb 471 527 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup471, nestingLookup527]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq471 nestingEntries_eq527]
  decide

theorem canClimb_471_628 : canClimb 471 628 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup471, nestingLookup628]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq471 nestingEntries_eq628]
  decide

theorem canClimb_472_1 : canClimb 472 1 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup472, nestingLookup001]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq472 nestingIdentity_entries]
  rw [nestingIdentity_denominator, functionNestedCheck_identity]
  decide

theorem canClimb_472_527 : canClimb 472 527 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup472, nestingLookup527]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq472 nestingEntries_eq527]
  decide

theorem canClimb_472_634 : canClimb 472 634 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup472, nestingLookup634]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq472 nestingEntries_eq634]
  decide

theorem canClimb_473_1 : canClimb 473 1 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup473, nestingLookup001]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq473 nestingIdentity_entries]
  rw [nestingIdentity_denominator, functionNestedCheck_identity]
  decide

theorem canClimb_473_529 : canClimb 473 529 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup473, nestingLookup529]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq473 nestingEntries_eq529]
  decide

theorem canClimb_473_628 : canClimb 473 628 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup473, nestingLookup628]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq473 nestingEntries_eq628]
  decide

theorem canClimb_474_1 : canClimb 474 1 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup474, nestingLookup001]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq474 nestingIdentity_entries]
  rw [nestingIdentity_denominator, functionNestedCheck_identity]
  decide

theorem canClimb_474_529 : canClimb 474 529 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup474, nestingLookup529]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq474 nestingEntries_eq529]
  decide

theorem canClimb_474_634 : canClimb 474 634 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup474, nestingLookup634]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq474 nestingEntries_eq634]
  decide

theorem canClimb_475_1 : canClimb 475 1 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup475, nestingLookup001]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq475 nestingIdentity_entries]
  rw [nestingIdentity_denominator, functionNestedCheck_identity]
  decide

theorem canClimb_475_628 : canClimb 475 628 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup475, nestingLookup628]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq475 nestingEntries_eq628]
  decide

theorem canClimb_475_634 : canClimb 475 634 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup475, nestingLookup634]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq475 nestingEntries_eq634]
  decide

theorem canClimb_476_1 : canClimb 476 1 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup476, nestingLookup001]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq476 nestingIdentity_entries]
  rw [nestingIdentity_denominator, functionNestedCheck_identity]
  decide

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem canClimb_476_539 : canClimb 476 539 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup476, nestingLookup539]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq476 nestingEntries_eq539]
  decide

theorem canClimb_476_545 : canClimb 476 545 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup476, nestingLookup545]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq476 nestingEntries_eq545]
  decide

theorem canClimb_477_1 : canClimb 477 1 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup477, nestingLookup001]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq477 nestingIdentity_entries]
  rw [nestingIdentity_denominator, functionNestedCheck_identity]
  decide

theorem canClimb_477_539 : canClimb 477 539 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup477, nestingLookup539]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq477 nestingEntries_eq539]
  decide

theorem canClimb_477_615 : canClimb 477 615 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup477, nestingLookup615]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq477 nestingEntries_eq615]
  decide

theorem canClimb_478_1 : canClimb 478 1 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup478, nestingLookup001]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq478 nestingIdentity_entries]
  rw [nestingIdentity_denominator, functionNestedCheck_identity]
  decide

theorem canClimb_478_539 : canClimb 478 539 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup478, nestingLookup539]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq478 nestingEntries_eq539]
  decide

theorem canClimb_478_620 : canClimb 478 620 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup478, nestingLookup620]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq478 nestingEntries_eq620]
  decide

theorem canClimb_479_1 : canClimb 479 1 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup479, nestingLookup001]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq479 nestingIdentity_entries]
  rw [nestingIdentity_denominator, functionNestedCheck_identity]
  decide

theorem canClimb_479_545 : canClimb 479 545 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup479, nestingLookup545]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq479 nestingEntries_eq545]
  decide

theorem canClimb_479_615 : canClimb 479 615 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup479, nestingLookup615]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq479 nestingEntries_eq615]
  decide

theorem canClimb_480_1 : canClimb 480 1 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup480, nestingLookup001]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq480 nestingIdentity_entries]
  rw [nestingIdentity_denominator, functionNestedCheck_identity]
  decide

theorem canClimb_480_545 : canClimb 480 545 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup480, nestingLookup545]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq480 nestingEntries_eq545]
  decide

theorem canClimb_480_620 : canClimb 480 620 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup480, nestingLookup620]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq480 nestingEntries_eq620]
  decide

theorem canClimb_481_1 : canClimb 481 1 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup481, nestingLookup001]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq481 nestingIdentity_entries]
  rw [nestingIdentity_denominator, functionNestedCheck_identity]
  decide

theorem canClimb_481_615 : canClimb 481 615 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup481, nestingLookup615]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq481 nestingEntries_eq615]
  decide

theorem canClimb_481_620 : canClimb 481 620 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup481, nestingLookup620]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq481 nestingEntries_eq620]
  decide

theorem canClimb_482_1 : canClimb 482 1 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup482, nestingLookup001]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq482 nestingIdentity_entries]
  rw [nestingIdentity_denominator, functionNestedCheck_identity]
  decide

theorem canClimb_482_541 : canClimb 482 541 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup482, nestingLookup541]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq482 nestingEntries_eq541]
  decide

theorem canClimb_482_543 : canClimb 482 543 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup482, nestingLookup543]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq482 nestingEntries_eq543]
  decide

theorem canClimb_483_1 : canClimb 483 1 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup483, nestingLookup001]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq483 nestingIdentity_entries]
  rw [nestingIdentity_denominator, functionNestedCheck_identity]
  decide

theorem canClimb_483_541 : canClimb 483 541 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup483, nestingLookup541]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq483 nestingEntries_eq541]
  decide

theorem canClimb_483_613 : canClimb 483 613 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup483, nestingLookup613]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq483 nestingEntries_eq613]
  decide

theorem canClimb_484_1 : canClimb 484 1 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup484, nestingLookup001]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq484 nestingIdentity_entries]
  rw [nestingIdentity_denominator, functionNestedCheck_identity]
  decide

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem canClimb_484_541 : canClimb 484 541 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup484, nestingLookup541]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq484 nestingEntries_eq541]
  decide

theorem canClimb_484_618 : canClimb 484 618 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup484, nestingLookup618]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq484 nestingEntries_eq618]
  decide

theorem canClimb_485_1 : canClimb 485 1 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup485, nestingLookup001]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq485 nestingIdentity_entries]
  rw [nestingIdentity_denominator, functionNestedCheck_identity]
  decide

theorem canClimb_485_543 : canClimb 485 543 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup485, nestingLookup543]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq485 nestingEntries_eq543]
  decide

theorem canClimb_485_613 : canClimb 485 613 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup485, nestingLookup613]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq485 nestingEntries_eq613]
  decide

theorem canClimb_486_1 : canClimb 486 1 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup486, nestingLookup001]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq486 nestingIdentity_entries]
  rw [nestingIdentity_denominator, functionNestedCheck_identity]
  decide

theorem canClimb_486_543 : canClimb 486 543 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup486, nestingLookup543]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq486 nestingEntries_eq543]
  decide

theorem canClimb_486_618 : canClimb 486 618 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup486, nestingLookup618]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq486 nestingEntries_eq618]
  decide

theorem canClimb_487_1 : canClimb 487 1 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup487, nestingLookup001]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq487 nestingIdentity_entries]
  rw [nestingIdentity_denominator, functionNestedCheck_identity]
  decide

theorem canClimb_487_613 : canClimb 487 613 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup487, nestingLookup613]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq487 nestingEntries_eq613]
  decide

theorem canClimb_487_618 : canClimb 487 618 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup487, nestingLookup618]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq487 nestingEntries_eq618]
  decide

theorem canClimb_488_1 : canClimb 488 1 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup488, nestingLookup001]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq488 nestingIdentity_entries]
  rw [nestingIdentity_denominator, functionNestedCheck_identity]
  decide

theorem canClimb_488_533 : canClimb 488 533 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup488, nestingLookup533]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq488 nestingEntries_eq533]
  decide

theorem canClimb_488_537 : canClimb 488 537 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup488, nestingLookup537]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq488 nestingEntries_eq537]
  decide

theorem canClimb_489_1 : canClimb 489 1 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup489, nestingLookup001]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq489 nestingIdentity_entries]
  rw [nestingIdentity_denominator, functionNestedCheck_identity]
  decide

theorem canClimb_489_533 : canClimb 489 533 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup489, nestingLookup533]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq489 nestingEntries_eq533]
  decide

theorem canClimb_489_630 : canClimb 489 630 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup489, nestingLookup630]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq489 nestingEntries_eq630]
  decide

theorem canClimb_490_1 : canClimb 490 1 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup490, nestingLookup001]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq490 nestingIdentity_entries]
  rw [nestingIdentity_denominator, functionNestedCheck_identity]
  decide

theorem canClimb_490_533 : canClimb 490 533 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup490, nestingLookup533]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq490 nestingEntries_eq533]
  decide

theorem canClimb_490_635 : canClimb 490 635 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup490, nestingLookup635]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq490 nestingEntries_eq635]
  decide

theorem canClimb_491_1 : canClimb 491 1 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup491, nestingLookup001]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq491 nestingIdentity_entries]
  rw [nestingIdentity_denominator, functionNestedCheck_identity]
  decide

theorem canClimb_491_537 : canClimb 491 537 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup491, nestingLookup537]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq491 nestingEntries_eq537]
  decide

theorem canClimb_491_630 : canClimb 491 630 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup491, nestingLookup630]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq491 nestingEntries_eq630]
  decide

theorem canClimb_492_1 : canClimb 492 1 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup492, nestingLookup001]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq492 nestingIdentity_entries]
  rw [nestingIdentity_denominator, functionNestedCheck_identity]
  decide

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem canClimb_492_537 : canClimb 492 537 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup492, nestingLookup537]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq492 nestingEntries_eq537]
  decide

theorem canClimb_492_635 : canClimb 492 635 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup492, nestingLookup635]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq492 nestingEntries_eq635]
  decide

theorem canClimb_493_1 : canClimb 493 1 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup493, nestingLookup001]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq493 nestingIdentity_entries]
  rw [nestingIdentity_denominator, functionNestedCheck_identity]
  decide

theorem canClimb_493_630 : canClimb 493 630 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup493, nestingLookup630]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq493 nestingEntries_eq630]
  decide

theorem canClimb_493_635 : canClimb 493 635 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup493, nestingLookup635]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq493 nestingEntries_eq635]
  decide

theorem canClimb_494_1 : canClimb 494 1 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup494, nestingLookup001]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq494 nestingIdentity_entries]
  rw [nestingIdentity_denominator, functionNestedCheck_identity]
  decide

theorem canClimb_494_556 : canClimb 494 556 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup494, nestingLookup556]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq494 nestingEntries_eq556]
  decide

theorem canClimb_494_562 : canClimb 494 562 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup494, nestingLookup562]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq494 nestingEntries_eq562]
  decide

theorem canClimb_495_1 : canClimb 495 1 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup495, nestingLookup001]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq495 nestingIdentity_entries]
  rw [nestingIdentity_denominator, functionNestedCheck_identity]
  decide

theorem canClimb_495_556 : canClimb 495 556 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup495, nestingLookup556]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq495 nestingEntries_eq556]
  decide

theorem canClimb_495_606 : canClimb 495 606 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup495, nestingLookup606]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq495 nestingEntries_eq606]
  decide

theorem canClimb_496_1 : canClimb 496 1 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup496, nestingLookup001]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq496 nestingIdentity_entries]
  rw [nestingIdentity_denominator, functionNestedCheck_identity]
  decide

theorem canClimb_496_556 : canClimb 496 556 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup496, nestingLookup556]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq496 nestingEntries_eq556]
  decide

theorem canClimb_496_611 : canClimb 496 611 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup496, nestingLookup611]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq496 nestingEntries_eq611]
  decide

theorem canClimb_497_1 : canClimb 497 1 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup497, nestingLookup001]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq497 nestingIdentity_entries]
  rw [nestingIdentity_denominator, functionNestedCheck_identity]
  decide

theorem canClimb_497_562 : canClimb 497 562 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup497, nestingLookup562]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq497 nestingEntries_eq562]
  decide

theorem canClimb_497_606 : canClimb 497 606 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup497, nestingLookup606]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq497 nestingEntries_eq606]
  decide

theorem canClimb_498_1 : canClimb 498 1 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup498, nestingLookup001]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq498 nestingIdentity_entries]
  rw [nestingIdentity_denominator, functionNestedCheck_identity]
  decide

theorem canClimb_498_562 : canClimb 498 562 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup498, nestingLookup562]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq498 nestingEntries_eq562]
  decide

theorem canClimb_498_611 : canClimb 498 611 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup498, nestingLookup611]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq498 nestingEntries_eq611]
  decide

theorem canClimb_499_1 : canClimb 499 1 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup499, nestingLookup001]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq499 nestingIdentity_entries]
  rw [nestingIdentity_denominator, functionNestedCheck_identity]
  decide

theorem canClimb_499_606 : canClimb 499 606 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup499, nestingLookup606]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq499 nestingEntries_eq606]
  decide

theorem canClimb_499_611 : canClimb 499 611 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup499, nestingLookup611]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq499 nestingEntries_eq611]
  decide

theorem canClimb_500_1 : canClimb 500 1 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup500, nestingLookup001]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq500 nestingIdentity_entries]
  rw [nestingIdentity_denominator, functionNestedCheck_identity]
  decide

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem canClimb_500_565 : canClimb 500 565 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup500, nestingLookup565]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq500 nestingEntries_eq565]
  decide

theorem canClimb_500_570 : canClimb 500 570 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup500, nestingLookup570]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq500 nestingEntries_eq570]
  decide

theorem canClimb_501_1 : canClimb 501 1 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup501, nestingLookup001]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq501 nestingIdentity_entries]
  rw [nestingIdentity_denominator, functionNestedCheck_identity]
  decide

theorem canClimb_501_565 : canClimb 501 565 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup501, nestingLookup565]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq501 nestingEntries_eq565]
  decide

theorem canClimb_501_598 : canClimb 501 598 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup501, nestingLookup598]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq501 nestingEntries_eq598]
  decide

theorem canClimb_502_1 : canClimb 502 1 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup502, nestingLookup001]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq502 nestingIdentity_entries]
  rw [nestingIdentity_denominator, functionNestedCheck_identity]
  decide

theorem canClimb_502_565 : canClimb 502 565 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup502, nestingLookup565]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq502 nestingEntries_eq565]
  decide

theorem canClimb_502_603 : canClimb 502 603 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup502, nestingLookup603]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq502 nestingEntries_eq603]
  decide

theorem canClimb_503_1 : canClimb 503 1 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup503, nestingLookup001]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq503 nestingIdentity_entries]
  rw [nestingIdentity_denominator, functionNestedCheck_identity]
  decide

theorem canClimb_503_570 : canClimb 503 570 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup503, nestingLookup570]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq503 nestingEntries_eq570]
  decide

theorem canClimb_503_598 : canClimb 503 598 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup503, nestingLookup598]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq503 nestingEntries_eq598]
  decide

theorem canClimb_504_1 : canClimb 504 1 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup504, nestingLookup001]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq504 nestingIdentity_entries]
  rw [nestingIdentity_denominator, functionNestedCheck_identity]
  decide

theorem canClimb_504_570 : canClimb 504 570 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup504, nestingLookup570]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq504 nestingEntries_eq570]
  decide

theorem canClimb_504_603 : canClimb 504 603 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup504, nestingLookup603]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq504 nestingEntries_eq603]
  decide

theorem canClimb_505_1 : canClimb 505 1 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup505, nestingLookup001]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq505 nestingIdentity_entries]
  rw [nestingIdentity_denominator, functionNestedCheck_identity]
  decide

theorem canClimb_505_598 : canClimb 505 598 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup505, nestingLookup598]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq505 nestingEntries_eq598]
  decide

theorem canClimb_505_603 : canClimb 505 603 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup505, nestingLookup603]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq505 nestingEntries_eq603]
  decide

theorem canClimb_506_1 : canClimb 506 1 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup506, nestingLookup001]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq506 nestingIdentity_entries]
  rw [nestingIdentity_denominator, functionNestedCheck_identity]
  decide

theorem canClimb_506_344 : canClimb 506 344 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup506, nestingLookup344]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq506 nestingEntries_eq344]
  decide

theorem canClimb_506_345 : canClimb 506 345 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup506, nestingLookup345]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq506 nestingEntries_eq345]
  decide

theorem canClimb_506_347 : canClimb 506 347 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup506, nestingLookup347]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq506 nestingEntries_eq347]
  decide

theorem canClimb_506_348 : canClimb 506 348 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup506, nestingLookup348]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq506 nestingEntries_eq348]
  decide

theorem canClimb_506_349 : canClimb 506 349 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup506, nestingLookup349]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq506 nestingEntries_eq349]
  decide

theorem canClimb_506_351 : canClimb 506 351 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup506, nestingLookup351]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq506 nestingEntries_eq351]
  decide

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem canClimb_506_352 : canClimb 506 352 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup506, nestingLookup352]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq506 nestingEntries_eq352]
  decide

theorem canClimb_506_353 : canClimb 506 353 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup506, nestingLookup353]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq506 nestingEntries_eq353]
  decide

theorem canClimb_506_354 : canClimb 506 354 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup506, nestingLookup354]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq506 nestingEntries_eq354]
  decide

theorem canClimb_506_355 : canClimb 506 355 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup506, nestingLookup355]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq506 nestingEntries_eq355]
  decide

theorem canClimb_506_356 : canClimb 506 356 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup506, nestingLookup356]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq506 nestingEntries_eq356]
  decide

theorem canClimb_506_357 : canClimb 506 357 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup506, nestingLookup357]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq506 nestingEntries_eq357]
  decide

theorem canClimb_506_358 : canClimb 506 358 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup506, nestingLookup358]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq506 nestingEntries_eq358]
  decide

theorem canClimb_506_360 : canClimb 506 360 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup506, nestingLookup360]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq506 nestingEntries_eq360]
  decide

theorem canClimb_506_361 : canClimb 506 361 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup506, nestingLookup361]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq506 nestingEntries_eq361]
  decide

theorem canClimb_507_326 : canClimb 507 326 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup507, nestingLookup326]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq507 nestingEntries_eq326]
  decide

theorem canClimb_507_327 : canClimb 507 327 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup507, nestingLookup327]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq507 nestingEntries_eq327]
  decide

theorem canClimb_507_329 : canClimb 507 329 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup507, nestingLookup329]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq507 nestingEntries_eq329]
  decide

theorem canClimb_507_330 : canClimb 507 330 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup507, nestingLookup330]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq507 nestingEntries_eq330]
  decide

theorem canClimb_507_331 : canClimb 507 331 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup507, nestingLookup331]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq507 nestingEntries_eq331]
  decide

theorem canClimb_507_332 : canClimb 507 332 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup507, nestingLookup332]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq507 nestingEntries_eq332]
  decide

theorem canClimb_507_333 : canClimb 507 333 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup507, nestingLookup333]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq507 nestingEntries_eq333]
  decide

theorem canClimb_507_334 : canClimb 507 334 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup507, nestingLookup334]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq507 nestingEntries_eq334]
  decide

theorem canClimb_507_337 : canClimb 507 337 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup507, nestingLookup337]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq507 nestingEntries_eq337]
  decide

theorem canClimb_507_338 : canClimb 507 338 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup507, nestingLookup338]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq507 nestingEntries_eq338]
  decide

theorem canClimb_507_339 : canClimb 507 339 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup507, nestingLookup339]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq507 nestingEntries_eq339]
  decide

theorem canClimb_507_340 : canClimb 507 340 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup507, nestingLookup340]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq507 nestingEntries_eq340]
  decide

theorem canClimb_507_341 : canClimb 507 341 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup507, nestingLookup341]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq507 nestingEntries_eq341]
  decide

theorem canClimb_507_342 : canClimb 507 342 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup507, nestingLookup342]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq507 nestingEntries_eq342]
  decide

theorem canClimb_507_343 : canClimb 507 343 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup507, nestingLookup343]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq507 nestingEntries_eq343]
  decide

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem canClimb_508_1 : canClimb 508 1 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup508, nestingLookup001]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq508 nestingIdentity_entries]
  rw [nestingIdentity_denominator, functionNestedCheck_identity]
  decide

theorem canClimb_508_416 : canClimb 508 416 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup508, nestingLookup416]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq508 nestingEntries_eq416]
  decide

theorem canClimb_508_417 : canClimb 508 417 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup508, nestingLookup417]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq508 nestingEntries_eq417]
  decide

theorem canClimb_508_418 : canClimb 508 418 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup508, nestingLookup418]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq508 nestingEntries_eq418]
  decide

theorem canClimb_508_419 : canClimb 508 419 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup508, nestingLookup419]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq508 nestingEntries_eq419]
  decide

theorem canClimb_508_420 : canClimb 508 420 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup508, nestingLookup420]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq508 nestingEntries_eq420]
  decide

theorem canClimb_508_422 : canClimb 508 422 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup508, nestingLookup422]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq508 nestingEntries_eq422]
  decide

theorem canClimb_508_423 : canClimb 508 423 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup508, nestingLookup423]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq508 nestingEntries_eq423]
  decide

theorem canClimb_508_424 : canClimb 508 424 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup508, nestingLookup424]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq508 nestingEntries_eq424]
  decide

theorem canClimb_508_425 : canClimb 508 425 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup508, nestingLookup425]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq508 nestingEntries_eq425]
  decide

theorem canClimb_508_426 : canClimb 508 426 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup508, nestingLookup426]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq508 nestingEntries_eq426]
  decide

theorem canClimb_508_427 : canClimb 508 427 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup508, nestingLookup427]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq508 nestingEntries_eq427]
  decide

theorem canClimb_508_428 : canClimb 508 428 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup508, nestingLookup428]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq508 nestingEntries_eq428]
  decide

theorem canClimb_508_429 : canClimb 508 429 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup508, nestingLookup429]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq508 nestingEntries_eq429]
  decide

theorem canClimb_508_430 : canClimb 508 430 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup508, nestingLookup430]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq508 nestingEntries_eq430]
  decide

theorem canClimb_508_432 : canClimb 508 432 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup508, nestingLookup432]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq508 nestingEntries_eq432]
  decide

theorem canClimb_508_433 : canClimb 508 433 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup508, nestingLookup433]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq508 nestingEntries_eq433]
  decide

theorem canClimb_509_1 : canClimb 509 1 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup509, nestingLookup001]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq509 nestingIdentity_entries]
  rw [nestingIdentity_denominator, functionNestedCheck_identity]
  decide

theorem canClimb_509_380 : canClimb 509 380 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup509, nestingLookup380]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq509 nestingEntries_eq380]
  decide

theorem canClimb_509_381 : canClimb 509 381 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup509, nestingLookup381]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq509 nestingEntries_eq381]
  decide

theorem canClimb_509_382 : canClimb 509 382 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup509, nestingLookup382]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq509 nestingEntries_eq382]
  decide

theorem canClimb_509_383 : canClimb 509 383 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup509, nestingLookup383]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq509 nestingEntries_eq383]
  decide

theorem canClimb_509_384 : canClimb 509 384 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup509, nestingLookup384]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq509 nestingEntries_eq384]
  decide

theorem canClimb_509_385 : canClimb 509 385 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup509, nestingLookup385]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq509 nestingEntries_eq385]
  decide

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem canClimb_509_386 : canClimb 509 386 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup509, nestingLookup386]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq509 nestingEntries_eq386]
  decide

theorem canClimb_509_387 : canClimb 509 387 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup509, nestingLookup387]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq509 nestingEntries_eq387]
  decide

theorem canClimb_509_389 : canClimb 509 389 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup509, nestingLookup389]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq509 nestingEntries_eq389]
  decide

theorem canClimb_509_390 : canClimb 509 390 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup509, nestingLookup390]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq509 nestingEntries_eq390]
  decide

theorem canClimb_509_391 : canClimb 509 391 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup509, nestingLookup391]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq509 nestingEntries_eq391]
  decide

theorem canClimb_509_392 : canClimb 509 392 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup509, nestingLookup392]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq509 nestingEntries_eq392]
  decide

theorem canClimb_509_393 : canClimb 509 393 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup509, nestingLookup393]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq509 nestingEntries_eq393]
  decide

theorem canClimb_509_395 : canClimb 509 395 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup509, nestingLookup395]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq509 nestingEntries_eq395]
  decide

theorem canClimb_509_396 : canClimb 509 396 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup509, nestingLookup396]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq509 nestingEntries_eq396]
  decide

theorem canClimb_509_397 : canClimb 509 397 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup509, nestingLookup397]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq509 nestingEntries_eq397]
  decide

theorem canClimb_510_1 : canClimb 510 1 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup510, nestingLookup001]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq510 nestingIdentity_entries]
  rw [nestingIdentity_denominator, functionNestedCheck_identity]
  decide

theorem canClimb_511_1 : canClimb 511 1 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup511, nestingLookup001]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq511 nestingIdentity_entries]
  rw [nestingIdentity_denominator, functionNestedCheck_identity]
  decide

theorem canClimb_512_1 : canClimb 512 1 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup512, nestingLookup001]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq512 nestingIdentity_entries]
  rw [nestingIdentity_denominator, functionNestedCheck_identity]
  decide

theorem canClimb_513_1 : canClimb 513 1 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup513, nestingLookup001]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq513 nestingIdentity_entries]
  rw [nestingIdentity_denominator, functionNestedCheck_identity]
  decide

theorem canClimb_514_1 : canClimb 514 1 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup514, nestingLookup001]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq514 nestingIdentity_entries]
  rw [nestingIdentity_denominator, functionNestedCheck_identity]
  decide

theorem canClimb_515_1 : canClimb 515 1 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup515, nestingLookup001]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq515 nestingIdentity_entries]
  rw [nestingIdentity_denominator, functionNestedCheck_identity]
  decide

theorem canClimb_516_1 : canClimb 516 1 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup516, nestingLookup001]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq516 nestingIdentity_entries]
  rw [nestingIdentity_denominator, functionNestedCheck_identity]
  decide

theorem canClimb_517_1 : canClimb 517 1 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup517, nestingLookup001]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq517 nestingIdentity_entries]
  rw [nestingIdentity_denominator, functionNestedCheck_identity]
  decide

theorem canClimb_518_1 : canClimb 518 1 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup518, nestingLookup001]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq518 nestingIdentity_entries]
  rw [nestingIdentity_denominator, functionNestedCheck_identity]
  decide

theorem canClimb_519_398 : canClimb 519 398 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup519, nestingLookup398]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq519 nestingEntries_eq398]
  decide

theorem canClimb_519_400 : canClimb 519 400 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup519, nestingLookup400]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq519 nestingEntries_eq400]
  decide

theorem canClimb_519_402 : canClimb 519 402 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup519, nestingLookup402]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq519 nestingEntries_eq402]
  decide

theorem canClimb_519_403 : canClimb 519 403 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup519, nestingLookup403]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq519 nestingEntries_eq403]
  decide

theorem canClimb_519_404 : canClimb 519 404 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup519, nestingLookup404]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq519 nestingEntries_eq404]
  decide

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem canClimb_519_405 : canClimb 519 405 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup519, nestingLookup405]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq519 nestingEntries_eq405]
  decide

theorem canClimb_519_407 : canClimb 519 407 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup519, nestingLookup407]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq519 nestingEntries_eq407]
  decide

theorem canClimb_519_409 : canClimb 519 409 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup519, nestingLookup409]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq519 nestingEntries_eq409]
  decide

theorem canClimb_519_410 : canClimb 519 410 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup519, nestingLookup410]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq519 nestingEntries_eq410]
  decide

theorem canClimb_519_413 : canClimb 519 413 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup519, nestingLookup413]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq519 nestingEntries_eq413]
  decide

theorem canClimb_519_414 : canClimb 519 414 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup519, nestingLookup414]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq519 nestingEntries_eq414]
  decide

theorem canClimb_519_415 : canClimb 519 415 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup519, nestingLookup415]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq519 nestingEntries_eq415]
  decide

theorem canClimb_520_362 : canClimb 520 362 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup520, nestingLookup362]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq520 nestingEntries_eq362]
  decide

theorem canClimb_520_363 : canClimb 520 363 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup520, nestingLookup363]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq520 nestingEntries_eq363]
  decide

theorem canClimb_520_365 : canClimb 520 365 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup520, nestingLookup365]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq520 nestingEntries_eq365]
  decide

theorem canClimb_520_366 : canClimb 520 366 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup520, nestingLookup366]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq520 nestingEntries_eq366]
  decide

theorem canClimb_520_368 : canClimb 520 368 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup520, nestingLookup368]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq520 nestingEntries_eq368]
  decide

theorem canClimb_520_369 : canClimb 520 369 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup520, nestingLookup369]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq520 nestingEntries_eq369]
  decide

theorem canClimb_520_370 : canClimb 520 370 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup520, nestingLookup370]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq520 nestingEntries_eq370]
  decide

theorem canClimb_520_373 : canClimb 520 373 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup520, nestingLookup373]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq520 nestingEntries_eq373]
  decide

theorem canClimb_520_375 : canClimb 520 375 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup520, nestingLookup375]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq520 nestingEntries_eq375]
  decide

theorem canClimb_520_377 : canClimb 520 377 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup520, nestingLookup377]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq520 nestingEntries_eq377]
  decide

theorem canClimb_520_378 : canClimb 520 378 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup520, nestingLookup378]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq520 nestingEntries_eq378]
  decide

theorem canClimb_520_379 : canClimb 520 379 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup520, nestingLookup379]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq520 nestingEntries_eq379]
  decide

theorem canClimb_521_488 : canClimb 521 488 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup521, nestingLookup488]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq521 nestingEntries_eq488]
  decide

theorem canClimb_521_489 : canClimb 521 489 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup521, nestingLookup489]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq521 nestingEntries_eq489]
  decide

theorem canClimb_521_492 : canClimb 521 492 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup521, nestingLookup492]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq521 nestingEntries_eq492]
  decide

theorem canClimb_521_493 : canClimb 521 493 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup521, nestingLookup493]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq521 nestingEntries_eq493]
  decide

theorem canClimb_521_494 : canClimb 521 494 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup521, nestingLookup494]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq521 nestingEntries_eq494]
  decide

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem canClimb_521_495 : canClimb 521 495 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup521, nestingLookup495]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq521 nestingEntries_eq495]
  decide

theorem canClimb_521_496 : canClimb 521 496 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup521, nestingLookup496]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq521 nestingEntries_eq496]
  decide

theorem canClimb_521_498 : canClimb 521 498 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup521, nestingLookup498]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq521 nestingEntries_eq498]
  decide

theorem canClimb_521_500 : canClimb 521 500 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup521, nestingLookup500]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq521 nestingEntries_eq500]
  decide

theorem canClimb_521_502 : canClimb 521 502 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup521, nestingLookup502]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq521 nestingEntries_eq502]
  decide

theorem canClimb_521_503 : canClimb 521 503 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup521, nestingLookup503]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq521 nestingEntries_eq503]
  decide

theorem canClimb_521_504 : canClimb 521 504 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup521, nestingLookup504]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq521 nestingEntries_eq504]
  decide

theorem canClimb_522_471 : canClimb 522 471 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup522, nestingLookup471]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq522 nestingEntries_eq471]
  decide

theorem canClimb_522_472 : canClimb 522 472 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup522, nestingLookup472]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq522 nestingEntries_eq472]
  decide

theorem canClimb_522_473 : canClimb 522 473 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup522, nestingLookup473]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq522 nestingEntries_eq473]
  decide

theorem canClimb_522_474 : canClimb 522 474 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup522, nestingLookup474]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq522 nestingEntries_eq474]
  decide

theorem canClimb_522_476 : canClimb 522 476 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup522, nestingLookup476]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq522 nestingEntries_eq476]
  decide

theorem canClimb_522_477 : canClimb 522 477 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup522, nestingLookup477]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq522 nestingEntries_eq477]
  decide

theorem canClimb_522_479 : canClimb 522 479 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup522, nestingLookup479]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq522 nestingEntries_eq479]
  decide

theorem canClimb_522_480 : canClimb 522 480 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup522, nestingLookup480]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq522 nestingEntries_eq480]
  decide

theorem canClimb_522_482 : canClimb 522 482 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup522, nestingLookup482]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq522 nestingEntries_eq482]
  decide

theorem canClimb_522_484 : canClimb 522 484 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup522, nestingLookup484]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq522 nestingEntries_eq484]
  decide

theorem canClimb_522_486 : canClimb 522 486 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup522, nestingLookup486]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq522 nestingEntries_eq486]
  decide

theorem canClimb_522_487 : canClimb 522 487 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup522, nestingLookup487]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq522 nestingEntries_eq487]
  decide

theorem canClimb_523_452 : canClimb 523 452 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup523, nestingLookup452]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq523 nestingEntries_eq452]
  decide

theorem canClimb_523_453 : canClimb 523 453 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup523, nestingLookup453]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq523 nestingEntries_eq453]
  decide

theorem canClimb_523_454 : canClimb 523 454 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup523, nestingLookup454]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq523 nestingEntries_eq454]
  decide

theorem canClimb_523_457 : canClimb 523 457 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup523, nestingLookup457]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq523 nestingEntries_eq457]
  decide

theorem canClimb_523_459 : canClimb 523 459 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup523, nestingLookup459]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq523 nestingEntries_eq459]
  decide

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem canClimb_523_460 : canClimb 523 460 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup523, nestingLookup460]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq523 nestingEntries_eq460]
  decide

theorem canClimb_523_462 : canClimb 523 462 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup523, nestingLookup462]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq523 nestingEntries_eq462]
  decide

theorem canClimb_523_463 : canClimb 523 463 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup523, nestingLookup463]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq523 nestingEntries_eq463]
  decide

theorem canClimb_523_464 : canClimb 523 464 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup523, nestingLookup464]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq523 nestingEntries_eq464]
  decide

theorem canClimb_523_466 : canClimb 523 466 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup523, nestingLookup466]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq523 nestingEntries_eq466]
  decide

theorem canClimb_523_467 : canClimb 523 467 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup523, nestingLookup467]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq523 nestingEntries_eq467]
  decide

theorem canClimb_523_468 : canClimb 523 468 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup523, nestingLookup468]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq523 nestingEntries_eq468]
  decide

theorem canClimb_524_434 : canClimb 524 434 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup524, nestingLookup434]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq524 nestingEntries_eq434]
  decide

theorem canClimb_524_435 : canClimb 524 435 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup524, nestingLookup435]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq524 nestingEntries_eq435]
  decide

theorem canClimb_524_436 : canClimb 524 436 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup524, nestingLookup436]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq524 nestingEntries_eq436]
  decide

theorem canClimb_524_437 : canClimb 524 437 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup524, nestingLookup437]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq524 nestingEntries_eq437]
  decide

theorem canClimb_524_440 : canClimb 524 440 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup524, nestingLookup440]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq524 nestingEntries_eq440]
  decide

theorem canClimb_524_442 : canClimb 524 442 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup524, nestingLookup442]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq524 nestingEntries_eq442]
  decide

theorem canClimb_524_443 : canClimb 524 443 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup524, nestingLookup443]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq524 nestingEntries_eq443]
  decide

theorem canClimb_524_445 : canClimb 524 445 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup524, nestingLookup445]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq524 nestingEntries_eq445]
  decide

theorem canClimb_524_446 : canClimb 524 446 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup524, nestingLookup446]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq524 nestingEntries_eq446]
  decide

theorem canClimb_524_448 : canClimb 524 448 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup524, nestingLookup448]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq524 nestingEntries_eq448]
  decide

theorem canClimb_524_450 : canClimb 524 450 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup524, nestingLookup450]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq524 nestingEntries_eq450]
  decide

theorem canClimb_524_451 : canClimb 524 451 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup524, nestingLookup451]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq524 nestingEntries_eq451]
  decide

theorem canClimb_525_1 : canClimb 525 1 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup525, nestingLookup001]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq525 nestingIdentity_entries]
  rw [nestingIdentity_denominator, functionNestedCheck_identity]
  decide

theorem canClimb_526_1 : canClimb 526 1 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup526, nestingLookup001]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq526 nestingIdentity_entries]
  rw [nestingIdentity_denominator, functionNestedCheck_identity]
  decide

theorem canClimb_527_1 : canClimb 527 1 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup527, nestingLookup001]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq527 nestingIdentity_entries]
  rw [nestingIdentity_denominator, functionNestedCheck_identity]
  decide

theorem canClimb_528_1 : canClimb 528 1 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup528, nestingLookup001]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq528 nestingIdentity_entries]
  rw [nestingIdentity_denominator, functionNestedCheck_identity]
  decide

theorem canClimb_529_1 : canClimb 529 1 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup529, nestingLookup001]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq529 nestingIdentity_entries]
  rw [nestingIdentity_denominator, functionNestedCheck_identity]
  decide

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem canClimb_530_1 : canClimb 530 1 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup530, nestingLookup001]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq530 nestingIdentity_entries]
  rw [nestingIdentity_denominator, functionNestedCheck_identity]
  decide

theorem canClimb_531_1 : canClimb 531 1 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup531, nestingLookup001]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq531 nestingIdentity_entries]
  rw [nestingIdentity_denominator, functionNestedCheck_identity]
  decide

theorem canClimb_532_1 : canClimb 532 1 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup532, nestingLookup001]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq532 nestingIdentity_entries]
  rw [nestingIdentity_denominator, functionNestedCheck_identity]
  decide

theorem canClimb_533_1 : canClimb 533 1 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup533, nestingLookup001]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq533 nestingIdentity_entries]
  rw [nestingIdentity_denominator, functionNestedCheck_identity]
  decide

theorem canClimb_534_1 : canClimb 534 1 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup534, nestingLookup001]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq534 nestingIdentity_entries]
  rw [nestingIdentity_denominator, functionNestedCheck_identity]
  decide

theorem canClimb_535_1 : canClimb 535 1 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup535, nestingLookup001]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq535 nestingIdentity_entries]
  rw [nestingIdentity_denominator, functionNestedCheck_identity]
  decide

theorem canClimb_536_1 : canClimb 536 1 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup536, nestingLookup001]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq536 nestingIdentity_entries]
  rw [nestingIdentity_denominator, functionNestedCheck_identity]
  decide

theorem canClimb_537_1 : canClimb 537 1 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup537, nestingLookup001]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq537 nestingIdentity_entries]
  rw [nestingIdentity_denominator, functionNestedCheck_identity]
  decide

theorem canClimb_538_1 : canClimb 538 1 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup538, nestingLookup001]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq538 nestingIdentity_entries]
  rw [nestingIdentity_denominator, functionNestedCheck_identity]
  decide

theorem canClimb_539_1 : canClimb 539 1 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup539, nestingLookup001]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq539 nestingIdentity_entries]
  rw [nestingIdentity_denominator, functionNestedCheck_identity]
  decide

theorem canClimb_540_1 : canClimb 540 1 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup540, nestingLookup001]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq540 nestingIdentity_entries]
  rw [nestingIdentity_denominator, functionNestedCheck_identity]
  decide

theorem canClimb_541_1 : canClimb 541 1 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup541, nestingLookup001]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq541 nestingIdentity_entries]
  rw [nestingIdentity_denominator, functionNestedCheck_identity]
  decide

theorem canClimb_542_1 : canClimb 542 1 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup542, nestingLookup001]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq542 nestingIdentity_entries]
  rw [nestingIdentity_denominator, functionNestedCheck_identity]
  decide

theorem canClimb_543_1 : canClimb 543 1 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup543, nestingLookup001]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq543 nestingIdentity_entries]
  rw [nestingIdentity_denominator, functionNestedCheck_identity]
  decide

theorem canClimb_544_1 : canClimb 544 1 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup544, nestingLookup001]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq544 nestingIdentity_entries]
  rw [nestingIdentity_denominator, functionNestedCheck_identity]
  decide

theorem canClimb_545_1 : canClimb 545 1 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup545, nestingLookup001]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq545 nestingIdentity_entries]
  rw [nestingIdentity_denominator, functionNestedCheck_identity]
  decide

theorem canClimb_546_1 : canClimb 546 1 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup546, nestingLookup001]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq546 nestingIdentity_entries]
  rw [nestingIdentity_denominator, functionNestedCheck_identity]
  decide

theorem canClimb_547_1 : canClimb 547 1 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup547, nestingLookup001]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq547 nestingIdentity_entries]
  rw [nestingIdentity_denominator, functionNestedCheck_identity]
  decide

theorem canClimb_548_1 : canClimb 548 1 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup548, nestingLookup001]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq548 nestingIdentity_entries]
  rw [nestingIdentity_denominator, functionNestedCheck_identity]
  decide

theorem canClimb_549_1 : canClimb 549 1 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup549, nestingLookup001]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq549 nestingIdentity_entries]
  rw [nestingIdentity_denominator, functionNestedCheck_identity]
  decide

theorem canClimb_550_1 : canClimb 550 1 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup550, nestingLookup001]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq550 nestingIdentity_entries]
  rw [nestingIdentity_denominator, functionNestedCheck_identity]
  decide

theorem canClimb_551_1 : canClimb 551 1 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup551, nestingLookup001]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq551 nestingIdentity_entries]
  rw [nestingIdentity_denominator, functionNestedCheck_identity]
  decide

theorem canClimb_552_1 : canClimb 552 1 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup552, nestingLookup001]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq552 nestingIdentity_entries]
  rw [nestingIdentity_denominator, functionNestedCheck_identity]
  decide

theorem canClimb_553_1 : canClimb 553 1 = true := by
  unfold canClimb
  rw [frameNested_eq, nestingLookup553, nestingLookup001]
  rw [nestedCheck_eq_function _ _ _ _ nestingEntries_eq553 nestingIdentity_entries]
  rw [nestingIdentity_denominator, functionNestedCheck_identity]
  decide

end CSL.Construction.PhysicalFramePaths


