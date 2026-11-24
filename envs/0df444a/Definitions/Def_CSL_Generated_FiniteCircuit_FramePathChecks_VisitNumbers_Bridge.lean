-- Prove2me | Definitions.Def_CSL_Generated_FiniteCircuit_FramePathChecks_VisitNumbers_Bridge
-- name    : CSL_Generated_FiniteCircuit_FramePathChecks_VisitNumbers_Bridge
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T14:28:15.586007+00:00
-- url     : https://prove2.me/theorems/12f527d4-7666-46bb-8e73-d1f914e05494
-- title:
--   Coded sorting library: Generated / FiniteCircuit / FramePathChecks / VisitNumbers / Bridge
-- statement:
--   Module `CodedSorting.Generated.FiniteCircuit.FramePathChecks.VisitNumbers.Bridge` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Generated.FiniteCircuit.FramePathChecks.VisitNumbers.Bridge

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Circuit_MemoryAccess_PhysicalFrameFastVisits
import Definitions.Def_CSL_Generated_FiniteCircuit_FramePathChecks_VisitNumbers_Base

namespace CSL.Construction.PhysicalFramePaths

theorem forward_visits_computed (r : Nat) :
    eventVisits r forwardEvents = computedForwardVisits r :=
  forward_visits_fast r

end CSL.Construction.PhysicalFramePaths


