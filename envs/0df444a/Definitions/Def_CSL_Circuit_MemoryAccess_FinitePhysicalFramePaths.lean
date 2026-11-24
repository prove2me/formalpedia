-- Prove2me | Definitions.Def_CSL_Circuit_MemoryAccess_FinitePhysicalFramePaths
-- name    : CSL_Circuit_MemoryAccess_FinitePhysicalFramePaths
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T20:28:08.138307+00:00
-- url     : https://prove2.me/theorems/0957a6d0-d5a4-41dd-9651-c17542b4a18f
-- title:
--   Coded sorting library: Circuit / MemoryAccess / FinitePhysicalFramePaths
-- statement:
--   Module `CodedSorting.Circuit.MemoryAccess.FinitePhysicalFramePaths` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Circuit.MemoryAccess.FinitePhysicalFramePaths

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Generated_FiniteCircuit_FramePathChecks
import Definitions.Def_CSL_Circuit_Local_LocalPhysicalSemantics

namespace CSL.Construction

theorem actualForwardPathValid (r : LocalPhysicalSemantics.OriginalReg) :
    PhysicalFramePaths.forwardPathValid r.val = true :=
  PhysicalFramePaths.allForwardPathValid r.val r.isLt

#print axioms actualForwardPathValid
end CSL.Construction


