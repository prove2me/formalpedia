-- Prove2me | Definitions.Def_CSL_Generated_FiniteCircuit_FramePathChecks_Base
-- name    : CSL_Generated_FiniteCircuit_FramePathChecks_Base
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T13:08:09.306089+00:00
-- url     : https://prove2.me/theorems/6da815ca-e15f-4aad-b0e0-bc24c164f8a6
-- title:
--   Coded sorting library: Generated / FiniteCircuit / FramePathChecks / Base
-- statement:
--   Module `CodedSorting.Generated.FiniteCircuit.FramePathChecks.Base` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   Generated physical-frame checks. Uncompiled until a build record exists.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Generated.FiniteCircuit.FramePathChecks.Base

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Circuit_MemoryAccess_PhysicalFrameWordData
import Definitions.Def_CSL_Generated_FiniteCircuit_ArrayLookup
import Definitions.Def_CSL_Circuit_Local_SSAArrayConcat

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

def nestedCheck (p q : Projection) : Bool :=
  (List.range 8).all fun i => (List.range 8).all fun j =>
    (List.range 8).foldl
      (fun s k => s + matrixEntry q i k * matrixEntry p k j) 0 ==
      q.denominator * matrixEntry p i j

theorem frameNested_eq (a b : Nat) :
    frameNested a b = nestedCheck projections[a]! projections[b]! := rfl

@[simp] theorem canClimb_self (a : Nat) : canClimb a a = true := by
  simp [canClimb]

end CSL.Construction.PhysicalFramePaths


