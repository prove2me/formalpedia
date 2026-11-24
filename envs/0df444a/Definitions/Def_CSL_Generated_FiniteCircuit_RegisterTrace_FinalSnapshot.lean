-- Prove2me | Definitions.Def_CSL_Generated_FiniteCircuit_RegisterTrace_FinalSnapshot
-- name    : CSL_Generated_FiniteCircuit_RegisterTrace_FinalSnapshot
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T14:07:24.992255+00:00
-- url     : https://prove2.me/theorems/6b82e948-c2e1-4954-9fbe-39268e7462f7
-- title:
--   Coded sorting library: Generated / FiniteCircuit / RegisterTrace / FinalSnapshot
-- statement:
--   Module `CodedSorting.Generated.FiniteCircuit.RegisterTrace.FinalSnapshot` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Generated.FiniteCircuit.RegisterTrace.FinalSnapshot

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Generated_FiniteCircuit_RegisterTrace_Steps5376To5582
import Definitions.Def_CSL_Generated_FiniteCircuit_SSARows

namespace CSL.Construction.FiniteSSA.Verified
open CSL.Construction.FiniteCertificate CSL.Construction.SSAFunctionCertificate
noncomputable section
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem finalScalarRows : ∀ r : Fin 661,
    rows (Block174.after r.val) =
      if 111 ≤ r.val && r.val < 222 then
        Nat.xor (2 ^ r.val) (2 ^ (r.val - 111)) else 2 ^ r.val := by
  decide +kernel

theorem finalRows : ∀ r : Fin 661,
    rows (Block174.after r.val) = coefficientExpected[r.val]! := by
  intro r
  simpa [coefficientExpected, registerCount, portCount, getElem!_pos, r.isLt]
    using finalScalarRows r

#print axioms finalScalarRows
#print axioms finalRows
end
end CSL.Construction.FiniteSSA.Verified


