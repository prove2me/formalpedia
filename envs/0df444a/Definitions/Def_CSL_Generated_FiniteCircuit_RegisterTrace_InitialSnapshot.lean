-- Prove2me | Definitions.Def_CSL_Generated_FiniteCircuit_RegisterTrace_InitialSnapshot
-- name    : CSL_Generated_FiniteCircuit_RegisterTrace_InitialSnapshot
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T14:07:01.091534+00:00
-- url     : https://prove2.me/theorems/eb2b8027-0af1-4b51-97b7-0ca27836b4e2
-- title:
--   Coded sorting library: Generated / FiniteCircuit / RegisterTrace / InitialSnapshot
-- statement:
--   Module `CodedSorting.Generated.FiniteCircuit.RegisterTrace.InitialSnapshot` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Generated.FiniteCircuit.RegisterTrace.InitialSnapshot

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Generated_FiniteCircuit_RegisterTrace_Steps0000To0255
import Definitions.Def_CSL_Generated_FiniteCircuit_SSARows

namespace CSL.Construction.FiniteSSA.Verified
open CSL.Construction.FiniteCertificate CSL.Construction.SSAFunctionCertificate
noncomputable section
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem initialRows : ∀ r : Fin 661, rows (Block000.before r.val) = 2 ^ r.val := by
  decide +kernel

theorem initial_represents : Represents rows Block000.before coefficientStart := by
  intro r hr
  have hr' : r < 661 := by simpa [coefficientStart, registerCount] using hr
  rw [initialRows ⟨r, hr'⟩]
  simp [coefficientStart, registerCount, getElem!_pos, hr']

#print axioms initialRows
#print axioms initial_represents
end
end CSL.Construction.FiniteSSA.Verified


