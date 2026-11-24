-- Prove2me | Definitions.Def_CSL_Generated_FiniteCircuit_RegisterTrace_Replay
-- name    : CSL_Generated_FiniteCircuit_RegisterTrace_Replay
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T14:41:28.573439+00:00
-- url     : https://prove2.me/theorems/b1aafde2-c897-46b6-9889-17661988d402
-- title:
--   Coded sorting library: Generated / FiniteCircuit / RegisterTrace / Replay
-- statement:
--   Module `CodedSorting.Generated.FiniteCircuit.RegisterTrace.Replay` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Generated.FiniteCircuit.RegisterTrace.Replay

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Generated_FiniteCircuit_RegisterTrace_Composition
import Definitions.Def_CSL_Generated_FiniteCircuit_RegisterTrace_FinalSnapshot
import Definitions.Def_CSL_Generated_FiniteCircuit_RegisterTrace_InitialSnapshot

namespace CSL.Construction.FiniteCertificate
open CSL.Construction.FiniteSSA CSL.Construction.FiniteSSA.Verified
  CSL.Construction.SSAFunctionCertificate

/-- The complete 5583-gate word, checked by composition of independent
ordinary Lean kernel certificates and literal endpoint snapshots. -/
theorem scalarCoefficientReplay : runCoefficients gates = coefficientExpected :=
  runCoefficients_of_blocks rows gates allSteps Block000.before Block174.after
    program_eq initial_represents allSteps_sound finalRows

end CSL.Construction.FiniteCertificate

#print axioms CSL.Construction.FiniteCertificate.scalarCoefficientReplay


