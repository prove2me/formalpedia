-- Prove2me | Definitions.Def_PricingWithTips3DM_ec8ee304a04c4c3ad3171807
-- name    : PricingWithTips3DM_ec8ee304a04c4c3ad3171807
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T21:04:18.842692+00:00
-- url     : https://prove2.me/theorems/a5c290be-f122-4f4e-9220-2c989029e05f
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.NP
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_10e78846fac3b5dcfc571733
import Definitions.Def_PricingWithTips3DM_a82ad24f6122eea7c40fd2b4
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# General circuit satisfiability is in NP

The executable certificate semantics and the concrete polynomial-time TM2
witness are assembled here into the chapter-level membership theorem.
-/

namespace CLRS.Chapter34

/-- `GeneralCircuitSAT` has polynomial-size assignment certificates checked by
the concrete polynomial-time verifier machine. -/
theorem generalCircuitSAT_polyTimeVerifiable :
    PolyTimeVerifiable GeneralCircuitSAT := by
  refine ⟨generalCircuitVerifier, Polynomial.X, ?_, ?_⟩
  · exact ⟨Turing.GeneralCircuitVerifier.generalCircuitVerifierComputableInPolyTime⟩
  · intro input
    simpa using mem_generalCircuitSAT_iff_exists_certificate input

/-- Public textbook-facing name for polynomial verifiability of general
circuit satisfiability. -/
theorem generalCircuitSAT_verifiable :
    PolyTimeVerifiable GeneralCircuitSAT :=
  generalCircuitSAT_polyTimeVerifiable

/-- The honest serialized general-circuit satisfiability language belongs to
the complexity class `NP`. -/
theorem generalCircuitSAT_mem_ClassNP :
    GeneralCircuitSAT ∈ ClassNP CircuitSym :=
  (mem_ClassNP GeneralCircuitSAT).2 generalCircuitSAT_polyTimeVerifiable

end CLRS.Chapter34


