-- Prove2me | Definitions.Def_PricingWithTips3DM_bd93dc426cbb18c2459ae23b
-- name    : PricingWithTips3DM_bd93dc426cbb18c2459ae23b
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T21:04:05.338986+00:00
-- url     : https://prove2.me/theorems/656d1953-edd2-4351-a94b-eb91438658db
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.ReductionMap
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_a48ce47a0de3e40308c5df13
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Function-level Cook--Levin map

The closed verifier circuit is serialized into the general-circuit language.
This gives the reduction an explicit function-level interface together with
its exact language semantics and output-length polynomial.
-/

namespace CLRS.Chapter34.Turing.CookLevin

noncomputable section

/-- The explicit Cook--Levin map from verifier inputs to circuit encodings. -/
def cookLevinMap {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (x : List Γ) : List CircuitSym :=
  encodeCircuit (verifierCircuit W x)

/-- The explicit reduction map preserves and reflects language membership. -/
theorem cookLevinMap_mem_generalCircuitSAT_iff {Γ : Type}
    {L : Language Γ} (W : VerifierWitness L) (x : List Γ) :
    cookLevinMap W x ∈ GeneralCircuitSAT ↔ x ∈ L := by
  rw [cookLevinMap, encodeCircuit_mem_generalCircuitSAT_iff,
    verifierCircuit_satisfiable_iff]

/-- The explicit reduction map has polynomially bounded output length. -/
theorem cookLevinMap_length_le {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (x : List Γ) :
    (cookLevinMap W x).length ≤
      (verifierCircuitEncodingBound W).eval x.length := by
  exact verifierCircuit_encoding_length_le W x

end

end CLRS.Chapter34.Turing.CookLevin


