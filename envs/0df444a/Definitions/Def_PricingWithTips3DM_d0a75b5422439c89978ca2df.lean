-- Prove2me | Definitions.Def_PricingWithTips3DM_d0a75b5422439c89978ca2df
-- name    : PricingWithTips3DM_d0a75b5422439c89978ca2df
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T05:56:49.455705+00:00
-- url     : https://prove2.me/theorems/2bdaeb0b-9387-4239-b24b-6b9e64cb277d
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.ToSAT.Reduction
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_b4c86087b487e6fd844dd77b
import Definitions.Def_PricingWithTips3DM_c2c769ccc443b1a929b3ced9
import Definitions.Def_PricingWithTips3DM_016f4b89ca40933af432d715
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-! # General CIRCUIT-SAT to SAT: many-one reduction -/

namespace CLRS.Chapter34

/-- The direct consistency-formula construction is a genuine polynomial-time
many-one reduction on the honest raw languages. -/
theorem generalCircuitSAT_reducible_to_SAT :
    PolyTimeReducible GeneralCircuitSAT SAT := by
  refine ⟨generalCircuitToSATMap,
    ⟨Turing.GeneralCircuitToSAT.computableInPolyTime⟩, ?_⟩
  intro input
  exact (generalCircuitToSATMap_mem_SAT_iff input).symm

/-- SAT is NP-hard, obtained directly from the completed Cook--Levin target
and the verified general-circuit-to-formula machine. -/
theorem SAT_npHard : NPHard SAT :=
  NPHard.of_reducible Turing.CookLevin.generalCircuitSAT_npHard
    generalCircuitSAT_reducible_to_SAT

end CLRS.Chapter34


