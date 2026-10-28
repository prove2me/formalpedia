-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint16Invariant
-- name    : BS2_b3ba934b_Endpoint16Invariant
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T20:27:55.275248+00:00
-- url     : https://prove2.me/theorems/4e0ce44f-1883-4518-885a-2133f40b32a2
-- title:
--   Sensitivity separation: Endpoint16Invariant (complete source module)
-- statement:
--   Complete Lean source module `Endpoint16Invariant` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint16Invariant.lean; original SHA-256 ced2787968d936495f545676768057bca62f551fbbb52ef1ae465362d76c1b84; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint16NumericData
import Definitions.Def_BS2_b3ba934b_NatTableChecks
import Definitions.Def_BS2_b3ba934b_NumericAdmissibility

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace ThreeBoundMinmaxNumeric.Endpoint16
open ThreeBoundNumeric ThreeBoundProfiles ThreeBoundFullProfile

def initialABTable : NatTable := match profileTable0 with
  | .leaf v => .leaf v
  | .branch _ left _ => left

theorem base_ab_table : NatTable.lowerCheck 1 initialABTable=true := by decide +kernel

theorem period_table : NatTable.dominates 31192129 profileTable4 profileTable0=true := by
  decide +kernel

theorem period_inequality (coord : Coord 16) : profile4 coord≤31192129*profile0 coord :=
  NatTable.dominates_sound 31192129 profileTable4 profileTable0 period_table (flatIndex coord)

theorem base_ab_indices : ∀ i j : Fin 16,
    flatIndex (Coord.a i j)<272 ∧ flatIndex (Coord.b i j)<272 := by decide +kernel

theorem base_positive : BasePositive profile0 := by
  have htable := NatTable.lowerCheck_sound 1 initialABTable base_ab_table
  intro i j hij
  constructor
  · change 1≤(if flatIndex (Coord.a i j)<272 then initialABTable.get (flatIndex (.a i j)) else _)
    rw [if_pos (base_ab_indices i j).1]
    exact htable _
  · change 1≤(if flatIndex (Coord.b i j)<272 then initialABTable.get (flatIndex (.b i j)) else _)
    rw [if_pos (base_ab_indices i j).2]
    exact htable _

theorem actual_base_upper : Upper (Sensitivity10007Endpoint16.family 0) profile0 :=
  oneBit_upper profile0 base_positive

theorem ordered0 : Ordered profile0 := by decide +kernel

theorem ordered1 : Ordered profile1 := by decide +kernel

theorem ordered2 : Ordered profile2 := by decide +kernel

theorem ordered3 : Ordered profile3 := by decide +kernel

end ThreeBoundMinmaxNumeric.Endpoint16

#print axioms ThreeBoundMinmaxNumeric.Endpoint16.actual_base_upper
#print axioms ThreeBoundMinmaxNumeric.Endpoint16.period_inequality
#print axioms ThreeBoundMinmaxNumeric.Endpoint16.ordered3


