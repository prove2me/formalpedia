-- Prove2me | Definitions.Def_BS2_b3ba934b_IntegerComparisons
-- name    : BS2_b3ba934b_IntegerComparisons
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T05:46:30.425071+00:00
-- url     : https://prove2.me/theorems/568d07a9-726c-4ba1-ba6e-4b7dd5692e33
-- title:
--   Sensitivity separation: IntegerComparisons (complete source module)
-- statement:
--   Complete Lean source module `IntegerComparisons` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/IntegerComparisons.lean; original SHA-256 cd97ab3b21a85e788e4974cfb79a5ab7d11136e053e7e4b37547fc5813129384; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- Exact arithmetic only: these comparisons are not Boolean-construction proofs. -/
import Lean
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option Elab.async false

namespace ThreeBoundArithmetic

theorem comparison_213303 :
    (10007^4 : Nat)^100000 > 31739938^213303 := by decide +kernel

theorem comparison_213519 :
    (10007^4 : Nat)^100000 > 31192129^213519 := by decide +kernel

theorem comparison_213981 :
    (5591^4 : Nat)^100000 > 10121928^213981 := by decide +kernel

end ThreeBoundArithmetic

#print axioms ThreeBoundArithmetic.comparison_213303
#print axioms ThreeBoundArithmetic.comparison_213519
#print axioms ThreeBoundArithmetic.comparison_213981


