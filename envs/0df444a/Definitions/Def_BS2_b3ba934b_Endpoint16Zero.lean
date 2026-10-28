-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint16Zero
-- name    : BS2_b3ba934b_Endpoint16Zero
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T21:02:46.390081+00:00
-- url     : https://prove2.me/theorems/49d732ca-4c66-4210-b488-4fcb34d75061
-- title:
--   Sensitivity separation: Endpoint16Zero (complete source module)
-- statement:
--   Complete Lean source module `Endpoint16Zero` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint16Zero.lean; original SHA-256 44e3998c5f9ae85576b088ea5f424f570c6823cdebe70e6278fa5e13da3a2fbe; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- Unconditional strict-zero coordinate for the second campaign endpoint. -/
import Definitions.Def_BS2_b3ba934b_MinmaxZeroExpression
import Definitions.Def_BS2_b3ba934b_Endpoint16Transfer

set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 20000
set_option linter.unusedSectionVars false

namespace ThreeBoundEndpoint16Zero
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open ThreeBoundNumeric ThreeBoundFullProfile ThreeBoundMinmaxNumeric
open ThreeBoundEndpoint16Pairs ThreeBoundMinmaxZeroSets ThreeBoundMinmaxZeroExpression
open scoped Classical
noncomputable section
variable {I : Type} [Fintype I]

theorem zero_caps_match : ZeroCapsMatch ThreeBoundMinmaxNumeric.Endpoint16.caps :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem stage_exclusions (p : Fin 4) (F : Fin 16 → (I → Bool) → Bool) :
    Exclusions ((Sensitivity10007Endpoint16.recipe p).stage F) where
  ordinary := (ThreeBoundEndpoint16Transfer.stage_caps_sound p F).ordinary 0 (by decide)
  source := (ThreeBoundEndpoint16Transfer.stage_caps_sound p F).source
  double := (ThreeBoundEndpoint16Transfer.stage_caps_sound p F).double

theorem zero_bound (p : Fin 4) (F : Fin 16 → (I → Bool) → Bool) (hF : Nested F)
    (v : Profile 16) (hv : Upper F v) : ThreeBoundEndpoint16Transfer.ZeroBound p F v := by
  intro i j hij hq
  exact zeroAExpr_sound ((Sensitivity10007Endpoint16.recipe p).stage F)
    (ThreeBoundEndpoint16Transfer.stage_tournament p F) F hF i j (pairData p F i j hij)
    (ThreeBoundMinmaxNumeric.Endpoint16.recipe p i) (ThreeBoundMinmaxNumeric.Endpoint16.recipe p j)
    (entryMatch p F i j hij) v hv ThreeBoundMinmaxNumeric.Endpoint16.caps zero_caps_match
    (stage_exclusions p F) hq

end
end ThreeBoundEndpoint16Zero

#print axioms ThreeBoundEndpoint16Zero.zero_bound


