-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint16Complete
-- name    : BS2_b3ba934b_Endpoint16Complete
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T21:10:13.633577+00:00
-- url     : https://prove2.me/theorems/30cee561-a5df-4bb3-9cde-beaae4986483
-- title:
--   Sensitivity separation: Endpoint16Complete (complete source module)
-- statement:
--   Complete Lean source module `Endpoint16Complete` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint16Complete.lean; original SHA-256 66b5963c3e0a45271173da38e1fd2883addc468f1ad5b77a41f4d26c16fa37d9; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- The second endpoint's complete actual semantic transfer.  Every raw
coordinate, including the strict-zero eight-branch case, is proved here. -/
import Definitions.Def_BS2_b3ba934b_Endpoint16Zero
import Definitions.Def_BS2_b3ba934b_Endpoint16Assembly
import Definitions.Def_BS2_b3ba934b_Endpoint16Seeds

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace ThreeBoundEndpoint16Complete
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundFullProfile ThreeBoundNumeric

theorem raw_sound {I : Type} [Fintype I]
    (p : Fin 4) (F : Fin 16 → (I → Bool) → Bool) (hF : Nested F)
    (v : Profile 16) (hv : Upper F v) (hordered : Ordered v)
    (hrecords : ∀ xs ∈ ThreeBoundQ2.records, xs ∈ ThreeBoundMinmaxNumeric.Endpoint16.records) :
    Upper (parent ((Sensitivity10007Endpoint16.recipe p).stage F) F)
      (ThreeBoundMinmaxNumeric.Endpoint16.raw p v) :=
  ThreeBoundEndpoint16Transfer.raw_sound_of_zero p F hF v hv hordered hrecords
    (ThreeBoundEndpoint16Zero.zero_bound p F hF v hv)

theorem raw_preserves_of_records
    (hrecords : ∀ xs ∈ ThreeBoundQ2.records, xs ∈ ThreeBoundMinmaxNumeric.Endpoint16.records)
    (p : Fin 4) : ThreeBoundMinmaxNumeric.Endpoint16.RawPreserves p := by
  intro I hI F hF v hordered hv
  exact raw_sound p F hF v hv hordered hrecords

theorem seeds_of_checks
    (hrecords : ∀ xs ∈ ThreeBoundQ2.records, xs ∈ ThreeBoundMinmaxNumeric.Endpoint16.records)
    (hnumerical : ThreeBoundMinmaxNumeric.Endpoint16.RawNumericalBounds) :
    ∀ m : ℕ, ∃ (n : ℕ) (f : (Fin n → Bool) → Bool),
      16^m ≤ sensitivity f ∧
      sensitivity f ≤ ThreeBoundEndpoint16Seeds.prefactor*31192129^m ∧
      (10007^4)^m ≤ blockSensitivity f :=
  ThreeBoundEndpoint16Seeds.seeds_of_periodic_upper
    (ThreeBoundMinmaxNumeric.Endpoint16.periodic_upper (raw_preserves_of_records hrecords) hnumerical)

theorem achieves_213519_of_checks
    (hrecords : ∀ xs ∈ ThreeBoundQ2.records, xs ∈ ThreeBoundMinmaxNumeric.Endpoint16.records)
    (hnumerical : ThreeBoundMinmaxNumeric.Endpoint16.RawNumericalBounds) :
    SensitivityCampaign.AchievesExponent ((213519 : ℝ)/100000) :=
  ThreeBoundEndpoint16Seeds.achieves_213519_of_periodic_upper
    (ThreeBoundMinmaxNumeric.Endpoint16.periodic_upper (raw_preserves_of_records hrecords) hnumerical)

end ThreeBoundEndpoint16Complete

#print axioms ThreeBoundEndpoint16Complete.raw_sound
#print axioms ThreeBoundEndpoint16Complete.achieves_213519_of_checks


