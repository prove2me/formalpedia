-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40Campaign
-- name    : BS2_b3ba934b_Endpoint40Campaign
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T06:50:18.420546+00:00
-- url     : https://prove2.me/theorems/f61a73c3-8937-4e5a-9352-96a1af055934
-- title:
--   Sensitivity separation: Endpoint40Campaign (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40Campaign` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40Campaign.lean; original SHA-256 0996ee2ffef9b601c8bc25b7af8a15ab3149e55698cba292dea295a92b004562; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- Assembly of the first campaign exponent from the concrete semantic
   transfer, finite record coverage, and the numeric raw-profile checks. -/
import Definitions.Def_BS2_b3ba934b_Endpoint40Transfer
import Definitions.Def_BS2_b3ba934b_Endpoint40Assembly
import Definitions.Def_BS2_b3ba934b_Endpoint40Seeds

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace ThreeBoundEndpoint40Campaign
open OAI.Paper320 ThreeBoundNumeric ThreeBoundFullProfile

theorem raw_preserves_of_records
    (hrecords : ∀ xs∈ThreeBoundQ2.records, xs∈Endpoint40.records)
    (p : Fin 4) : Endpoint40.RawPreserves p := by
  intro I hI F hF v hadmissible hv
  exact ThreeBoundEndpoint40Transfer.raw_sound p F hF v hv hadmissible.1 hrecords

theorem seeds_of_checks
    (hrecords : ∀ xs∈ThreeBoundQ2.records, xs∈Endpoint40.records)
    (hnumerical : Endpoint40.RawNumericalBounds) :
    ∀ m : ℕ, ∃ (n : ℕ) (f : (Fin n → Bool) → Bool),
      16^m ≤ sensitivity f ∧
      sensitivity f ≤ ThreeBoundEndpoint40Seeds.prefactor*31739938^m ∧
      (10007^4)^m ≤ blockSensitivity f :=
  ThreeBoundEndpoint40Seeds.seeds_of_periodic_upper
    (Endpoint40.periodic_upper (raw_preserves_of_records hrecords) hnumerical)

theorem achieves_213303_of_checks
    (hrecords : ∀ xs∈ThreeBoundQ2.records, xs∈Endpoint40.records)
    (hnumerical : Endpoint40.RawNumericalBounds) :
    SensitivityCampaign.AchievesExponent ((213303 : ℝ)/100000) :=
  ThreeBoundEndpoint40Seeds.achieves_213303_of_periodic_upper
    (Endpoint40.periodic_upper (raw_preserves_of_records hrecords) hnumerical)

end ThreeBoundEndpoint40Campaign

#print axioms ThreeBoundEndpoint40Campaign.raw_preserves_of_records
#print axioms ThreeBoundEndpoint40Campaign.achieves_213303_of_checks


