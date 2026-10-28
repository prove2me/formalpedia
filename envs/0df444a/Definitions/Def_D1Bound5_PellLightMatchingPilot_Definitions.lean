-- Prove2me | Definitions.Def_D1Bound5_PellLightMatchingPilot_Definitions
-- name    : D1Bound5_PellLightMatchingPilot_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T22:33:56.788667+00:00
-- url     : https://prove2.me/theorems/071b149a-8285-42bc-8af9-3f4a5c9aba96
-- title:
--   Pell Light Matching Pilot
-- statement:
--   Definitions for pell light matching pilot in the argument bounding Diophantine D(1) sets in imaginary quadratic integer rings. The named objects in this bundle include `PellMatchingLightProduction.pellMagnitudes_4519`, `PellMatchingLightProduction.pellMasks_4519`, `PellMatchingLightProduction.pellWitnesses_4519`. The accompanying auxiliary certificates are included with their original proofs.
-- source:
--   D1Bound5/PellLightMatchingPilot.lean, lines 7-8, SHA-256 fd6bdb61a62a75e7b9a4af72ac86f459323d2aaf21cd0fb2a902afa854de4091; D1Bound5/PellLightMatchingPilot.lean, lines 10-11, SHA-256 fd6bdb61a62a75e7b9a4af72ac86f459323d2aaf21cd0fb2a902afa854de4091; D1Bound5/PellLightMatchingPilot.lean, lines 13-14, SHA-256 fd6bdb61a62a75e7b9a4af72ac86f459323d2aaf21cd0fb2a902afa854de4091; D1Bound5/PellLightMatchingPilot.lean, lines 16-18, SHA-256 fd6bdb61a62a75e7b9a4af72ac86f459323d2aaf21cd0fb2a902afa854de4091; D1Bound5/PellLightMatchingPilot.lean, lines 20-22, SHA-256 fd6bdb61a62a75e7b9a4af72ac86f459323d2aaf21cd0fb2a902afa854de4091; D1Bound5/PellLightMatchingPilot.lean, lines 24-26, SHA-256 fd6bdb61a62a75e7b9a4af72ac86f459323d2aaf21cd0fb2a902afa854de4091. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PellLightMatching_Definitions

section
namespace D1Bound5.PellMatchingLightProduction
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

def pellMagnitudes_4519 : List Int :=
  [848247818120463021285124851606930862336855497344396380221506360,2441339877028287880387027742081015912269810837458221794307071425553480314877231622120056055752431898741696290082876610874203572328469388452474394706852168840956618160109824554622925173304920,7026414059484291798607794929249050022180847423505684967142089606508643602821239389632732503113051266089627968271727993353343972650017663770155401856533070161443282841450028429424527764546535868706833302271778074616364344264022502340013836763512699704350784624771545514576974512418382446598843854356587230234600011800,20222704343573243261472243630775381356638468860392091268505441486210800753228376755674617039728240484581457434957225328200659967880133736366409614292520379155119662872136639637683884773292331095034110608154524032276669157316560425043988423514166916009856743627341980656025310067978949138485084066140313603115497494858746932773179937719128911452607441713788233519535492947428330743968807510273023662783589904567006164433911577973928210847791480]

def pellMasks_4519 : List PellLightSquareMasks :=
  [⟨8,147,147⟩,⟨10,571,571⟩,⟨12,5659,2533⟩]

def pellWitnesses_4519 : List (List (Nat × Nat)) :=
  [[(0,1),(0,1),(0,1)],[(0,1),(0,2)],[(0,1)],[]]

theorem pellMasks_4519_valid :
    (pellMasks_4519.all fun m => m.validBool 4519) = true := by
  decide +kernel

theorem pellMatching_4519_checked :
    pellLightMatchingCheck pellMasks_4519 pellMagnitudes_4519 pellWitnesses_4519 = true := by
  decide +kernel

theorem pellMagnitudes_4519_large :
    (pellMagnitudes_4519.all fun x => decide (2 ≤ x)) = true := by
  decide +kernel

end D1Bound5.PellMatchingLightProduction
end


