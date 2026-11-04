-- Prove2me | Definitions.Def_Submission_ThreeSum_TernaryExtensionRelations
-- name    : Submission_ThreeSum_TernaryExtensionRelations
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:54:11.02836+00:00
-- url     : https://prove2.me/theorems/ef9593c4-a3ce-48b4-b298-5c8bc27d13e9
-- title:
--   Ternary Extension Relations
-- statement:
--   Definitions and structural lemmas for Ternary Extension Relations, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryExtensionRelations.lean

import Definitions.Def_Submission_ThreeSum_TernaryExtensionCandidates
set_option autoImplicit false
noncomputable section
namespace ThreeSum.TernaryExtensionEncoding
open Polynomial Finset
set_option maxHeartbeats 3000000
variable {p : ℕ} [Fact p.Prime]
def remainderRelation {f : (ZMod p)[X]}
    (a b h r : Fin f.natDegree → ZMod p) : Prop :=
  vectorPolynomial a*vectorPolynomial b=vectorPolynomial h*f+vectorPolynomial r
end ThreeSum.TernaryExtensionEncoding


