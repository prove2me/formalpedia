-- Prove2me | Definitions.Def_Submission_ThreeSum_LightExtensionFactorSearch
-- name    : Submission_ThreeSum_LightExtensionFactorSearch
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:34:56.23207+00:00
-- url     : https://prove2.me/theorems/be4931f3-13dc-419d-ad16-4f84778818c4
-- title:
--   Light Extension Factor Search
-- statement:
--   Definitions and structural lemmas for Light Extension Factor Search, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightExtensionFactorSearch.lean

import Definitions.Def_Submission_ThreeSum_LightExtensionFactorPredicate
import Definitions.Def_Submission_ThreeSum_LightPairSearchProgram
set_option autoImplicit false
noncomputable section
namespace ThreeSum.LightExtensionFactorSearch
open Light LightExtensionFactorPredicate
set_option maxHeartbeats 1000000
variable {lim : Limits}
noncomputable local instance _p2m_local_instance_9c16afeb32_9 (Q : Prop) : Decidable Q := Classical.propDecidable Q
def good (C : Layout) (f : ℕ → ℕ) (u v : ℕ) : Prop :=
  u<C.p^C.degree ∧ v<C.p^(C.dim-C.degree) ∧
    LightPolynomialProductCheck.Valid C.p
      (LightExtensionFactorCheck.digits C.p (u+C.p^C.degree))
      (LightExtensionFactorCheck.digits C.p (v+C.p^(C.dim-C.degree))) f
      (C.degree+1) (C.dim-C.degree+1) (2*C.dim)
def program : Program := LightPairSearch.program LightExtensionFactorPredicate.program 0
end ThreeSum.LightExtensionFactorSearch


