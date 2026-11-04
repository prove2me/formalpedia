-- Prove2me | Definitions.Def_Submission_ThreeSum_LightExtensionQuotientSearch
-- name    : Submission_ThreeSum_LightExtensionQuotientSearch
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:35:17.338089+00:00
-- url     : https://prove2.me/theorems/65b37cd8-5b82-404e-87c3-6eb715ad1afa
-- title:
--   Light Extension Quotient Search
-- statement:
--   Definitions and structural lemmas for Light Extension Quotient Search, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightExtensionQuotientSearch.lean

import Definitions.Def_Submission_ThreeSum_LightExtensionQuotientPredicate
import Definitions.Def_Submission_ThreeSum_LightPairSearchProgram
set_option autoImplicit false
noncomputable section
namespace ThreeSum.LightExtensionQuotientSearch
open Light
open LightExtensionQuotientPredicate
set_option maxHeartbeats 1000000
variable {lim : Limits}
noncomputable local instance _p2m_local_instance_7afa0e64b3_11 (Q : Prop) : Decidable Q := Classical.propDecidable Q
def good (C : Layout) (x y f : ℕ → ℕ) (u v : ℕ) : Prop :=
  LightPolynomialProductCheck.Valid C.p x y
    (LightPolynomialQuotientCheck.expected C.p C.dim (digits C.p u) f (digits C.p v))
    C.dim C.dim (2*C.dim)
def program : Program := LightPairSearch.program LightExtensionQuotientPredicate.program 0
end ThreeSum.LightExtensionQuotientSearch


