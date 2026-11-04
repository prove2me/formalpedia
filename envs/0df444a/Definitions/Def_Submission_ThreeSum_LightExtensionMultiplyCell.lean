-- Prove2me | Definitions.Def_Submission_ThreeSum_LightExtensionMultiplyCell
-- name    : Submission_ThreeSum_LightExtensionMultiplyCell
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:38:24.345398+00:00
-- url     : https://prove2.me/theorems/de84d411-8e71-4592-ba49-92437947a88e
-- title:
--   Light Extension Multiply Cell
-- statement:
--   Definitions and structural lemmas for Light Extension Multiply Cell, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightExtensionMultiplyCell.lean

import Definitions.Def_Submission_ThreeSum_LightExtensionQuotientSearch
import Theorems.Thm_Light_Ends_call

set_option autoImplicit false
noncomputable section
namespace ThreeSum.LightExtensionMultiplyCell
open Light LightExtensionQuotientPredicate
set_option maxHeartbeats 4000000
set_option maxRecDepth 6000
noncomputable local instance _p2m_local_instance_2d48f70718_8 (Q : Prop) : Decidable Q := Classical.propDecidable Q
def body (pDecode pSearch pDigit : ℕ) : Stmt :=
  .call pDecode [v 4,v 3,v 0,v 5,k 0,k 1,v 6,v 4] 9 ;;
  .call pDecode [v 4,v 3,v 1,v 5,k 0,k 1,v 7,v 4] 9 ;;
  .call pSearch [v 8,v 2] 9 ;;
  .call pDigit [v 9 -' k 1,k 1,v 8] 0
def searchTime (C : Layout) (q : ℕ) : ℕ :=
  q*q*(LightExtensionQuotientPredicate.time C.dim C.p q q+200)+100
def time (C : Layout) (q : ℕ) : ℕ :=
  2*LightCoefficientDecode.time C.dim q+searchTime C q+LightRadixDigit.time (q*q)+500
def word (C : Layout) (q ctx : ℕ) : ℕ :=
  LightCoefficientDecode.word C.dim C.p q 0 1+
  LightExtensionQuotientPredicate.word C.dim C.p q q+
  LightRadixDigit.word (q*q) 1 q+q*q+q+ctx+100
variable {lim : Limits} {P : Program} {depth : ℕ}
def program : Program := LightExtensionQuotientSearch.program++[body 1 12 2]
end ThreeSum.LightExtensionMultiplyCell


