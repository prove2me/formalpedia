-- Prove2me | Definitions.Def_Submission_ThreeSum_LightReportingFilter
-- name    : Submission_ThreeSum_LightReportingFilter
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:24:38.667966+00:00
-- url     : https://prove2.me/theorems/ede25156-2ec6-4136-b03b-cfeb3cad6956
-- title:
--   Light Reporting Filter
-- statement:
--   Definitions and structural lemmas for Light Reporting Filter, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightReportingFilter.lean

import Definitions.Def_Submission_ThreeSum_LightReportingAffine
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_Light_Ends_skip
import Theorems.Thm_Light_Ends_store

set_option autoImplicit false
namespace ThreeSum.LightReportingFilter
open Light
variable {lim : Limits} {P : Program}
def selected (count : ℕ → ℕ) (j : ℕ) : List ℕ :=
  (List.range j).filter fun i => 0 < count i
def roundBody : Stmt :=
  .ite (k 0 <' M (v 1 +' v 4))
    (.store (v 2 +' v 3) (v 4) ;; .set 3 (v 3 +' k 1))
    .skip
def body : Stmt :=
  .set 3 (k 0) ;;
  .for 4 (v 0) roundBody ;;
  .set 0 (v 3)
def time (n : ℕ) : ℕ := 100*n+40
def Inv (μ : ℕ → ℤ) (count : ℕ → ℕ) (n src dst j : ℕ) (σ : State) : Prop :=
  ∃ μ' : ℕ → ℤ,
    σ = ⟨frame [n,src,dst,(selected count j).length,j],μ'⟩ ∧
    SegN μ' dst (selected count j) ∧ SameOutside μ μ' dst n
def program : Program := [body]
end ThreeSum.LightReportingFilter


