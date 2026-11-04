-- Prove2me | Definitions.Def_Submission_ThreeSum_LightSpanCatalogTest
-- name    : Submission_ThreeSum_LightSpanCatalogTest
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:43:48.867225+00:00
-- url     : https://prove2.me/theorems/6af30c67-1c00-428a-b164-51ba392e2b7f
-- title:
--   Light Span Catalog Test
-- statement:
--   Definitions and structural lemmas for Light Span Catalog Test, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSpanCatalogTest.lean

import Definitions.Def_Submission_ThreeSum_LightSpanCatalogStep
import Definitions.Def_Submission_ThreeSum_TernaryOriginalSpanCatalog
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_Light_Ends_skip

set_option autoImplicit false
noncomputable section
namespace ThreeSum.LightSpanRowEqual
open Light
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 3000000
def flag (f g : ℕ → ℤ) (j : ℕ) : ℕ := if ∀ i<j, f i=g i then 1 else 0
def roundBody : Stmt := .ite (M (v 0 +' v 4) =' M (v 1 +' v 4)) .skip (.set 3 (k 0))
def body : Stmt := .set 3 (k 1) ;; .for 4 (v 2) roundBody ;; .set 0 (v 3)
def time (J : ℕ) : ℕ := 60*J+50
variable {lim : Limits} {P : Program}
end ThreeSum.LightSpanRowEqual
namespace ThreeSum.LightSpanCatalogTest
open Light
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
def Present (f : ℕ → ℕ → ℤ) (row : ℕ → ℤ) (J n : ℕ) : Prop := ∃ k<n, ∀ i<J, f k i=row i
def flag (f : ℕ → ℕ → ℤ) (row : ℕ → ℤ) (J n : ℕ) : ℕ := if Present f row J n then 0 else 1
def roundBody (pEq : ℕ) : Stmt :=
  .call pEq [v 0 +' v 2 *' v 5,v 3,v 2] 6 ;;
  .ite (v 6 =' k 1) (.set 4 (k 0)) .skip
def body (pEq : ℕ) : Stmt := .set 4 (k 1) ;; .for 5 (v 1) (roundBody pEq) ;; .set 0 (v 4)
def time (J n : ℕ) : ℕ := n*(LightSpanRowEqual.time J+150)+100
def Inv (μ : ℕ → ℤ) (catalog n J candidate : ℕ) (f : ℕ → ℕ → ℤ) (row : ℕ → ℤ) (k : ℕ) (σ : State) : Prop :=
  ∃ result : ℤ, σ=⟨frame [catalog,n,J,candidate,flag f row J k,k,result],μ⟩
variable {lim : Limits} {P : Program}
def program : Program := [body 1,LightSpanRowEqual.body]
end ThreeSum.LightSpanCatalogTest


