-- Prove2me | Definitions.Def_Submission_ThreeSum_LightBlockCoefficients
-- name    : Submission_ThreeSum_LightBlockCoefficients
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:28:41.796522+00:00
-- url     : https://prove2.me/theorems/5d20edf7-4693-4955-aeff-4eacd8aa270b
-- title:
--   Light Block Coefficients
-- statement:
--   Definitions and structural lemmas for Light Block Coefficients, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBlockCoefficients.lean

import Definitions.Def_Submission_ThreeSum_LightScaleArray
import Definitions.Def_Submission_ThreeSum_LightSubsetAddress
import Definitions.Def_Submission_ThreeSum_BlockIndex
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
namespace ThreeSum.LightBlockCoefficients
open Light
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
variable {lim : Limits} {P : Program}
def Powers (μ : ℕ → ℤ) (work J p : ℕ) : Prop :=
  ∀ i ≤ J, μ (work+i) = ((p^i : ℕ) : ℤ)
def Rows (μ : ℕ → ℤ) (dst0 dst1 L p : ℕ) (sel : ℕ → ℕ)
    (w0 w1 : ℕ → ℕ → ℕ) (j : ℕ) : Prop :=
  ∀ a < j, ∀ i < L,
    μ (dst0+a*L+i) = ((p^a*w0 (sel a) i : ℕ) : ℤ) ∧
    μ (dst1+a*L+i) = ((p^a*w1 (sel a) i : ℕ) : ℤ)
def roundBody (pScale : ℕ) : Stmt :=
  .set 9 (v 4 +' k 2 *' v 1 *' M (v 3 +' v 8)) ;;
  .set 10 (v 5 +' v 8 *' v 1) ;;
  .set 11 (v 6 +' v 8 *' v 1) ;;
  .call pScale [v 9,v 10,v 1,M (v 7 +' v 8)] 12 ;;
  .call pScale [v 9 +' v 1,v 11,v 1,M (v 7 +' v 8)] 13
def body (pPowers pScale : ℕ) : Stmt :=
  .call pPowers [v 7,v 0 +' k 1,v 2] 8 ;;
  .for 8 (v 0) (roundBody pScale)
def roundTime (L : ℕ) : ℕ := 2*LightScaleArray.time L+100
def time (J L : ℕ) : ℕ := powTableTime (J+1)+J*(roundTime L+20)+100
def word (J p U : ℕ) : ℕ := p^(J+1)*(U+1)
def Inv (μ : ℕ → ℤ) (J L p occ maps dst0 dst1 work : ℕ)
    (sel : ℕ → ℕ) (w0 w1 : ℕ → ℕ → ℕ) (j : ℕ) (σ : State) : Prop :=
  ∃ (s a b r0 r1 : ℤ) (ν : ℕ → ℤ),
    σ = ⟨frame [J,L,p,occ,maps,dst0,dst1,work,j,s,a,b,r0,r1],ν⟩ ∧
    Rows ν dst0 dst1 L p sel w0 w1 j ∧ Kept μ ν dst0 ∧ Powers ν work J p
def program : Program := [body 1 2,powTableBody,LightScaleArray.body]
end ThreeSum.LightBlockCoefficients


