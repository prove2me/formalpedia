-- Prove2me | Definitions.Def_Submission_ThreeSum_LightSpanCatalogStep
-- name    : Submission_ThreeSum_LightSpanCatalogStep
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:40:34.786184+00:00
-- url     : https://prove2.me/theorems/33d09439-f93f-4118-8201-14e58010c652
-- title:
--   Light Span Catalog Step
-- statement:
--   Definitions and structural lemmas for Light Span Catalog Step, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSpanCatalogStep.lean

import Definitions.Def_Submission_ThreeSum_LightSpanAxpy
import Theorems.Thm_Light_Ends_call

set_option autoImplicit false
namespace ThreeSum.LightSpanCatalogBlock
open Light
set_option maxHeartbeats 4000000
set_option maxRecDepth 12000
def roundBody (pAxpy : ℕ) : Stmt :=
  .call pAxpy [v 0 +' v 4 *' v 7,v 2,v 3 +' v 4 *' v 7,v 4,v 5,v 6] 8
def body (pAxpy : ℕ) : Stmt := .for 7 (v 1) (roundBody pAxpy)
def time (J p n : ℕ) : ℕ := n*(LightSpanAxpy.time J p+150)+20
def Inv (μ : ℕ → ℤ) (src n rowBase dst J a p : ℕ) (f : ℕ → ℕ → ℕ) (row : ℕ → ℕ)
    (k : ℕ) (σ : State) : Prop := ∃ result : ℤ, ∃ ν : ℕ → ℤ,
    σ=⟨frame [src,n,rowBase,dst,J,a,p,k,result],ν⟩ ∧ SameOutside μ ν dst (J*n) ∧
      ∀ t<k, ∀ i<J, ν (dst+J*t+i)=LightSpanAxpy.values (f t) row a p i
variable {lim : Limits} {P : Program}
end ThreeSum.LightSpanCatalogBlock
namespace ThreeSum.LightSpanCatalogStep
open Light
set_option maxHeartbeats 4000000
set_option maxRecDepth 12000
def roundBody (pBlock : ℕ) : Stmt :=
  .call pBlock [v 0,v 1,v 2,v 3 +' v 4 *' v 1 *' v 6,v 4,v 6,v 5] 7
def body (pBlock : ℕ) : Stmt := .for 6 (v 5) (roundBody pBlock)
def time (J p n : ℕ) : ℕ := p*(LightSpanCatalogBlock.time J p n+150)+20
def Inv (μ : ℕ → ℤ) (src n rowBase dst J p : ℕ) (f : ℕ → ℕ → ℕ) (row : ℕ → ℕ)
    (a : ℕ) (σ : State) : Prop := ∃ result : ℤ, ∃ ν : ℕ → ℤ,
    σ=⟨frame [src,n,rowBase,dst,J,p,a,result],ν⟩ ∧ SameOutside μ ν dst (J*n*p) ∧
      ∀ u<a, ∀ k<n, ∀ i<J, ν (dst+J*n*u+J*k+i)=LightSpanAxpy.values (f k) row u p i
variable {lim : Limits} {P : Program}
def program : Program := [body 1,LightSpanCatalogBlock.body 2,LightSpanAxpy.body 3,
  LightPrimeCoefficient.mulAddBody 4,LightSmallDivide.body]
end ThreeSum.LightSpanCatalogStep


