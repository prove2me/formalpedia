-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_SourceCountHost
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_SourceCountHost
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T11:13:11.906199+00:00
-- url     : https://prove2.me/theorems/380f9a7a-2bd4-4bd7-b8ae-f7e4a14bca57
-- title:
--   SourceCountHost
-- statement:
--   Definitions and structural lemmas for SourceCountHost, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/SourceCountHost.lean

import Definitions.Def_Submission_ThreeSum_LightTernarySourceHost
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_CountFrontend
import Definitions.Def_Submission_ThreeSum_TernarySourceHostModel
import Theorems.Thm_Light_Ends_call

set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
namespace ThreeSum.LightWeightedSourceCountHost
open Light
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000
def sources (xl yl zl xr yr zr : List ℤ) : Program :=
  ReportingHostRelocation.program (LightTernarySourceHost.program xl yl zl)
    (LightTernarySourceHost.program xr yr zr)
def libraries (xl yl zl xr yr zr : List ℤ) : Program :=
  ReportingHostRelocation.program (sources xl yl zl xr yr zr)
    LightWeightedCountFrontend.program
def callArgs (offset count : ℕ) : List Expr :=
  (List.range count).map (fun i => v (offset+i))
def body : Stmt :=
  .call 34 (callArgs 0 23) 106 ;;
  .call 69 (callArgs 23 23) 107 ;;
  .call 133 (callArgs 46 60) 0
def program (xl yl zl xr yr zr : List ℤ) : Program :=
  libraries xl yl zl xr yr zr++[body]
def sourceArgs (base0 dst0 base1 dst1 base2 dst2 J p0 p1 p2
    src count modulus free bankCodes bankSize oldPowers lookupDepth
    keyBase valueBase weightBase factor groups : ℕ) : List ℤ :=
  [base0,dst0,base1,dst1,base2,dst2,J,p0,p1,p2,src,count,modulus,free,
    bankCodes,bankSize,oldPowers,lookupDepth,keyBase,valueBase,weightBase,factor,groups]
def args (left right frontend : List ℤ) : List ℤ :=left++right++frontend
def time (leftTime rightTime frontendTime : ℕ) : ℕ :=
  leftTime+rightTime+frontendTime+500
def Reads (loc : ℕ → ℤ) (offset : ℕ) (vals : List ℤ) : Prop :=
  ∀ i<vals.length, loc (offset+i)=vals.getD i 0
def BankReads (μ : ℕ → ℤ) (base groups bank : ℕ) (values : ℕ → ℕ → ℤ) : Prop :=
  ∀ g<groups, ∀ j<bank, μ (base+g*bank+j)=values g j
end ThreeSum.LightWeightedSourceCountHost
end
end WeightedCache3SUMRefinement_e1ae71d


