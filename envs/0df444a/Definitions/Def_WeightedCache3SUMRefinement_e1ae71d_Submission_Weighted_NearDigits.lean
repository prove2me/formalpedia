-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_NearDigits
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_NearDigits
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T10:06:01.157218+00:00
-- url     : https://prove2.me/theorems/ea5f263b-a81e-4ae6-b1ef-293aafb12717
-- title:
--   NearDigits
-- statement:
--   Definitions and structural lemmas for NearDigits, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/NearDigits.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Enumeration
import Definitions.Def_Submission_ThreeSum_LightTernaryRank
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_Light_Ends_store

set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
namespace ThreeSum.LightWeightedNearDigits
open Light ThreeSum.LightSubsetAddress
open ThreeSum.WeightedEnumeration (digitCost)
open ThreeSum.TernaryJointType ThreeSum.TernaryCodeSemantics
set_option maxHeartbeats 3000000
set_option maxRecDepth 24000
def roundBody (pDigit : ℕ) : Stmt :=
  .set 6 (k 2 *' (v 0 -' k 1 -' v 5)) ;;
  .set 7 (v 6 +' k 1) ;;
  .call pDigit [k 2 *' v 0,v 6,v 7,v 1,v 2] 8 ;;
  .ite (v 8 =' k 2) (.store (v 3 +' v 5) (k 2740))
    (.store (v 3 +' v 5) (k 1369 *' v 8)) ;;
  .store (v 4 +' v 5) (k 1)
def body (pDigit : ℕ) : Stmt := .for 5 (v 0) (roundBody pDigit)
def time (N : ℕ) : ℕ := N*(LightTernaryCodes.digitTime (2*N)+240)+20
def Inv (μ : ℕ → ℤ) (N m powers caps active j : ℕ) (σ : State) : Prop :=
  ∃ lo hi dig : ℤ, ∃ ν : ℕ → ℤ,
    σ=⟨frame [N,m,powers,caps,active,j,lo,hi,dig],ν⟩ ∧
    SameOutside μ ν caps (active+N-caps) ∧
    (∀ i<j, ν (caps+i)=(digitCost (LightTernaryRank.digitAt N m i) : ℤ)) ∧
    (∀ i<j, ν (active+i)=1)
variable {lim : Limits} {P : Program}
end ThreeSum.LightWeightedNearDigits
end WeightedCache3SUMRefinement_e1ae71d


