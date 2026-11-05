-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_BankSweep
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_BankSweep
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T10:11:20.669139+00:00
-- url     : https://prove2.me/theorems/1b78a45c-8e10-4c5f-994b-ead52b1526e6
-- title:
--   BankSweep
-- statement:
--   Definitions and structural lemmas for BankSweep, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/BankSweep.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_BankCoordinate
import Theorems.Thm_Light_Ends_call

set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
namespace ThreeSum.LightWeightedBankSweep
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.WeightedBankStageModel
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryFrozenQueryStages
set_option maxHeartbeats 5000000
variable {lim : Limits} {P : Program}
def roundBody (pCoord : ℕ) : Stmt :=
  .call pCoord [v 0,k 2 *' (v 0 -' (v 7 +' k 1)),k 2 *' (v 0 -' (v 7 +' k 1)) +' k 1,
    v 1,v 2,v 3,v 4,v 5,v 6 +' v 7 *' v 2,v 6 +' (v 7 +' k 1) *' v 2] 8
def body (pCoord : ℕ) : Stmt := .for 7 (v 0) (roundBody pCoord)
def time (N L n : ℕ) : ℕ :=N*(LightWeightedBankCoordinate.time N L n+100)+100
def Preserved (μ μ' : ℕ→ℤ) (keyBase n base N : ℕ) : Prop :=
  ∀ x, (x<keyBase ∨ keyBase+4*n≤x) → (x<base+n ∨ base+(N+1)*n≤x) → μ' x=μ x
def Stages {N T n : ℕ} (E : Enumeration N T n) (φ : ℕ→TritWord N→ℤ)
    (base : ℕ) (k : ℕ) (μ : ℕ→ℤ) : Prop :=
  ∀ s≤k, ∀ j<n, μ (base+s*n+j)=φ s (E.word j)
def Inv {N T n : ℕ} (E : Enumeration N T n) (φ : ℕ→TritWord N→ℤ)
    (μ : ℕ→ℤ) (a powers L keyBase base : ℕ) (k : ℕ) (σ : State) : Prop :=
  ∃ (r : ℤ) (μ' : ℕ→ℤ), σ=⟨frame [N,a,n,powers,L,keyBase,base,k,r],μ'⟩ ∧
    Stages E φ base k μ' ∧ Preserved μ μ' keyBase n base N ∧
    Powers μ' powers (2*N)
end ThreeSum.LightWeightedBankSweep
end WeightedCache3SUMRefinement_e1ae71d


