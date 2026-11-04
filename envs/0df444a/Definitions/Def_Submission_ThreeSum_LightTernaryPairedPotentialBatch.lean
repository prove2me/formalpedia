-- Prove2me | Definitions.Def_Submission_ThreeSum_LightTernaryPairedPotentialBatch
-- name    : Submission_ThreeSum_LightTernaryPairedPotentialBatch
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:49:51.488343+00:00
-- url     : https://prove2.me/theorems/8cb61456-afa3-4ff3-9de3-a07fb7de727b
-- title:
--   Light Ternary Paired Potential Batch
-- statement:
--   Definitions and structural lemmas for Light Ternary Paired Potential Batch, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryPairedPotentialBatch.lean

import Definitions.Def_Submission_ThreeSum_LightTernaryPairedPotential
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
noncomputable section
namespace ThreeSum.LightTernaryPairedPotentialBatch
open Light LightTernaryPairedPotential
open scoped BigOperators
set_option maxHeartbeats 2000000
def body (pPotential : ℕ) : Stmt :=
  .set 5 (k 0) ;;
  .for 6 (v 2) (
    .call pPotential [v 0 +' v 6 *' (v 1 *' v 1 *' v 1 *' v 1),v 1,v 3,v 4] 7 ;;
    .set 5 (v 5 +' v 7)) ;;
  .set 0 (v 5)
def time (K Λ H : ℕ) : ℕ := H*(LightTernaryPairedPotential.time K Λ+100)+50
def term (K base Λ : ℕ) (μ : ℕ→ℤ) (i : ℕ) : ℤ :=
  LightTernaryPairedPotential.prefixSum K (base+i*Λ^4) Λ μ (Λ^TernaryPairedColumnEnumeration.width K)
def total (K base Λ : ℕ) (μ : ℕ→ℤ) (H : ℕ) : ℤ := ∑ i∈Finset.range H, term K base Λ μ i
def Inv (K base Λ H cols powers cutoff : ℕ) (μ : ℕ→ℤ) (i : ℕ) (σ : State) : Prop :=
  ∃ (ret : ℤ) (ν : ℕ→ℤ),
    σ=⟨frame [base,Λ,H,cols,powers,total K base Λ μ i,i,ret],ν⟩ ∧ Kept μ ν cutoff
end ThreeSum.LightTernaryPairedPotentialBatch


