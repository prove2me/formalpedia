-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_BankAssembly
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_BankAssembly
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T10:12:46.717203+00:00
-- url     : https://prove2.me/theorems/21c82bcc-a2d3-496a-96a7-e4d483a60e3c
-- title:
--   BankAssembly
-- statement:
--   Definitions and structural lemmas for BankAssembly, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/BankAssembly.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_BankStages
import Definitions.Def_Submission_ThreeSum_LightTernaryProduct
import Theorems.Thm_Light_Ends_call

set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
namespace ThreeSum.LightWeightedBankAssembly
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.WeightedBankStageModel
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryQuery ThreeSum.TernaryFrozenQueryStages
open ThreeSum.LightWeightedBankSweep
set_option maxHeartbeats 6000000
variable {lim : Limits}
def body : Stmt :=
  .call 1 [v 0,v 1,v 2,v 3,v 4,v 5,v 6] 9 ;;
  .call 1 [v 0,v 1,v 2,v 3,v 4,v 5,v 7] 9 ;;
  .call 16 [v 6 +' v 0 *' v 2,v 7 +' v 0 *' v 2,v 8,v 2] 9 ;;
  .call 11 [v 0,v 1,v 2,v 3,v 4,v 5,v 8] 9
def program : Program := [body,
  LightWeightedBankSweep.body 2,
  LightWeightedBankCoordinate.body 3 7,
  LightTernaryMetadata.body 4 5 6,
  LightTernaryCodes.zeroBody 6,
  LightTernaryCodes.digitBody 6,
  LightMaskErase.body 6,
  LightTernaryPass.body 8,
  LightTernaryLookup.body 9 10,
  LightBandLookup.searchBody 9,
  LightTernaryCell.zetaBody,
  LightWeightedBankSweep.body 12,
  LightWeightedBankCoordinate.body 3 13,
  LightTernaryInversePass.body 14,
  LightTernaryLookup.body 9 15,
  LightTernaryCell.inverseBody,
  LightTernaryProduct.body]
def product {N : ℕ} (F G : TritWord N→ℤ) (R : TritWord N) : ℤ :=
  forwardStage N F R*forwardStage N G R
def valueBound (N V : ℕ) : ℕ :=(4^N*V)*(4^N*V)
def time (N L n : ℕ) : ℕ :=3*LightWeightedBankSweep.time N L n+LightTernaryProduct.time n+300
def Preserved (μ μ' : ℕ→ℤ) (keyBase n fbase gbase hbase N : ℕ) : Prop :=
  ∀ x, (x<keyBase ∨ keyBase+4*n≤x) →
    (x<fbase+n ∨ fbase+(N+1)*n≤x) →
    (x<gbase+n ∨ gbase+(N+1)*n≤x) →
    (x<hbase ∨ hbase+(N+1)*n≤x) → μ' x=μ x
end ThreeSum.LightWeightedBankAssembly
end WeightedCache3SUMRefinement_e1ae71d


