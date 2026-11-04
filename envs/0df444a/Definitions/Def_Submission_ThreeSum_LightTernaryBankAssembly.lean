-- Prove2me | Definitions.Def_Submission_ThreeSum_LightTernaryBankAssembly
-- name    : Submission_ThreeSum_LightTernaryBankAssembly
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:53:50.587222+00:00
-- url     : https://prove2.me/theorems/44213b86-e903-4b44-a735-3d7494fa8b5f
-- title:
--   Light Ternary Bank Assembly
-- statement:
--   Definitions and structural lemmas for Light Ternary Bank Assembly, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryBankAssembly.lean

import Definitions.Def_Submission_ThreeSum_LightTernaryBankStages
import Definitions.Def_Submission_ThreeSum_LightTernaryProduct
import Theorems.Thm_Light_Ends_call

set_option autoImplicit false
namespace ThreeSum.LightTernaryBankAssembly
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.TernaryBankStageModel
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryQuery ThreeSum.TernaryFrozenQueryStages
open ThreeSum.LightTernaryBankSweep
set_option maxHeartbeats 6000000
variable {lim : Limits}
def body : Stmt :=
  .call 1 [v 0,v 1,v 2,v 3,v 4,v 5,v 6] 9 ;;
  .call 1 [v 0,v 1,v 2,v 3,v 4,v 5,v 7] 9 ;;
  .call 16 [v 6 +' v 0 *' v 2,v 7 +' v 0 *' v 2,v 8,v 2] 9 ;;
  .call 11 [v 0,v 1,v 2,v 3,v 4,v 5,v 8] 9
def program : Program := [body,
  LightTernaryBankSweep.body 2,
  LightTernaryBankCoordinate.body 3 7,
  LightTernaryMetadata.body 4 5 6,
  LightTernaryCodes.zeroBody 6,
  LightTernaryCodes.digitBody 6,
  LightMaskErase.body 6,
  LightTernaryPass.body 8,
  LightTernaryLookup.body 9 10,
  LightBandLookup.searchBody 9,
  LightTernaryCell.zetaBody,
  LightTernaryBankSweep.body 12,
  LightTernaryBankCoordinate.body 3 13,
  LightTernaryInversePass.body 14,
  LightTernaryLookup.body 9 15,
  LightTernaryCell.inverseBody,
  LightTernaryProduct.body]
def product {N : ℕ} (F G : TritWord N→ℤ) (R : TritWord N) : ℤ :=
  forwardStage N F R*forwardStage N G R
def valueBound (N V : ℕ) : ℕ :=(4^N*V)*(4^N*V)
def time (N L n : ℕ) : ℕ :=3*LightTernaryBankSweep.time N L n+LightTernaryProduct.time n+300
def Preserved (μ μ' : ℕ→ℤ) (keyBase n fbase gbase hbase N : ℕ) : Prop :=
  ∀ x, (x<keyBase ∨ keyBase+4*n≤x) →
    (x<fbase+n ∨ fbase+(N+1)*n≤x) →
    (x<gbase+n ∨ gbase+(N+1)*n≤x) →
    (x<hbase ∨ hbase+(N+1)*n≤x) → μ' x=μ x
end ThreeSum.LightTernaryBankAssembly


