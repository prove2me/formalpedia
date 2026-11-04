-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryTensorWordResources
-- name    : Submission_Weighted_Global_TernaryTensorWordResources
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T14:35:02.860159+00:00
-- url     : https://prove2.me/theorems/c140262a-37b5-436f-baa1-c1a0e3725c44
-- title:
--   Ternary Tensor Word Resources
-- statement:
--   Definitions and structural lemmas for Ternary Tensor Word Resources, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryTensorWordResources.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryTensorFactoryReady
import Definitions.Def_Submission_ThreeSum_PolynomialResources
set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalTensorWordResources
open LightTernaryPairedPolynomial TernaryPairedColumnEnumeration StageBounds
def polynomialBound (K V : ℕ) : ℕ :=
  (polynomial K).coefficient.toNat*(V+1)^(polynomial K).degree
def potentialWord (K J V : ℕ) : ℕ :=
  10*((J+2)^(width K+1)+(J+2)^width K+width K+(J+2)+2)+
    2*((J+2)^width K+1)*(polynomialBound K V+1)
def word (K J count V sourceU : ℕ) : ℕ :=
  potentialWord K J V+polynomialBound K V+
    count*(J+2)^width K*polynomialBound K V+
    LightWeightRow.word 4 (J+2) ((J+2)^4) 0 1+
    J+3+count+(J+2)^4+(sourceU+1)^2+1
def need (K J count V sourceU : ℕ) : Light.Need :=
  ⟨word K J count V sourceU,count*(J+2)^4+width K+(width K+1)+12,5⟩
def Poly (f : ℕ→ℕ) : Prop :=∃ a : ℝ, PowerBound f a
end ThreeSum.WeightedGlobalTensorWordResources


