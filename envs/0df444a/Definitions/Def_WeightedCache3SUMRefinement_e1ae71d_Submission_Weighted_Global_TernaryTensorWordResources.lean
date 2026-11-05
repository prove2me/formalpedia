-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryTensorWordResources
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryTensorWordResources
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T11:57:09.099061+00:00
-- url     : https://prove2.me/theorems/896a0c0c-eac6-4851-ba9c-684b6b595444
-- title:
--   TernaryTensorWordResources
-- statement:
--   Definitions and structural lemmas for TernaryTensorWordResources, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryTensorWordResources.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryTensorFactoryReady
import Definitions.Def_Submission_ThreeSum_PolynomialResources
set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
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
end
end WeightedCache3SUMRefinement_e1ae71d


