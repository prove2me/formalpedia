-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_Detector_GramCommonLinear
-- name    : OAI_NumberTheory_DirichletL_Detector_GramCommonLinear
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T19:52:05.026566+00:00
-- url     : https://prove2.me/theorems/c84408a1-1029-412c-a69a-f0946e20ba06
-- title:
--   Gram Common Linear
-- statement:
--   Definitions and structural lemmas for Gram Common Linear, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Detector/GramCommonLinear.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_Detector_GramCommonParam
import Theorems.Thm_OAI_SevenEighths_CenteredMomentCorrelation_scaledResidue_mk
import Theorems.Thm_OAI_SevenEighths_ProbeGramCommon_solutionEquiv_val
attribute [local simp] OAI.SevenEighths.CenteredMomentCorrelation.scaledResidue_mk
attribute [local simp] OAI.SevenEighths.ProbeGramCommon.solutionEquiv_val


set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open CenteredMomentCorrelation
variable {R : Type*} [CommRing R]
def bezoutPairEquiv (n₁ n₂ a b : R) (hab : a*n₁+b*n₂=1) : R×R≃R×R where
  toFun p := (b*p.2+n₁*p.1,-a*p.2+n₂*p.1)
  invFun p := (a*p.1+b*p.2,n₂*p.1-n₁*p.2)
  left_inv p := by
    apply Prod.ext
    · dsimp only
      linear_combination p.1*hab
    · dsimp only
      linear_combination p.2*hab
  right_inv p := by
    apply Prod.ext
    · dsimp only
      linear_combination p.1*hab
    · dsimp only
      linear_combination p.2*hab
end SevenEighths.ProbeGramCommon
end
end OAI


