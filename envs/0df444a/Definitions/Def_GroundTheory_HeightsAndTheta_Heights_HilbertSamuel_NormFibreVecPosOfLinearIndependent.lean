-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_NormFibreVecPosOfLinearIndependent
-- name    : GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_NormFibreVecPosOfLinearIndependent
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:31:52.509121+00:00
-- url     : https://prove2.me/theorems/72ee0474-7371-4341-ae0e-0fd106b47cc3
-- title:
--   Norm Fibre Vec Pos Of Linear Independent
-- statement:
--   Definitions and structural lemmas for Norm Fibre Vec Pos Of Linear Independent, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/NormFibreVecPosOfLinearIndependent.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsLattice
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StandardLatticeVecIndep
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ShortFamilyEquivSmallFamilyVec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
open NumberField TensorProduct
noncomputable section
variable {K : Type} [Field K] [NumberField K]
omit [NumberField K] in

def posOrOne (f : (K →+* ℂ) → ℝ) (σ : K →+* ℂ) : ℝ := if 0 < f σ then f σ else 1
omit [NumberField K] in
theorem le_posOrOne {f : (K →+* ℂ) → ℝ} {σ : K →+* ℂ} {y : ℝ} (h : y ≤ f σ) :
    y ≤ posOrOne f σ := by
  unfold posOrOne
  split_ifs with hf
  · exact h
  · have hf' := not_lt.mp hf; linarith
def ShortFamily.posOrOne {E : HermitianBundle.{0} K} {lam : (K →+* ℂ) → ℝ}
    (F : ShortFamily E lam) : ShortFamily E (posOrOne lam) where
  vec := F.vec
  linearIndependent := F.linearIndependent
  norm_le σ i := le_posOrOne (F.norm_le σ i)
end
end GroundTheory.Heights₂.Heights.HilbertSamuel


