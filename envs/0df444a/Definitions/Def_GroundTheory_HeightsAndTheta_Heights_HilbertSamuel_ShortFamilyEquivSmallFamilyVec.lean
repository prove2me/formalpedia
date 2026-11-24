-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ShortFamilyEquivSmallFamilyVec
-- name    : GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ShortFamilyEquivSmallFamilyVec
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:22:03.040818+00:00
-- url     : https://prove2.me/theorems/cdae1f6b-ee72-47d1-b26a-f8e3f8c3a505
-- title:
--   Short Family Equiv Small Family Vec
-- statement:
--   Definitions and structural lemmas for Short Family Equiv Small Family Vec, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/ShortFamilyEquivSmallFamilyVec.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsLattice
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StandardLatticeVecIndep
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
theorem fibreNorm_one_tmul (E : HermitianBundle.{0} K) (σ : K →+* ℂ) (v : E.carrier) :
    fibreNorm E σ ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] v) = ‖fibreVec E.metric σ v‖ :=
  rfl
def ShortFamily.toSmallFamily {E : HermitianBundle.{0} K} {lam : (K →+* ℂ) → ℝ}
    (F : ShortFamily E lam) : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel.SmallFamily E lam where
  vec := F.vec
  indep := F.linearIndependent
  norm_le σ i := by
    rw [← fibreNorm_one_tmul]
    exact F.norm_le σ i
def ShortFamily.ofSmallFamily {E : HermitianBundle.{0} K} {lam : (K →+* ℂ) → ℝ}
    (F : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel.SmallFamily E lam) : ShortFamily E lam where
  vec := F.vec
  linearIndependent := F.indep
  norm_le σ i := by
    rw [fibreNorm_one_tmul]
    exact F.norm_le σ i
def shortFamilyEquivSmallFamily (E : HermitianBundle.{0} K) (lam : (K →+* ℂ) → ℝ) :
    ShortFamily E lam ≃ GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel.SmallFamily E lam where
  toFun := ShortFamily.toSmallFamily
  invFun := ShortFamily.ofSmallFamily
  left_inv _ := rfl
  right_inv _ := rfl
end
end GroundTheory.Heights₂.Heights.HilbertSamuel


