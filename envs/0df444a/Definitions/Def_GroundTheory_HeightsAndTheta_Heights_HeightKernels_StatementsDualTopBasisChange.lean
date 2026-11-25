-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsDualTopBasisChange
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsDualTopBasisChange
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T05:56:23.568383+00:00
-- url     : https://prove2.me/theorems/4e206ffb-1232-531e-908a-cff57f215355
-- title:
--   Statements Dual Top Basis Change
-- statement:
--   Definitions and structural lemmas for Statements Dual Top Basis Change, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/StatementsDualTopBasisChange.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ScaledExample
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualEmbBijective
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualEmbBijective_proof_80ddea4cacea

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo NumberField
open scoped ComplexOrder
noncomputable section
def DualTopBasisChange.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F : HermLattice K i) (T T₂ : Type) [Fintype T]
    [DecidableEq T] [Fintype T₂] [DecidableEq T₂] (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b)))
    (b₂ : Module.Basis T₂ ℤ (dualLattice F))
    (hb₂ : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b₂))) (II : IntersectionSystem),
    1 ≤ i → IsIntersectionSystem II →
    II Unit (dualBlocks T₂) (dualIdeal b₂) i (fun _ => dualLine F b₂ hb₂) =
      II Unit (dualBlocks T) (dualIdeal b) i (fun _ => dualLine F b hb)
def dualBasisStandardNeg : Module.Basis (Fin 1) ℤ (dualLattice (HermLattice.standard ℚ 1)) :=
  (dualBasisStandard.map (LinearEquiv.neg ℤ)).reindex (Equiv.ofUnique Unit (Fin 1))
example : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix dualBasisStandard)) ∧
    Function.Bijective (Matrix.mulVecLin (dualEmbMatrix dualBasisStandardNeg)) ∧ 1 ≤ 1 ∧
    (dualBasisStandardNeg 0 : Fin 1 → ℚ) ≠ (dualBasisStandard () : Fin 1 → ℚ) := by
  refine ⟨dualEmbMatrix_standard_bijective, DualEmbBijective.proof ℚ 1 _ _ _, le_rfl, fun h => ?_⟩
  have h0 := congrFun h 0
  simp [dualBasisStandardNeg, dualBasisStandard_apply, oneDual] at h0
  norm_num at h0
end
end GroundTheory.Heights₂.Heights


