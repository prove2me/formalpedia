-- Prove2me | Definitions.Def_OAIQ050L024
-- name    : OAIQ050L024
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T11:04:29.451663+00:00
-- url     : https://prove2.me/theorems/d4bf4928-f759-459f-8754-4515eb95db9e
-- title:
--   Definitions bundle OAIQ050L024 of the split of OpenAI, A Fock-space inequality and the Laughlin spectral gap
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Laughlin.planar_gap`, carved from OpenAI's openai/math development (OpenAI, *A Fock-space inequality and the Laughlin spectral gap*, OpenAI Math Release, September 24, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 11 declarations of OpenAI's Lean: 2 definitions and 9 theorems. The definitions and types are `OAI.Laughlin.Spin.fourBodySpinRepresentation`, `OAI.Laughlin.Spin.wedgePairRepresentation`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Laughlin_FourBody_GroupIntertwining`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/FourBody/GroupIntertwining.lean), [`Laughlin_Operators_WedgePairRepresentation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/Operators/WedgePairRepresentation.lean), [`Laughlin_Operators_WedgePairRotation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/Operators/WedgePairRotation.lean), [`Laughlin_Spin_Endpoint`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/Spin/Endpoint.lean), [`Laughlin_Spin_Intertwining`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/Spin/Intertwining.lean).
--
--   **Imports.** It imports the bundle `OAIQ050L022` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI_Laughlin_Fock_sourceFourFamilyEnd_rotation`, `OAI.Laughlin.Fock.sourceFourFamilyEnd_rotation_s50`, `OAI_Laughlin_Fock_sourceFourVector_rotation`, `OAI.Laughlin.Fock.sourceFourVector_rotation_s50`, `OAI_Laughlin_Spin_fourBody_cross_orbit`, `OAI.Laughlin.Spin.fourBody_cross_orbit_s50`, `OAI_Laughlin_Spin_fourBody_haar_compressed`, `OAI.Laughlin.Spin.fourBody_haar_compressed_s50`, `OAI_Laughlin_Spin_fourBody_haar_unequal_spin`, `OAI.Laughlin.Spin.fourBody_haar_unequal_spin_s50`, `OAI_Laughlin_Spin_physicalFourBodyHaar_hermitian`, `OAI.Laughlin.Spin.physicalFourBodyHaar_hermitian_s50`, `OAI_Laughlin_Spin_physicalFourBodyHaar_high_column`, `OAI.Laughlin.Spin.physicalFourBodyHaar_high_column_s50`, `OAI_Laughlin_Spin_physicalFourBodyHaar_retained_sum`, `OAI.Laughlin.Spin.physicalFourBodyHaar_retained_sum_s50`, `OAI_Laughlin_Spin_physical_fourBody_haar_multiplicity`, `OAI.Laughlin.Spin.physical_fourBody_haar_multiplicity_s50`, `OAI_Laughlin_Spin_retainedFourInclusion_adjoint_SU2` and `OAI.Laughlin.Spin.retainedFourInclusion_adjoint_SU2_s50`; the proofs of `OAI_Laughlin_Fock_physicalFourCopyEnd_cross_haar`, `OAI.Laughlin.Fock.physicalFourCopyEnd_cross_haar_s50`, `OAI_Laughlin_Fock_sourceA4Form_retained`, `OAI.Laughlin.Fock.sourceA4Form_retained_s50`, `OAI_Laughlin_Fock_sourceFourFamilyEnd_rotation`, `OAI.Laughlin.Fock.sourceFourFamilyEnd_rotation_s50`, `OAI_Laughlin_Fock_sourceFourVector_rotation`, `OAI.Laughlin.Fock.sourceFourVector_rotation_s50`, `OAI_Laughlin_Fock_sourceThreeHighestEnd_haar`, `OAI.Laughlin.Fock.sourceThreeHighestEnd_haar_s50`, `OAI_Laughlin_Spin_fourBody_cross_orbit`, `OAI.Laughlin.Spin.fourBody_cross_orbit_s50`, `OAI_Laughlin_Spin_fourBody_haar_compressed`, `OAI.Laughlin.Spin.fourBody_haar_compressed_s50`, `OAI_Laughlin_Spin_fourBody_haar_unequal_spin`, `OAI.Laughlin.Spin.fourBody_haar_unequal_spin_s50`, `OAI_Laughlin_Spin_physicalFourBodyHaar_hermitian`, `OAI.Laughlin.Spin.physicalFourBodyHaar_hermitian_s50`, `OAI_Laughlin_Spin_physicalFourBodyHaar_high_column`, `OAI.Laughlin.Spin.physicalFourBodyHaar_high_column_s50`, `OAI_Laughlin_Spin_physicalFourBodyHaar_retained_sum`, `OAI.Laughlin.Spin.physicalFourBodyHaar_retained_sum_s50`, `OAI_Laughlin_Spin_physical_fourBody_haar_multiplicity`, `OAI.Laughlin.Spin.physical_fourBody_haar_multiplicity_s50`, `OAI_Laughlin_Spin_retainedFourInclusion_adjoint_SU2`, `OAI.Laughlin.Spin.retainedFourInclusion_adjoint_SU2_s50`, `OAI_Laughlin_Spin_threeBody_haar_diagonal_block`, `OAI.Laughlin.Spin.threeBody_haar_diagonal_block_s50`, `OAI_Laughlin_Spin_threeBody_haar_offdiagonal_block`, `OAI.Laughlin.Spin.threeBody_haar_offdiagonal_block_s50`, `OAI_Laughlin_Spin_threeCoupledInclusion_adjoint_SU2` and `OAI.Laughlin.Spin.threeCoupledInclusion_adjoint_SU2_s50`.
-- source:
--   OpenAI, A Fock-space inequality and the Laughlin spectral gap, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ050L022

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Spin_Endpoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

theorem genericUnitDescendant_raising_succ (A B z n : ℕ) (hA : z ≤ A) (hB : z ≤ B)
    (hn : n < genericCoupledWeight A B z) :
    totalRaise A B *ᵥ genericUnitDescendant A B z hA hB (n+1) =
      Real.sqrt (((n : ℝ)+1)*((genericCoupledWeight A B z : ℝ)-n)) •
        genericUnitDescendant A B z hA hB n := by
  have hr : totalRaise A B *ᵥ genericDescendant A B z hA hB (n+1) =
      (((n : ℝ)+1)*((genericCoupledWeight A B z : ℝ)-n)) • genericDescendant A B z hA hB n := by
    exact descendant_raising (totalRaise A B) (totalWeight A B) (totalRaise A B)ᵀ
      (genericHighest A B z hA hB) (genericCoupledWeight A B z)
      (total_raise_lower_commutator A B) (total_weight_lower_commutator A B)
      (genericHighest_weight A B z hA hB) (genericHighest_raising_zero A B z hA hB) n
  have hc : 0 < ((n : ℝ)+1)*((genericCoupledWeight A B z : ℝ)-n) := by
    have hn' : (n : ℝ) < genericCoupledWeight A B z := by exact_mod_cast hn
    positivity
  have hden : Real.sqrt (vectorNormSq (genericDescendant A B z hA hB (n+1))) =
      Real.sqrt (((n : ℝ)+1)*((genericCoupledWeight A B z : ℝ)-n))*
        Real.sqrt (vectorNormSq (genericDescendant A B z hA hB n)) := by
    rw [genericDescendant_norm_step,Real.sqrt_mul (le_of_lt hc)]
  have hx : (Real.sqrt (((n : ℝ)+1)*((genericCoupledWeight A B z : ℝ)-n)))⁻¹ *
      (((n : ℝ)+1)*((genericCoupledWeight A B z : ℝ)-n)) =
        Real.sqrt (((n : ℝ)+1)*((genericCoupledWeight A B z : ℝ)-n)) := by
    apply mul_left_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr hc))
    rw [mul_inv_cancel_left₀ (ne_of_gt (Real.sqrt_pos.mpr hc))]
    exact (Real.mul_self_sqrt (le_of_lt hc)).symm
  unfold genericUnitDescendant
  rw [Matrix.mulVec_smul,hr,smul_smul,smul_smul,hden,mul_inv_rev]
  rw [mul_assoc,hx,mul_comm]

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Spin_Intertwining
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix Kronecker

theorem genericCoupledInclusion_raising (A B z : ℕ) (hA : z ≤ A) (hB : z ≤ B) :
    totalRaise A B*genericCoupledInclusion A B z hA hB =
      genericCoupledInclusion A B z hA hB*raiseMatrix (genericCoupledWeight A B z) := by
  funext i n
  change (totalRaise A B *ᵥ genericUnitDescendant A B z hA hB n.val) i =
    ∑ k, genericUnitDescendant A B z hA hB k.val i * raiseMatrix (genericCoupledWeight A B z) k n
  rw [raiseMatrix_column]
  by_cases hn : 0 < n.val
  · rw [dite_eq_left hn]
    have h := genericUnitDescendant_raising_succ A B z (n.val-1) hA hB (by omega)
    rw [show n.val-1+1=n.val by omega] at h
    have he := congrFun h i
    simpa [ladder,Nat.cast_sub (show n.val-1 ≤ genericCoupledWeight A B z by omega),mul_comm] using he
  · rw [dite_eq_right hn]
    have hz : n.val=0 := by omega
    rw [hz,genericUnitDescendant_zero,genericHighest_raising_zero]
    rfl

theorem genericCoupledInclusion_SU2 (A B z : ℕ) (hA : z ≤ A) (hB : z ≤ B)
    (g : Rotation.SourceSU2) :
    (Rotation.sourceSpinRepresentation A g ⊗ₖ Rotation.sourceSpinRepresentation B g)*
      (genericCoupledInclusion A B z hA hB).map Complex.ofReal =
      (genericCoupledInclusion A B z hA hB).map Complex.ofReal*
        Rotation.sourceSpinRepresentation (genericCoupledWeight A B z) g := by
  apply Rotation.ladder_intertwiner_SU2 A B z (genericCoupledWeight A B z)
    (by unfold genericCoupledWeight; omega)
  · intro i n hn
    simp only [Matrix.map_apply,genericCoupledInclusion,genericUnitDescendant_off A B z n.val hA hB i hn,
      Complex.ofReal_zero]
  · ext i n
    have h := congrArg Complex.ofReal (congrFun (congrFun (genericCoupledInclusion_raising A B z hA hB) i) n)
    simpa [Rotation.totalRaiseComplex,Rotation.spinRaiseComplex,Matrix.mul_apply] using h
  · ext i n
    have h := congrArg Complex.ofReal (congrFun (congrFun (genericCoupledInclusion_lowering A B z hA hB) i) n)
    simpa [Rotation.totalRaiseComplex,Rotation.spinRaiseComplex,Matrix.mul_apply,Matrix.transpose_apply] using h

theorem physicalCoupledInclusion_SU2 (A B z : ℕ) (hA : z ≤ A) (hB : z ≤ B)
    (g : Rotation.SourceSU2) :
    (Rotation.sourceSpinRepresentation A g ⊗ₖ Rotation.sourceSpinRepresentation B g)*
      physicalCoupledInclusion A B z hA hB =
      physicalCoupledInclusion A B z hA hB*
        Rotation.sourceSpinRepresentation (genericCoupledWeight A B z) g := by
  simp only [physicalCoupledInclusion,Matrix.mul_smul,Matrix.smul_mul,genericCoupledInclusion_SU2]

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Operators_WedgePairRotation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open Rotation
open scoped BigOperators Matrix Kronecker

theorem pairCoupledInclusion_SU2 (Q r : ℕ) (hr : r ≤ Q) (hor : Odd r) (g : SourceSU2) :
    wedgePairMatrix Q g * (pairCoupledInclusion Q r hr).map Complex.ofReal =
      (pairCoupledInclusion Q r hr).map Complex.ofReal *
        sourceSpinRepresentation (genericCoupledWeight Q Q r) g := by
  ext i n
  have hp : physicalCoupledInclusion Q Q r hr hr =
      (fun j k => (pairCoupledTensor Q r hr k.val j : ℂ)) := by
    ext j k
    simp [physicalCoupledInclusion,genericCoupledInclusion,pairCoupledTensor]
  have h := congrFun (congrFun (physicalCoupledInclusion_SU2 Q Q r hr hr g) i.val) n
  rw [hp] at h
  have hf (a b : Fin (Q+1)) :
      (pairCoupledTensor Q r hr n.val (b,a) : ℂ) = -(pairCoupledTensor Q r hr n.val (a,b) : ℂ) := by
    exact_mod_cast pairCoupledTensor_antisymmetric Q r n.val hr hor a b
  change (wedgePairMatrix Q g *ᵥ
    (fun j => (pairCoupledWedge Q r hr n.val j : ℂ))) i = _
  simp only [pairCoupledWedge,tensorToWedgePair,Complex.ofReal_mul]
  rw [wedgePairMatrix_tensor Q g (fun j : SpinIndex Q Q => (pairCoupledTensor Q r hr n.val j : ℂ)) hf i]
  change ((sourceSpinRepresentation Q g ⊗ₖ sourceSpinRepresentation Q g) *ᵥ
    (fun j : SpinIndex Q Q => (pairCoupledTensor Q r hr n.val j : ℂ))) i.val =
      ∑ k, (pairCoupledTensor Q r hr k.val i.val : ℂ) *
        sourceSpinRepresentation (genericCoupledWeight Q Q r) g k n at h
  rw [h]
  simp only [Matrix.mul_apply,Matrix.map_apply,pairCoupledInclusion,pairCoupledWedge,
    tensorToWedgePair,Complex.ofReal_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  ring

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Operators_WedgePairRepresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open Rotation
open scoped BigOperators Matrix

theorem wedgePairMatrix_basis (Q : ℕ) (g : SourceSU2) :
    wedgePairMatrix Q g * complexPairBasis Q = complexPairBasis Q * pairBasisAction Q g := by
  ext i s
  have hb : (complexPairBasis Q * pairBasisAction Q g) i s =
      ∑ n, complexPairBasis Q i ⟨s.1,n⟩ *
        sourceSpinRepresentation (genericCoupledWeight Q Q (oddPairDeficit s.1)) g n s.2 := by
    rw [Matrix.mul_apply,Fintype.sum_sigma,Finset.sum_eq_single s.1]
    · cases s; simp only [pairBasisAction,Matrix.blockDiagonal'_apply_eq]
    · intro r hr hrs
      simp only [pairBasisAction,Matrix.blockDiagonal'_apply_ne _ _ _ hrs,mul_zero,Finset.sum_const_zero]
    · simp
  rw [hb]
  exact congrFun (congrFun (pairCoupledInclusion_SU2 Q (oddPairDeficit s.1)
    (oddPairDeficit_le s.1) (oddPairDeficit_odd s.1) g) i) s.2

theorem wedgePairMatrix_factor (Q : ℕ) (g : SourceSU2) :
    wedgePairMatrix Q g = complexPairBasis Q * pairBasisAction Q g * (complexPairBasis Q)ᴴ := by
  rw [← wedgePairMatrix_basis,Matrix.mul_assoc,complexPairBasis_complete,Matrix.mul_one]

theorem wedgePairMatrix_one (Q : ℕ) : wedgePairMatrix Q 1=1 := by
  rw [wedgePairMatrix_factor,pairBasisAction_one,Matrix.mul_one,complexPairBasis_complete]

theorem wedgePairMatrix_mul (Q : ℕ) (g h : SourceSU2) :
    wedgePairMatrix Q (g*h) = wedgePairMatrix Q g * wedgePairMatrix Q h := by
  rw [wedgePairMatrix_factor,wedgePairMatrix_factor Q g,wedgePairMatrix_factor Q h,pairBasisAction_mul]
  calc
    _ = complexPairBasis Q * pairBasisAction Q g *
      ((complexPairBasis Q)ᴴ * complexPairBasis Q) * pairBasisAction Q h * (complexPairBasis Q)ᴴ := by
      rw [complexPairBasis_isometry,Matrix.mul_one]
      simp only [Matrix.mul_assoc]
    _ = _ := by simp only [Matrix.mul_assoc]

noncomputable def wedgePairRepresentation (Q : ℕ) :
    SourceSU2 →* Matrix (WedgePairIndex Q) (WedgePairIndex Q) ℂ where
  toFun := wedgePairMatrix Q
  map_one' := wedgePairMatrix_one Q
  map_mul' := wedgePairMatrix_mul Q

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_GroupIntertwining
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open Rotation
open scoped BigOperators Matrix Kronecker

noncomputable def fourBodySpinRepresentation (Q : ℕ) :
    SourceSU2 →* Matrix (FourWedgeIndex Q) (FourWedgeIndex Q) ℂ where
  toFun g := sourceSpinRepresentation (2*Q-2) g ⊗ₖ wedgePairRepresentation Q g
  map_one' := by simp only [map_one,Matrix.one_kronecker_one]
  map_mul' g h := by simp only [map_mul,Matrix.mul_kronecker_mul]

end Laughlin.Spin

end OAI
end


