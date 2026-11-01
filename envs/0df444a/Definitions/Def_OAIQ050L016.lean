-- Prove2me | Definitions.Def_OAIQ050L016
-- name    : OAIQ050L016
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T09:11:09.714595+00:00
-- url     : https://prove2.me/theorems/7fead470-ff1d-48f7-aa39-adced4d04217
-- title:
--   Definitions bundle OAIQ050L016 of the split of OpenAI, A Fock-space inequality and the Laughlin spectral gap
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Laughlin.planar_gap`, carved from OpenAI's openai/math development (OpenAI, *A Fock-space inequality and the Laughlin spectral gap*, OpenAI Math Release, September 24, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 32 declarations of OpenAI's Lean: 29 definitions and 3 theorems. The definitions and types are `OAI.Laughlin.Fock.averagedFourTransferError`, `OAI.Laughlin.Fock.complexThreeSpinProjector`, `OAI.Laughlin.Fock.exteriorRotation`, `OAI.Laughlin.Fock.fourBodyRho`, `OAI.Laughlin.Fock.fourCopyOperator`, `OAI.Laughlin.Fock.fourOccupationEquiv`, `OAI.Laughlin.Fock.limitFourMiddle`, `OAI.Laughlin.Fock.limitLocalFourMatrix`, `OAI.Laughlin.Fock.occupationQuadruple`, `OAI.Laughlin.Fock.orbitalRotation`, `OAI.Laughlin.Fock.physicalFourCopyEnd`, `OAI.Laughlin.Fock.physicalLimitMiddle`, `OAI.Laughlin.Fock.quadrupleEmbedding`, `OAI.Laughlin.Fock.retainedFourAllowance`, `OAI.Laughlin.Fock.uniformFourBodyRho`, `OAI.Laughlin.Rotation.sourceSpinRepresentation`, `OAI.Laughlin.Spin.coupledBasisMatrix`, `OAI.Laughlin.Spin.coupledDescendant`, `OAI.Laughlin.Spin.coupledHighest`, `OAI.Laughlin.Spin.fourBodyCopy`, `OAI.Laughlin.Spin.fourWedgeInclusion`, `OAI.Laughlin.Spin.normalizedCoupledDescendant`, `OAI.Laughlin.Spin.pairCoupledInclusion`, `OAI.Laughlin.Spin.pairCoupledTensor`, `OAI.Laughlin.Spin.pairCoupledWedge`, `OAI.Laughlin.Spin.pairOrbitalUnit`, `OAI.Laughlin.Spin.retainedFourInclusion`, `OAI.Laughlin.Spin.tensorPairInclusion`, `OAI.Laughlin.Spin.threeSpinProjector`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `Laughlin_Exterior_SpinAction`, `Laughlin_Fock_Quadruple`, `Laughlin_FourBody_Copies`, `Laughlin_FourBody_CopyFormAllowance`, `Laughlin_FourBody_CopyOperatorHaar`, `Laughlin_FourBody_HaarTransfer`, `Laughlin_FourBody_MiddleLimit`, `Laughlin_FourBody_RetainedInclusions`, `Laughlin_FourBody_TensorIntertwining`, `Laughlin_FourBody_TransferCoefficients`, `Laughlin_FourBody_TransferConjugation`, `Laughlin_FourBody_UniformTransfer`, `Laughlin_FourBody_WedgeCompression`, `Laughlin_Operators_FourOccupationEquiv`, `Laughlin_Pair_CoupledIsometry`, `Laughlin_Pair_CoupledParity`, `Laughlin_Polynomial_AntisymmetricCoordinates`, `Laughlin_Spin_Basis`, `Laughlin_Spin_DescendantNorm`, `Laughlin_Spin_Representation`, `Laughlin_ThreeBody_Descendants`, `Laughlin_ThreeBody_HighestEigen`, `Laughlin_ThreeBody_NullSectors`, `Laughlin_ThreeBody_PhysicalMatrix`, `Laughlin_ThreeBody_SpinProjectors`.
--
--   **Imports.** It imports the published bundle `Def_LaughlinPlanar`; the bundles `OAIQ050L010`, `OAIQ050L011` and `OAIQ050L012` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ050L020` and `OAIQ050L021`; the statements `OAI_Laughlin_Fock_complexThreeGram_sub_one_spectral`, `OAI.Laughlin.Fock.complexThreeGram_sub_one_spectral_s50`, `OAI_Laughlin_Fock_contractionForm_haar`, `OAI.Laughlin.Fock.contractionForm_haar_s50`, `OAI_Laughlin_Fock_exteriorFamily_contraction_rotation`, `OAI.Laughlin.Fock.exteriorFamily_contraction_rotation_s50`, `OAI_Laughlin_Fock_exteriorRotation_unitary`, `OAI.Laughlin.Fock.exteriorRotation_unitary_s50`, `OAI_Laughlin_Fock_finiteLocalFourMatrix_tendsto`, `OAI.Laughlin.Fock.finiteLocalFourMatrix_tendsto_s50`, `OAI_Laughlin_Fock_fourCopyMiddleForm`, `OAI.Laughlin.Fock.fourCopyMiddleForm_s50`, `OAI_Laughlin_Fock_linearMap_rotation_norm_integrable`, `OAI.Laughlin.Fock.linearMap_rotation_norm_integrable_s50`, `OAI_Laughlin_Fock_occupationQuadratic_rotation_integrable`, `OAI.Laughlin.Fock.occupationQuadratic_rotation_integrable_s50`, `OAI_Laughlin_Fock_physicalFourCopyEnd_column`, `OAI.Laughlin.Fock.physicalFourCopyEnd_column_s50`, `OAI_Laughlin_Fock_physicalFourCopyEnd_cross_haar`, `OAI.Laughlin.Fock.physicalFourCopyEnd_cross_haar_s50`, `OAI_Laughlin_Fock_physicalFourOccupationColumns_positive`, `OAI.Laughlin.Fock.physicalFourOccupationColumns_positive_s50`, `OAI_Laughlin_Fock_physical_family_spin_norm_haar`, `OAI.Laughlin.Fock.physical_family_spin_norm_haar_s50`, `OAI_Laughlin_Fock_physical_fourBody_haar_transfer`, `OAI.Laughlin.Fock.physical_fourBody_haar_transfer_s50`, `OAI_Laughlin_Fock_physical_fourBody_total_bessel_haar_allowance`, `OAI.Laughlin.Fock.physical_fourBody_total_bessel_haar_allowance_s50`, `OAI_Laughlin_Fock_physical_fourCopyOperator_haar`, `OAI.Laughlin.Fock.physical_fourCopyOperator_haar_s50`, `OAI_Laughlin_Fock_physical_pair_norm_haar_real`, `OAI.Laughlin.Fock.physical_pair_norm_haar_real_s50`, `OAI_Laughlin_Fock_physical_threeBody_Fock_null`, `OAI.Laughlin.Fock.physical_threeBody_Fock_null_s50`, `OAI_Laughlin_Fock_physical_threeBody_projector_bound`, `OAI.Laughlin.Fock.physical_threeBody_projector_bound_s50`, `OAI_Laughlin_Fock_physical_threeBody_projector_nonneg`, `OAI.Laughlin.Fock.physical_threeBody_projector_nonneg_s50`, `OAI_Laughlin_Fock_physical_twoBody_certificate_haar`, `OAI.Laughlin.Fock.physical_twoBody_certificate_haar_s50`, `OAI_Laughlin_Fock_sourcePairEnd_rotation`, `OAI.Laughlin.Fock.sourcePairEnd_rotation_s50`, `OAI_Laughlin_Fock_sourceThreeEnd_rotation`, `OAI_Laughlin_Fock_sourceThreeHighestEnd_haar`, `OAI.Laughlin.Fock.sourceThreeHighestEnd_haar_s50`, `OAI_Laughlin_Fock_source_fourBody_limitpositive`, `OAI.Laughlin.Fock.source_fourBody_limitpositive_s50`, `OAI_Laughlin_Rotation_embedded_spin_haar`, `OAI.Laughlin.Rotation.embedded_spin_haar_s50`, `OAI_Laughlin_Rotation_physicalPairInclusion_SU2`, `OAI.Laughlin.Rotation.physicalPairInclusion_SU2_s50`, `OAI_Laughlin_Rotation_source_spin_commutant_scalar`, `OAI.Laughlin.Rotation.source_spin_commutant_scalar_s50`, `OAI_Laughlin_Rotation_source_spin_haar_schur`, `OAI.Laughlin.Rotation.source_spin_haar_schur_s50`, `OAI_Laughlin_Rotation_source_unequal_spin_haar_zero`, `OAI.Laughlin.Rotation.source_unequal_spin_haar_zero_s50`, `OAI_Laughlin_Spin_normalizedCoupledDescendant_eigen`, `OAI.Laughlin.Spin.normalizedCoupledDescendant_eigen_s50`, `OAI_Laughlin_Spin_physicalFourBodyMatrix_high_wedge_copy` and `OAI.Laughlin.Spin.physicalFourBodyMatrix_high_wedge_copy_s50`; the proofs of `OAI_Laughlin_Fock_contractionForm_haar`, `OAI.Laughlin.Fock.contractionForm_haar_s50`, `OAI_Laughlin_Fock_exteriorFamily_contraction_rotation`, `OAI.Laughlin.Fock.exteriorFamily_contraction_rotation_s50`, `OAI_Laughlin_Fock_exteriorRotation_unitary`, `OAI.Laughlin.Fock.exteriorRotation_unitary_s50`, `OAI_Laughlin_Fock_finiteLocalFourMatrix_tendsto`, `OAI.Laughlin.Fock.finiteLocalFourMatrix_tendsto_s50`, `OAI_Laughlin_Fock_fourCopyMiddleForm`, `OAI.Laughlin.Fock.fourCopyMiddleForm_s50`, `OAI_Laughlin_Fock_linearMap_rotation_norm_integrable`, `OAI.Laughlin.Fock.linearMap_rotation_norm_integrable_s50`, `OAI_Laughlin_Fock_occupationQuadratic_rotation_integrable`, `OAI.Laughlin.Fock.occupationQuadratic_rotation_integrable_s50`, `OAI_Laughlin_Fock_physicalFourOccupationColumns_positive`, `OAI.Laughlin.Fock.physicalFourOccupationColumns_positive_s50`, `OAI_Laughlin_Fock_physicalLimitGram_eq`, `OAI.Laughlin.Fock.physicalLimitGram_eq_s50`, `OAI_Laughlin_Fock_physicalWedgeColumns_gram`, `OAI.Laughlin.Fock.physicalWedgeColumns_gram_s50`, `OAI_Laughlin_Fock_physical_family_spin_norm_haar`, `OAI.Laughlin.Fock.physical_family_spin_norm_haar_s50`, `OAI_Laughlin_Fock_physical_fourBody_haar_transfer`, `OAI.Laughlin.Fock.physical_fourBody_haar_transfer_s50`, `OAI_Laughlin_Fock_physical_fourBody_total_bessel_haar_allowance`, `OAI.Laughlin.Fock.physical_fourBody_total_bessel_haar_allowance_s50`, `OAI_Laughlin_Fock_physical_fourCopyOperator_haar`, `OAI.Laughlin.Fock.physical_fourCopyOperator_haar_s50`, `OAI_Laughlin_Fock_physical_pair_norm_haar_real`, `OAI.Laughlin.Fock.physical_pair_norm_haar_real_s50`, `OAI_Laughlin_Fock_physical_threeBody_Fock_null`, `OAI.Laughlin.Fock.physical_threeBody_Fock_null_s50`, `OAI_Laughlin_Fock_physical_threeBody_projector_bound`, `OAI.Laughlin.Fock.physical_threeBody_projector_bound_s50`, `OAI_Laughlin_Fock_physical_threeBody_projector_nonneg`, `OAI.Laughlin.Fock.physical_threeBody_projector_nonneg_s50`, `OAI_Laughlin_Fock_physical_twoBody_certificate_haar`, `OAI.Laughlin.Fock.physical_twoBody_certificate_haar_s50`, `OAI_Laughlin_Fock_sourcePairEnd_rotation`, `OAI.Laughlin.Fock.sourcePairEnd_rotation_s50`, `OAI_Laughlin_Fock_sourceThreeEnd_rotation`, `OAI_Laughlin_Fock_source_fourBody_limitpositive`, `OAI.Laughlin.Fock.source_fourBody_limitpositive_s50`, `OAI_Laughlin_Rotation_embedded_spin_haar`, `OAI.Laughlin.Rotation.embedded_spin_haar_s50`, `OAI_Laughlin_Rotation_source_spin_commutant_scalar`, `OAI.Laughlin.Rotation.source_spin_commutant_scalar_s50`, `OAI_Laughlin_Rotation_source_spin_haar_schur`, `OAI.Laughlin.Rotation.source_spin_haar_schur_s50`, `OAI_Laughlin_Rotation_source_unequal_spin_haar_zero`, `OAI.Laughlin.Rotation.source_unequal_spin_haar_zero_s50`, `OAI_Laughlin_Spin_normalizedCoupledDescendant_eigen` and `OAI.Laughlin.Spin.normalizedCoupledDescendant_eigen_s50`.
-- source:
--   OpenAI, A Fock-space inequality and the Laughlin spectral gap, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_LaughlinPlanar
import Definitions.Def_OAIQ050L010
import Definitions.Def_OAIQ050L011
import Definitions.Def_OAIQ050L012

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Spin_Representation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Rotation
open scoped BigOperators Matrix

 theorem sourceSpinMatrix_one (Q : ℕ) : sourceSpinMatrix Q 1=1 := by
  simp only [sourceSpinMatrix,map_one,Matrix.mul_one,symmetricTensorInclusion_isometry]

noncomputable def sourceSpinRepresentation (Q : ℕ) : SourceSU2 →* Matrix (Fin (Q+1)) (Fin (Q+1)) ℂ where
  toFun := sourceSpinMatrix Q
  map_one' := sourceSpinMatrix_one Q
  map_mul' := sourceSpinMatrix_mul Q

end Laughlin.Rotation

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Exterior_SpinAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators Matrix
open Rotation

noncomputable def orbitalRotation (Q : ℕ) (g : SourceSU2) : Orbital Q →ₗ[ℂ] Orbital Q where
  toFun v := sourceSpinRepresentation Q g *ᵥ v
  map_add' v w := Matrix.mulVec_add _ v w
  map_smul' c v := Matrix.mulVec_smul _ c v

noncomputable def exteriorRotation (Q : ℕ) (g : SourceSU2) : Space Q →ₐ[ℂ] Space Q :=
  ExteriorAlgebra.map (orbitalRotation Q g)

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Fock_Quadruple
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

noncomputable def occupationQuadruple (Q D : ℕ) (A : FourOccupation Q D) :
    {t : ℕ×ℕ×ℕ×ℕ // t ∈ Certificate.quadruples D} :=
  let l := occupationFourLabels Q A.val A.property.1
  ⟨((l 0).val,(l 1).val,(l 2).val,(l 3).val),
    (Certificate.mem_quadruples D _ _ _ _).mpr
      ⟨l.strictMono (by decide),l.strictMono (by decide),l.strictMono (by decide),
        (occupationFourLabels_sum Q A.val A.property.1).symm.trans A.property.2⟩⟩

theorem occupationQuadruple_injective (Q D : ℕ) : Function.Injective (occupationQuadruple Q D) := by
  intro A B h
  have ht := congrArg Subtype.val h
  simp only [occupationQuadruple,Prod.mk.injEq] at ht
  have hl : occupationFourLabels Q A.val A.property.1 = occupationFourLabels Q B.val B.property.1 := by
    ext i
    fin_cases i
    · exact ht.1
    · exact ht.2.1
    · exact ht.2.2.1
    · exact ht.2.2.2
  apply Subtype.ext
  rw [← occupationFourLabels_range Q A.val A.property.1,
    ← occupationFourLabels_range Q B.val B.property.1,hl]

noncomputable def quadrupleEmbedding (Q D a b c d : ℕ) (hQ : D+1 ≤ Q)
    (h : (a,b,c,d) ∈ Certificate.quadruples D) : Fin 4 ↪o Fin (Q+1) := by
  have hh := (Certificate.mem_quadruples D a b c d).mp h
  let f : Fin 4 → Fin (Q+1) := ![⟨a,by omega⟩,⟨b,by omega⟩,⟨c,by omega⟩,⟨d,by omega⟩]
  have hf : StrictMono f := by
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> simp [f,Fin.lt_def] <;> omega
  exact OrderEmbedding.ofStrictMono f hf

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Pair_CoupledParity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

noncomputable def pairCoupledTensor (Q r : ℕ) (hr : r ≤ Q) (n : ℕ) : SpinIndex Q Q → ℝ :=
  (-1 : ℝ)^r • genericUnitDescendant Q Q r hr hr n

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Polynomial_AntisymmetricCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

noncomputable def pairCoupledWedge (Q r : ℕ) (hr : r ≤ Q) (n : ℕ) : WedgePairIndex Q → ℝ :=
  tensorToWedgePair Q (pairCoupledTensor Q r hr n)

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Pair_CoupledIsometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

noncomputable def pairCoupledInclusion (Q r : ℕ) (hr : r ≤ Q) :
    Matrix (WedgePairIndex Q) (Fin (genericCoupledWeight Q Q r+1)) ℝ :=
  fun i n => pairCoupledWedge Q r hr n.val i

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_Copies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix Kronecker

noncomputable def tensorPairInclusion (A Q r : ℕ) (hr : r ≤ Q) :
    Matrix (Fin (A+1) × WedgePairIndex Q) (SpinIndex A (genericCoupledWeight Q Q r)) ℝ :=
  (1 : Matrix (Fin (A+1)) (Fin (A+1)) ℝ) ⊗ₖ pairCoupledInclusion Q r hr

noncomputable def fourBodyCopy (Q r D : ℕ) (hr : r ≤ Q)
    (hA : D-r ≤ 2*Q-2) (hB : D-r ≤ genericCoupledWeight Q Q r) (n : ℕ) :
    Fin ((2*Q-2)+1) × WedgePairIndex Q → ℝ :=
  tensorPairInclusion (2*Q-2) Q r hr *ᵥ
    ((-1 : ℝ)^(D-r) • genericUnitDescendant (2*Q-2) (genericCoupledWeight Q Q r)
      (D-r) hA hB n)

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_ThreeBody_HighestEigen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

noncomputable def coupledHighest (Q z : ℕ) (hQ : 2 ≤ Q) (hz : z ≤ Q) : PairOrbitalIndex Q → ℝ :=
  extendWeightSlice (2*Q-2) Q z (by omega) hz (fun p => highestUnit (2*Q-2) Q z p.val)

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_ThreeBody_Descendants
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

noncomputable def coupledDescendant (Q z : ℕ) (hQ : 2 ≤ Q) (hz : z ≤ Q) (n : ℕ) :
    PairOrbitalIndex Q → ℝ :=
  ((totalRaise (2*Q-2) Q)ᵀ ^ n) *ᵥ coupledHighest Q z hQ hz

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Spin_DescendantNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

noncomputable def normalizedCoupledDescendant (Q z : ℕ) (hQ : 2 ≤ Q) (hz : z ≤ Q) (n : ℕ) :
    PairOrbitalIndex Q → ℝ :=
  (Real.sqrt (vectorNormSq (coupledDescendant Q z hQ hz n)))⁻¹ • coupledDescendant Q z hQ hz n

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_TransferConjugation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators
open Spin

noncomputable def physicalFourCopyEnd (Q r D : ℕ) (hDQ : D ≤ Q) : Module.End ℂ (Space Q) :=
  ∑ b : LocalFourIndex D,
    (fourBodyCoefficient Q r D D b.val.1.val b.val.2.1.val b.val.2.2.val : ℂ) •
    sourceFourEnd Q b.val.1.val ⟨b.val.2.1.val,by omega⟩ ⟨b.val.2.2.val,by omega⟩

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Operators_FourOccupationEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem occupationQuadruple_surjective (Q D : ℕ) (hQ : D+1 ≤ Q) :
    Function.Surjective (occupationQuadruple Q D) := by
  rintro ⟨⟨a,b,c,d⟩,h⟩
  let l := quadrupleEmbedding Q D a b c d hQ h
  let A := Set.powersetCard.ofFinEmbEquiv l
  have hl : occupationFourLabels Q A.val A.property = l :=
    Set.powersetCard.ofFinEmbEquiv.symm_apply_apply l
  have hw : (∑ i ∈ A.val, i.val)=D+1 := by
    rw [occupationFourLabels_sum Q A.val A.property,hl]
    exact (Certificate.mem_quadruples D a b c d).mp h |>.2.2.2
  refine ⟨⟨A.val,A.property,hw⟩,?_⟩
  apply Subtype.ext
  simp only [occupationQuadruple,hl]
  rfl

noncomputable def fourOccupationEquiv (Q D : ℕ) (hQ : D+1 ≤ Q) :
    FourOccupation Q D ≃ {t : ℕ×ℕ×ℕ×ℕ // t ∈ Certificate.quadruples D} :=
  Equiv.ofBijective (occupationQuadruple Q D)
    ⟨occupationQuadruple_injective Q D,occupationQuadruple_surjective Q D hQ⟩

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_WedgeCompression
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped Matrix BigOperators ComplexOrder
open Matrix Spin

noncomputable def physicalLimitMiddle (D : ℕ) : Matrix (Fin ((D+1)/2)) (Fin ((D+1)/2)) ℂ :=
  (Certificate.certificateDiagonal D - physicalLimitError D).map Complex.ofReal

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_MiddleLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators Matrix Topology
open Filter Spin

noncomputable def limitFourMiddle (D : ℕ) : Matrix (Fin ((D+1)/2)) (Fin ((D+1)/2)) ℝ :=
  Certificate.certificateDiagonal D - physicalLimitError D

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_TransferCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators Topology
open Filter Spin

noncomputable def limitLocalFourMatrix (D : ℕ) : LocalFourIndex D → LocalFourIndex D → ℝ :=
  copyQuadraticMatrix (limitFourMiddle D)
    (fun i b => fourBodyLimitCoefficient (Certificate.copyLabel i) D D
      b.val.1.val b.val.2.1.val b.val.2.2.val)

noncomputable def fourBodyRho (D Q : ℕ) : ℝ :=
  matrixMetricError 24 Q (finiteLocalFourMatrix Q D) (limitLocalFourMatrix D) *
    (Fintype.card (LocalFourIndex D) : ℝ)^2

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_UniformTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators Topology
open Filter Spin

noncomputable def uniformFourBodyRho (Q : ℕ) : ℝ := ∑ D ∈ Finset.range 24, fourBodyRho D Q

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_HaarTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Rotation Spin MeasureTheory
open scoped BigOperators Topology

noncomputable def averagedFourTransferError (Q : ℕ) : ℝ := 24 * uniformFourBodyRho Q

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Spin_Basis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

noncomputable def coupledBasisMatrix (Q : ℕ) (hQ : 2 ≤ Q) :
    Matrix (PairOrbitalIndex Q) (CoupledIndex Q) ℝ := fun i s =>
  normalizedCoupledDescendant Q s.1.val hQ (by omega) s.2.val i

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_TensorIntertwining
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open Rotation
open scoped BigOperators Matrix Kronecker

noncomputable def fourWedgeInclusion (Q r D : ℕ) (hr : r ≤ Q)
    (hA : D-r ≤ 2*Q-2) (hB : D-r ≤ genericCoupledWeight Q Q r) :
    Matrix (Fin (2*Q-2+1) × WedgePairIndex Q)
      (Fin (genericCoupledWeight (2*Q-2) (genericCoupledWeight Q Q r) (D-r)+1)) ℂ :=
  fun i n => (fourBodyCopy Q r D hr hA hB n.val i : ℂ)

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_RetainedInclusions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open Rotation
open scoped BigOperators Matrix

noncomputable def retainedFourInclusion (Q D : ℕ) (hQ : D+2 ≤ Q) (r : OddPairLabel D) :
    Matrix (FourWedgeIndex Q) (Fin (fourSpinWeight Q D+1)) ℂ :=
  castSpinColumns _ _ (four_nested_weight Q D (oddPairDeficit r) hQ (oddPairDeficit_le r))
    (fourWedgeInclusion Q (oddPairDeficit r) D
      (by have := oddPairDeficit_le r; omega)
      (by have := oddPairDeficit_le r; omega)
      (by have := oddPairDeficit_le r; unfold genericCoupledWeight; omega))

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_CopyOperatorHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Rotation Spin MeasureTheory
open scoped BigOperators Matrix

noncomputable def fourCopyOperator (Q D : ℕ) (hQ : D+2 ≤ Q)
    (C : OddPairLabel D → OddPairLabel D → ℝ) : Matrix (FourWedgeIndex Q) (FourWedgeIndex Q) ℂ :=
  ∑ r, ∑ s, (C r s : ℂ) •
    (retainedFourInclusion Q D hQ r * (retainedFourInclusion Q D hQ s)ᴴ)

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_CopyFormAllowance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Spin Rotation MeasureTheory
open scoped BigOperators Matrix

noncomputable def retainedFourAllowance (Q : ℕ) (hQ : 25 ≤ Q) (x : Space Q) : ℝ :=
  ∑ d : Fin 23, (((2*Q-2+1 : ℕ) : ℝ)/((4*Q-1-2*(d.val+1) : ℕ) : ℝ)) *
    (∑ r : OddPairLabel (d.val+1), (contractionForm Q (sourceFourFamilyEnd Q)
      (retainedFourInclusion Q (d.val+1) (by omega) r*
        (retainedFourInclusion Q (d.val+1) (by omega) r)ᴴ) x).re)

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_ThreeBody_SpinProjectors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

noncomputable def threeSpinProjector (Q : ℕ) (hQ : 2 ≤ Q) (z : Fin (Q+1)) :
    Matrix (PairOrbitalIndex Q) (PairOrbitalIndex Q) ℝ :=
  coupledBasisMatrix Q hQ * coupledSelector Q z * (coupledBasisMatrix Q hQ)ᵀ

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_ThreeBody_NullSectors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators Matrix

noncomputable def complexThreeSpinProjector (Q : ℕ) (hQ : 2 ≤ Q) (z : Fin (Q+1)) :
    Matrix (Spin.PairOrbitalIndex Q) (Spin.PairOrbitalIndex Q) ℂ :=
  fun a b => (Spin.threeSpinProjector Q hQ z a b : ℂ)

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_ThreeBody_PhysicalMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

noncomputable def pairOrbitalUnit (Q p j : ℕ) : PairOrbitalIndex Q → ℝ :=
  fun i => if i.1.val=p ∧ i.2.val=j then 1 else 0

end Laughlin.Spin

end OAI
end


