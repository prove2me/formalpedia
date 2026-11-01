-- Prove2me | Definitions.Def_OAIQ050L012
-- name    : OAIQ050L012
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T09:09:08.019779+00:00
-- url     : https://prove2.me/theorems/8abca299-a02a-42d5-af87-7adf07a5ad2e
-- title:
--   Definitions bundle OAIQ050L012 of the split of OpenAI, A Fock-space inequality and the Laughlin spectral gap
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Laughlin.planar_gap`, carved from OpenAI's openai/math development (OpenAI, *A Fock-space inequality and the Laughlin spectral gap*, OpenAI Math Release, September 24, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 49 declarations of OpenAI's Lean: 43 definitions, 5 instances and 1 theorem. The definitions and types are `OAI.Laughlin.Fock.fourOccupationCoefficient`, `OAI.Laughlin.Fock.fourOccupationCreate`, `OAI.Laughlin.Fock.fourOccupationEnd`, `OAI.Laughlin.Fock.insertionSign`, `OAI.Laughlin.Fock.limitFourColumn`, `OAI.Laughlin.Fock.limitFourCopyEnd`, `OAI.Laughlin.Fock.localFourOperators`, `OAI.Laughlin.Fock.occupationQuadratic`, `OAI.Laughlin.Fock.pairCreateEnd`, `OAI.Laughlin.Fock.pairExterior`, `OAI.Laughlin.Fock.physicalFourOccupationColumns`, `OAI.Laughlin.Fock.physicalLimitGram`, `OAI.Laughlin.Fock.physicalTwoBodyMatrix`, `OAI.Laughlin.Fock.physicalWedgeColumns`, `OAI.Laughlin.Fock.restrictedSphereEnergy`, `OAI.Laughlin.Fock.restrictedSphereHamiltonian`, `OAI.Laughlin.Fock.restrictedSpherePairCreateEnd`, `OAI.Laughlin.Fock.restrictedSpherePairEnd`, `OAI.Laughlin.Fock.rowOutputMode`, `OAI.Laughlin.Fock.sourceFockEnergy`, `OAI.Laughlin.Fock.sourceFockHamiltonian`, `OAI.Laughlin.Fock.sourceFourEnd`, `OAI.Laughlin.Fock.sourceFourFamilyEnd`, `OAI.Laughlin.Fock.sourceFourVector`, `OAI.Laughlin.Fock.sourcePairCreateEnd`, `OAI.Laughlin.Fock.sourcePairEnd`, `OAI.Laughlin.Fock.sourcePairVector`, `OAI.Laughlin.Fock.sourcePairWindow`, `OAI.Laughlin.Fock.threeBodyColumn`, `OAI.Laughlin.Fock.truncatedModeFactor`, `OAI.Laughlin.Fock.wedgePairVector`, `OAI.Laughlin.Planar.sphereCoefficient`, `OAI.Laughlin.Planar.spherePairMatrix`, `OAI.Laughlin.Rotation.sourceHaar`, `OAI.Laughlin.Spin.FourWedgeIndex`, `OAI.Laughlin.Spin.WedgePairIndex`, `OAI.Laughlin.Spin.fourBodyTermMatrix`, `OAI.Laughlin.Spin.fourSignedUnit`, `OAI.Laughlin.Spin.fourWedgeUnit`, `OAI.Laughlin.Spin.limitSliceCoefficient` and 3 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `Laughlin_Asymptotics_TruncatedMetricPerturbation`, `Laughlin_Asymptotics_TruncatedScaling`, `Laughlin_Exterior_FourConjugation`, `Laughlin_Exterior_PairConjugation`, `Laughlin_Fock_Annihilation`, `Laughlin_Fock_Hamiltonian`, `Laughlin_Fock_PairNormalization`, `Laughlin_FourBody_ColumnExpansion`, `Laughlin_FourBody_FockCovariance`, `Laughlin_FourBody_GroupIntertwining`, `Laughlin_FourBody_LimitPositive`, `Laughlin_FourBody_OccupationCoefficient`, `Laughlin_FourBody_PhysicalCertificate`, `Laughlin_FourBody_PhysicalColumn`, `Laughlin_FourBody_PhysicalMatrix`, `Laughlin_FourBody_PhysicalSlaterReadout`, `Laughlin_FourBody_SignedCoordinates`, `Laughlin_FourBody_SliceCoefficient`, `Laughlin_FourBody_Square`, `Laughlin_FourBody_WedgeCompression`, `Laughlin_Operators_CollectionAnnihilatorBound`, `Laughlin_Operators_TruncatedFourCopy`, `Laughlin_Pair_CoupledBasis`, `Laughlin_Pair_ExteriorRotation`, `Laughlin_Planar_DegreeRestriction`, `Laughlin_Planar_Model`, `Laughlin_Polynomial_AntisymmetricCoordinates`, `Laughlin_Spin_Compact`, `Laughlin_Spin_Haar`, `Laughlin_Spin_TwoBodyCertificateHaar`, `Laughlin_ThreeBody_PairAction`.
--
--   **Imports.** It imports the published bundle `Def_LaughlinPlanar`; the bundles `OAIQ050L000`, `OAIQ050L001`, `OAIQ050L002`, `OAIQ050L005`, `OAIQ050L006` and `OAIQ050L007` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ050L016`, `OAIQ050L017` and `OAIQ050L018`; the statements `OAI_Laughlin_Fock_annihilate_coordinate`, `OAI.Laughlin.Fock.annihilate_coordinate_s50`, `OAI_Laughlin_Fock_fourOccupation_adjoint`, `OAI.Laughlin.Fock.fourOccupation_adjoint_s50`, `OAI_Laughlin_Fock_limitFourColumn_adjoint`, `OAI.Laughlin.Fock.limitFourColumn_adjoint_s50`, `OAI_Laughlin_Fock_limitFourColumn_expansion`, `OAI.Laughlin.Fock.limitFourColumn_expansion_s50`, `OAI_Laughlin_Fock_limitFourColumn_mul_adjoint`, `OAI.Laughlin.Fock.limitFourColumn_mul_adjoint_s50`, `OAI_Laughlin_Fock_limitFourColumn_occupation_coefficient`, `OAI.Laughlin.Fock.limitFourColumn_occupation_coefficient_s50`, `OAI_Laughlin_Fock_limitFourColumn_physical_L`, `OAI.Laughlin.Fock.limitFourColumn_physical_L_s50`, `OAI_Laughlin_Fock_limitFourCopyEnd_Slater_readout`, `OAI_Laughlin_Fock_limitFourCopyEnd_local_sum`, `OAI.Laughlin.Fock.limitFourCopyEnd_local_sum_s50`, `OAI_Laughlin_Fock_limitFourCopyEnd_matrix_expansion`, `OAI.Laughlin.Fock.limitFourCopyEnd_matrix_expansion_s50`, `OAI_Laughlin_Fock_localFourOperators_bound`, `OAI.Laughlin.Fock.localFourOperators_bound_s50`, `OAI_Laughlin_Fock_occupationQuadratic_factor`, `OAI.Laughlin.Fock.occupationQuadratic_factor_s50`, `OAI_Laughlin_Fock_pairCreate_pair_adjoint`, `OAI.Laughlin.Fock.pairCreate_pair_adjoint_s50`, `OAI_Laughlin_Fock_physicalLimitGram_eq`, `OAI.Laughlin.Fock.physicalLimitGram_eq_s50`, `OAI_Laughlin_Fock_physicalWedgeColumns_gram`, `OAI.Laughlin.Fock.physicalWedgeColumns_gram_s50`, `OAI_Laughlin_Fock_sourceFockEnergy_fockInclusion`, `OAI.Laughlin.Fock.sourceFockEnergy_fockInclusion_s50`, `OAI_Laughlin_Fock_sourceFockHamiltonian_fockInclusion`, `OAI.Laughlin.Fock.sourceFockHamiltonian_fockInclusion_s50`, `OAI_Laughlin_Fock_sourceFourVector_adjoint`, `OAI.Laughlin.Fock.sourceFourVector_adjoint_s50`, `OAI_Laughlin_Fock_sourcePairCreate_inner`, `OAI.Laughlin.Fock.sourcePairCreate_inner_s50`, `OAI_Laughlin_Fock_source_physical_four_body_certificates`, `OAI.Laughlin.Fock.source_physical_four_body_certificates_s50`, `OAI_Laughlin_Fock_threeBodyColumn_gram`, `OAI.Laughlin.Fock.threeBodyColumn_gram_s50`, `OAI_Laughlin_Planar_finite_degree_endpoint_of_fock_square`, `OAI.Laughlin.Planar.finite_degree_endpoint_of_fock_square_s50`, `OAI_Laughlin_Spin_fourWeightSlice_sum`, `OAI.Laughlin.Spin.fourWeightSlice_sum_s50`, `OAI_Laughlin_Spin_limitSliceCoefficient_antisymmetric`, `OAI.Laughlin.Spin.limitSliceCoefficient_antisymmetric_s50`, `OAI_Laughlin_Spin_source_fourBody_coefficients_norm`, `OAI.Laughlin.Spin.source_fourBody_coefficients_norm_s50`, `OAI_Laughlin_Spin_source_fourBody_local_orthonormal` and `OAI.Laughlin.Spin.source_fourBody_local_orthonormal_s50`; the proofs of `OAI_Laughlin_Fock_annihilate_coordinate`, `OAI.Laughlin.Fock.annihilate_coordinate_s50`, `OAI_Laughlin_Fock_annihilate_create_inner`, `OAI.Laughlin.Fock.annihilate_create_inner_s50`, `OAI_Laughlin_Fock_create_create_inner`, `OAI.Laughlin.Fock.create_create_inner_s50`, `OAI_Laughlin_Fock_fourOccupation_adjoint`, `OAI.Laughlin.Fock.fourOccupation_adjoint_s50`, `OAI_Laughlin_Fock_limitFourColumn_adjoint`, `OAI.Laughlin.Fock.limitFourColumn_adjoint_s50`, `OAI_Laughlin_Fock_limitFourColumn_expansion`, `OAI.Laughlin.Fock.limitFourColumn_expansion_s50`, `OAI_Laughlin_Fock_limitFourColumn_mul_adjoint`, `OAI.Laughlin.Fock.limitFourColumn_mul_adjoint_s50`, `OAI_Laughlin_Fock_limitFourColumn_occupation_coefficient`, `OAI.Laughlin.Fock.limitFourColumn_occupation_coefficient_s50`, `OAI_Laughlin_Fock_limitFourColumn_physical_L`, `OAI.Laughlin.Fock.limitFourColumn_physical_L_s50`, `OAI_Laughlin_Fock_limitFourCopyEnd_Slater_readout`, `OAI_Laughlin_Fock_limitFourCopyEnd_local_sum`, `OAI.Laughlin.Fock.limitFourCopyEnd_local_sum_s50`, `OAI_Laughlin_Fock_limitFourCopyEnd_matrix_expansion`, `OAI.Laughlin.Fock.limitFourCopyEnd_matrix_expansion_s50`, `OAI_Laughlin_Fock_localFourOperators_bound`, `OAI.Laughlin.Fock.localFourOperators_bound_s50`, `OAI_Laughlin_Fock_occupationQuadratic_factor`, `OAI.Laughlin.Fock.occupationQuadratic_factor_s50`, `OAI_Laughlin_Fock_pairCreate_pair_adjoint`, `OAI.Laughlin.Fock.pairCreate_pair_adjoint_s50`, `OAI_Laughlin_Fock_pair_annihilate_high_degree`, `OAI.Laughlin.Fock.pair_annihilate_high_degree_s50`, `OAI_Laughlin_Fock_physical_threeBody_tail_sum`, `OAI_Laughlin_Fock_row_normal_square`, `OAI.Laughlin.Fock.row_normal_square_s50`, `OAI_Laughlin_Fock_sourceFockEnergy_fockInclusion`, `OAI.Laughlin.Fock.sourceFockEnergy_fockInclusion_s50`, `OAI_Laughlin_Fock_sourceFockHamiltonian_fockInclusion`, `OAI.Laughlin.Fock.sourceFockHamiltonian_fockInclusion_s50`, `OAI_Laughlin_Fock_sourceFourVector_adjoint`, `OAI.Laughlin.Fock.sourceFourVector_adjoint_s50`, `OAI_Laughlin_Fock_sourcePairCreate_inner`, `OAI.Laughlin.Fock.sourcePairCreate_inner_s50`, `OAI_Laughlin_Fock_source_physical_four_body_certificates`, `OAI.Laughlin.Fock.source_physical_four_body_certificates_s50`, `OAI_Laughlin_Fock_threeBodyColumn_gram`, `OAI.Laughlin.Fock.threeBodyColumn_gram_s50`, `OAI_Laughlin_Fock_vectorCreate_adjoint`, `OAI.Laughlin.Fock.vectorCreate_adjoint_s50`, `OAI_Laughlin_Spin_fourWeightSlice_sum`, `OAI.Laughlin.Spin.fourWeightSlice_sum_s50`, `OAI_Laughlin_Spin_source_fourBody_local_normalization` and `OAI.Laughlin.Spin.source_fourBody_local_normalization_s50`.
-- source:
--   OpenAI, A Fock-space inequality and the Laughlin spectral gap, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_LaughlinPlanar
import Definitions.Def_OAIQ050L000
import Definitions.Def_OAIQ050L001
import Definitions.Def_OAIQ050L002
import Definitions.Def_OAIQ050L005
import Definitions.Def_OAIQ050L006
import Definitions.Def_OAIQ050L007

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Exterior_PairConjugation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

noncomputable def sourcePairEnd (Q p : ℕ) : Module.End ℂ (Space Q) :=
  pairEnd Q (fun i j => ((pairCoefficient Q p i j / Real.sqrt 2 : ℝ) : ℂ))

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Exterior_FourConjugation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock

noncomputable def sourceFourEnd (Q p : ℕ) (j k : Fin (Q+1)) : Module.End ℂ (Space Q) :=
  annihilate k * annihilate j * sourcePairEnd Q p

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Fock_Annihilation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock

noncomputable def insertionSign (Q : ℕ) (i : Fin (Q+1)) (A : Finset (Fin (Q+1))) : ℂ :=
  if h : i ∉ A then (create_unoccupied_sign Q i A h).choose else 1

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Operators_CollectionAnnihilatorBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

noncomputable def sourcePairWindow (Q : ℕ) (x : Space Q) : ℝ :=
  ∑ p ∈ Finset.range 24, occupationNormSq Q (sourcePairEnd Q p x)

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Asymptotics_TruncatedScaling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

noncomputable def truncatedModeFactor (L Q : ℕ) (i : Fin (Q+1)) : ℝ :=
  if i.val ≤ L then modeFactor Q i.val else 1

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Asymptotics_TruncatedMetricPerturbation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators InnerProductSpace

noncomputable def occupationQuadratic {I : Type*} [Fintype I]
    (Q : ℕ) (R : I → I → ℝ) (v : I → Space Q) : ℝ :=
  (∑ i, ∑ j, (R i j : ℂ) * occupationInner Q (v i) (v j)).re

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Fock_Hamiltonian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

noncomputable def pairCreateEnd (Q : ℕ) (c : Fin (Q+1) → Fin (Q+1) → ℂ) :
    Module.End ℂ (Space Q) := ∑ i, ∑ j, star (c i j) • (create i * create j)

noncomputable def sourcePairCreateEnd (Q p : ℕ) : Module.End ℂ (Space Q) :=
  pairCreateEnd Q (fun i j => ((pairCoefficient Q p i j / Real.sqrt 2 : ℝ) : ℂ))

noncomputable def sourceFockHamiltonian (Q : ℕ) : Module.End ℂ (Space Q) :=
  ∑ p ∈ Finset.range (2*Q-1), sourcePairCreateEnd Q p * sourcePairEnd Q p

noncomputable def sourceFockEnergy (Q : ℕ) (x : Space Q) : ℝ :=
  ∑ p ∈ Finset.range (2*Q-1), occupationNormSq Q (sourcePairEnd Q p x)

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Fock_PairNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

noncomputable def sourcePairVector (Q p : ℕ) : Space Q :=
  ∑ i, ∑ j, ((pairCoefficient Q p i j / Real.sqrt 2 : ℝ) : ℂ) •
    create i (create j (1 : Space Q))

end Laughlin.Fock

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

abbrev WedgePairIndex (Q : ℕ) := {i : SpinIndex Q Q // i.1 < i.2}

noncomputable def tensorToWedgePair (Q : ℕ) (f : SpinIndex Q Q → ℝ) :
    WedgePairIndex Q → ℝ := fun i => Real.sqrt 2 * f i.val

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_ThreeBody_PairAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

noncomputable def threeBodyColumn (Q p : ℕ) (k : Fin (Q+1)) : Space Q :=
  sourcePairCreateEnd Q p (create k (1 : Space Q))

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_SliceCoefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators

noncomputable def limitSliceCoefficient (r D p j k : ℕ) : ℝ :=
  if p+j+k=D then fourBodyLimitCoefficient r D D p j k else 0

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_PhysicalSlaterReadout
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators
open Spin

noncomputable def limitFourCopyEnd (Q r D : ℕ) : Module.End ℂ (Space Q) :=
  ∑ p ∈ Finset.range (D+1), weightedFourEnd Q p (fun j k => limitSliceCoefficient r D p j.val k.val)

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_PhysicalColumn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators
open Spin

noncomputable def limitFourColumn (Q r D : ℕ) : Space Q :=
  ∑ p ∈ Finset.range (D+1), ∑ j : Fin (Q+1), ∑ k : Fin (Q+1),
    ∑ x : Fin (Q+1), ∑ y : Fin (Q+1),
      (((limitSliceCoefficient r D p j.val k.val / 2) *
        (pairLimitCoefficient p x.val y.val / Real.sqrt 2) : ℝ) : ℂ) •
        create x (create y (create j (create k (1 : Space Q))))

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_OccupationCoefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators
open Spin

noncomputable def fourOccupationCoefficient (Q r D : ℕ) (A : Finset (Fin (Q+1))) : ℝ :=
  if hA : A.card=4 then
    if (∑ i ∈ A, i.val)=D+1 then
      let l := occupationFourLabels Q A hA
      Real.sqrt (sourceCopyWeight D r /
        ((l 0).val.factorial*(l 1).val.factorial*(l 2).val.factorial*(l 3).val.factorial : ℝ)) *
        (Certificate.L D r ((l 0).val,(l 1).val,(l 2).val,(l 3).val) : ℝ)
    else 0
  else 0

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_ColumnExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators
open Spin

noncomputable def fourOccupationCreate (Q D : ℕ) (A : FourOccupation Q D) : Module.End ℂ (Space Q) :=
  let l := occupationFourLabels Q A.val A.property.1
  create (l 0)*create (l 1)*create (l 2)*create (l 3)

noncomputable def fourOccupationEnd (Q D : ℕ) (A : FourOccupation Q D) : Module.End ℂ (Space Q) :=
  let l := occupationFourLabels Q A.val A.property.1
  annihilate (l 3)*annihilate (l 2)*annihilate (l 1)*annihilate (l 0)

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Spin_Compact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Rotation
open scoped BigOperators Matrix

instance sourceSU2_continuousInv : ContinuousInv SourceSU2 where
  continuous_inv := by
    apply continuous_induced_rng.mpr
    change Continuous (fun g : SourceSU2 => (g.val)ᴴ)
    fun_prop

instance sourceSU2_topologicalGroup : IsTopologicalGroup SourceSU2 where

instance sourceSU2_compactSpace : CompactSpace SourceSU2 :=
  isCompact_iff_compactSpace.mp sourceSU2_isCompact

end Laughlin.Rotation

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Spin_Haar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Rotation
open MeasureTheory MeasureTheory.Measure TopologicalSpace

noncomputable instance sourceSU2_measurableSpace : MeasurableSpace SourceSU2 := borel SourceSU2
instance sourceSU2_borelSpace : BorelSpace SourceSU2 := ⟨rfl⟩

noncomputable def sourceHaar : Measure SourceSU2 :=
  haarMeasure (⊤ : PositiveCompacts SourceSU2)

end Laughlin.Rotation

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Pair_CoupledBasis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

def oddPairDeficit {Q : ℕ} (r : OddPairLabel Q) : ℕ := 2*r.val+1

theorem oddPairDeficit_le {Q : ℕ} (r : OddPairLabel Q) : oddPairDeficit r ≤ Q := by
  have := r.isLt
  dsimp [oddPairDeficit]
  omega

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

abbrev FourWedgeIndex (Q : ℕ) := Fin (2*Q-2+1) × WedgePairIndex Q

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Pair_ExteriorRotation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Rotation
open scoped BigOperators Matrix Kronecker

noncomputable def pairExterior (Q : ℕ) (v : Spin.SpinIndex Q Q → ℂ) : Space Q :=
  ∑ i, v i • create i.1 (create i.2 (1 : Space Q))

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_FockCovariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Rotation Spin
open scoped BigOperators Matrix Kronecker

noncomputable def wedgePairVector (Q : ℕ) (i : WedgePairIndex Q) : Space Q :=
  create i.val.1 (create i.val.2 1)

noncomputable def sourceFourVector (Q : ℕ) (i : FourWedgeIndex Q) : Space Q :=
  sourcePairVector Q i.1.val * wedgePairVector Q i.2

noncomputable def sourceFourFamilyEnd (Q : ℕ) (i : FourWedgeIndex Q) : Module.End ℂ (Space Q) :=
  sourceFourEnd Q i.1.val i.2.val.1 i.2.val.2

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_PhysicalCertificate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped Matrix

noncomputable def physicalLimitGram (Q D : ℕ) : Matrix (Fin ((D+1)/2)) (Fin ((D+1)/2)) ℝ :=
  fun i j => (occupationInner Q (limitFourColumn Q (Certificate.copyLabel i) D)
    (limitFourColumn Q (Certificate.copyLabel j) D)).re

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

noncomputable def physicalWedgeColumns (Q D : ℕ) :
    Matrix (Finset (Fin (Q+1))) (Fin ((D+1)/2)) ℂ :=
  fun A i => (occupationBasis Q).repr (limitFourColumn Q (Certificate.copyLabel i) D) A

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_LimitPositive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped Matrix BigOperators ComplexOrder
open Matrix Spin

noncomputable def physicalFourOccupationColumns (Q D : ℕ) :
    Matrix (FourOccupation Q D) (Fin ((D+1)/2)) ℂ :=
  fun A i => physicalWedgeColumns Q D A.val i

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_SignedCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

noncomputable def fourWedgeUnit (Q p j k : ℕ) : Fin (2*Q-2+1) × WedgePairIndex Q → ℝ :=
  fun i => if i.1.val=p ∧ i.2.val.1.val=j ∧ i.2.val.2.val=k then 1 else 0

noncomputable def fourSignedUnit (Q p j k : ℕ) : Fin (2*Q-2+1) × WedgePairIndex Q → ℝ :=
  fourWedgeUnit Q p j k - fourWedgeUnit Q p k j

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_PhysicalMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

noncomputable def fourBodyTermMatrix (Q t : ℕ) (e f : ℕ × ℕ × ℤ) :
    Matrix (Fin (2*Q-2+1) × WedgePairIndex Q) (Fin (2*Q-2+1) × WedgePairIndex Q) ℝ :=
  -(sourceAlpha t e * sourceAlpha t f) •
    realOuter (fourSignedUnit Q e.1 e.2.1 (f.1+f.2.1-t))
      (fourSignedUnit Q f.1 f.2.1 (e.1+e.2.1-t))

noncomputable def physicalFourBodyMatrix (Q : ℕ) :
    Matrix (Fin (2*Q-2+1) × WedgePairIndex Q) (Fin (2*Q-2+1) × WedgePairIndex Q) ℝ :=
  (Certificate.rows.map (fun row => (row.2.2.map (fun e =>
    (row.2.2.map (fun f => fourBodyTermMatrix Q row.1 e f)).sum)).sum)).sum

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Operators_TruncatedFourCopy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators
open Spin

noncomputable def localFourOperators (Q D : ℕ) (hDQ : D ≤ Q) (b : LocalFourIndex D) : Module.End ℂ (Space Q) :=
  limitFourEnd Q b.val.1.val ⟨b.val.2.1.val,by omega⟩ ⟨b.val.2.2.val,by omega⟩

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Spin_TwoBodyCertificateHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Rotation MeasureTheory
open scoped BigOperators Matrix

noncomputable def physicalTwoBodyMatrix (Q : ℕ) :
    Matrix (Fin (2*Q-2+1)) (Fin (2*Q-2+1)) ℂ :=
  (Certificate.rows.map (physicalPairRowMatrix Q)).sum

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_Square
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Spin
open scoped BigOperators Matrix

def rowOutputMode (Q t : ℕ) (hQ : 15 ≤ Q) (T : RowLevel t) : Fin (Q+1) :=
  ⟨T.val.val-t,by have h := T.val.isLt; omega⟩

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Planar_Model
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Planar
open Fock Filter
open scoped BigOperators Topology Matrix

noncomputable def sphereCoefficient (Q p i j : ℕ) : ℂ :=
  ((modeFactor Q i * modeFactor Q j * pairFactor Q p *
    pairLimitCoefficient p i j / Real.sqrt 2 : ℝ) : ℂ)

noncomputable def spherePairMatrix (L Q p : ℕ) : Matrix (Occupations L) (Occupations L) ℂ :=
  pairMatrix L (fun i j => sphereCoefficient Q p i.val j.val)

end Laughlin.Planar

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Planar_DegreeRestriction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

noncomputable def restrictedSpherePairEnd (L Q p : ℕ) : Module.End ℂ (Space L) :=
  pairEnd L (fun i j => Planar.sphereCoefficient Q p i.val j.val)

noncomputable def restrictedSpherePairCreateEnd (L Q p : ℕ) : Module.End ℂ (Space L) :=
  pairCreateEnd L (fun i j => Planar.sphereCoefficient Q p i.val j.val)

noncomputable def restrictedSphereHamiltonian (L Q : ℕ) : Module.End ℂ (Space L) :=
  ∑ p ∈ Finset.range (2*L+1), restrictedSpherePairCreateEnd L Q p * restrictedSpherePairEnd L Q p

noncomputable def restrictedSphereEnergy (L Q : ℕ) (x : Space L) : ℝ :=
  ∑ p ∈ Finset.range (2*L+1), occupationNormSq L (restrictedSpherePairEnd L Q p x)

end Laughlin.Fock

end OAI
end


