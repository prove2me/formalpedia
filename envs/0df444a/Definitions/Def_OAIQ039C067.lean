-- Prove2me | Definitions.Def_OAIQ039C067
-- name    : OAIQ039C067
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T09:19:23.106834+00:00
-- url     : https://prove2.me/theorems/913ff2bc-348c-43d2-81f3-f43a46090f98
-- title:
--   Definitions bundle OAIQ039C067 of the split of OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 12 declarations of OpenAI's Lean: 9 definitions, 1 instance and 2 theorems. The definitions and types are `OAI.Kadison.MatrixTower.normalizedInclusion`, `OAI.Kadison.MatrixTower.normalizedIndex`, `OAI.Kadison.MatrixTower.normalizedStage`, `OAI.Kadison.MatrixTower.stageInclusion`, `OAI.Kadison.OperatorAmplification.amplifiedStage`, `OAI.Kadison.OperatorAmplification.matrixGNSOperator`, `OAI.Kadison.TracialGNS.sumConjugation`, `OAI.Kadison.TracialSequence.FreeCornerPosition`, `OAI.Kadison.TracialSequence.constantAction`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/Commutator, in whole or in part: `Commutator_AmplifiedTowerStage`, `Commutator_InvariantSum`, `Commutator_MatrixGNSCornerBound`, `Commutator_MatrixIndexEquiv`, `Commutator_MatrixTowerInclusion`, `Commutator_TracialFreePositionCriterion`, `Commutator_TracialGeneratedAlgebra`.
--
--   **Imports.** It imports the bundles `OAIQ039C058`, `OAIQ039C060`, `OAIQ039C061`, `OAIQ039C062` and `OAIQ039C064` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ039C072`; the statements `OAI.Kadison.MatrixTower.exists_matrix_freeCornerPosition`, `OAI.Kadison.MatrixTower.finite_standard_entrywise_bound`, `OAI.Kadison.MatrixTower.finite_standard_gauge_bound`, `OAI.Kadison.MatrixTower.rectangular_bound_after_average`, `OAI.Kadison.MatrixTower.rectangular_contraction_after_average`, `OAI.Kadison.MatrixTower.square_contraction_after_average`, `OAI.Kadison.MatrixTower.square_symmetry_after_average`, `OAI.Kadison.OperatorAmplification.amplifiedStage_diagonal`, `OAI.Kadison.OperatorAmplification.amplifiedStage_in_relative`, `OAI.Kadison.OperatorAmplification.amplifiedStage_irreducible`, `OAI.Kadison.OperatorAmplification.amplifiedStage_monotone`, `OAI.Kadison.OperatorAmplification.matrixGNSOperator_commutator_norm`, `OAI.Kadison.OperatorAmplification.matrixGNSOperator_commutes`, `OAI.Kadison.OperatorAmplification.matrixGNSOperator_small_corner`, `OAI.Kadison.OperatorAmplification.matrixGNSOperator_small_real_corner`, `OAI.Kadison.OperatorAmplification.matrix_free_symmetry_bound`, `OAI.Kadison.TracialGNS.actual_word_structure`, `OAI.Kadison.TracialSequence.FreeCornerPosition.symmetry_bound`, `OAI.Kadison.TracialSequence.constantAction_apply`, `OAI.Kadison.TracialSequence.exists_freeCornerPosition_of_equiv_stages`, `OAI.Kadison.TracialSequence.exists_freeCornerPosition_of_equiv_tower`, `OAI.Kadison.TracialSequence.freeCornerPosition_of_unitary_abstract` and `OAI.Kadison.TracialSequence.generated_free_small_corners_bound`; the proofs of `OAI.Kadison.MatrixTower.exists_matrix_freeCornerPosition`, `OAI.Kadison.MatrixTower.finite_standard_bound`, `OAI.Kadison.MatrixTower.finite_standard_entrywise_bound`, `OAI.Kadison.MatrixTower.finite_standard_gauge_bound`, `OAI.Kadison.MatrixTower.rectangular_bound_after_average`, `OAI.Kadison.MatrixTower.rectangular_contraction_after_average`, `OAI.Kadison.MatrixTower.square_contraction_after_average`, `OAI.Kadison.MatrixTower.square_symmetry_after_average`, `OAI.Kadison.OperatorAmplification.amplifiedStage_diagonal`, `OAI.Kadison.OperatorAmplification.amplifiedStage_in_relative`, `OAI.Kadison.OperatorAmplification.amplifiedStage_irreducible`, `OAI.Kadison.OperatorAmplification.amplifiedStage_monotone`, `OAI.Kadison.OperatorAmplification.matrixGNSOperator_commutator_norm`, `OAI.Kadison.OperatorAmplification.matrixGNSOperator_commutes`, `OAI.Kadison.OperatorAmplification.matrixGNSOperator_small_corner`, `OAI.Kadison.OperatorAmplification.matrixGNSOperator_small_real_corner`, `OAI.Kadison.OperatorAmplification.matrix_free_symmetry_bound`, `OAI.Kadison.TracialGNS.actual_word_structure`, `OAI.Kadison.TracialSequence.FreeCornerPosition.symmetry_bound`, `OAI.Kadison.TracialSequence.constantAction_apply`, `OAI.Kadison.TracialSequence.exists_freeCornerPosition_of_equiv_stages` and `OAI.Kadison.TracialSequence.exists_freeCornerPosition_of_equiv_tower`.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/Commutator at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ039C058
import Definitions.Def_OAIQ039C060
import Definitions.Def_OAIQ039C061
import Definitions.Def_OAIQ039C062
import Definitions.Def_OAIQ039C064

section
-- module Solutions.OAIQ039_CM.Commutator_AmplifiedTowerStage
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator

namespace Kadison.OperatorAmplification

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ι : Type) [Fintype ι] (i₀ : ι) (M : VonNeumannAlgebra H)

attribute [local instance] OAI.Kadison.OperatorAmplification.amplifiedTowerStageDecidableEq
lemma scalar_diagonal_commute (x : Matrix ι ι ℂ) (a : M) :
    Commute (scalarMatrixHom ι i₀ M x) (diagonalHom ι i₀ M a) := by
  change _*_=_*_
  apply Subtype.ext
  change (scalarMatrixHom ι i₀ M x:SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι)*
    (diagonalHom ι i₀ M a:SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι)=
    (diagonalHom ι i₀ M a:SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι)*
    (scalarMatrixHom ι i₀ M x:SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι)
  rw [scalarMatrixHom_coe,coe_diagonalHom]
  simp only [Finset.sum_mul,Finset.mul_sum,smul_mul_assoc,mul_smul_comm,matrixUnit_commutes]

variable (E : MatrixTower.Stage M)

def amplifiedStage : MatrixTower.Stage (matrixVonNeumann ι i₀ M) where
  I := ι×E.I
  finite := inferInstance
  dec := inferInstance
  nonempty := ⟨(i₀,Classical.choice inferInstance)⟩
  hom := MatrixTensor.representation (scalarMatrixHom ι i₀ M) ((diagonalHom ι i₀ M).comp E.hom)
    (fun x y => scalar_diagonal_commute ι i₀ M x (E.hom y))

end Kadison.OperatorAmplification

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_InvariantSum
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct
open scoped TensorProduct InnerProductSpace Topology
open UniformSpace Completion Filter
open scoped TensorProduct
open UniformSpace Completion
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open scoped InnerProductSpace TensorProduct ComplexOrder
open UniformSpace
open scoped InnerProductSpace _root_.Topology
open scoped TensorProduct
open UniformSpace
open scoped TensorProduct InnerProductSpace
open scoped InnerProductSpace ENNReal
open ContinuousLinearMap
open scoped InnerProductSpace ENNReal
open scoped ComplexOrder InnerProductSpace TensorProduct
open UniformSpace ContinuousLinearMap

namespace Kadison.TracialGNS

open PreHilbert HilbertTensor

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b : A, τ (a*b)=τ (b*a)) (h1 : τ 1=1)

variable (J : ℕ → Type*) [∀ k, NormedAddCommGroup (J k)]
  [∀ k, InnerProductSpace ℂ (J k)] [∀ k, CompleteSpace (J k)]

instance sumLevelInner (k : ℕ) : InnerProductSpace ℂ (sumLevel τ J k) :=
  inferInstanceAs (InnerProductSpace ℂ (Completion (wordSpace (fullSpace τ) (zeroSpace τ) k ⊗[ℂ] J k)))

def sumConjugation (u : unitary A) (k : ℕ) : sumLevel τ J k →L[ℂ] sumLevel τ J k :=
  HilbertTensor.map (wordConjugation τ hτ u k).toContinuousLinearMap 1

end Kadison.TracialGNS
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixGNSCornerBound
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped BigOperators InnerProductSpace ComplexOrder

namespace Kadison.OperatorAmplification

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ι : Type) [Fintype ι] [Nonempty ι] (i₀ : ι) (M Q : VonNeumannAlgebra H) (hQM : Q≤M)

attribute [local instance] OAI.Kadison.OperatorAmplification.instDecidableEq_solutions_3
variable (τ : M →ₚ[ℂ] ℂ)

def matrixGNSOperator (T : SumSpace (H:=τ.GNS) ι →L[ℂ] SumSpace (H:=τ.GNS) ι) :
    (MatrixGNS.trace (ι:=ι) τ).GNS →L[ℂ] (MatrixGNS.trace (ι:=ι) τ).GNS :=
  (MatrixGNS.unitary (ι:=ι) τ).symm.conjStarAlgEquiv
    (diagonal (H:=SumSpace (H:=τ.GNS) ι) ι T)

end Kadison.OperatorAmplification

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixTowerInclusion
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder

namespace Kadison.MatrixTower

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (F : ℕ → Stage M)

variable [Nontrivial M] (hF : Monotone (fun n => (F n).hom.range))

def stageInclusion {n m : ℕ} (h : n ≤ m) :
    Matrix (F n).I (F n).I ℂ →⋆ₐ[ℂ] Matrix (F m).I (F m).I ℂ :=
  (StarAlgEquiv.ofInjective (F m).hom (stage_injective M F m)).symm.toStarAlgHom.comp
    ((StarSubalgebra.inclusion (hF h)).comp (F n).hom.rangeRestrict)

end Kadison.MatrixTower

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixIndexEquiv
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped Matrix.Norms.L2Operator

namespace Kadison.MatrixTower

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (F : ℕ → Stage M)

lemma normalizedSize_succ (n : ℕ) : normalizedSize M F n+1=Fintype.card (F n).I := by
  have h := Fintype.card_pos (α := (F n).I)
  unfold normalizedSize
  omega

def normalizedIndex (n : ℕ) : Fin (normalizedSize M F n+1) ≃ (F n).I :=
  (finCongr (normalizedSize_succ M F n)).trans (Fintype.equivFin (F n).I).symm

def normalizedStage (n : ℕ) : Matrix (Fin (normalizedSize M F n+1)) (Fin (normalizedSize M F n+1)) ℂ →⋆ₐ[ℂ] M :=
  (F n).hom.comp (matrixIndexEquiv (normalizedIndex M F n)).toStarAlgHom

variable [Nontrivial M] (hF : Monotone (fun n => (F n).hom.range))

def normalizedInclusion {n m : ℕ} (h : n ≤ m) :
    Matrix (Fin (normalizedSize M F n+1)) (Fin (normalizedSize M F n+1)) ℂ →⋆ₐ[ℂ]
    Matrix (Fin (normalizedSize M F m+1)) (Fin (normalizedSize M F m+1)) ℂ :=
  (matrixIndexEquiv (normalizedIndex M F m)).symm.toStarAlgHom.comp
    ((stageInclusion M F hF h).comp (matrixIndexEquiv (normalizedIndex M F n)).toStarAlgHom)

end Kadison.MatrixTower

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_TracialGeneratedAlgebra
attribute [-instance] _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped ComplexOrder InnerProductSpace

namespace Kadison.TracialSequence

def constantAction {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ) :
    A →⋆ₐ[ℂ] (boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω) :=
  (leftRestricted τ ω).comp constantSequence

end Kadison.TracialSequence

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_TracialFreePositionCriterion
attribute [-instance] _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator

open Filter

namespace Kadison.TracialSequence

open FreeMoments

variable {A K : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

abbrev FreeCornerPosition (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ)
    (Q : VonNeumannAlgebra K) (j : Q →⋆ₐ[ℂ] A) :=
  FreeCornerPositionData (sequenceVacuum τ ω) (constantAction τ ω)
    (Set.range ((leftRestricted τ ω).comp (mapSequence j)))

end Kadison.TracialSequence

end

end OAI
end


