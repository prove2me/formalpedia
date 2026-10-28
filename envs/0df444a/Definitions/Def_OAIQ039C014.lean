-- Prove2me | Definitions.Def_OAIQ039C014
-- name    : OAIQ039C014
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T06:13:21.052159+00:00
-- url     : https://prove2.me/theorems/d633fc04-9c8f-4c42-994e-efa7853c32b2
-- title:
--   Definitions bundle OAIQ039C014 of the split of OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 34 declarations of OpenAI's Lean: 29 definitions and 5 theorems. The definitions and types are `OAI.Kadison.MatrixModules.inflate`, `OAI.Kadison.MatrixModules.matrixRepresentation`, `OAI.Kadison.MatrixTower.finiteRectangularBoundColumnDecidableEq`, `OAI.Kadison.MatrixTower.finiteRectangularBoundDoubledSumDecidableEq`, `OAI.Kadison.MatrixTower.finiteRectangularContractionDoubledSumDecidableEq`, `OAI.Kadison.MatrixTower.finiteSquareConditionalBoundDecidableEq`, `OAI.Kadison.MatrixTower.finiteSquareContractionDoubledIndexDecidableEq`, `OAI.Kadison.MatrixTower.finiteStandardGaugeColumnDecidableEq`, `OAI.Kadison.MatrixTower.finiteStandardGaugeDoubledSumDecidableEq`, `OAI.Kadison.MatrixTower.finiteStandardMainInterfaceDoubledSumDecidableEq`, `OAI.Kadison.MatrixTower.finiteStandardRangeIndexDecidableEq`, `OAI.Kadison.MatrixTower.finiteStandardRepresentedDoubledSumDecidableEq`, `OAI.Kadison.MatrixTower.matrixFreePositionProducerDecidableEq`, `OAI.Kadison.MatrixTower.matrixIndexEquiv`, `OAI.Kadison.OperatorAmplification.amplifiedTowerGeometryIndexDecidableEq`, `OAI.Kadison.OperatorAmplification.amplifiedTowerStageDecidableEq`, `OAI.Kadison.OperatorAmplification.blockDilationFinTwoDecidableEq`, `OAI.Kadison.OperatorAmplification.blockDilationIndexDecidableEq`, `OAI.Kadison.OperatorAmplification.instDecidableEq_solutions`, `OAI.Kadison.OperatorAmplification.instDecidableEq_solutions_1`, `OAI.Kadison.OperatorAmplification.instDecidableEq_solutions_2`, `OAI.Kadison.OperatorAmplification.instDecidableEq_solutions_3`, `OAI.Kadison.OperatorAmplification.instDecidableEq_solutions_4`, `OAI.Kadison.OperatorAmplification.matrixDiffuseTransferIndexDecidableEq`, `OAI.Kadison.OperatorAmplification.matrixFreeSymmetryDecidableEq`, `OAI.Kadison.OperatorFunctionals.coefficientDual`, `OAI.Kadison.OperatorFunctionals.finiteFunctional`, `OAI.Kadison.SchurWeyl.cycleSet`, `OAI.Kadison.TailSlots`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/Commutator, in whole or in part: `Commutator_AmplifiedTowerGeometry`, `Commutator_AmplifiedTowerStage`, `Commutator_BlockDilationBound`, `Commutator_CycleInvariants`, `Commutator_FiniteFunctionalFactorization`, `Commutator_FiniteMatrixSmallCorner`, `Commutator_FinitePairings3`, `Commutator_FiniteRectangularBound`, `Commutator_FiniteRectangularContraction`, `Commutator_FiniteSquareConditionalBound`, `Commutator_FiniteSquareContraction`, `Commutator_FiniteStandardGauge`, `Commutator_FiniteStandardMainInterface`, `Commutator_FiniteStandardRange`, `Commutator_FiniteStandardRepresented`, `Commutator_FiniteSupportFactorization`, `Commutator_MatrixAlgebraEquiv`, `Commutator_MatrixClassification`, `Commutator_MatrixDiffuseTransfer`, `Commutator_MatrixFreePositionProducer`, `Commutator_MatrixFreeSymmetry`, `Commutator_MatrixGNSCornerBound`, `Commutator_MatrixGNSRealCorner`, `Commutator_MatrixIndexEquiv`, `Commutator_MatrixModules`, `Commutator_MatrixNormalTrace`, `Commutator_MatrixTensor`, `Commutator_NormalGNSContinuity`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ039C029`, `OAIQ039C030` and `OAIQ039C031`; the statements `OAI.Kadison.finite_pairing_source_bound` and `OAI.Kadison.finite_pairing_test_bound`; the proofs of `OAI.Kadison.MatrixGNS.flatBalanced_commutator_dominates`, `OAI.Kadison.finite_pairing_source_bound` and `OAI.Kadison.finite_pairing_test_bound`.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/Commutator at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixAlgebraEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped BigOperators InnerProductSpace

namespace Kadison.OperatorAmplification

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ι : Type*) [Fintype ι] (i₀ : ι) (M : VonNeumannAlgebra H)

local instance instDecidableEq_solutions : DecidableEq ι := Classical.decEq ι

end Kadison.OperatorAmplification

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixNormalTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped BigOperators InnerProductSpace ComplexOrder Topology

open ContinuousLinearMapWOT

namespace Kadison.OperatorAmplification

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ι : Type*) [Fintype ι] (i₀ : ι) (M : VonNeumannAlgebra H)

local instance instDecidableEq_solutions_1 : DecidableEq ι := Classical.decEq ι

end Kadison.OperatorAmplification

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators

namespace Kadison.MatrixTensor

open Matrix

variable {A I J : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

variable (φ : Matrix I I ℂ →⋆ₐ[ℂ] A) (ψ : Matrix J J ℂ →⋆ₐ[ℂ] A)
  (hc : ∀ x y,Commute (φ x) (ψ y))

omit [StarModule ℂ A] in
include hc in
lemma units_star (i j : I×J) :
    star (φ (single i.1 j.1 1)*ψ (single i.2 j.2 1))=
      φ (single j.1 i.1 1)*ψ (single j.2 i.2 1) := by
  simp only [star_mul,←map_star,Matrix.star_eq_conjTranspose,conjTranspose_single,star_one]
  exact (hc _ _).eq.symm

omit [StarModule ℂ A] in
lemma units_one : (∑ i : I×J,φ (single i.1 i.1 1)*ψ (single i.2 i.2 1))=1 := by
  rw [Fintype.sum_prod_type]
  simp only [←Finset.mul_sum,←map_sum,sum_single_one,map_one,mul_one]

end Kadison.MatrixTensor

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixDiffuseTransfer
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

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ι : Type*) [Fintype ι] (i₀ : ι) (M : VonNeumannAlgebra H)

local instance matrixDiffuseTransferIndexDecidableEq : DecidableEq ι := Classical.decEq ι

end Kadison.OperatorAmplification

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_AmplifiedTowerStage
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

local instance amplifiedTowerStageDecidableEq : DecidableEq ι := Classical.decEq ι

end Kadison.OperatorAmplification

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_AmplifiedTowerGeometry
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

local instance amplifiedTowerGeometryIndexDecidableEq : DecidableEq ι := Classical.decEq ι

end Kadison.OperatorAmplification

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_BlockDilationBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace ComplexOrder

namespace Kadison.OperatorAmplification

variable {A H ι : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [Fintype ι]

local instance blockDilationIndexDecidableEq : DecidableEq ι := Classical.decEq ι

local instance blockDilationFinTwoDecidableEq : DecidableEq (Fin 2) := Classical.decEq (Fin 2)

end Kadison.OperatorAmplification

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_CycleInvariants
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

namespace Kadison.SchurWeyl

open Matrix

variable {𝕜 : Type*} [CommRing 𝕜]

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

def cycleSet (σ : Equiv.Perm J) := Quotient (Equiv.Perm.SameCycle.setoid σ)

end Kadison.SchurWeyl
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FiniteFunctionalFactorization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace

namespace Kadison.OperatorFunctionals

open InnerProductSpace ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def coefficientDual (φ : StrongDual ℂ (H →L[ℂ] H)) (b : H) : StrongDual ℂ H :=
  φ.comp ((rankOne ℂ : H →L[ℂ] H →L⋆[ℂ] H →L[ℂ] H).flip b)

@[simp] lemma coefficientDual_apply (φ : StrongDual ℂ (H →L[ℂ] H)) (a b : H) :
    coefficientDual φ b a=φ (rankOne ℂ a b) := rfl

end Kadison.OperatorFunctionals

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FiniteMatrixSmallCorner
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

variable {H K : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

variable (ι : Type) [Fintype ι] (i₀ : ι) (M Q : VonNeumannAlgebra H) (hQM : Q≤M)

local instance instDecidableEq_solutions_2 : DecidableEq ι := Classical.decEq ι

end Kadison.OperatorAmplification

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FinitePairings3
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

namespace Kadison

abbrev TailSlots (k l : ℕ) := Fin k ⊕ₗ Fin l

end Kadison
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixGNSCornerBound
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

local instance instDecidableEq_solutions_3 : DecidableEq ι := Classical.decEq ι

end Kadison.OperatorAmplification

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixGNSRealCorner
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

namespace Kadison

namespace OperatorAmplification

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ι : Type) [Fintype ι] [Nonempty ι] (i₀ : ι) (M Q : VonNeumannAlgebra H) (hQM : Q≤M)

local instance instDecidableEq_solutions_4 : DecidableEq ι := Classical.decEq ι

end OperatorAmplification

end Kadison

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixModules
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

namespace Kadison.MatrixModules

open Matrix

variable {𝕜 I E : Type*} [Field 𝕜] [Fintype I] [DecidableEq I]
  [AddCommGroup E] [Module 𝕜 E]

variable (ρ : Matrix I I 𝕜 →ₐ[𝕜] Module.End 𝕜 E) (o : I)

section Coordinates

variable {R : Type*} [Fintype R]

def inflate [DecidableEq R] (a : Matrix I I 𝕜) : Matrix (I × R) (I × R) 𝕜 :=
  fun x y => if x.2 = y.2 then a x.1 y.1 else 0

end Coordinates

end Kadison.MatrixModules
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixClassification
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

namespace Kadison.MatrixModules

open Matrix

variable {𝕜 I K R : Type*} [Field 𝕜]
  [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]
  [Fintype R] [DecidableEq R]

variable (φ : Matrix I I 𝕜 →ₐ[𝕜] Matrix K K 𝕜) (o : I)

abbrev matrixRepresentation : Matrix I I 𝕜 →ₐ[𝕜] Module.End 𝕜 (K → 𝕜) :=
  Matrix.toLinAlgEquiv'.toAlgHom.comp φ

end Kadison.MatrixModules
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FiniteSupportFactorization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace

namespace Kadison.OperatorFunctionals

open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (K : Submodule ℂ H) [K.HasOrthogonalProjection]

variable {ι : Type*} [Fintype ι]

def finiteFunctional (x y : ι → H) : StrongDual ℂ (H →L[ℂ] H) :=
  ∑ i, (innerSL ℂ (y i)).comp (ContinuousLinearMap.apply ℂ H (x i))

omit [CompleteSpace H] in
@[simp] lemma finiteFunctional_apply (x y : ι → H) (T : H →L[ℂ] H) :
    finiteFunctional x y T=∑ i, inner ℂ (y i) (T (x i)) := by
  simp [finiteFunctional]

end Kadison.OperatorFunctionals

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_NormalGNSContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace Topology ComplexOrder NNReal

open Filter

namespace Kadison.NormalGNS

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

lemma wot_tendsto_of_dense {ι B : Type*} {l : Filter ι} (v : B → E) (hv : DenseRange v)
    (T : ι → E →L[ℂ] E) (S : E →L[ℂ] E) (C : ℝ≥0) (hT : ∀ i,‖T i‖≤C)
    (hlim : ∀ a b,Tendsto (fun i => inner ℂ (v a) (T i (v b))) l
      (𝓝 (inner ℂ (v a) (S (v b))))) (x y : E) :
    Tendsto (fun i => inner ℂ x (T i y)) l (𝓝 (inner ℂ x (S y))) := by
  have hfirst (b : B) (x : E) : Tendsto (fun i => inner ℂ x (T i (v b))) l
      (𝓝 (inner ℂ x (S (v b)))) := by
    have hequi : Equicontinuous (fun i x => inner ℂ x (T i (v b))) := by
      apply (LipschitzWith.uniformEquicontinuous _ (C*‖v b‖₊) ?_).equicontinuous
      intro i
      apply LipschitzWith.of_dist_le_mul
      intro x y
      rw [dist_eq_norm,←inner_sub_left]
      apply (norm_inner_le_norm _ _).trans
      have hn : ‖T i (v b)‖≤C*‖v b‖ :=
        (T i).le_opNorm (v b) |>.trans (mul_le_mul_of_nonneg_right (hT i) (norm_nonneg _))
      simpa only [NNReal.coe_mul,coe_nnnorm,dist_eq_norm,mul_comm] using
        mul_le_mul_of_nonneg_left hn (norm_nonneg (x-y))
    exact (hequi x).tendsto_of_mem_closure
      ((continuous_id.inner continuous_const).continuousAt.mono_left inf_le_left)
      (by rintro _ ⟨a,rfl⟩; exact hlim a b) (hv x)
  have hequi : Equicontinuous (fun i y => inner ℂ x (T i y)) := by
    apply (LipschitzWith.uniformEquicontinuous _ (‖x‖₊*C) ?_).equicontinuous
    intro i
    apply LipschitzWith.of_dist_le_mul
    intro y z
    rw [dist_eq_norm,←inner_sub_right,←map_sub]
    apply (norm_inner_le_norm _ _).trans
    have hn : ‖T i (y-z)‖≤C*‖y-z‖ :=
      (T i).le_opNorm (y-z) |>.trans (mul_le_mul_of_nonneg_right (hT i) (norm_nonneg _))
    simpa only [NNReal.coe_mul,coe_nnnorm,dist_eq_norm,mul_assoc] using
      mul_le_mul_of_nonneg_left hn (norm_nonneg x)
  exact (hequi y).tendsto_of_mem_closure
    ((continuous_const.inner S.continuous).continuousAt.mono_left inf_le_left)
    (by rintro _ ⟨b,rfl⟩; exact hfirst b x) (hv y)

end Kadison.NormalGNS

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixFreeSymmetry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator

open Filter

namespace Kadison.OperatorAmplification

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ι : Type) [Fintype ι] [Nonempty ι] (i₀ : ι) (M Q : VonNeumannAlgebra H) (hQM : Q≤M)

local instance matrixFreeSymmetryDecidableEq : DecidableEq ι := Classical.decEq ι

end Kadison.OperatorAmplification

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FiniteSquareConditionalBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator

open Filter

namespace Kadison

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

namespace MatrixTower

open OperatorAmplification

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ι : Type) [Fintype ι] [Nonempty ι] (i₀ : ι)

local instance finiteSquareConditionalBoundDecidableEq : DecidableEq ι := Classical.decEq ι

end MatrixTower

end Kadison

end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FiniteSquareContraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator

open Filter

namespace Kadison.MatrixTower

open OperatorAmplification

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ι : Type) [Fintype ι] [Nonempty ι] (i₀ : ι)

local instance instDecidableEq_solutions_rfa0a12_1 : DecidableEq ι := Classical.decEq ι
local instance finiteSquareContractionDoubledIndexDecidableEq : DecidableEq ((Fin 2)×ι) := Classical.decEq _

end Kadison.MatrixTower

end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FiniteRectangularContraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator

open Filter

namespace Kadison.MatrixTower

open OperatorAmplification

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ι κ : Type) [Fintype ι] [Fintype κ] [Nonempty κ] (k₀ : κ)

local instance finiteRectangularContractionIndexDecidableEq_rfa0a12_1 : DecidableEq ι := Classical.decEq ι
local instance finiteRectangularContractionColumnDecidableEq_rfa0a12_1 : DecidableEq κ := Classical.decEq κ
local instance finiteRectangularContractionSumDecidableEq_rfa0a12_1 : DecidableEq (κ⊕ι) := Classical.decEq _
local instance finiteRectangularContractionDoubledSumDecidableEq : DecidableEq ((Fin 2)×(κ⊕ι)) := Classical.decEq _

end Kadison.MatrixTower

end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FiniteRectangularBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator

open Filter

namespace Kadison.MatrixTower

open OperatorAmplification

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ι κ : Type) [Fintype ι] [Fintype κ] [Nonempty κ] (k₀ : κ)

local instance finiteRectangularBoundColumnDecidableEq : DecidableEq κ := Classical.decEq κ

local instance finiteRectangularBoundIndexDecidableEq_rfa0a12_1 : DecidableEq ι := Classical.decEq ι
local instance finiteRectangularBoundSumDecidableEq_rfa0a12_1 : DecidableEq (κ⊕ι) := Classical.decEq _
local instance finiteRectangularBoundDoubledSumDecidableEq : DecidableEq ((Fin 2)×(κ⊕ι)) := Classical.decEq _

end Kadison.MatrixTower

end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FiniteStandardGauge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator

open Filter

namespace Kadison.MatrixTower

open OperatorAmplification

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ι κ : Type) [Fintype ι] [Nonempty ι] [Fintype κ] [Nonempty κ] (k₀ : κ)

local instance finiteStandardGaugeColumnDecidableEq : DecidableEq κ := Classical.decEq κ

local instance finiteStandardGaugeIndexDecidableEq_rfa0a12_1 : DecidableEq ι := Classical.decEq ι
local instance finiteStandardGaugeSumDecidableEq_rfa0a12_1 : DecidableEq (κ⊕ι) := Classical.decEq _
local instance finiteStandardGaugeDoubledSumDecidableEq : DecidableEq ((Fin 2)×(κ⊕ι)) := Classical.decEq _

end Kadison.MatrixTower

end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FiniteStandardRange
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped InnerProductSpace ComplexOrder

namespace Kadison.MatrixTower

open OperatorAmplification

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ι : Type) [Fintype ι] [Nonempty ι]

local instance finiteStandardRangeIndexDecidableEq : DecidableEq ι := Classical.decEq ι

end Kadison.MatrixTower

end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FiniteStandardRepresented
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator

open Filter

namespace Kadison.MatrixTower

open OperatorAmplification

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ι κ : Type) [Fintype ι] [Nonempty ι] [Fintype κ] [Nonempty κ] (k₀ : κ)

local instance finiteStandardRepresentedIndexDecidableEq_rfa0a12_1 : DecidableEq ι := Classical.decEq ι
local instance finiteStandardRepresentedColumnDecidableEq_rfa0a12_1 : DecidableEq κ := Classical.decEq κ
local instance finiteStandardRepresentedSumDecidableEq_rfa0a12_1 : DecidableEq (κ⊕ι) := Classical.decEq _
local instance finiteStandardRepresentedDoubledSumDecidableEq : DecidableEq ((Fin 2)×(κ⊕ι)) := Classical.decEq _

end Kadison.MatrixTower

end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FiniteStandardMainInterface
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator

open Filter

namespace Kadison.MatrixTower

open OperatorAmplification

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ι : Type) [Fintype ι] [Nonempty ι] (h : ℕ) (hh : 1 ≤ h)

local instance finiteStandardMainInterfaceIndexDecidableEq_rfa0a12_1 : DecidableEq ι := Classical.decEq ι
local instance finiteStandardMainInterfaceColumnDecidableEq_rfa0a12_1 : DecidableEq (Fin h) := Classical.decEq (Fin h)
local instance finiteStandardMainInterfaceSumDecidableEq_rfa0a12_1 : DecidableEq (Fin h⊕ι) := Classical.decEq _
local instance finiteStandardMainInterfaceDoubledSumDecidableEq : DecidableEq ((Fin 2)×(Fin h⊕ι)) := Classical.decEq _

end Kadison.MatrixTower

end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixIndexEquiv
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

def matrixIndexEquiv {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (e : I ≃ J) : Matrix I I ℂ ≃⋆ₐ[ℂ] Matrix J J ℂ where
  __ := (Matrix.reindexAlgEquiv ℂ ℂ e).toRingEquiv
  map_smul' c a := by ext i j; rfl
  map_star' a := by
    change Matrix.reindex e e a.conjTranspose=(Matrix.reindex e e a).conjTranspose
    exact (Matrix.conjTranspose_reindex e e a).symm

end Kadison.MatrixTower

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixFreePositionProducer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped Topology ComplexOrder Matrix.Norms.L2Operator

open Filter

namespace Kadison.MatrixTower

open OperatorAmplification

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ι : Type) [Fintype ι] (i₀ : ι) (M : VonNeumannAlgebra H) [Nontrivial M]

local instance matrixFreePositionProducerDecidableEq : DecidableEq ι := Classical.decEq ι

end Kadison.MatrixTower

end

end
end

end OAI
end


