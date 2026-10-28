-- Prove2me | Definitions.Def_OAIQ039C063
-- name    : OAIQ039C063
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T09:17:30.085302+00:00
-- url     : https://prove2.me/theorems/f9b54b30-df34-4d56-b42d-7ee7cd108ede
-- title:
--   Definitions bundle OAIQ039C063 of the split of OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 6 declarations of OpenAI's Lean: 4 definitions, 1 instance and 1 theorem. The definitions and types are `OAI.Kadison.FreeBlocks.embeddedSourceWord`, `OAI.Kadison.OperatorAmplification.matrixEquiv`, `OAI.Kadison.OperatorAmplification.matrixInclusion`, `OAI.Kadison.OperatorAmplification.standardMatrixRepresentation`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/Commutator, in whole or in part: `Commutator_FreeActualStructure`, `Commutator_InvariantSum`, `Commutator_MatrixAlgebraEquiv`, `Commutator_MatrixCornerInclusion`, `Commutator_MatrixStandardForm`.
--
--   **Imports.** It imports the bundles `OAIQ039C055`, `OAIQ039C056` and `OAIQ039C057` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ039C068` and `OAIQ039C069`; the statements `OAI.Kadison.FreeBlocks.free_word_structure`, `OAI.Kadison.MatrixTower.exists_matrix_freeCornerPosition`, `OAI.Kadison.MatrixTower.finite_standard_entrywise_bound`, `OAI.Kadison.MatrixTower.finite_standard_gauge_bound`, `OAI.Kadison.MatrixTower.rectangular_bound_after_average`, `OAI.Kadison.MatrixTower.rectangular_contraction_after_average`, `OAI.Kadison.MatrixTower.square_contraction_after_average`, `OAI.Kadison.MatrixTower.square_symmetry_after_average`, `OAI.Kadison.OperatorAmplification.matrixGNSOperator_commutes`, `OAI.Kadison.OperatorAmplification.matrixGNSOperator_small_corner`, `OAI.Kadison.OperatorAmplification.matrixGNSOperator_small_real_corner`, `OAI.Kadison.OperatorAmplification.matrixInclusion_commutes`, `OAI.Kadison.OperatorAmplification.matrixInclusion_entry`, `OAI.Kadison.OperatorAmplification.matrixInclusion_row` and `OAI.Kadison.OperatorAmplification.matrix_free_symmetry_bound`; the proofs of `OAI.Kadison.FreeBlocks.stage_hankel_bound`, `OAI.Kadison.MatrixTower.finite_standard_bound`, `OAI.Kadison.MatrixTower.finite_standard_entrywise_bound`, `OAI.Kadison.MatrixTower.finite_standard_gauge_bound`, `OAI.Kadison.MatrixTower.rectangular_bound_after_average`, `OAI.Kadison.MatrixTower.rectangular_contraction_after_average`, `OAI.Kadison.MatrixTower.square_contraction_after_average`, `OAI.Kadison.MatrixTower.square_symmetry_after_average`, `OAI.Kadison.OperatorAmplification.matrixGNSOperator_commutes`, `OAI.Kadison.OperatorAmplification.matrixGNSOperator_small_real_corner`, `OAI.Kadison.OperatorAmplification.matrixInclusion_commutes`, `OAI.Kadison.OperatorAmplification.matrixInclusion_entry`, `OAI.Kadison.OperatorAmplification.matrixInclusion_row`, `OAI.Kadison.OperatorAmplification.matrix_free_symmetry_bound` and `OAI.Kadison.TracialGNS.actual_word_structure`.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/Commutator at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ039C055
import Definitions.Def_OAIQ039C056
import Definitions.Def_OAIQ039C057

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

instance sumLevelComplete (k : ℕ) : CompleteSpace (sumLevel τ J k) :=
  inferInstanceAs (CompleteSpace (Completion (wordSpace (fullSpace τ) (zeroSpace τ) k ⊗[ℂ] J k)))

end Kadison.TracialGNS
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FreeActualStructure
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped ComplexOrder InnerProductSpace TensorProduct

open UniformSpace

namespace Kadison.FreeBlocks

open FreeWordTensor FreeMoments FreeWordAction

variable {A D : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable (t : FaithfulState A) (ht : ∀ a b : A, t.functional (a*b)=t.functional (b*a))

variable (f : D →⋆ₐ[ℂ] A) (hf : Function.Injective f)

variable {ι : Type*} (S : ι → StarSubalgebra ℂ A) (i j : ι) (hS : S i=f.range)

variable (hfree : Free S t.functional.toLinearMap)
  (hgen : ∀ a : A, t.functional.gnsStarAlgHom a ∈
    Set.centralizer (Set.centralizer (generatedOperators t S : Set _)))

variable (hij : i≠j) (hcolors : ∀ c : ι, c=i ∨ c=j)

variable (I : ℕ → Type*) [∀ n, Fintype (I n)] [∀ n, DecidableEq (I n)] [∀ n, Nonempty (I n)]

variable (φ : ∀ n, Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] D)

variable (e : ∀ {n m : ℕ}, n ≤ m → Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] Matrix (I m) (I m) ℂ)

variable (he : ∀ n m (h : n ≤ m) a, φ m (e h a)=φ n a)

variable (hsize : ∀ n q : ℕ, ∃ m, n ≤ m ∧ q ≤ Fintype.card (I m))

variable (hDgen : ∀ a : D, (factorTrace t f hf).gnsStarAlgHom a ∈
  Set.centralizer (Set.centralizer
    (TracialGNS.stageAlgebra (factorTrace t f hf) I φ : Set _)))

variable (G : t.functional.GNS →L[ℂ] t.functional.GNS)

variable (hGL : ∀ a : D, G.comp (t.functional.gnsStarAlgHom (f a))=
  (t.functional.gnsStarAlgHom (f a)).comp G)

abbrev embeddedSourceWord (level : ℕ) (scalar : factorFull t f hf)
    (centered : factorZero t f hf) (coefficient : multiplicityLevel t S j level) :
    t.functional.GNS :=
  sourceLevelEmbedding t f hf S i j hS hfree hij level
    (HilbertTensor.pair (E := sourceScalar t f hf level) (J := multiplicityLevel t S j level)
      (PreHilbert.word (factorFull t f hf) (factorZero t f hf) level scalar
        (fun _ => centered)) coefficient)

end Kadison.FreeBlocks

end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixAlgebraEquiv
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

open scoped BigOperators InnerProductSpace

namespace Kadison.OperatorAmplification

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ι : Type*) [Fintype ι] (i₀ : ι) (M : VonNeumannAlgebra H)

attribute [local instance] OAI.Kadison.OperatorAmplification.instDecidableEq_solutions
def matrixEquiv : CStarMatrix ι ι M ≃⋆ₐ[ℂ] matrixVonNeumann ι i₀ M :=
  StarAlgEquiv.ofBijective (matrixHom ι i₀ M) (matrixHom_bijective ι i₀ M)

end Kadison.OperatorAmplification

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixCornerInclusion
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

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ι : Type*) [Fintype ι] (i₀ : ι) (M Q : VonNeumannAlgebra H) (hQM : Q≤M)

attribute [local instance] OAI.Kadison.OperatorAmplification.matrixCornerInclusionDecidableEq
def matrixInclusion : matrixVonNeumann ι i₀ Q →⋆ₐ[ℂ] CStarMatrix ι ι M :=
  (matrixEquiv ι i₀ M).symm.toStarAlgHom.comp
    (NormalSubalgebra.inclusion (matrixVonNeumann ι i₀ M) (matrixVonNeumann ι i₀ Q)
      (matrixVonNeumann_mono ι i₀ hQM))

end Kadison.OperatorAmplification

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixStandardForm
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

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ι : Type*) [Fintype ι] (i₀ : ι) (M : VonNeumannAlgebra H)

attribute [local instance] OAI.Kadison.OperatorAmplification.matrixStandardFormDecidableEq
variable (τ : M →ₚ[ℂ] ℂ)

def standardMatrixRepresentation : matrixVonNeumann ι i₀ M →⋆ₐ[ℂ]
    (MatrixGNS.ArraySpace (ι:=ι) τ →L[ℂ] MatrixGNS.ArraySpace (ι:=ι) τ) :=
  (MatrixGNS.representation (ι:=ι) τ).comp (matrixEquiv ι i₀ M).symm.toStarAlgHom

lemma standardMatrixRepresentation_equiv (X : CStarMatrix ι ι M) :
    standardMatrixRepresentation ι i₀ M τ (matrixEquiv ι i₀ M X)=
      MatrixGNS.representation (ι:=ι) τ X := by
  change MatrixGNS.representation (ι:=ι) τ
    ((matrixEquiv ι i₀ M).symm (matrixEquiv ι i₀ M X))=_
  exact congrArg (MatrixGNS.representation (ι:=ι) τ) ((matrixEquiv ι i₀ M).symm_apply_apply X)

end Kadison.OperatorAmplification

end

end
end

end OAI
end


