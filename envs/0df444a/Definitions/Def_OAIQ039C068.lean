-- Prove2me | Definitions.Def_OAIQ039C068
-- name    : OAIQ039C068
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T09:21:08.066632+00:00
-- url     : https://prove2.me/theorems/a9718fc1-8e0b-4d9f-8dbd-853937b3b611
-- title:
--   Definitions bundle OAIQ039C068 of the split of OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 6 declarations of OpenAI's Lean: 3 definitions and 3 theorems. The definitions and types are `OAI.Kadison.OperatorAmplification.matrixTrace`, `OAI.Kadison.OperatorAmplification.standardMatrixUnitary`, `OAI.Kadison.ProjectionJoin.sup`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/Commutator, in whole or in part: `Commutator_CountableProjectionJoin`, `Commutator_MatrixNormalTrace`, `Commutator_MatrixStandardForm`.
--
--   **Imports.** It imports the bundles `OAIQ039C058`, `OAIQ039C059`, `OAIQ039C061` and `OAIQ039C063` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI.Kadison.OperatorAmplification.matrixTrace_apply`, `OAI.Kadison.OperatorAmplification.matrixTrace_diagonal`, `OAI.Kadison.OperatorAmplification.matrixTrace_faithful`, `OAI.Kadison.OperatorAmplification.matrixTrace_normal`, `OAI.Kadison.OperatorAmplification.matrixTrace_restrict`, `OAI.Kadison.OperatorAmplification.matrixTrace_tracial`, `OAI.Kadison.OperatorAmplification.matrix_small_corner_bound` and `OAI.Kadison.ProjectionJoin.dimension_sup_le`; the proofs of `OAI.Kadison.MatrixTower.exists_matrix_freeCornerPosition`, `OAI.Kadison.OperatorAmplification.matrixGNSOperator_small_corner`, `OAI.Kadison.OperatorAmplification.matrixTrace_apply`, `OAI.Kadison.OperatorAmplification.matrixTrace_diagonal`, `OAI.Kadison.OperatorAmplification.matrixTrace_faithful`, `OAI.Kadison.OperatorAmplification.matrixTrace_normal`, `OAI.Kadison.OperatorAmplification.matrixTrace_restrict`, `OAI.Kadison.OperatorAmplification.matrixTrace_tracial`, `OAI.Kadison.OperatorAmplification.matrix_diffuse_of_stages`, `OAI.Kadison.OperatorAmplification.matrix_small_corner_bound`, `OAI.Kadison.ProjectionDimensionTopology.vector_uniform_absolute_continuity` and `OAI.Kadison.ProjectionJoin.dimension_sup_le`.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/Commutator at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ039C058
import Definitions.Def_OAIQ039C059
import Definitions.Def_OAIQ039C061
import Definitions.Def_OAIQ039C063

section
-- module Solutions.OAIQ039_CM.Commutator_CountableProjectionJoin
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open Filter

open scoped ComplexOrder InnerProductSpace Topology BigOperators

namespace Kadison.ProjectionJoin

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem exists_countable_sup (M : VonNeumannAlgebra H) (P : ℕ → H →L[ℂ] H)
    (hP : ∀ n,IsStarProjection (P n)) (hPM : ∀ n,P n∈M) :
    ∃ W : H →L[ℂ] H,W∈M ∧ IsStarProjection W ∧ (∀ n,P n≤W) ∧
      (∀ x,Tendsto (fun n => finiteJoin P n x) atTop (𝓝 (W x))) ∧
      ∀ Q : H →L[ℂ] H,IsStarProjection Q → (∀ n,P n≤Q) → W≤Q := by
  obtain ⟨W,hWM,hW,hPW,hlim,hle⟩ := ProjectionChains.exists_strong_sup M (finiteJoin P)
    (finiteJoin_projection P) (finiteJoin_mem M P hPM) (finiteJoin_mono P)
  exact ⟨W,hWM,hW,fun n => (le_finiteJoin_succ P hP n).trans (hPW (n+1)),hlim,
    fun Q hQ hPQ => hle Q hQ (finiteJoin_le P hP hQ hPQ)⟩

def sup (M : VonNeumannAlgebra H) (P : ℕ → H →L[ℂ] H)
    (hP : ∀ n,IsStarProjection (P n)) (hPM : ∀ n,P n∈M) : H →L[ℂ] H :=
  (exists_countable_sup M P hP hPM).choose

open PartialIsometryOrder PartialIsometryOrder.DyadicPartition

end Kadison.ProjectionJoin

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixNormalTrace
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

open scoped BigOperators InnerProductSpace ComplexOrder Topology

open ContinuousLinearMapWOT

namespace Kadison.OperatorAmplification

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ι : Type*) [Fintype ι] (i₀ : ι) (M : VonNeumannAlgebra H)

attribute [local instance] OAI.Kadison.OperatorAmplification.instDecidableEq_solutions_1
variable (τ : M →ₚ[ℂ] ℂ)

def matrixTrace : matrixVonNeumann ι i₀ M →ₚ[ℂ] ℂ where
  toLinearMap := (MatrixGNS.trace (ι:=ι) τ).toLinearMap.comp
    (matrixEquiv ι i₀ M).symm.toStarAlgHom.toLinearMap
  monotone' := (MatrixGNS.trace (ι:=ι) τ).monotone.comp
    (OrderHomClass.monotone (matrixEquiv ι i₀ M).symm.toStarAlgHom)

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

lemma standardMatrixTrace_vector (X : matrixVonNeumann ι i₀ M) :
    matrixTrace ι i₀ M τ X=inner ℂ (MatrixGNS.vacuum (ι:=ι) τ)
      (standardMatrixRepresentation ι i₀ M τ X (MatrixGNS.vacuum (ι:=ι) τ)) := rfl

lemma standardMatrix_vacuum_cyclic : DenseRange (fun X : matrixVonNeumann ι i₀ M =>
    standardMatrixRepresentation ι i₀ M τ X (MatrixGNS.vacuum (ι:=ι) τ)) := by
  let : Nonempty ι := ⟨i₀⟩
  apply (MatrixGNS.dense_vacuumOrbit (ι:=ι) τ).mono
  rintro y ⟨X,rfl⟩
  exact ⟨matrixEquiv ι i₀ M X,congrArg (fun T => T (MatrixGNS.vacuum (ι:=ι) τ))
    (standardMatrixRepresentation_equiv ι i₀ M τ X)⟩

def standardMatrixUnitary :=
  VectorGNS.equivalence (matrixTrace ι i₀ M τ) (standardMatrixRepresentation ι i₀ M τ)
    (MatrixGNS.vacuum (ι:=ι) τ) (standardMatrixTrace_vector ι i₀ M τ)
    (standardMatrix_vacuum_cyclic ι i₀ M τ)

end Kadison.OperatorAmplification

end

end
end

end OAI
end


