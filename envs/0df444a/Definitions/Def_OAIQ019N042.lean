-- Prove2me | Definitions.Def_OAIQ019N042
-- name    : OAIQ019N042
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T06:10:19.426254+00:00
-- url     : https://prove2.me/theorems/07e8da0e-5276-46da-a181-90596a343850
-- title:
--   Definitions bundle OAIQ019N042 of the split of OpenAI, An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.NuclearUltrapower.main_no_embedding`, carved from OpenAI's openai/math development (OpenAI, *An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292)*, OpenAI Math Release, September 23, 2026, result family 292, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 12 declarations of OpenAI's Lean: 7 definitions and 5 theorems. The definitions and types are `OAI.NuclearUltrapower.CuntzAveraging.amplified`, `OAI.NuclearUltrapower.CuntzAveraging.completedEval`, `OAI.NuclearUltrapower.CuntzAveraging.defect`, `OAI.NuclearUltrapower.CuntzAveraging.instNormedSpaceComplexTarget`, `OAI.NuclearUltrapower.CuntzAveraging.instNormedSpaceComplexTargetCarrier`, `OAI.NuclearUltrapower.CuntzAveraging.instNormedSpaceComplexTarget_1`, `OAI.NuclearUltrapower.CuntzAveraging.jointDefect`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`NuclearUltrapower_CuntzIntertwining`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/CuntzIntertwining.lean), [`NuclearUltrapower_CuntzNuclearity`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/CuntzNuclearity.lean).
--
--   **Imports.** It imports the published bundle `Def_NuclearUltrapower`; the bundles `OAIQ019N039` and `OAIQ019N045` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ019N048`; the statements `OAI.NuclearUltrapower.CuntzAveraging.defect_adjoint_bound`, `OAI.NuclearUltrapower.CuntzAveraging.defect_generator_bound`, `OAI.NuclearUltrapower.CuntzAveraging.defect_polynomial_tendsto`, `OAI.NuclearUltrapower.CuntzAveraging.defect_tendsto` and `OAI.NuclearUltrapower.CuntzAveraging.jointDefect_tendsto`; the proofs of `OAI.NuclearUltrapower.CuntzAveraging.defect_polynomial_tendsto` and `OAI.NuclearUltrapower.CuntzAveraging.defect_tendsto`.
-- source:
--   OpenAI, An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 292; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/NuclearUltrapower.lean; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_NuclearUltrapower
import Definitions.Def_OAIQ019N039
import Definitions.Def_OAIQ019N045

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_CuntzIntertwining
attribute [-instance] _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.VariableUltra.instCStarAlgebraAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instCompleteSpaceAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedAddCommGroupAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedAlgebraComplexAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedRingAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instStarAlgebra _root_.OAI.NuclearUltrapower.lp_finiteDimensional _root_.OAI.NuclearUltrapower.strongDualInner _root_.OAI.NuclearUltrapower.tensorBoundedSMul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Filter
open scoped TensorProduct InnerProductSpace Topology
namespace NuclearUltrapower.CuntzAveraging
open CuntzModel CuntzWords CuntzUniversal

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (R : Algebra →⋆ₙₐ[ℂ] (H →L[ℂ] H))

attribute [local instance] OAI.NuclearUltrapower.CuntzAveraging.instIsBoundedSMulComplexTensorProductSubtypePreLpIndexMemAddSubgroupSpace
local instance instNormedSpaceComplexTarget : NormedSpace ℂ (Target H) := inferInstance

def amplified : Algebra →⋆ₐ[ℂ] (Target H →L[ℂ] Target H) :=
  tensorLeftHom.comp concrete

@[simp] theorem amplified_generator (i : Fin 2) : amplified (H := H) (generator i) = left i := by
  change tensorLeftHom (concrete (generator i)) = _
  rw [concrete,modelMap_generator]
  rfl

abbrev defect (n : ℕ) : Algebra →ₗ[ℂ] (H →L[ℂ] Target H) :=
  intertwiningDefect R amplified.toNonUnitalStarAlgHom (averaged R n)

@[simp] theorem averaged_support (n : ℕ) : (averaged R n).comp (R 1) = averaged R n := by
  ext x
  change weight n • (rowSum R ((n+1)^2) (R 1 x)) =
    weight n • (rowSum R ((n+1)^2) x)
  congr 1
  simp only [rowSum_apply]
  apply Finset.sum_congr rfl
  intro k _
  exact congrArg (fun T : H →L[ℂ] Target H => T x) (row_support R k)

@[simp] theorem defect_one (n : ℕ) : defect R n 1 = 0 := by
  change (averaged R n).comp (R 1) - (amplified 1).comp (averaged R n) = 0
  rw [averaged_support,map_one]
  change averaged R n - (ContinuousLinearMap.id ℂ _).comp (averaged R n) = 0
  rw [ContinuousLinearMap.id_comp,sub_self]

end NuclearUltrapower.CuntzAveraging
end
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_CuntzNuclearity
attribute [-instance] _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.VariableUltra.instCStarAlgebraAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instCompleteSpaceAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedAddCommGroupAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedAlgebraComplexAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedRingAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instStarAlgebra _root_.OAI.NuclearUltrapower.lp_finiteDimensional _root_.OAI.NuclearUltrapower.strongDualInner _root_.OAI.NuclearUltrapower.tensorBoundedSMul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Filter
open scoped Topology TensorProduct
namespace NuclearUltrapower.CuntzAveraging
open CuntzUniversal
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (R : Algebra →⋆ₙₐ[ℂ] (H →L[ℂ] H))

local instance instIsBoundedSMulComplexTensorProductSubtypePreLpIndexMemAddSubgroupSpace_1_rfdd818_1 : IsBoundedSMul ℂ (CuntzModel.Space ⊗[ℂ] H) := NormedSpace.toIsBoundedSMul
local instance instNormedSpaceComplexTarget_1 : NormedSpace ℂ (Target H) := inferInstance

end NuclearUltrapower.CuntzAveraging
end
end

section

noncomputable section
open Filter
open scoped TensorProduct Topology
namespace NuclearUltrapower
namespace CuntzAveraging
open CuntzUniversal CuntzModel

variable {C : Type} [NonUnitalCStarAlgebra C] (H : ComplexHilbert.{0})
  (R : Algebra →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (S : C →⋆ₙₐ[ℂ] (H →L[ℂ] H))

local instance instIsBoundedSMulComplexTensorProductSubtypePreLpIndexMemAddSubgroupSpaceCarrier : IsBoundedSMul ℂ (Space ⊗[ℂ] H) := NormedSpace.toIsBoundedSMul
local instance instNormedSpaceComplexTargetCarrier : NormedSpace ℂ (Target H) := inferInstance

/-- The concrete spatial representation on the completed Hilbert tensor product. -/
def completedEval : Algebra ⊗[ℂ] C →ₗ[ℂ] (Target H →L[ℂ] Target H) :=
  commutingEval ⟨Target H⟩
    (tensorLeftRep (H := ⟨Space⟩) (K := H) concrete.toNonUnitalStarAlgHom)
    (tensorRightRep (H := ⟨Space⟩) (K := H) S)

@[simp] theorem completedEval_tmul (a : Algebra) (c : C) :
    completedEval H S (a ⊗ₜ[ℂ] c) = amplified a * right (S c) := rfl

def jointDefect (n : ℕ) (x : Algebra ⊗[ℂ] C) : H →L[ℂ] Target H :=
  (averaged R n).comp (commutingEval H R S x) - (completedEval H S x).comp (averaged R n)

end CuntzAveraging

end NuclearUltrapower
end
end

end OAI
end


