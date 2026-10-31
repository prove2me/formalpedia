-- Prove2me | Definitions.Def_OAIQ023F022
-- name    : OAIQ023F022
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T18:23:51.751981+00:00
-- url     : https://prove2.me/theorems/9094fc09-c8d3-45a8-969c-ffada1ff63d5
-- title:
--   Definitions bundle OAIQ023F022 of the split of OpenAI, An algebra of infinite little finitistic dimension (result family 198)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.LittleFinitistic.Main.exists_counterexample`, carved from OpenAI's openai/math development (OpenAI, *An algebra of infinite little finitistic dimension (result family 198)*, OpenAI Math Release, September 23, 2026, result family 198, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 20 declarations of OpenAI's Lean: 8 definitions, 2 instances and 10 theorems. The definitions and types are `OAI.LittleFinitistic.BimoduleTotal.evaluationAtIndex`, `OAI.LittleFinitistic.BimoduleTotal.evaluationTermIso`, `OAI.LittleFinitistic.BimoduleTotal.shiftColumnIso`, `OAI.LittleFinitistic.BimoduleTotal.shiftReindex`, `OAI.LittleFinitistic.BimoduleTotal.shiftTermIso`, `OAI.LittleFinitistic.BimoduleTotal.underlyingComparison`, `OAI.LittleFinitistic.BimoduleTotal.underlyingIso`, `OAI.LittleFinitistic.BimoduleTotal.underlyingTerm`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`Finitistic_Bimodule_BimoduleAugmentationEpi`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/Finitistic/Bimodule/BimoduleAugmentationEpi.lean), [`Finitistic_Bimodule_BimoduleShiftCoherence`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/Finitistic/Bimodule/BimoduleShiftCoherence.lean), [`Finitistic_Bimodule_BimoduleShiftColumns`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/Finitistic/Bimodule/BimoduleShiftColumns.lean), [`Finitistic_Bimodule_BimoduleShiftTotal`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/Finitistic/Bimodule/BimoduleShiftTotal.lean), [`Finitistic_Bimodule_BimoduleSingleTerms`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/Finitistic/Bimodule/BimoduleSingleTerms.lean), [`Finitistic_Bimodule_BimoduleTotalFunctor`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/Finitistic/Bimodule/BimoduleTotalFunctor.lean), [`Finitistic_Bimodule_BimoduleTotalUnderlying`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/Finitistic/Bimodule/BimoduleTotalUnderlying.lean), [`Finitistic_Rectification_AdjacentArrowSum`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/Finitistic/Rectification/AdjacentArrowSum.lean), [`Finitistic_Rectification_ColumnFinite`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/Finitistic/Rectification/ColumnFinite.lean), [`Finitistic_Rectification_ColumnProperties`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/Finitistic/Rectification/ColumnProperties.lean), [`Finitistic_Rectification_TotalFinite`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/Finitistic/Rectification/TotalFinite.lean).
--
--   **Imports.** It imports the bundles `OAIQ023F039`, `OAIQ023F018` and `OAIQ023F019` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ023F025` and `OAIQ023F026`.
-- source:
--   OpenAI, An algebra of infinite little finitistic dimension (result family 198), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 198; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-algebra-of-infinite-little-finitistic-dimension-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ023F039
import Definitions.Def_OAIQ023F018
import Definitions.Def_OAIQ023F019

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_ColumnProperties
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.ExternalTensor.Section4.SourceFiltration.inclusion2_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroCone_inclusion_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroTermSubsingleton _root_.OAI.ExternalTensor.Section4.forgetK_additive _root_.OAI.LittleFinitistic.BalancedVertexFunctor.additive _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.additive _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.finite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.scalarTower _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.columnFunctor_additive _root_.OAI.LittleFinitistic.BimoduleTotal.inputFunctor_additive _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct ModuleCat.Algebra
noncomputable section
namespace ExternalTensor.Section4
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B]
attribute [local instance] ExternalTensor.bimodule ExternalTensor.rightModule

variable {k B}
variable {A J R : Type} [Fintype A] [Fintype J] [Fintype R]
variable (s : Quadratic k B (A := A) (J := J) (R := R))
variable (D₀ D₁ D₂ : RightComplex B)
variable (f : A → (D₀ ⟶ D₁)) (g : J → (D₁ ⟶ D₂))

/-- Exactly the three right-projectivity inputs to RectificationTotal.total_projective_after. -/
theorem columns_right_projective
    (h₀ : ∀ n, Module.Projective Bᵐᵒᵖ (D₀.X n))
    (h₁ : ∀ n, Module.Projective Bᵐᵒᵖ (D₁.X n))
    (h₂ : ∀ n, Module.Projective Bᵐᵒᵖ (D₂.X n)) (n : ℤ) :
    Projective ((forgetRight k B).obj ((L0Prime s D₀ D₁ D₂ f g).X n)) ∧
    Projective ((forgetRight k B).obj ((L1Prime s D₀ D₁ D₂ f g).X n)) ∧
    Projective ((forgetRight k B).obj ((L2Prime s D₀ D₁ D₂ f g).X n)) := by
  let := h₀ n
  let := h₁ n
  let := h₂ n
  refine ⟨?_, ?_, ?_⟩
  · apply biprod_right_projective
    · exact column_right_projective k B s.e₀ (D₀.X n)
    · apply biprod_right_projective
      · exact column_right_projective k B s.e₁ (D₁.X n)
      · exact column_right_projective k B s.e₂ (D₂.X n)
  · apply biprod_right_projective
    · apply sum_right_projective
      intro a
      exact column_right_projective k B s.e₁ (D₀.X n)
    · apply sum_right_projective
      intro b
      exact column_right_projective k B s.e₂ (D₁.X n)
  · apply sum_right_projective
    intro r
    exact column_right_projective k B s.e₂ (D₀.X n)

end ExternalTensor.Section4

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_AdjacentArrowSum
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.ExternalTensor.Section4.SourceFiltration.inclusion2_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroCone_inclusion_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroTermSubsingleton _root_.OAI.ExternalTensor.Section4.forgetK_additive _root_.OAI.ExternalTensor.Section4.forgetRight_additive _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.LittleFinitistic.BalancedVertexFunctor.additive _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.additive _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.finite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.scalarTower _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.columnFunctor_additive _root_.OAI.LittleFinitistic.BimoduleTotal.inputFunctor_additive _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.BimoduleVertex.linear _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticPresentation.instFiniteAuxiliaryEquation _root_.OAI.LittleFinitistic.QuadraticPresentation.instFiniteAuxiliaryLetter _root_.OAI.LittleFinitistic.QuadraticPresentation.step_finite _root_.OAI.LittleFinitistic.QuadraticPresentation.word_finite _root_.OAI.LittleFinitistic.TensorComplex.linear _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated _root_.OAI.LittleFinitistic.cyclicRing_finiteInst
attribute [-simp] _root_.OAI.ExternalTensor.Section4.ArrowVertex.arrow_id _root_.OAI.ExternalTensor.Section4.ArrowVertex.arrow_original _root_.OAI.ExternalTensor.Section4.ArrowVertex.iota_original _root_.OAI.ExternalTensor.Section4.ArrowVertex.left_mul _root_.OAI.ExternalTensor.Section4.ArrowVertex.map_left _root_.OAI.ExternalTensor.Section4.ArrowVertex.mem_space _root_.OAI.LittleFinitistic.BalancedVertexImage.equiv_apply_val _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.smul_mk _root_.OAI.LittleFinitistic.BimoduleTotal.leftTotalMap_apply _root_.OAI.LittleFinitistic.BimoduleTotal.leftTotalMap_comp _root_.OAI.LittleFinitistic.BimoduleTotal.leftTotalMap_id _root_.OAI.LittleFinitistic.BimoduleTotal.tensorAcross_comp _root_.OAI.LittleFinitistic.BimoduleTotal.tensorAcross_id _root_.OAI.LittleFinitistic.BimoduleTotal.tensorAcross_mk _root_.OAI.LittleFinitistic.BimoduleTotal.tensorAcross_zero_left _root_.OAI.LittleFinitistic.BimoduleTotal.tensorAcross_zero_right _root_.OAI.LittleFinitistic.BimoduleTotal.termMap_comp _root_.OAI.LittleFinitistic.BimoduleTotal.termMap_id _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.arrowAction_basis _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.rawPathAction_tmul _root_.OAI.LittleFinitistic.RelationBasisAction.pathValue_basis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ModuleCat.Algebra
namespace LittleFinitistic.AdjacentArrowSum
universe u
variable {k V W U : Type u} [Field k] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W] [AddCommGroup U] [Module k U]
variable (μ : W →ₗ[k] V →ₗ[k] U)
variable (D : CochainComplex (ModuleCat.{u} (ThreeVertexAlgebra μ)ᵐᵒᵖ) ℤ)
local notation "T" => ThreeVertexAlgebra μ

attribute [local instance] OAI.LittleFinitistic.AdjacentArrowSum.instHasFiniteBiproductsCochainComplexModuleCatMulOppositeThreeVertexAlgebraInt
/-- An actual adjacent path family becomes the full arrow basis under corner coordinates. -/
theorem desc_isIso (v i : Fin 3) (d : ℕ)
    (ξ : CornerSpaces.corner μ v i ≃ₗ[k] QuadraticEncoding.Arrows k d)
    (a : Fin (d+1) → ThreeVertexAlgebra μ)
    (ha : ∀ j, a j * ThreeVertexAlgebra.vertex μ i = a j)
    (hc : ∀ j c, ξ (CornerColumnPaths.cornerMap μ v i v (a j) (ha j)
      ((CornerSpaces.diagonalEquiv μ v).symm c)) = c • QuadraticEncoding.basis j) :
    IsIso (biproduct.desc (fun j => (vertexComplex μ v).map
      (ExternalTensor.Section4.path k T (ThreeVertexAlgebra.vertex μ i)
        (ThreeVertexAlgebra.vertex μ v) (a j) (ha j) D))) := by
  let F := TensorComplex.tensorFunctor (k := k) D
  apply TensorArrowSum.desc_isIso_of_coordinates k d F _ _
    (fun _ => sourceIso μ D v) (targetIso μ D v i d ξ)
  intro j
  have hm : ModuleCat.ofHom (CornerSpaces.diagonalEquiv μ v).toLinearMap ≫
      TensorArrowSum.insertion k d j =
      ModuleCat.ofHom (CornerColumnPaths.cornerMap μ v i v (a j) (ha j)) ≫
        ModuleCat.ofHom ξ.toLinearMap := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (TensorArrowSum.insertion k d j).hom ((CornerSpaces.diagonalEquiv μ v) x) =
      ξ (CornerColumnPaths.cornerMap μ v i v (a j) (ha j) x)
    rw [TensorArrowSum.insertion_apply]
    simpa only [LinearEquiv.symm_apply_apply]
      using (hc j ((CornerSpaces.diagonalEquiv μ v) x)).symm
  have hF := congrArg F.map hm
  simp only [Functor.map_comp] at hF
  apply (cancel_epi (CornerColumnComplex.complexIso μ v v D).hom).1
  calc
    _ = F.map (ModuleCat.ofHom (CornerSpaces.diagonalEquiv μ v).toLinearMap) ≫
        F.map (TensorArrowSum.insertion k d j) := by
      change (CornerColumnComplex.complexIso μ v v D).hom ≫
        ((CornerColumnComplex.complexIso μ v v D).inv ≫
          F.map (ModuleCat.ofHom (CornerSpaces.diagonalEquiv μ v).toLinearMap)) ≫
        F.map (TensorArrowSum.insertion k d j) = _
      erw [Category.assoc]
      exact (CornerColumnComplex.complexIso μ v v D).hom_inv_id_assoc _
    _ = F.map (ModuleCat.ofHom (CornerColumnPaths.cornerMap μ v i v (a j) (ha j))) ≫
        F.map (ModuleCat.ofHom ξ.toLinearMap) := hF
    _ = (F.map (ModuleCat.ofHom
          (CornerColumnPaths.cornerMap μ v i v (a j) (ha j))) ≫
        (CornerColumnComplex.complexIso μ v i D).hom) ≫
          (targetIso μ D v i d ξ).hom := by
      simp [targetIso,F,TensorComplex.tensorFunctor]
      show _ = (_ ≫ (CornerColumnComplex.complexIso μ v i D).hom) ≫
        ((CornerColumnComplex.complexIso μ v i D).inv ≫ _)
      rw [Category.assoc]
      erw [Iso.hom_inv_id_assoc]
      rfl
    _ = _ := by
      erw [CornerColumnPaths.path_naturality]
      exact Category.assoc _ _ _
end LittleFinitistic.AdjacentArrowSum

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bimodule_BimoduleTotalFunctor
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.ExternalTensor.Section4.SourceFiltration.inclusion2_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroCone_inclusion_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroTermSubsingleton _root_.OAI.ExternalTensor.Section4.forgetK_additive _root_.OAI.LittleFinitistic.BalancedTensor.tensorFinite _root_.OAI.LittleFinitistic.BalancedVertexFunctor.additive _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.columnFunctor_additive _root_.OAI.LittleFinitistic.BimoduleTotal.inputFunctor_additive _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.OrdinarySimulation.shifted_right_projective _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.PDBarQuotient.leftTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.ArrowVertex.arrow_id _root_.OAI.ExternalTensor.Section4.ArrowVertex.arrow_original _root_.OAI.ExternalTensor.Section4.ArrowVertex.iota_original _root_.OAI.ExternalTensor.Section4.ArrowVertex.left_mul _root_.OAI.ExternalTensor.Section4.ArrowVertex.map_left _root_.OAI.ExternalTensor.Section4.ArrowVertex.mem_space _root_.OAI.LittleFinitistic.BalancedAssociativity.forwardAt_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.forward_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.inverseAt_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.inverse_mk _root_.OAI.LittleFinitistic.BalancedTensor.FreeLeft.evaluation_single _root_.OAI.LittleFinitistic.BalancedTensor.FreeLeft.insertion_single _root_.OAI.LittleFinitistic.BalancedTensor.bimoduleAction_tmul_mk _root_.OAI.LittleFinitistic.BalancedTensor.leftAction_mk _root_.OAI.LittleFinitistic.BalancedTensor.mapRight_mk _root_.OAI.LittleFinitistic.BalancedTensor.rightAction_mk _root_.OAI.LittleFinitistic.BalancedTensor.tensorFunctorEquiv_mk _root_.OAI.LittleFinitistic.BalancedVertexImage.equiv_apply_val _root_.OAI.LittleFinitistic.BimoduleTotal.leftTotalMap_apply _root_.OAI.LittleFinitistic.BimoduleTotal.leftTotalMap_comp _root_.OAI.LittleFinitistic.BimoduleTotal.leftTotalMap_id _root_.OAI.LittleFinitistic.BimoduleTotal.tensorAcross_comp _root_.OAI.LittleFinitistic.BimoduleTotal.tensorAcross_id _root_.OAI.LittleFinitistic.BimoduleTotal.tensorAcross_mk _root_.OAI.LittleFinitistic.BimoduleTotal.tensorAcross_zero_left _root_.OAI.LittleFinitistic.BimoduleTotal.tensorAcross_zero_right _root_.OAI.LittleFinitistic.BimoduleTotal.termMap_comp _root_.OAI.LittleFinitistic.BimoduleTotal.termMap_id _root_.OAI.LittleFinitistic.OrdinarySimulation.BlockTensor.firstTotalEquiv_apply _root_.OAI.LittleFinitistic.PDBarQuotient.forward_mk _root_.OAI.LittleFinitistic.PDBarQuotient.inverse_quotient _root_.OAI.LittleFinitistic.PDResidueAssociativity.inner_mk _root_.OAI.LittleFinitistic.PDResidueAssociativity.inverse_mk _root_.OAI.LittleFinitistic.PDTensor.mapRight_mk _root_.OAI.LittleFinitistic.PDTensor.residueEval_mk _root_.OAI.LittleFinitistic.PDTensor.residueInverse_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.BimoduleTotal
open ExternalTensor.Section4
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B]
variable (P : BiComplex k B) {l : ℕ} (p : Fin l → ℤ) (hp : StrictMono p)
variable (Z : CochainComplex (ModuleCat.{u} B) ℤ)

set_option allowUnsafeReducibility true in
attribute [local reducible] CategoryTheory.Functor.mapHomologicalComplex

variable {Z} {Z' Z'' : CochainComplex (ModuleCat.{u} B) ℤ}

instance additive : (functor k B P p hp).Additive where
  map_add {Z Z'} {f g} := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext i
    change ((ComplexTensor.finiteTotalMap k B (right k B P) p hp (f+g)).f n).hom x i =
      ((ComplexTensor.finiteTotalMap k B (right k B P) p hp f).f n).hom x i +
      ((ComplexTensor.finiteTotalMap k B (right k B P) p hp g).f n).hom x i
    erw [ComplexTensor.finiteTotalMap_apply, ComplexTensor.finiteTotalMap_apply, ComplexTensor.finiteTotalMap_apply]
    induction x i using BalancedTensor.induction_on with
    | hz =>
      simp
      exact (zero_add _).symm
    | ht a b => exact (BalancedTensor.mk k B _ _ a).map_add _ _
    | ha a b ha hb => simp_all [map_add]; abel
end LittleFinitistic.BimoduleTotal

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bimodule_BimoduleTotalUnderlying
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.ExternalTensor.Section4.SourceFiltration.inclusion2_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroCone_inclusion_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroTermSubsingleton _root_.OAI.ExternalTensor.Section4.forgetK_additive _root_.OAI.LittleFinitistic.BalancedVertexFunctor.additive _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.columnFunctor_additive _root_.OAI.LittleFinitistic.BimoduleTotal.inputFunctor_additive _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.BimoduleTotal
open ExternalTensor.Section4
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B]
variable (P : BiComplex k B) {l : ℕ} (p : Fin l → ℤ) (hp : StrictMono p)

variable (Z : CochainComplex (ModuleCat.{u} B) ℤ)

def underlyingTerm (n : ℤ) :
    ((forget k B).obj (total k B P p hp Z)).X n ≃ₗ[k]
      (vectorTotal k B P p hp Z).X n where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c x := by
    funext i
    exact BimoduleBalancedTensor.algebraMap_smul k B (P.X (p i))
      (ComplexTensor.leftTerm k B Z (n + -(p i))) c (x i)

/-- Forgetting the full left action recovers the frozen signed tensor total with its actual differential. -/
def underlyingIso : (forget k B).obj (total k B P p hp Z) ≅ vectorTotal k B P p hp Z :=
  HomologicalComplex.Hom.isoOfComponents (fun n => (underlyingTerm k B P p hp Z n).toModuleIso)
    (by intros n m h; apply ModuleCat.hom_ext; apply LinearMap.ext; intro x; rfl)

/-- The comparison preserves the original maps in the arbitrary input complex. -/
def underlyingComparison :
    functor k B P p hp ⋙ forget k B ≅ ComplexTensor.finiteTotalFunctor k B (right k B P) p hp :=
  NatIso.ofComponents (underlyingIso k B P p hp) (by
    intros Z Z' f
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl)

end LittleFinitistic.BimoduleTotal

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bimodule_BimoduleSingleTerms
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.ExternalTensor.Section4.SourceFiltration.inclusion2_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroCone_inclusion_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroTermSubsingleton _root_.OAI.ExternalTensor.Section4.forgetK_additive _root_.OAI.LittleFinitistic.BalancedTensor.tensorFinite _root_.OAI.LittleFinitistic.BalancedVertexFunctor.additive _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.PDBarQuotient.leftTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.BimoduleTotal
open ExternalTensor.Section4
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B]
variable (P : BiComplex k B) (N : ModuleCat.{u} B)

variable {k B}

variable (k B) {l : ℕ} (p : Fin l → ℤ) (hp : StrictMono p)

def evaluationAtIndex (i : Fin l) :
    ModuleCat.of B (TotalTerm k B P p (singleInput B N) (p i)) ≅
      (moduleEvaluation k B P N).X (p i) :=
  (piSingleEquiv (fun j => Term k B P (singleInput B N) (p j) (p i + -(p j))) i
    (fun j h => ModuleCat.subsingleton_of_isZero
      (singleTerm_isZero k B P N (p i) (p j) (fun hji => h (hp.injective hji))))).toModuleIso ≪≫
    singleTermIso k B P N (p i) (p i) rfl

/-- The finite total and the native module evaluation agree in every degree, provided every nonzero P-degree is included. -/
def evaluationTermIso
    (hP : ∀ n, (∀ i, p i ≠ n) → IsZero (P.X n)) (n : ℤ) :
    ModuleCat.of B (TotalTerm k B P p (singleInput B N) n) ≅ (moduleEvaluation k B P N).X n := by
  classical
  by_cases h : ∃ i, p i=n
  · let i := h.choose
    have hi : p i=n := h.choose_spec
    exact eqToIso (congrArg (fun n => ModuleCat.of B (TotalTerm k B P p (singleInput B N) n)) hi.symm) ≪≫
      evaluationAtIndex k B P N p hp i ≪≫ (moduleEvaluation k B P N).XIsoOfEq hi
  · have hn : ∀ i, p i ≠ n := by simpa only [not_exists] using h
    exact (totalSingle_isZero k B P N p n hn).iso
      ((BimoduleBalancedTensor.functor k B (BalancedTensor.ScalarLeftModule k B N)).map_isZero (hP n hn))
end LittleFinitistic.BimoduleTotal

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bimodule_BimoduleAugmentationEpi
attribute [-instance] _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.ExternalTensor.Section4.SourceFiltration.inclusion2_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroCone_inclusion_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroTermSubsingleton _root_.OAI.ExternalTensor.Section4.forgetK_additive _root_.OAI.LittleFinitistic.BalancedVertexFunctor.additive _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.ArrowVertex.arrow_id _root_.OAI.ExternalTensor.Section4.ArrowVertex.arrow_original _root_.OAI.ExternalTensor.Section4.ArrowVertex.iota_original _root_.OAI.ExternalTensor.Section4.ArrowVertex.left_mul _root_.OAI.ExternalTensor.Section4.ArrowVertex.map_left _root_.OAI.ExternalTensor.Section4.ArrowVertex.mem_space _root_.OAI.LittleFinitistic.BalancedVertexImage.equiv_apply_val
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace LittleFinitistic.BimoduleTotal
open ExternalTensor.Section4
universe u
variable {k B : Type u} [Field k] [Ring B] [Algebra k B]
variable {P : BiComplex k B} {X : ModuleCat.{u} (Enveloping k B)}
variable (res : AugmentedProjective k B P X)

/-- A quasi-isomorphism onto a stalk is surjective in each degree; this is
proved from its homology map, not imposed on the resolution data. -/
theorem augmentation_epi_f (n : ℤ) : Epi (res.augmentation.f n) := by
  let T := bimoduleStalk k B X
  let := res.quasiIso
  have : IsIso (T.homologyπ n) := T.isIso_homologyπ (n-1) n (by simp) (by simp [T,bimoduleStalk])
  have : IsIso (T.iCycles n) := T.isIso_iCycles n (n+1) (by simp) (by simp [T,bimoduleStalk])
  have heq : cyclesMap res.augmentation n = P.homologyπ n ≫
      homologyMap res.augmentation n ≫ inv (T.homologyπ n) := by
    rw [← Category.assoc,homologyπ_naturality,Category.assoc,IsIso.hom_inv_id,Category.comp_id]
  have : Epi (cyclesMap res.augmentation n) := by
    rw [heq]
    infer_instance
  have : Epi (P.iCycles n ≫ res.augmentation.f n) := by
    rw [← cyclesMap_i]
    infer_instance
  exact epi_of_epi (P.iCycles n) (res.augmentation.f n)
end LittleFinitistic.BimoduleTotal

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bimodule_BimoduleShiftColumns
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.ExternalTensor.Section4.SourceFiltration.inclusion2_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroCone_inclusion_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroTermSubsingleton _root_.OAI.ExternalTensor.Section4.forgetK_additive _root_.OAI.LittleFinitistic.BalancedTensor.tensorFinite _root_.OAI.LittleFinitistic.BalancedVertexFunctor.additive _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.PDBarQuotient.leftTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.BimoduleTotal
open ExternalTensor.Section4
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B]
variable (P : BiComplex k B) (Z : CochainComplex (ModuleCat.{u} B) ℤ)

/-- The tensor shift has the Koszul sign (-1)^(s*p) on its pth column. -/
def shiftColumnIso (s p : ℤ) :
    (columnFunctor k B P p).obj (Z⟦s⟧) ≅ ((columnFunctor k B P p).obj Z)⟦s⟧ :=
  OrdinarySimulation.integerUnitIso _ (s*p).negOnePow ≪≫
    (shiftFunctor _ (-p)).mapIso
      (((inputFunctor k B (P.X p)).mapHomologicalComplex (.up ℤ)).commShiftIso s |>.app Z) ≪≫
    (shiftFunctorComm (CochainComplex (ModuleCat.{u} B) ℤ) s (-p)).app
      (((inputFunctor k B (P.X p)).mapHomologicalComplex (.up ℤ)).obj Z)

def shiftReindex (s a n : ℤ) :
    ((columnFunctor k B P a).obj (Z⟦s⟧)).X n ≅
      (((columnFunctor k B P a).obj Z)⟦s⟧).X n :=
  eqToIso (congrArg (fun q => ModuleCat.of B (Term k B P Z a q))
    (show n + -a + s = n + s + -a by omega))

theorem shiftColumn_hom_f (s a n : ℤ) :
    ((shiftColumnIso k B P Z s a).hom).f n =
      (s*a).negOnePow • (shiftReindex k B P Z s a n).hom := by
  simp only [shiftColumnIso, Iso.trans_hom, HomologicalComplex.comp_f]
  change ((s*a).negOnePow • 𝟙 (((columnFunctor k B P a).obj (Z⟦s⟧)).X n)) ≫ _ = _
  rw [Linear.units_smul_comp, Category.id_comp]
  congr 1
  simp only [Functor.mapIso_hom, Iso.app_hom, CochainComplex.shiftFunctor_map_f',
    Functor.mapHomologicalComplex_commShiftIso_hom_app_f,
    CochainComplex.shiftFunctorComm_hom_app_f]
  rfl
end LittleFinitistic.BimoduleTotal

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bimodule_BimoduleShiftTotal
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.SourceFiltration.inclusion2_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroCone_inclusion_isIso _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.ArrowVertex.arrow_id _root_.OAI.ExternalTensor.Section4.ArrowVertex.arrow_original _root_.OAI.ExternalTensor.Section4.ArrowVertex.iota_original _root_.OAI.LittleFinitistic.BimoduleTotal.leftTotalMap_apply _root_.OAI.LittleFinitistic.BimoduleTotal.leftTotalMap_comp _root_.OAI.LittleFinitistic.BimoduleTotal.leftTotalMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.BimoduleTotal
open ExternalTensor.Section4
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B]
variable (P : BiComplex k B) {l : ℕ} (p : Fin l → ℤ) (hp : StrictMono p)
variable (Z : CochainComplex (ModuleCat.{u} B) ℤ)

def shiftTermIso (s n : ℤ) :
    (total k B P p hp (Z⟦s⟧)).X n ≅ ((total k B P p hp Z)⟦s⟧).X n :=
  (LinearEquiv.piCongrRight (fun i : Fin l =>
    (HomologicalComplex.Hom.isoApp (shiftColumnIso k B P Z s (p i)) n).toLinearEquiv)).toModuleIso

@[simp] theorem shiftTerm_hom_apply (s n : ℤ)
    (x : TotalTerm k B P p (Z⟦s⟧) n) (i : Fin l) :
    (shiftTermIso k B P p hp Z s n).hom.hom x i =
      (((shiftColumnIso k B P Z s (p i)).hom).f n).hom (x i) := rfl

end LittleFinitistic.BimoduleTotal

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bimodule_BimoduleShiftCoherence
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.ExternalTensor.Section4.SourceFiltration.inclusion2_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroCone_inclusion_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroTermSubsingleton _root_.OAI.ExternalTensor.Section4.forgetK_additive _root_.OAI.LittleFinitistic.BalancedTensor.tensorFinite _root_.OAI.LittleFinitistic.BalancedVertexFunctor.additive _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.OrdinarySimulation.shifted_right_projective _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.PDBarQuotient.leftTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.ArrowVertex.arrow_id _root_.OAI.ExternalTensor.Section4.ArrowVertex.arrow_original _root_.OAI.ExternalTensor.Section4.ArrowVertex.iota_original _root_.OAI.ExternalTensor.Section4.ArrowVertex.left_mul _root_.OAI.ExternalTensor.Section4.ArrowVertex.map_left _root_.OAI.ExternalTensor.Section4.ArrowVertex.mem_space _root_.OAI.LittleFinitistic.BalancedAssociativity.forwardAt_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.forward_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.inverseAt_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.inverse_mk _root_.OAI.LittleFinitistic.BalancedTensor.FreeLeft.evaluation_single _root_.OAI.LittleFinitistic.BalancedTensor.FreeLeft.insertion_single _root_.OAI.LittleFinitistic.BalancedTensor.bimoduleAction_tmul_mk _root_.OAI.LittleFinitistic.BalancedTensor.leftAction_mk _root_.OAI.LittleFinitistic.BalancedTensor.mapRight_mk _root_.OAI.LittleFinitistic.BalancedTensor.rightAction_mk _root_.OAI.LittleFinitistic.BalancedTensor.tensorFunctorEquiv_mk _root_.OAI.LittleFinitistic.BalancedVertexImage.equiv_apply_val _root_.OAI.LittleFinitistic.BimoduleTotal.leftTotalMap_apply _root_.OAI.LittleFinitistic.BimoduleTotal.leftTotalMap_comp _root_.OAI.LittleFinitistic.BimoduleTotal.leftTotalMap_id _root_.OAI.LittleFinitistic.BimoduleTotal.tensorAcross_comp _root_.OAI.LittleFinitistic.BimoduleTotal.tensorAcross_id _root_.OAI.LittleFinitistic.BimoduleTotal.tensorAcross_mk _root_.OAI.LittleFinitistic.BimoduleTotal.tensorAcross_zero_left _root_.OAI.LittleFinitistic.BimoduleTotal.tensorAcross_zero_right _root_.OAI.LittleFinitistic.OrdinarySimulation.BlockTensor.firstTotalEquiv_apply _root_.OAI.LittleFinitistic.PDBarQuotient.forward_mk _root_.OAI.LittleFinitistic.PDBarQuotient.inverse_quotient _root_.OAI.LittleFinitistic.PDResidueAssociativity.inner_mk _root_.OAI.LittleFinitistic.PDResidueAssociativity.inverse_mk _root_.OAI.LittleFinitistic.PDTensor.mapRight_mk _root_.OAI.LittleFinitistic.PDTensor.residueEval_mk _root_.OAI.LittleFinitistic.PDTensor.residueInverse_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.BimoduleTotal
open ExternalTensor.Section4
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B]

attribute [local instance] OAI.LittleFinitistic.BimoduleTotal.signedShift
instance columnCommShift (P : BiComplex k B) (a : ℤ) :
    (columnFunctor k B P a).CommShift ℤ := by unfold columnFunctor; infer_instance

variable (P : BiComplex k B)

theorem column_commShiftIso_eq (Z : CochainComplex (ModuleCat.{u} B) ℤ) (s a : ℤ) :
    ((columnFunctor k B P a).commShiftIso s).app Z = shiftColumnIso k B P Z s a := by
  apply Iso.ext
  apply HomologicalComplex.Hom.ext
  funext n
  rw [shiftColumn_hom_f]
  simp only [Iso.app_hom,columnFunctor,Functor.commShiftIso_comp_hom_app,
    HomologicalComplex.comp_f,CochainComplex.shiftFunctor_map_f',
    Functor.mapHomologicalComplex_commShiftIso_hom_app_f]
  change ((signedShiftIso (ModuleCat.{u} B) (-a) s).hom.app
    (((inputFunctor k B (P.X a)).mapHomologicalComplex (.up ℤ)).obj Z)).f n = _
  rw [signedShiftIso_hom_f]
  simp [shiftReindex,HomologicalComplex.XIsoOfEq,mul_comm]
  rfl

variable {Z Z' : CochainComplex (ModuleCat.{u} B) ℤ}

theorem fullColumn_map (f : Z ⟶ Z') (a n : ℤ) (x : Term k B P Z a (n + -a)) :
    (((columnFunctor k B P a).map f).f n).hom x =
      ComplexTensor.inputMap k B (right k B P) f a (n + -a) x := by
  induction x using BalancedTensor.induction_on with
  | hz => exact (map_zero _).trans (map_zero _).symm
  | ht m y => rfl
  | ha x y hx hy =>
    exact (map_add _ _ _).trans ((congrArg₂ (· + ·) hx hy).trans (map_add _ _ _).symm)

end LittleFinitistic.BimoduleTotal

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_ColumnFinite
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.ExternalTensor.Section4.SourceFiltration.inclusion2_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroCone_inclusion_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroTermSubsingleton _root_.OAI.LittleFinitistic.BalancedTensor.scalarModuleTower _root_.OAI.LittleFinitistic.BalancedVertexFunctor.additive _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.additive _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.finite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.scalarTower _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleCoefficients.towerRight _root_.OAI.LittleFinitistic.BimoduleTotal.additive _root_.OAI.LittleFinitistic.BimoduleTotal.columnCommShift _root_.OAI.LittleFinitistic.BimoduleTotal.columnFunctor_additive _root_.OAI.LittleFinitistic.BimoduleTotal.inputFunctor_additive _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.DirectedBound.DirectedSystem.cover_addCommGroup _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TensorComplex.scalarTower _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct ModuleCat.Algebra
noncomputable section
namespace ExternalTensor.Section4
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B]
attribute [local instance] ExternalTensor.bimodule ExternalTensor.rightModule

theorem column_finite [FiniteDimensional k B] (e : B)
    (N : ModuleCat.{u} Bᵐᵒᵖ) [Module.Finite Bᵐᵒᵖ N] :
    FiniteDimensional k ((forgetK k B).obj ((columnFunctor k B e).obj N)) :=
  finite_of_iso k (columnKIso k B e N) (column_finiteDimensional k B N e)

variable {k B}
variable {A J R : Type} [Fintype A] [Fintype J] [Fintype R]
variable (s : Quadratic k B (A := A) (J := J) (R := R))
variable (D₀ D₁ D₂ : RightComplex B)
variable (f : A → (D₀ ⟶ D₁)) (g : J → (D₁ ⟶ D₂))

/-- Finite-dimensionality of the actual three induced columns, from exactly
finite-dimensional B and finite generation of the right-module input terms. -/
theorem columns_finite [FiniteDimensional k B]
    (h₀ : ∀ n, Module.Finite Bᵐᵒᵖ (D₀.X n))
    (h₁ : ∀ n, Module.Finite Bᵐᵒᵖ (D₁.X n))
    (h₂ : ∀ n, Module.Finite Bᵐᵒᵖ (D₂.X n)) (n : ℤ) :
    FiniteDimensional k ((forgetK k B).obj ((L0Prime s D₀ D₁ D₂ f g).X n)) ∧
    FiniteDimensional k ((forgetK k B).obj ((L1Prime s D₀ D₁ D₂ f g).X n)) ∧
    FiniteDimensional k ((forgetK k B).obj ((L2Prime s D₀ D₁ D₂ f g).X n)) := by
  let := h₀ n
  let := h₁ n
  let := h₂ n
  refine ⟨?_, ?_, ?_⟩
  · apply biprod_term_finite
    · exact column_finite k B s.e₀ (D₀.X n)
    · apply biprod_term_finite
      · exact column_finite k B s.e₁ (D₁.X n)
      · exact column_finite k B s.e₂ (D₂.X n)
  · apply biprod_term_finite
    · apply sum_finite
      intro a
      exact column_finite k B s.e₁ (D₀.X n)
    · apply sum_finite
      intro b
      exact column_finite k B s.e₂ (D₁.X n)
  · apply sum_finite
    intro r
    exact column_finite k B s.e₂ (D₀.X n)
end ExternalTensor.Section4

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_TotalFinite
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.ExternalTensor.Section4.SourceFiltration.inclusion2_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroCone_inclusion_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroTermSubsingleton _root_.OAI.LittleFinitistic.BalancedVertexFunctor.additive _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.additive _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.finite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.scalarTower _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.additive _root_.OAI.LittleFinitistic.BimoduleTotal.columnCommShift _root_.OAI.LittleFinitistic.BimoduleTotal.columnFunctor_additive _root_.OAI.LittleFinitistic.BimoduleTotal.inputFunctor_additive _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
noncomputable section
namespace ExternalTensor.Section4
universe u
variable {k : Type u} [Field k]

variable {B : Type u} [Ring B] [Algebra k B]
variable {A J R : Type} [Fintype A] [Fintype J] [Fintype R]
variable (s : Quadratic k B (A := A) (J := J) (R := R))
variable (D₀ D₁ D₂ : RightComplex B)
variable (f : A → (D₀ ⟶ D₁)) (g : J → (D₁ ⟶ D₂))
variable (H : ∀ r, Homotopy (relationMap s D₀ D₁ D₂ f g r) 0)

/-- The finite-dimensionality conclusion for the manuscript's constructed P,
with no projectivity or finite-dimensionality assumption on P or its columns. -/
theorem induced_total_finite [FiniteDimensional k B]
    (h₀ : ∀ i, Module.Finite Bᵐᵒᵖ (D₀.X i))
    (h₁ : ∀ i, Module.Finite Bᵐᵒᵖ (D₁.X i))
    (h₂ : ∀ i, Module.Finite Bᵐᵒᵖ (D₂.X i)) (i : ℤ) :
    FiniteDimensional k ((forgetK k B).obj
      ((LittleFinitistic.RectificationTotal.total (p s D₀ D₁ D₂ f g)
        (q s D₀ D₁ D₂ f g) (nullHomotopy s D₀ D₁ D₂ f g H)).X i)) := by
  exact total_finite_after _ _ _ (forgetK k B)
    (fun n => (columns_finite s D₀ D₁ D₂ f g h₀ h₁ h₂ n).1)
    (fun n => (columns_finite s D₀ D₁ D₂ f g h₀ h₁ h₂ n).2.1)
    (fun n => (columns_finite s D₀ D₁ D₂ f g h₀ h₁ h₂ n).2.2) i
end ExternalTensor.Section4

end

end OAI
end


