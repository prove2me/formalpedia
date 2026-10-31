-- Prove2me | Definitions.Def_OAIQ023F039
-- name    : OAIQ023F039
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T18:19:23.824996+00:00
-- url     : https://prove2.me/theorems/1cfba3e5-34e4-4e5d-ac32-d9bad0b54edc
-- title:
--   Definitions bundle OAIQ023F039 of the split of OpenAI, An algebra of infinite little finitistic dimension (result family 198)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.LittleFinitistic.Main.exists_counterexample`, carved from OpenAI's openai/math development (OpenAI, *An algebra of infinite little finitistic dimension (result family 198)*, OpenAI Math Release, September 23, 2026, result family 198, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 29 declarations of OpenAI's Lean: 13 definitions, 3 instances and 13 theorems. The definitions and types are `OAI.ExternalTensor.Section4.SourceFiltration.Complex.source0`, `OAI.ExternalTensor.Section4.SourceFiltration.Complex.source1`, `OAI.ExternalTensor.Section4.SourceFiltration.Exactness.G1`, `OAI.ExternalTensor.Section4.SourceFiltration.Exactness.pi1`, `OAI.ExternalTensor.Section4.SourceFiltration.grade1ConeIso`, `OAI.ExternalTensor.Section4.SourceFiltration.hGrade1`, `OAI.ExternalTensor.Section4.SourceFiltration.quotient1`, `OAI.ExternalTensor.Section4.columnKIso`, `OAI.LittleFinitistic.AdjacentArrowSum.sourceIso`, `OAI.LittleFinitistic.AdjacentArrowSum.targetIso`, `OAI.LittleFinitistic.QuadraticEncoding.B`, `OAI.LittleFinitistic.QuadraticEncoding.composition`, `OAI.LittleFinitistic.QuadraticEncoding.relationSpace`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: `Finitistic_Bar_CountProjective`, `Finitistic_Encoding_ArrowBasisIso`, `Finitistic_Encoding_QuadraticEncoding`, `Finitistic_Rectification_AdjacentArrowSum`, `Finitistic_Rectification_ColumnFinite`, `Finitistic_Rectification_ColumnProperties`, `Finitistic_Rectification_FiltrationExactness`, `Finitistic_Rectification_SourceFiltration`, `Finitistic_Rectification_SourceFiltrationComplex`, `Finitistic_Rectification_SourceFiltrationCone`, `Finitistic_Rectification_SourceFiltrationExact`, `Finitistic_Rectification_SourceFiltrationReal`, `Finitistic_Rectification_TensorArrowSum`.
--
--   **Imports.** It imports the bundles `OAIQ023F012` and `OAIQ023F017` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ023F021`, `OAIQ023F022` and `OAIQ023F023`.
-- source:
--   OpenAI, An algebra of infinite little finitistic dimension (result family 198), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 198; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-algebra-of-infinite-little-finitistic-dimension-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ023F012
import Definitions.Def_OAIQ023F017

set_option maxHeartbeats 1000000

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_CountProjective
attribute [-instance] _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory CategoryTheory.Limits TensorProduct TrivSqZeroExt
open scoped TensorProduct DirectSum
noncomputable section
namespace DerivedBar
universe u
variable (k D X N : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
  [AddCommGroup N] [Module k N]
open Multibar.Indexed

local instance countProjectiveShapeDecidableEq_ra0118b_1 (n r : ℕ) : DecidableEq (Shape n r) :=
  Classical.decEq _
variable [Module (TrivSqZeroExt D X) N] [IsScalarTower k (TrivSqZeroExt D X) N]
  (hN : ∀ (x : X) (v : N), (inr x : TrivSqZeroExt D X) • v = 0)

instance countSum_projective (n : ℕ) :
    Projective ((directSumComplex (SquareZero.twoSidedWeightComplex k D X N hN)).X n) := by
  classical
  let (r : ℕ) : Module.Free D ((SquareZero.twoSidedWeightComplex k D X N hN r).X n) :=
    countWeight_free k D X N n r
  change Projective (ModuleCat.of D (⨁ r : ℕ, (SquareZero.twoSidedWeightComplex k D X N hN r).X n))
  infer_instance

instance integerCount_isKProjective (r : ℕ) :
    ((integerExtension D).obj (SquareZero.twoSidedWeightComplex k D X N hN r)).IsKProjective := by
  change CochainComplex.IsKProjective ((SquareZero.twoSidedWeightComplex k D X N hN r).extend
    ComplexShape.embeddingDownNat)
  infer_instance

instance integerCountSum_isKProjective :
    ((integerExtension D).obj (directSumComplex
      (SquareZero.twoSidedWeightComplex k D X N hN))).IsKProjective := by
  change CochainComplex.IsKProjective ((directSumComplex (SquareZero.twoSidedWeightComplex k D X N hN)).extend
    ComplexShape.embeddingDownNat)
  infer_instance
end DerivedBar

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Encoding_QuadraticEncoding
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.ExternalTensor.envelopingScalarTower _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped TensorProduct
namespace LittleFinitistic.QuadraticEncoding
universe u v
variable {k : Type u} [Field k] {d t : ℕ}

/-- Exactly the span of a'_h s - s' a_h and all homogenized p_j. -/
def relationSpace (P : Relations k d t) : Submodule k (Paths k d) :=
  Submodule.span k (Set.range (commutation (k := k) (d := d)) ∪ Set.range (homogenized P))

/-- Compose arrows, then quotient only the length-two path space by the specified relations. -/
def composition (P : Relations k d t) :
    Arrows k d →ₗ[k] Arrows k d →ₗ[k] (Paths k d ⧸ relationSpace P) :=
  (TensorProduct.mk k (Arrows k d) (Arrows k d)).compr₂ (relationSpace P).mkQ

/-- The six path-endpoint components of the manuscript's directed encoding. -/
abbrev B (P : Relations k d t) := ThreeVertexAlgebra (composition P)

end LittleFinitistic.QuadraticEncoding

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Encoding_ArrowBasisIso
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticPresentation.instFiniteAuxiliaryEquation _root_.OAI.LittleFinitistic.QuadraticPresentation.instFiniteAuxiliaryLetter _root_.OAI.LittleFinitistic.QuadraticPresentation.step_finite _root_.OAI.LittleFinitistic.QuadraticPresentation.word_finite _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated _root_.OAI.LittleFinitistic.cyclicRing_finiteInst
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.arrowAction_basis _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.rawPathAction_tmul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.ArrowBasisIso
universe u
variable (k : Type u) [Field k] (d : ℕ)

/-- The coproduct injection sends a scalar to that scalar times its original arrow basis. -/
theorem injection_apply (i : Fin (d+1)) (c : k) :
    ((biproduct.ι (family k d) i ≫ (iso k d).hom).hom) c =
      c • QuadraticEncoding.basis i := by
  funext j
  have h := congrArg (fun f : (family k d i) ⟶ ModuleCat.of k k => f.hom c)
    (congrArg (fun f => biproduct.ι (family k d) i ≫ f) (hom_proj k d j))
  have h' : ((biproduct.ι (family k d) i ≫ (iso k d).hom).hom c) j =
      (biproduct.ι (family k d) i ≫ biproduct.π (family k d) j).hom c := h
  rw [h']
  classical
  by_cases hij : i=j
  · subst j
    simp [QuadraticEncoding.basis]
  · simp [hij,QuadraticEncoding.basis,Ne.symm hij]
end LittleFinitistic.ArrowBasisIso

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_TensorArrowSum
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticPresentation.instFiniteAuxiliaryEquation _root_.OAI.LittleFinitistic.QuadraticPresentation.instFiniteAuxiliaryLetter _root_.OAI.LittleFinitistic.QuadraticPresentation.step_finite _root_.OAI.LittleFinitistic.QuadraticPresentation.word_finite _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated _root_.OAI.LittleFinitistic.cyclicRing_finiteInst
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.arrowAction_basis _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.rawPathAction_tmul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.TensorArrowSum
universe u
variable (k : Type u) [Field k] (d : ℕ)

@[simp] theorem insertion_apply (a : Fin (d+1)) (c : k) :
    (insertion k d a).hom c = c • QuadraticEncoding.basis a :=
  ArrowBasisIso.injection_apply k d a c

/-- An additive realization of the actual arrow-basis sum is an isomorphism. -/
theorem desc_isIso {C : Type*} [Category C] [Preadditive C] [HasFiniteBiproducts C]
    (F : ModuleCat.{u} k ⥤ C) [F.Additive] :
    IsIso (biproduct.desc (fun a : Fin (d+1) => F.map (insertion k d a))) := by
  have he : biproduct.desc (fun a : Fin (d+1) => F.map (insertion k d a)) =
      (F.mapBiproduct (ArrowBasisIso.family k d)).inv ≫ F.map (ArrowBasisIso.iso k d).hom := by
    apply biproduct.hom_ext'
    intro a
    simp only [insertion, Functor.map_comp, Functor.mapBiproduct_inv]
    erw [biproduct.ι_desc, biproduct.ι_desc_assoc]
  rw [he]
  infer_instance

/-- Coordinate isomorphisms identify an actual arrow family with the realized basis. -/
theorem desc_isIso_of_coordinates {C : Type*} [Category C] [Preadditive C]
    [HasFiniteBiproducts C] (F : ModuleCat.{u} k ⥤ C) [F.Additive]
    (X : Fin (d+1) → C) (Y : C) (α : ∀ a, X a ≅ F.obj (ModuleCat.of k k))
    (β : Y ≅ F.obj (ModuleCat.of k (QuadraticEncoding.Arrows k d)))
    (f : ∀ a, X a ⟶ Y)
    (hf : ∀ a, (α a).hom ≫ F.map (insertion k d a) = f a ≫ β.hom) :
    IsIso (biproduct.desc f) := by
  have he : biproduct.desc f ≫ β.hom =
      (biproduct.mapIso α).hom ≫ biproduct.desc (fun a => F.map (insertion k d a)) := by
    apply biproduct.hom_ext'
    intro a
    simp only [biproduct.mapIso_hom,biproduct.ι_desc_assoc,biproduct.ι_map_assoc,biproduct.ι_desc]
    exact (hf a).symm
  let := desc_isIso k d F
  rw [← isIso_comp_right_iff _ β.hom,he]
  infer_instance
end LittleFinitistic.TensorArrowSum

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_AdjacentArrowSum
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.ExternalTensor.Section4.SourceFiltration.inclusion2_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroCone_inclusion_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroTermSubsingleton _root_.OAI.ExternalTensor.Section4.forgetK_additive _root_.OAI.ExternalTensor.Section4.forgetRight_additive _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.LittleFinitistic.BalancedVertexFunctor.additive _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.additive _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.finite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.scalarTower _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.BimoduleVertex.linear _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
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
def sourceIso (v : Fin 3) :
    (vertexComplex μ v).obj ((ExternalTensor.Section4.columnComplex k T
      (ThreeVertexAlgebra.vertex μ v)).obj D) ≅
      (TensorComplex.tensorFunctor (k := k) D).obj (ModuleCat.of k k) :=
  (CornerColumnComplex.complexIso μ v v D).symm ≪≫
    (TensorComplex.tensorFunctor (k := k) D).mapIso (CornerSpaces.diagonalEquiv μ v).toModuleIso

def targetIso (v i : Fin 3) (d : ℕ)
    (ξ : CornerSpaces.corner μ v i ≃ₗ[k] QuadraticEncoding.Arrows k d) :
    (vertexComplex μ v).obj ((ExternalTensor.Section4.columnComplex k T
      (ThreeVertexAlgebra.vertex μ i)).obj D) ≅
      (TensorComplex.tensorFunctor (k := k) D).obj (ModuleCat.of k (QuadraticEncoding.Arrows k d)) :=
  (CornerColumnComplex.complexIso μ v i D).symm ≪≫
    (TensorComplex.tensorFunctor (k := k) D).mapIso ξ.toModuleIso

end LittleFinitistic.AdjacentArrowSum

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_ColumnProperties
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.ExternalTensor.Section4.SourceFiltration.inclusion2_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroCone_inclusion_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroTermSubsingleton _root_.OAI.ExternalTensor.Section4.forgetK_additive _root_.OAI.LittleFinitistic.BalancedTensor.scalarModuleTower _root_.OAI.LittleFinitistic.BalancedVertexFunctor.additive _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.additive _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.finite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.scalarTower _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleCoefficients.towerRight _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TensorComplex.scalarTower _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
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

theorem column_right_projective (e : B) (N : ModuleCat.{u} Bᵐᵒᵖ)
    [Module.Projective Bᵐᵒᵖ N] :
    Projective ((forgetRight k B).obj ((columnFunctor k B e).obj N)) := by
  let := column_projective k B N e
  exact Projective.of_iso (columnRightIso k B e N).symm (by infer_instance)

end ExternalTensor.Section4

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_ColumnFinite
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.ExternalTensor.Section4.SourceFiltration.inclusion2_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroCone_inclusion_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroTermSubsingleton _root_.OAI.LittleFinitistic.BalancedTensor.scalarModuleTower _root_.OAI.LittleFinitistic.BalancedVertexFunctor.additive _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.additive _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.finite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.scalarTower _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleCoefficients.towerRight _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.DirectedBound.DirectedSystem.cover_addCommGroup _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.ProductModules.firstModule _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TensorComplex.scalarTower _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
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

set_option maxHeartbeats 0 in
def columnKIso (e : B) (N : ModuleCat.{u} Bᵐᵒᵖ) :
    (forgetK k B).obj ((columnFunctor k B e).obj N) ≅
      ModuleCat.of k (Column k B N e) :=
  (show ((forgetK k B).obj ((columnFunctor k B e).obj N)) ≃ₗ[k]
      (ModuleCat.of k (Column k B N e)) from
    { toFun := id
      invFun := id
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun c x => by
        change (algebraMap k (Enveloping k B) c) •
          (show Column k B N e from x) = c • (show Column k B N e from x)
        exact IsScalarTower.algebraMap_smul (Enveloping k B) c (show Column k B N e from x) }).toModuleIso

end ExternalTensor.Section4

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_SourceFiltration
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.ExternalTensor.Section4.SourceFiltration.inclusion2_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroCone_inclusion_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroTermSubsingleton _root_.OAI.ExternalTensor.Section4.forgetK_additive _root_.OAI.ExternalTensor.Section4.forgetRight_additive _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.LittleFinitistic.BalancedVertexFunctor.additive _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.additive _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.finite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.scalarTower _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.ArrowVertex.arrow_id _root_.OAI.ExternalTensor.Section4.ArrowVertex.arrow_original _root_.OAI.ExternalTensor.Section4.ArrowVertex.iota_original _root_.OAI.ExternalTensor.Section4.ArrowVertex.left_mul _root_.OAI.ExternalTensor.Section4.ArrowVertex.map_left _root_.OAI.ExternalTensor.Section4.ArrowVertex.mem_space _root_.OAI.LittleFinitistic.BalancedVertexImage.equiv_apply_val _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.smul_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open LittleFinitistic.RectificationTotal
open scoped TensorProduct ModuleCat.Algebra
noncomputable section
namespace ExternalTensor.Section4.SourceFiltration
universe u
variable {k B : Type u} [Field k] [Ring B] [Algebra k B]
variable {A J R : Type} [Fintype A] [Fintype J] [Fintype R]
variable (t : AssemblyData (C := BiComplex k B) (A := A) (J := J) (R := R))

variable (h : Homotopy (t.q ≫ t.p) 0)

def hGrade1 : Homotopy ((0 : Z ⟶ F1₁ t) ≫ pGrade1 t) 0 where
  hom _ _ := 0
  zero _ _ _ := rfl
  comm _ := by simp [dNext, prevD]

def quotient1 : MapData (p1 t) 0 (h1 t) (pGrade1 t) 0 (hGrade1 t) where
  f₀ := biprod.fst
  f₁ := 𝟙 _
  f₂ := 𝟙 _
  commP := by
    rw [Category.id_comp]
    apply biproduct.hom_ext'
    intro b
    simp [p1, pGrade1, Preadditive.sub_comp]
  commQ := by simp
  commH i j := by simp [h1, hGrade1]

end ExternalTensor.Section4.SourceFiltration

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_SourceFiltrationExact
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.ExternalTensor.Section4.SourceFiltration.inclusion2_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroCone_inclusion_isIso _root_.OAI.ExternalTensor.Section4.forgetK_additive _root_.OAI.ExternalTensor.Section4.forgetRight_additive _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.LittleFinitistic.BalancedVertexFunctor.additive _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.additive _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.finite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.scalarTower _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticPresentation.instFiniteAuxiliaryEquation _root_.OAI.LittleFinitistic.QuadraticPresentation.instFiniteAuxiliaryLetter _root_.OAI.LittleFinitistic.QuadraticPresentation.step_finite _root_.OAI.LittleFinitistic.QuadraticPresentation.word_finite _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated _root_.OAI.LittleFinitistic.cyclicRing_finiteInst
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open LittleFinitistic.RectificationTotal
noncomputable section
namespace ExternalTensor.Section4.SourceFiltration
universe u
variable {k B : Type u} [Field k] [Ring B] [Algebra k B]
variable {A J R : Type} [Fintype A] [Fintype J] [Fintype R]

variable (t : AssemblyData (C := BiComplex k B) (A := A) (J := J) (R := R))
variable (h : Homotopy (t.q ≫ t.p) 0)
variable (hh : ∀ i j, h.hom i j ≫ (biprod.fst : t.L₀ ⟶ t.V₀).f j = 0)

omit [Fintype R] in
theorem source1_component0 (n : ℤ) :
    Function.Injective ((include2 t).f₀.f n) ∧
    Function.Exact ((include2 t).f₀.f n) ((quotient1 t).f₀.f n) ∧
    Function.Surjective ((quotient1 t).f₀.f n) :=
  inr_fst_shortExact t.V₁ t.V₂ n

omit [Fintype R] in
theorem source1_component1 (n : ℤ) :
    Function.Injective ((include2 t).f₁.f n) ∧
    Function.Exact ((include2 t).f₁.f n) ((quotient1 t).f₁.f n) ∧
    Function.Surjective ((quotient1 t).f₁.f n) :=
  zero_id_shortExact (⨁ t.V) Z (fun _ => inferInstance) n

omit [Fintype R] in
theorem source1_component2 (n : ℤ) :
    Function.Injective ((include2 t).f₂.f n) ∧
    Function.Exact ((include2 t).f₂.f n) ((quotient1 t).f₂.f n) ∧
    Function.Surjective ((quotient1 t).f₂.f n) := by
  refine ⟨fun _ _ _ => Subsingleton.elim _ _, ?_, fun x => ⟨x, rfl⟩⟩
  intro x
  exact ⟨fun _ => ⟨x, rfl⟩, fun _ => Subsingleton.elim _ _⟩

omit [Fintype R] in
/-- The actual F>=2 inclusion and source-one quotient are termwise short exact. -/
theorem source1_shortExact (n : ℤ) :
    Function.Injective ((include2 t).totalMap.f n) ∧
    Function.Exact ((include2 t).totalMap.f n) ((quotient1 t).totalMap.f n) ∧
    Function.Surjective ((quotient1 t).totalMap.f n) := by
  exact (include2 t).totalMap_shortExact (quotient1 t)
    (fun n => (source1_component0 t n).2.1)
    (fun n => (source1_component1 t n).2.1)
    (fun n => (source1_component2 t n).2.1)
    (fun n => (source1_component0 t n).1)
    (fun n => (source1_component1 t n).1)
    (fun n => (source1_component2 t n).1)
    (fun n => (source1_component0 t n).2.2)
    (fun n => (source1_component1 t n).2.2)
    (fun n => (source1_component2 t n).2.2) n

end ExternalTensor.Section4.SourceFiltration

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_SourceFiltrationReal
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroCone_inclusion_isIso _root_.OAI.ExternalTensor.Section4.forgetK_additive _root_.OAI.ExternalTensor.Section4.forgetRight_additive _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.LittleFinitistic.BalancedVertexFunctor.additive _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.additive _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.finite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.scalarTower _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open LittleFinitistic.RectificationTotal
noncomputable section
namespace ExternalTensor.Section4.SourceFiltration
universe u
variable {k B : Type u} [Field k] [Ring B] [Algebra k B]
variable {A J R : Type} [Fintype A] [Fintype J] [Fintype R]
variable (t : AssemblyData (C := BiComplex k B) (A := A) (J := J) (R := R))

omit [Fintype R] in
/-- The source-one sequence with V2 itself as its first term. -/
theorem v2_shortExact (n : ℤ) :
    Function.Injective ((v2Inclusion t).f n) ∧
    Function.Exact ((v2Inclusion t).f n) ((quotient1 t).totalMap.f n) ∧
    Function.Surjective ((quotient1 t).totalMap.f n) := by
  have E := source1_shortExact t n
  have I := inclusion2_bijective t n
  rw [v2Inclusion_eq]
  refine ⟨E.1.comp I.1, ?_, E.2.2⟩
  intro y
  constructor
  · intro hy
    obtain ⟨x, hx⟩ := (E.2.1 y).mp hy
    obtain ⟨z, rfl⟩ := I.2 x
    exact ⟨z, hx⟩
  · rintro ⟨x, rfl⟩
    exact E.2.1.apply_apply_eq_zero _

end ExternalTensor.Section4.SourceFiltration

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_SourceFiltrationCone
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.ExternalTensor.Section4.forgetK_additive _root_.OAI.ExternalTensor.Section4.forgetRight_additive _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.LittleFinitistic.BalancedVertexFunctor.additive _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.additive _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.finite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.scalarTower _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open LittleFinitistic.RectificationTotal
noncomputable section
namespace ExternalTensor.Section4.SourceFiltration
universe u
variable {k B : Type u} [Field k] [Ring B] [Algebra k B]

variable (X : BiComplex k B)

variable {A J R : Type} [Fintype A] [Fintype J] [Fintype R]
variable (t : AssemblyData (C := BiComplex k B) (A := A) (J := J) (R := R))

def grade1ConeIso : mappingCone (pGrade1 t) ≅ total (pGrade1 t) 0 (hGrade1 t) :=
  twoColumnIso _ _ _
end ExternalTensor.Section4.SourceFiltration

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_FiltrationExactness
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.ExternalTensor.Section4.forgetK_additive _root_.OAI.ExternalTensor.Section4.forgetRight_additive _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.LittleFinitistic.BalancedVertexFunctor.additive _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.additive _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.finite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.scalarTower _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open LittleFinitistic.RectificationTotal
open scoped TensorProduct ModuleCat.Algebra
noncomputable section
namespace ExternalTensor.Section4.SourceFiltration.Exactness
universe u
variable {k B : Type u} [Field k] [Ring B] [Algebra k B]
variable {A J R : Type} [Fintype A] [Fintype J] [Fintype R]
variable (s : Quadratic k B (A := A) (J := J) (R := R))
variable (D₀ D₁ D₂ : RightComplex B)
variable (f : A → (D₀ ⟶ D₁)) (g : J → (D₁ ⟶ D₂))
variable (H : ∀ r, Homotopy (relationMap s D₀ D₁ D₂ f g r) 0)

abbrev G1 := total (pGrade1 (data s D₀ D₁ D₂ f g)) 0
  (hGrade1 (data s D₀ D₁ D₂ f g))

abbrev pi1 : F1 s D₀ D₁ D₂ f g ⟶ G1 s D₀ D₁ D₂ f g :=
  (quotient1 (data s D₀ D₁ D₂ f g)).totalMap

/-- Section 4's actual two nontrivial source-filtration steps. No decomposition,
exactness, extra coherence, vertex equivalence, or main theorem is an input. -/
theorem exact_source_filtration (n : ℤ) :
    (Function.Injective ((i1 s D₀ D₁ D₂ f g H).f n) ∧
     Function.Exact ((i1 s D₀ D₁ D₂ f g H).f n) ((pi0 s D₀ D₁ D₂ f g H).f n) ∧
     Function.Surjective ((pi0 s D₀ D₁ D₂ f g H).f n)) ∧
    (Function.Injective ((i2 s D₀ D₁ D₂ f g).f n) ∧
     Function.Exact ((i2 s D₀ D₁ D₂ f g).f n) ((pi1 s D₀ D₁ D₂ f g).f n) ∧
     Function.Surjective ((pi1 s D₀ D₁ D₂ f g).f n)) ∧
    i2 s D₀ D₁ D₂ f g ≫ i1 s D₀ D₁ D₂ f g H =
      (data s D₀ D₁ D₂ f g).in₂ ≫
        inclusion (p s D₀ D₁ D₂ f g) (q s D₀ D₁ D₂ f g)
          (nullHomotopy s D₀ D₁ D₂ f g H) :=
  ⟨induced_source0_shortExact s D₀ D₁ D₂ f g H n,
   v2_shortExact (data s D₀ D₁ D₂ f g) n,
   v2_nested (data s D₀ D₁ D₂ f g) (nullHomotopy s D₀ D₁ D₂ f g H)⟩

end ExternalTensor.Section4.SourceFiltration.Exactness

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_SourceFiltrationComplex
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.ExternalTensor.Section4.forgetK_additive _root_.OAI.ExternalTensor.Section4.forgetRight_additive _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.LittleFinitistic.BalancedVertexFunctor.additive _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.additive _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.finite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.scalarTower _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace ExternalTensor.Section4.SourceFiltration.Complex
universe u
variable {k B : Type u} [Field k] [Ring B] [Algebra k B]
variable {A J R : Type} [Fintype A] [Fintype J] [Fintype R]
variable (s : Quadratic k B (A := A) (J := J) (R := R))
variable (D₀ D₁ D₂ : RightComplex B)
variable (f : A → (D₀ ⟶ D₁)) (g : J → (D₁ ⟶ D₂))
variable (H : ∀ r, Homotopy (relationMap s D₀ D₁ D₂ f g r) 0)
open Exactness LittleFinitistic

def source0 := ModuleComplexExact.sequence (i1 s D₀ D₁ D₂ f g H)
  (pi0 s D₀ D₁ D₂ f g H)
  (fun n => (exact_source_filtration s D₀ D₁ D₂ f g H n).1.2.1)

def source1 := ModuleComplexExact.sequence (i2 s D₀ D₁ D₂ f g)
  (pi1 s D₀ D₁ D₂ f g)
  (fun n => (v2_shortExact (data s D₀ D₁ D₂ f g) n).2.1)

theorem source0_shortExact : (source0 s D₀ D₁ D₂ f g H).ShortExact :=
  ModuleComplexExact.shortExact _ _
    (fun n => (exact_source_filtration s D₀ D₁ D₂ f g H n).1)

omit [Fintype R] in
theorem source1_shortExact : (source1 s D₀ D₁ D₂ f g).ShortExact :=
  ModuleComplexExact.shortExact _ _ (v2_shortExact (data s D₀ D₁ D₂ f g))

end ExternalTensor.Section4.SourceFiltration.Complex

end

end OAI
end


