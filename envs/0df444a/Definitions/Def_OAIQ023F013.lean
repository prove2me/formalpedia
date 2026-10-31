-- Prove2me | Definitions.Def_OAIQ023F013
-- name    : OAIQ023F013
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T15:59:05.189044+00:00
-- url     : https://prove2.me/theorems/d7f9e766-9200-4a7c-966c-ac8942825782
-- title:
--   Definitions bundle OAIQ023F013 of the split of OpenAI, An algebra of infinite little finitistic dimension (result family 198)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.LittleFinitistic.Main.exists_counterexample`, carved from OpenAI's openai/math development (OpenAI, *An algebra of infinite little finitistic dimension (result family 198)*, OpenAI Math Release, September 23, 2026, result family 198, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 35 declarations of OpenAI's Lean: 16 definitions, 4 instances and 15 theorems. The definitions and types are `OAI.LittleFinitistic.CornerSpaces.corner10Equiv`, `OAI.LittleFinitistic.CornerSpaces.corner20Equiv`, `OAI.LittleFinitistic.CornerSpaces.corner21Equiv`, `OAI.LittleFinitistic.CornerTensor.scalarTensorEquiv`, `OAI.LittleFinitistic.IdempotentTensor.splitInclusion`, `OAI.LittleFinitistic.IdempotentTensor.splitProjection`, `OAI.LittleFinitistic.PathBasisIso.iso`, `OAI.LittleFinitistic.RelationBasisAction.pathValue`, `OAI.LittleFinitistic.RelationBasisCoefficients.pathBasis`, `OAI.LittleFinitistic.RelationMatrixSequence.pathIso`, `OAI.LittleFinitistic.RelationPathCoordinates.coordinates`, `OAI.LittleFinitistic.VertexDecomposition.Space`, `OAI.LittleFinitistic.VertexDecomposition.equiv`, `OAI.LittleFinitistic.VertexDecomposition.project`, `OAI.LittleFinitistic.VertexModuleAssembly.arrow`, `OAI.LittleFinitistic.VertexModuleAssembly.assembled`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: `Finitistic_Encoding_PathBasisIso`, `Finitistic_Encoding_RelationBasisAction`, `Finitistic_Encoding_RelationBasisCoefficients`, `Finitistic_Encoding_RelationMatrixSequence`, `Finitistic_Encoding_RelationPathCoordinates`, `Finitistic_Localization_BoundedDerivedEmbedding`, `Finitistic_Localization_FiniteProjectiveHomotopy`, `Finitistic_Rectification_CornerSpaces`, `Finitistic_Rectification_CornerTensor`, `Finitistic_Rectification_VertexDecomposition`, `Finitistic_Rectification_VertexModuleAssembly`, `Finitistic_Selected_SelectedTargetHomology`, `Finitistic_Tensor_IdempotentTensorMaps`.
--
--   **Imports.** It imports the bundles `OAIQ023F003`, `OAIQ023F005`, `OAIQ023F006` and `OAIQ023F007` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ023F019`.
-- source:
--   OpenAI, An algebra of infinite little finitistic dimension (result family 198), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 198; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-algebra-of-infinite-little-finitistic-dimension-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ023F003
import Definitions.Def_OAIQ023F005
import Definitions.Def_OAIQ023F006
import Definitions.Def_OAIQ023F007

section
-- module Solutions.OAIQ023_Fin.Finitistic_Encoding_RelationBasisCoefficients
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped TensorProduct
namespace LittleFinitistic.RelationBasisCoefficients
open QuadraticEncoding
universe u
variable {k : Type u} [Field k] {d t : ℕ} (P : Relations k d t)

/-- The actual ordered length-two path basis, with the later arrow first. -/
def pathBasis : Module.Basis (Fin (d+1) × Fin (d+1)) k (Paths k d) :=
  (Pi.basisFun k (Fin (d+1))).tensorProduct (Pi.basisFun k (Fin (d+1)))

end LittleFinitistic.RelationBasisCoefficients

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Encoding_PathBasisIso
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace LittleFinitistic.PathBasisIso
universe u
variable (k : Type u) [Field k] (d : ℕ)

/-- Group paths by their first traversed arrow; the later arrow is the first tensor factor. -/
def iso : (⨁ family k d) ≅ ModuleCat.of k (QuadraticEncoding.Paths k d) :=
  ModuleCat.biproductIsoPi (family k d) ≪≫
    (TensorProduct.piScalarRight k k (QuadraticEncoding.Arrows k d) (Fin (d+1))).symm.toModuleIso

theorem pi_hom_proj (j : Fin (d+1)) :
    (ModuleCat.biproductIsoPi (family k d)).hom ≫ ModuleCat.ofHom (LinearMap.proj j) =
      biproduct.π (family k d) j := by
  rw [← ModuleCat.biproductIsoPi_inv_comp_π (family k d) j]
  simp only [Iso.hom_inv_id_assoc]

theorem pi_injection_apply (a : Fin (d+1)) (w : QuadraticEncoding.Arrows k d) :
    (biproduct.ι (family k d) a ≫ (ModuleCat.biproductIsoPi (family k d)).hom).hom w = Pi.single a w := by
  funext j
  have h := congrArg (fun f : (family k d a) ⟶ family k d j => f.hom w)
    (congrArg (fun f => biproduct.ι (family k d) a ≫ f) (pi_hom_proj k d j))
  change ((biproduct.ι (family k d) a ≫ (ModuleCat.biproductIsoPi (family k d)).hom).hom w) j = _
  rw [show ((biproduct.ι (family k d) a ≫ (ModuleCat.biproductIsoPi (family k d)).hom).hom w) j =
      (biproduct.ι (family k d) a ≫ biproduct.π (family k d) j).hom w from h]
  classical
  by_cases haj : a=j
  · subst j; simp
  · simp [haj,Ne.symm haj]

/-- A summand w at a maps to the actual tensor path w tensor a. -/
theorem injection_apply (a : Fin (d+1)) (w : QuadraticEncoding.Arrows k d) :
    (biproduct.ι (family k d) a ≫ (iso k d).hom).hom w = w ⊗ₜ[k] QuadraticEncoding.basis a := by
  change (TensorProduct.piScalarRight k k (QuadraticEncoding.Arrows k d) (Fin (d+1))).symm
    ((biproduct.ι (family k d) a ≫ (ModuleCat.biproductIsoPi (family k d)).hom).hom w) = _
  rw [pi_injection_apply,TensorProduct.piScalarRight_symm_single]
  rfl
end LittleFinitistic.PathBasisIso

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Encoding_RelationBasisAction
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped TensorProduct
namespace LittleFinitistic.RelationBasisAction
open QuadraticEncoding RelationBasisCoefficients
universe u v
variable {k : Type u} [Field k] {R : Type v} [Ring R] [Algebra k R]
variable {d t : ℕ} (P : Relations k d t) (x : Fin d → R)

/-- Evaluate a length-two path b a in the original algebra. -/
def pathValue : Paths k d →ₗ[k] R :=
  (pathBasis (k := k) (d := d)).constr k (fun ba => arrow x ba.1 * arrow x ba.2)

@[simp] theorem pathValue_basis (b a : Fin (d+1)) :
    pathValue x (basis b ⊗ₜ[k] basis a) = arrow x b * arrow x a := by
  have hb : (pathBasis (k := k) (d := d)) (b,a) = basis b ⊗ₜ[k] basis a := by
    simp [pathBasis,basis]
  rw [← hb]
  exact (pathBasis (k := k) (d := d)).constr_basis k _ (b,a)

end LittleFinitistic.RelationBasisAction

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Encoding_RelationPathCoordinates
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped TensorProduct
namespace LittleFinitistic.RelationPathCoordinates
open QuadraticEncoding RelationBasisCoefficients
universe u
variable {k : Type u} [Field k] {d t : ℕ} (P : Relations k d t)

abbrev coordinates : Paths k d ≃ₗ[k] (Fin (d+1) → Arrows k d) :=
  TensorProduct.piScalarRight k k (Arrows k d) (Fin (d+1))

end LittleFinitistic.RelationPathCoordinates

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Encoding_RelationMatrixSequence
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace LittleFinitistic.RelationMatrixSequence
open QuadraticEncoding RelationBasisCoefficients
universe u
variable {k : Type u} [Field k] {d t : ℕ} (P : Relations k d t)

abbrev pathIso := PathBasisIso.iso k d

end LittleFinitistic.RelationMatrixSequence

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_FiniteProjectiveHomotopy
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FiniteProjectiveHomotopy.derivedEmbeddingFaithful _root_.OAI.LittleFinitistic.FiniteProjectiveHomotopy.derivedEmbeddingFull _root_.OAI.LittleFinitistic.FiniteProjectiveHomotopy.derivedEmbeddingShift _root_.OAI.LittleFinitistic.FiniteProjectiveHomotopy.underlyingKProjective _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.derivedEmbeddingAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.derivedToEssImageAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectedTargetHomology.instAdditiveFullSubcategoryDerivedCategoryModuleCatComplexEssImageKDerivedEmbeddingCCohomology _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated _root_.OAI.LittleFinitistic.VectorComplexFormality.finiteVectorDerivedIdempotentComplete _root_.OAI.LittleFinitistic.VectorComplexFormality.finiteVectorHomotopyIdempotentComplete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open ZeroObject
namespace LittleFinitistic.FiniteProjectiveHomotopy
universe u v
variable (R : Type u) [Ring R]

lemma mappingCone_property {K L : CochainComplex (ModuleCat.{v} R) ℤ} (f : K ⟶ L)
    (hK : ComplexProperty R K) (hL : ComplexProperty R L) :
    ComplexProperty R (CochainComplex.mappingCone f) := by
  obtain ⟨⟨a,b,hbK⟩,hpK⟩ := hK
  obtain ⟨⟨c,d,hbL⟩,hpL⟩ := hL
  constructor
  · refine ⟨min a c - 1,max b d,fun i hi => ?_⟩
    rw [CochainComplex.mappingCone.isZero_X_iff]
    exact ⟨hbK (i+1) (by omega),hbL i (by omega)⟩
  · intro i
    have := (hpK (i+1)).1
    have := (hpK (i+1)).2
    have := (hpL i).1
    have := (hpL i).2
    let e := HomologicalComplex.homotopyCofiber.XIsoBiprod f i (i+1) rfl
    have := finite_biprod R (K.X (i+1)) (L.X i)
    exact ⟨finite_of_iso R e.symm, Projective.of_iso e.symm inferInstance⟩

instance objectsClosed₃ : (objects.{u,v} R).IsTriangulatedClosed₃ where
  ext₃' T hT h₁ h₂ := by
    obtain ⟨f : T.obj₁.as ⟶ T.obj₂.as,hf⟩ := (HomotopyCategory.quotient _ _).map_surjective T.mor₁
    refine ⟨(HomotopyCategory.quotient _ _).obj (CochainComplex.mappingCone f),
      mappingCone_property R f h₁ h₂, ⟨?_⟩⟩
    exact Triangle.π₃.mapIso (isoTriangleOfIso₁₂ T _ hT
      (HomotopyCategory.mappingCone_triangleh_distinguished f)
      (Iso.refl _) (Iso.refl _) (by
        change T.mor₁ ≫ 𝟙 _ = 𝟙 _ ≫ (HomotopyCategory.quotient _ _).map f
        rw [Category.comp_id,Category.id_comp,hf]))

instance objectsTriangulated : (objects.{u,v} R).IsTriangulated where
  toIsTriangulatedClosed₂ := .of_isTriangulatedClosed₃

end LittleFinitistic.FiniteProjectiveHomotopy

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_BoundedDerivedEmbedding
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.derivedEmbeddingAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.derivedToEssImageAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectedTargetHomology.instAdditiveFullSubcategoryDerivedCategoryModuleCatComplexEssImageKDerivedEmbeddingCCohomology _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated _root_.OAI.LittleFinitistic.VectorComplexFormality.finiteVectorDerivedIdempotentComplete _root_.OAI.LittleFinitistic.VectorComplexFormality.finiteVectorHomotopyIdempotentComplete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
namespace LittleFinitistic.FiniteProjectiveHomotopy
universe u v
variable (R : Type u) [Ring R]

instance derivedEmbeddingTriangulated : (derivedEmbedding.{u,v} R).IsTriangulated :=
  inferInstanceAs (inclusion R ⋙ DerivedCategory.Qh).IsTriangulated

end LittleFinitistic.FiniteProjectiveHomotopy

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_CornerSpaces
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom _root_.OAI.LittleFinitistic.CornerProjection.projection_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LittleFinitistic.CornerSpaces
open ThreeVertexAlgebra

universe u
variable {k V W U : Type u} [Field k]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
  [AddCommGroup U] [Module k U]
variable (μ : W →ₗ[k] V →ₗ[k] U)

noncomputable def corner10Equiv : corner μ 1 0 ≃ₗ[k] V where
  toFun x := x.val.2.2.2.1
  invFun v := ⟨(0,0,0,v,0,0),by
    change mul μ (mul μ (vertex μ 1) (0,0,0,v,0,0)) (vertex μ 0) = _
    simp [vertex,mul]⟩
  left_inv x := by
    apply Subtype.ext
    have hx := x.property
    change mul μ (mul μ (vertex μ 1) x.val) (vertex μ 0) = x.val at hx
    simpa [vertex,mul] using hx
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def corner21Equiv : corner μ 2 1 ≃ₗ[k] W where
  toFun x := x.val.2.2.2.2.1
  invFun w := ⟨(0,0,0,0,w,0),by
    change mul μ (mul μ (vertex μ 2) (0,0,0,0,w,0)) (vertex μ 1) = _
    simp [vertex,mul]⟩
  left_inv x := by
    apply Subtype.ext
    have hx := x.property
    change mul μ (mul μ (vertex μ 2) x.val) (vertex μ 1) = x.val at hx
    simpa [vertex,mul] using hx
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def corner20Equiv : corner μ 2 0 ≃ₗ[k] U where
  toFun x := x.val.2.2.2.2.2
  invFun u := ⟨(0,0,0,0,0,u),by
    change mul μ (mul μ (vertex μ 2) (0,0,0,0,0,u)) (vertex μ 0) = _
    simp [vertex,mul]⟩
  left_inv x := by
    apply Subtype.ext
    have hx := x.property
    change mul μ (mul μ (vertex μ 2) x.val) (vertex μ 0) = x.val at hx
    simpa [vertex,mul] using hx
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- No path points backwards in the actual algebra. -/
theorem corner_zero_of_lt (i j : Fin 3) (hij : i < j) (x : corner μ i j) : x = 0 := by
  apply Subtype.ext
  have hx := x.property
  change (directedSystem μ).e i * x.val * (directedSystem μ).e j = x.val at hx
  rw [(directedSystem μ).directed j i hij x.val] at hx
  exact hx.symm
end LittleFinitistic.CornerSpaces

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_CornerTensor
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom _root_.OAI.LittleFinitistic.TensorComplex.mapRight_tmul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped TensorProduct

namespace LittleFinitistic.CornerTensor
open ThreeVertexAlgebra CornerSpaces CornerProjection TensorProjection
attribute [local instance] ExternalTensor.rightModule ExternalTensor.bimodule
universe u v
variable {k V W U : Type u} [Field k]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
  [AddCommGroup U] [Module k U]
variable (μ : W →ₗ[k] V →ₗ[k] U)
variable (N : Type v) [AddCommGroup N] [Module k N]
  [Module (ThreeVertexAlgebra μ)ᵐᵒᵖ N] [IsScalarTower k (ThreeVertexAlgebra μ)ᵐᵒᵖ N]

/-- Scalar tensor multiplication is right B-linear with the actual external action. -/
def scalarTensorEquiv : (k ⊗[k] N) ≃ₗ[(ThreeVertexAlgebra μ)ᵐᵒᵖ] N where
  __ := (TensorProduct.lid k N).toAddEquiv
  map_smul' c x := by
    induction x using OAI.tensorInductionOn with
    | tmul r n =>
      change r • (c • n) = c • (r • n)
      exact smul_comm r c n
    | add x y hx hy => simp_all [smul_add]

end LittleFinitistic.CornerTensor

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_VertexDecomposition
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
namespace LittleFinitistic.VertexDecomposition
universe u v
variable {k A : Type u} [Field k] [Ring A] [Algebra k A] {n : ℕ}
variable (D : DirectedBound.DirectedSystem k A n)
variable (M : Type v) [AddCommGroup M] [Module k M] [Module A M]
  [IsScalarTower k A M]

abbrev Space (i : Fin n) := IdempotentTensor.leftSpace (k := k) (D.e i) M

/-- Projection onto an actual vertex subspace. -/
def project (i : Fin n) : M →ₗ[k] Space D M i where
  toFun x := ⟨D.e i • x, by
    change D.e i • (D.e i • x) = D.e i • x
    rw [← mul_smul, D.idem]⟩
  map_add' x y := Subtype.ext (smul_add _ _ _)
  map_smul' c x := Subtype.ext (smul_comm _ _ _)

/-- A module decomposes into its actual vertex subspaces. This is a vector-space
isomorphism; off-diagonal arrows act between its factors. -/
def equiv : M ≃ₗ[k] ((i : Fin n) → Space D M i) where
  toFun x i := project D M i x
  invFun x := ∑ i, (x i).val
  map_add' x y := by funext i; exact (project D M i).map_add x y
  map_smul' c x := by funext i; exact (project D M i).map_smul c x
  left_inv x := by
    change ∑ i, D.e i • x = x
    rw [← Finset.sum_smul, D.complete, one_smul]
  right_inv x := by
    funext i
    apply Subtype.ext
    change D.e i • (∑ j, (x j).val) = (x i).val
    rw [Finset.smul_sum]
    rw [Finset.sum_eq_single i]
    · exact (x i).property
    · intro j _ hji
      rw [← (x j).property, ← mul_smul, D.orthogonal i j (Ne.symm hji), zero_smul]
    · simp

@[simp] theorem equiv_apply (x : M) (i : Fin n) :
    equiv D M x i = project D M i x := rfl

@[simp] theorem equiv_symm_apply (x : (i : Fin n) → Space D M i) :
    (equiv D M).symm x = ∑ i, (x i).val := rfl

lemma project_self (i : Fin n) (x : Space D M i) : project D M i x.val = x :=
  Subtype.ext x.property

lemma project_other (i j : Fin n) (hij : i ≠ j) (x : Space D M j) :
    project D M i x.val = 0 := by
  apply Subtype.ext
  change D.e i • x.val = 0
  rw [← x.property, ← mul_smul, D.orthogonal i j hij, zero_smul]
end LittleFinitistic.VertexDecomposition

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_VertexModuleAssembly
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
namespace LittleFinitistic.VertexModuleAssembly
open VertexDecomposition
universe u v w
variable {k A : Type u} [Field k] [Ring A] [Algebra k A] {n : ℕ}
variable (D : DirectedBound.DirectedSystem k A n)
variable {M : Type v} {N : Type w} [AddCommGroup M] [AddCommGroup N]
  [Module k M] [Module k N] [Module A M] [Module A N]
  [IsScalarTower k A M] [IsScalarTower k A N]
variable (E : ∀ i, Space D M i ≃ₗ[k] Space D N i)

/-- Assemble specified vertex isomorphisms into a vector-space isomorphism. -/
def assembled : M ≃ₗ[k] N :=
  (equiv D M).trans ((LinearEquiv.piCongrRight E).trans (equiv D N).symm)

lemma project_assembled (i : Fin n) (x : M) :
    project D N i (assembled D E x) = E i (project D M i x) := by
  exact congrFun ((equiv D N).apply_symm_apply
    ((LinearEquiv.piCongrRight E) (equiv D M x))) i

lemma assembled_vertex (i : Fin n) (x : Space D M i) :
    assembled D E x.val = (E i x).val := by
  apply (equiv D N).injective
  funext j
  rw [equiv_apply, project_assembled, equiv_apply]
  by_cases h : j = i
  · subst j
    rw [project_self, project_self]
  · rw [project_other D M j i h, project_other D N j i h, map_zero]

/-- The assembled map commutes with every vertex idempotent. -/
theorem vertex_smul (i : Fin n) (x : M) :
    assembled D E (D.e i • x) = D.e i • assembled D E x := by
  have h := assembled_vertex D E i (project D M i x)
  have hp := congrArg Subtype.val (project_assembled D E i x)
  exact h.trans hp.symm

/-- A supported arrow acts between its actual source and target subspaces. -/
def arrow {i j : Fin n} (a : A) (ha : D.e j * a = a) :
    Space D M i →ₗ[k] Space D M j where
  toFun x := ⟨a • x.val, by
    change D.e j • (a • x.val) = a • x.val
    rw [← mul_smul, ha]⟩
  map_add' x y := Subtype.ext (smul_add _ _ _)
  map_smul' c x := Subtype.ext (smul_comm _ _ _)

/-- Vertexwise compatibility with an actual arrow gives compatibility of the
assembled map on every element of the full module. -/
theorem arrow_smul {i j : Fin n} (a : A) (hl : D.e j * a = a) (hr : a * D.e i = a)
    (hE : ∀ x : Space D M i, E j (arrow D a hl x) = arrow D a hl (E i x))
    (x : M) : assembled D E (a • x) = a • assembled D E x := by
  have hax : a • (project D M i x).val = a • x := by
    change a • (D.e i • x) = a • x
    rw [← mul_smul, hr]
  have h := assembled_vertex D E j (arrow D a hl (project D M i x))
  change assembled D E (a • (project D M i x).val) =
    (E j (arrow D a hl (project D M i x))).val at h
  rw [hax, hE] at h
  have hp := congrArg Subtype.val (project_assembled D E i x)
  change D.e i • assembled D E x = (E i (project D M i x)).val at hp
  change assembled D E (a • x) = a • (E i (project D M i x)).val at h
  rw [← hp, ← mul_smul, hr] at h
  exact h
end LittleFinitistic.VertexModuleAssembly

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Tensor_IdempotentTensorMaps
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
namespace LittleFinitistic.IdempotentTensor
universe u v w
variable {A : Type v} [Ring A] {e e' : A}

/-- eA is a retract of the rank-one free right A-module. -/
def splitProjection (he : e*e=e) : Aᵐᵒᵖ →ₗ[Aᵐᵒᵖ] rightIdeal e where
  toFun a := ⟨e*a.unop, by change e*(e*a.unop)=e*a.unop; rw [← mul_assoc,he]⟩
  map_add' a b := Subtype.ext (mul_add e a.unop b.unop)
  map_smul' a b := by apply Subtype.ext; exact (mul_assoc e b.unop a.unop).symm

def splitInclusion : rightIdeal e →ₗ[Aᵐᵒᵖ] Aᵐᵒᵖ where
  toFun a := MulOpposite.op a.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem rightIdeal_projective (he : e*e=e) : Module.Projective Aᵐᵒᵖ (rightIdeal e) := by
  apply Module.Projective.of_split splitInclusion (splitProjection he)
  ext a
  exact a.property
end LittleFinitistic.IdempotentTensor

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Selected_SelectedTargetHomology
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
namespace LittleFinitistic.SelectedTargetHomology
open QuadraticEncoding FiniteProjectiveHomotopy
universe v
variable {Y : Type v}
  [AddCommGroup Y]
  [Module ℂ Y]
  [FiniteDimensional ℂ Y]
instance instPreservesBinaryBiproductsFullSubcategoryDerivedCategoryModuleCatComplexEssImageKDerivedEmbeddingCCohomology (n : ℤ) : PreservesBinaryBiproducts (cohomology.{v} n) :=
  preservesBinaryBiproducts_of_preservesBiproducts _

end LittleFinitistic.SelectedTargetHomology

end

end OAI
end


