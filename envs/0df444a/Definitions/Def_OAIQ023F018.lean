-- Prove2me | Definitions.Def_OAIQ023F018
-- name    : OAIQ023F018
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T16:07:43.039778+00:00
-- url     : https://prove2.me/theorems/e0041470-01b8-4b69-b540-f04cbb2fffa8
-- title:
--   Definitions bundle OAIQ023F018 of the split of OpenAI, An algebra of infinite little finitistic dimension (result family 198)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.LittleFinitistic.Main.exists_counterexample`, carved from OpenAI's openai/math development (OpenAI, *An algebra of infinite little finitistic dimension (result family 198)*, OpenAI Math Release, September 23, 2026, result family 198, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 76 declarations of OpenAI's Lean: 36 definitions, 2 inductive types or structures and 38 theorems. The definitions and types are `OAI.LittleFinitistic.BimoduleComplexTensor.derivedTotal`, `OAI.LittleFinitistic.BimoduleComplexTensor.derivedTotalComparison`, `OAI.LittleFinitistic.BimoduleComplexTensor.forgetTermIso`, `OAI.LittleFinitistic.BimoduleComplexTensor.forgetTotal`, `OAI.LittleFinitistic.BimoduleComplexTensor.forgetTotalIso`, `OAI.LittleFinitistic.BimoduleComplexTensor.rightTermEquiv`, `OAI.LittleFinitistic.BimoduleComplexTensor.rightTotalEquiv`, `OAI.LittleFinitistic.BimoduleComplexTensor.total`, `OAI.LittleFinitistic.BimoduleComplexTensor.totalAssociativityIso`, `OAI.LittleFinitistic.BimoduleComplexTensor.totalFunctor`, `OAI.LittleFinitistic.BimoduleComplexTensor.totalMap`, `OAI.LittleFinitistic.BimoduleComplexTensor.totalRightIso`, `OAI.LittleFinitistic.BimoduleTensorVertexBridge.comparison`, `OAI.LittleFinitistic.BimoduleTensorVertexBridge.equiv`, `OAI.LittleFinitistic.BimoduleTotal.AugmentedProjective`, `OAI.LittleFinitistic.BimoduleTotal.AugmentedProjective.tensorAugmentation`, `OAI.LittleFinitistic.BimoduleTotal.BoundedProjective`, `OAI.LittleFinitistic.BimoduleTotal.BoundedProjective.degrees`, `OAI.LittleFinitistic.BimoduleTotal.actualBarFunctor`, `OAI.LittleFinitistic.BimoduleTotal.barModule`, `OAI.LittleFinitistic.BimoduleTotal.bimoduleStalk`, `OAI.LittleFinitistic.BimoduleTotal.coefficient`, `OAI.LittleFinitistic.BimoduleTotal.entryBetween`, `OAI.LittleFinitistic.BimoduleTotal.functor`, `OAI.LittleFinitistic.BimoduleTotal.horizontalBetween`, `OAI.LittleFinitistic.BimoduleTotal.leftTensorNat`, `OAI.LittleFinitistic.BimoduleTotal.leftTermMap`, `OAI.LittleFinitistic.BimoduleTotal.leftTotalMap`, `OAI.LittleFinitistic.BimoduleTotal.leftTotalMapF`, `OAI.LittleFinitistic.BimoduleTotal.moduleEvaluation`, `OAI.LittleFinitistic.BimoduleTotal.right`, `OAI.LittleFinitistic.BimoduleTotal.singleTermIso`, `OAI.LittleFinitistic.BimoduleTotal.tensorAcross`, `OAI.LittleFinitistic.BimoduleTotal.termMap`, `OAI.LittleFinitistic.BimoduleTotal.total`, `OAI.LittleFinitistic.BimoduleTotal.totalMap`, `OAI.LittleFinitistic.BimoduleTotal.vectorTotal`, `OAI.LittleFinitistic.ComplexTensor.finiteTotalFunctor`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: `Finitistic_Bimodule_BimoduleAugmentedResolution`, `Finitistic_Bimodule_BimoduleBarComparisonMap`, `Finitistic_Bimodule_BimoduleDerivedInterval`, `Finitistic_Bimodule_BimoduleLeftNaturality`, `Finitistic_Bimodule_BimoduleLeftTotalMap`, `Finitistic_Bimodule_BimoduleSingleTerms`, `Finitistic_Bimodule_BimoduleTensorAcross`, `Finitistic_Bimodule_BimoduleTensorVertexBridge`, `Finitistic_Bimodule_BimoduleTotalCoefficient`, `Finitistic_Bimodule_BimoduleTotalDifferential`, `Finitistic_Bimodule_BimoduleTotalFunctor`, `Finitistic_Bimodule_BimoduleTotalTermMaps`, `Finitistic_Bimodule_BimoduleTotalTerms`, `Finitistic_Bimodule_BoundedBimoduleDerived`, `Finitistic_Ordinary_OrdinaryBimoduleCoefficientEquiv`, `Finitistic_Ordinary_OrdinaryBimoduleDerivedTensor`, `Finitistic_Ordinary_OrdinaryBimoduleTensorTotal`, `Finitistic_Ordinary_OrdinaryBimoduleTotalAssociativity`, `Finitistic_Ordinary_OrdinaryBimoduleTotalCongruence`, `Finitistic_Ordinary_OrdinaryBimoduleTotalForget`, `Finitistic_Ordinary_OrdinaryBimoduleTotalFunctor`, `Finitistic_Ordinary_OrdinaryBimoduleTotalMaps`, `Finitistic_Ordinary_OrdinaryTensorTotalFunctor`, `Finitistic_Rectification_ColumnFinite`, `Finitistic_Rectification_ColumnProperties`.
--
--   **Imports.** It imports the bundles `OAIQ023F011` and `OAIQ023F012` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ023F022`, `OAIQ023F023` and `OAIQ023F024`.
-- source:
--   OpenAI, An algebra of infinite little finitistic dimension (result family 198), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 198; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-algebra-of-infinite-little-finitistic-dimension-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ023F011
import Definitions.Def_OAIQ023F012

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_ColumnProperties
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.ExternalTensor.Section4.SourceFiltration.inclusion2_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroCone_inclusion_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroTermSubsingleton _root_.OAI.ExternalTensor.Section4.forgetK_additive _root_.OAI.LittleFinitistic.BalancedVertexFunctor.additive _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.additive _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.finite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.scalarTower _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticPresentation.instFiniteAuxiliaryEquation _root_.OAI.LittleFinitistic.QuadraticPresentation.instFiniteAuxiliaryLetter _root_.OAI.LittleFinitistic.QuadraticPresentation.step_finite _root_.OAI.LittleFinitistic.QuadraticPresentation.word_finite _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated _root_.OAI.LittleFinitistic.cyclicRing_finiteInst
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

theorem sum_right_projective {I : Type} [Fintype I] (K : I → BiComplex k B)
    (n : ℤ) (hK : ∀ i, Projective ((termRight k B n).obj (K i))) :
    Projective ((termRight k B n).obj (⨁ K)) := by
  let (i : I) : Projective ((termRight k B n).obj (K i)) := hK i
  apply Projective.of_iso ((termRight k B n).mapBiproduct K).symm
  refine ⟨fun f e _ => ⟨biproduct.desc (fun i => by
    letI : Projective (((termRight k B n).obj ∘ K) i) := hK i
    exact Projective.factorThru (biproduct.ι ((termRight k B n).obj ∘ K) i ≫ f) e), ?_⟩⟩
  apply biproduct.hom_ext'
  intro i
  let : Projective (((termRight k B n).obj ∘ K) i) := hK i
  simp only [biproduct.ι_desc_assoc, Projective.factorThru_comp]

variable {k B}
variable {A J R : Type} [Fintype A] [Fintype J] [Fintype R]
variable (s : Quadratic k B (A := A) (J := J) (R := R))
variable (D₀ D₁ D₂ : RightComplex B)
variable (f : A → (D₀ ⟶ D₁)) (g : J → (D₁ ⟶ D₂))

theorem columns_isZero (n : ℤ) (h₀ : IsZero (D₀.X n))
    (h₁ : IsZero (D₁.X n)) (h₂ : IsZero (D₂.X n)) :
    IsZero ((L0Prime s D₀ D₁ D₂ f g).X n) ∧
    IsZero ((L1Prime s D₀ D₁ D₂ f g).X n) ∧
    IsZero ((L2Prime s D₀ D₁ D₂ f g).X n) := by
  refine ⟨?_, ?_, ?_⟩
  · apply biprod_term_isZero
    · exact column_isZero k B s.e₀ D₀ n h₀
    · apply biprod_term_isZero
      · exact column_isZero k B s.e₁ D₁ n h₁
      · exact column_isZero k B s.e₂ D₂ n h₂
  · apply biprod_term_isZero
    · apply sum_term_isZero
      intro a
      exact column_isZero k B s.e₁ D₀ n h₀
    · apply sum_term_isZero
      intro b
      exact column_isZero k B s.e₂ D₁ n h₁
  · apply sum_term_isZero
    intro r
    exact column_isZero k B s.e₂ D₀ n h₀

/-- Uniform bounds on the input complexes give the same bounds on all three columns. -/
theorem columns_bounded (lo hi : ℤ)
    (h₀ : ∀ n, n < lo ∨ hi < n → IsZero (D₀.X n))
    (h₁ : ∀ n, n < lo ∨ hi < n → IsZero (D₁.X n))
    (h₂ : ∀ n, n < lo ∨ hi < n → IsZero (D₂.X n)) :
    ∀ n, n < lo ∨ hi < n →
      IsZero ((L0Prime s D₀ D₁ D₂ f g).X n) ∧
      IsZero ((L1Prime s D₀ D₁ D₂ f g).X n) ∧
      IsZero ((L2Prime s D₀ D₁ D₂ f g).X n) :=
  fun n hn => columns_isZero s D₀ D₁ D₂ f g n (h₀ n hn) (h₁ n hn) (h₂ n hn)
end ExternalTensor.Section4

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryTensorTotalFunctor
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BalancedTensor.tensorFinite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.finite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.scalarTower _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic
namespace ComplexTensor
open BalancedTensor
universe u
variable (k A : Type u) [Field k] [Ring A] [Algebra k A]
variable (Q : CochainComplex (ModuleCat.{u} Aᵐᵒᵖ) ℤ)
variable {Z Z' Z'' : CochainComplex (ModuleCat.{u} A) ℤ}
variable {l : ℕ} (p : Fin l → ℤ) (hp : StrictMono p)

/-- The actual signed finite tensor total is a functor on all input complexes. -/
def finiteTotalFunctor : CochainComplex (ModuleCat.{u} A) ℤ ⥤ CochainComplex (ModuleCat.{u} k) ℤ where
  obj Z := finiteTotal k A Q Z p hp
  map f := finiteTotalMap k A Q p hp f
  map_id Z := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    funext i
    change ((finiteTotalMap k A Q p hp (𝟙 Z)).f n).hom z i = z i
    erw [finiteTotalMap_apply,inputMap_id,LinearMap.id_apply]
  map_comp f g := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    funext i
    change ((finiteTotalMap k A Q p hp (f ≫ g)).f n).hom z i =
      ((finiteTotalMap k A Q p hp g).f n).hom (((finiteTotalMap k A Q p hp f).f n).hom z) i
    erw [finiteTotalMap_apply,finiteTotalMap_apply,finiteTotalMap_apply]
    exact (congrArg (fun h => h (z i)) (inputMap_comp k A Q f g (p i) (n + -(p i)))).symm
end ComplexTensor
end LittleFinitistic

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bimodule_BimoduleTotalTerms
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.Multibar.patternTower _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.DerivedBar.termTower _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.ExternalTensor.Section4.SourceFiltration.inclusion2_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroCone_inclusion_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroTermSubsingleton _root_.OAI.ExternalTensor.Section4.forgetK_additive _root_.OAI.LittleFinitistic.BalancedTensor.tensorFinite _root_.OAI.LittleFinitistic.BalancedVertexFunctor.additive _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleCoefficients.towerLeft _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDTensor.scalarModuleTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace LittleFinitistic.BimoduleTotal
open ExternalTensor.Section4
attribute [local instance] BimoduleBalancedTensor.inputEnveloping
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B]

abbrev right (P : BiComplex k B) : RightComplex B :=
  ((forgetRight k B).mapHomologicalComplex (.up ℤ)).obj P

variable {k B}
variable {P : BiComplex k B} {Z Z' : CochainComplex (ModuleCat.{u} B) ℤ}
variable {p p' q q' : ℤ}

/-- Balanced tensor maps retain the original outside left B action. -/
theorem bimap_smul (f : P.X p ⟶ P.X p') (g : Z.X q ⟶ Z'.X q')
    (b : B) (x : Term k B P Z p q) :
    @BalancedTensor.bimap k B
      (ComplexTensor.rightTerm k B (right k B P) p)
      (ComplexTensor.rightTerm k B (right k B P) p')
      (ComplexTensor.leftTerm k B Z q) (ComplexTensor.leftTerm k B Z' q') _ _ _
      _ _ _ (BalancedTensor.scalarLeftTower k Bᵐᵒᵖ ((right k B P).X p))
      _ _ _ (BalancedTensor.scalarLeftTower k Bᵐᵒᵖ ((right k B P).X p'))
      _ _ _ (BalancedTensor.scalarLeftTower k B (Z.X q))
      _ _ _ (BalancedTensor.scalarLeftTower k B (Z'.X q'))
      ((forgetRight k B).map f).hom g.hom (b • x) =
    b • (show Term k B P Z' p' q' from @BalancedTensor.bimap k B
      (ComplexTensor.rightTerm k B (right k B P) p)
      (ComplexTensor.rightTerm k B (right k B P) p')
      (ComplexTensor.leftTerm k B Z q) (ComplexTensor.leftTerm k B Z' q') _ _ _
      _ _ _ (BalancedTensor.scalarLeftTower k Bᵐᵒᵖ ((right k B P).X p))
      _ _ _ (BalancedTensor.scalarLeftTower k Bᵐᵒᵖ ((right k B P).X p'))
      _ _ _ (BalancedTensor.scalarLeftTower k B (Z.X q))
      _ _ _ (BalancedTensor.scalarLeftTower k B (Z'.X q'))
      ((forgetRight k B).map f).hom g.hom x) := by
  induction x using BalancedTensor.induction_on with
  | hz =>
    rw [smul_zero]
    exact (map_zero _).trans
      ((congrArg (fun y : Term k B P Z' p' q' => b • y) (map_zero _)).trans
        (smul_zero b : b • (0 : Term k B P Z' p' q') = 0)).symm
  | ht m n =>
    change BalancedTensor.mk k B (BimoduleBalancedTensor.Input k B (P.X p'))
      (ComplexTensor.leftTerm k B Z' q') (f.hom ((b ⊗ₜ[k] (1 : Bᵐᵒᵖ)) • (m : P.X p))) (g.hom n) =
      BalancedTensor.mk k B (BimoduleBalancedTensor.Input k B (P.X p'))
        (ComplexTensor.leftTerm k B Z' q') ((b ⊗ₜ[k] (1 : Bᵐᵒᵖ)) • (f.hom m : P.X p')) (g.hom n)
    exact congrArg (fun m' => BalancedTensor.mk k B (BimoduleBalancedTensor.Input k B (P.X p'))
      (ComplexTensor.leftTerm k B Z' q') m' (g.hom n))
      (f.hom.map_smul (b ⊗ₜ[k] (1 : Bᵐᵒᵖ)) (m : P.X p))
  | ha x y hx hy =>
    rw [smul_add]
    exact (map_add _ _ _).trans ((congrArg₂ (· + ·) hx hy).trans
      ((smul_add b (show Term k B P Z' p' q' from _)
        (show Term k B P Z' p' q' from _)).symm.trans
          (congrArg (fun y : Term k B P Z' p' q' => b • y) (map_add _ _ _).symm)))

variable (k B P Z)

theorem horizontal_smul (n p p' : ℤ) (h : p+1=p') (b : B)
    (x : Term k B P Z p (n + -p)) :
    ComplexTensor.horizontal k B (right k B P) Z n p p' h (b • x) =
      b • (show Term k B P Z p' ((n+1) + -p') from
        ComplexTensor.horizontal k B (right k B P) Z n p p' h x) :=
  bimap_smul (P.d p p') (eqToHom (congrArg Z.X (show n + -p = (n+1) + -p' by omega))) b x

theorem column_d_smul (p n m : ℤ) (b : B)
    (x : Term k B P Z p (n + -p)) :
    ((ComplexTensor.column k B (right k B P) Z p).d n m).hom (b • x) =
      b • (show Term k B P Z p (m + -p) from
        ((ComplexTensor.column k B (right k B P) Z p).d n m).hom x) := by
  rw [ComplexTensor.column_d]
  change (-p).negOnePow • (ComplexTensor.map k B (right k B P) Z (𝟙 _) (Z.d _ _) (b • x)) =
    b • ((-p).negOnePow • (show Term k B P Z p (m + -p) from
      ComplexTensor.map k B (right k B P) Z (𝟙 _) (Z.d _ _) x))
  rw [show ComplexTensor.map k B (right k B P) Z (𝟙 _) (Z.d _ _) (b • x) =
    b • (show Term k B P Z p (m + -p) from
      ComplexTensor.map k B (right k B P) Z (𝟙 _) (Z.d _ _) x) from
      bimap_smul (𝟙 (P.X p)) (Z.d _ _) b x]
  erw [Units.smul_def, Units.smul_def]
  exact ((DistribSMul.toAddMonoidHom (Term k B P Z p (m + -p)) b).map_zsmul _ _).symm

variable {Z}
theorem inputMap_smul (f : Z ⟶ Z') (p q : ℤ) (b : B) (x : Term k B P Z p q) :
    ComplexTensor.inputMap k B (right k B P) f p q (b • x) =
      b • (show Term k B P Z' p q from ComplexTensor.inputMap k B (right k B P) f p q x) :=
  bimap_smul (𝟙 (P.X p)) (f.f q) b x
end LittleFinitistic.BimoduleTotal

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bimodule_BimoduleTotalTermMaps
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.Multibar.patternTower _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.DerivedBar.termTower _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.ExternalTensor.Section4.SourceFiltration.inclusion2_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroCone_inclusion_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroTermSubsingleton _root_.OAI.ExternalTensor.Section4.forgetK_additive _root_.OAI.LittleFinitistic.BalancedTensor.tensorFinite _root_.OAI.LittleFinitistic.BalancedVertexFunctor.additive _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleCoefficients.towerLeft _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDTensor.scalarModuleTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.ArrowVertex.arrow_id _root_.OAI.ExternalTensor.Section4.ArrowVertex.arrow_original _root_.OAI.ExternalTensor.Section4.ArrowVertex.iota_original _root_.OAI.ExternalTensor.Section4.ArrowVertex.left_mul _root_.OAI.ExternalTensor.Section4.ArrowVertex.map_left _root_.OAI.ExternalTensor.Section4.ArrowVertex.mem_space _root_.OAI.LittleFinitistic.BalancedAssociativity.forwardAt_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.forward_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.inverseAt_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.inverse_mk _root_.OAI.LittleFinitistic.BalancedTensor.FreeLeft.evaluation_single _root_.OAI.LittleFinitistic.BalancedTensor.FreeLeft.insertion_single _root_.OAI.LittleFinitistic.BalancedTensor.bimoduleAction_tmul_mk _root_.OAI.LittleFinitistic.BalancedTensor.leftAction_mk _root_.OAI.LittleFinitistic.BalancedTensor.mapRight_mk _root_.OAI.LittleFinitistic.BalancedTensor.rightAction_mk _root_.OAI.LittleFinitistic.BalancedTensor.tensorFunctorEquiv_mk _root_.OAI.LittleFinitistic.BalancedVertexImage.equiv_apply_val
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
variable {k B : Type u} [Field k] [Ring B] [Algebra k B]
variable {P : BiComplex k B} {Z Z' Z'' : CochainComplex (ModuleCat.{u} B) ℤ}
variable {p p' p'' q q' q'' : ℤ}

def termMap (f : P.X p ⟶ P.X p') (g : Z.X q ⟶ Z'.X q') :
    Term k B P Z p q →ₗ[B] Term k B P Z' p' q' where
  __ := (@BalancedTensor.bimap k B
    (ComplexTensor.rightTerm k B (right k B P) p)
    (ComplexTensor.rightTerm k B (right k B P) p')
    (ComplexTensor.leftTerm k B Z q) (ComplexTensor.leftTerm k B Z' q') _ _ _
    _ _ _ (BalancedTensor.scalarLeftTower k Bᵐᵒᵖ ((right k B P).X p))
    _ _ _ (BalancedTensor.scalarLeftTower k Bᵐᵒᵖ ((right k B P).X p'))
    _ _ _ (BalancedTensor.scalarLeftTower k B (Z.X q))
    _ _ _ (BalancedTensor.scalarLeftTower k B (Z'.X q'))
    ((forgetRight k B).map f).hom g.hom).toAddMonoidHom
  map_smul' := bimap_smul f g

@[simp] theorem termMap_comp
    (f : P.X p ⟶ P.X p') (f' : P.X p' ⟶ P.X p'')
    (g : Z.X q ⟶ Z'.X q') (g' : Z'.X q' ⟶ Z''.X q'') :
    (termMap f' g').comp (termMap f g) = termMap (f ≫ f') (g ≫ g') := by
  apply LinearMap.ext
  intro x
  induction x using BalancedTensor.induction_on with
  | hz => simp
  | ht m n => rfl
  | ha x y hx hy =>
    exact (map_add _ _ _).trans
      ((congrArg₂ (· + ·) hx hy).trans (map_add _ _ _).symm)


@[simp] theorem termMap_id : termMap (𝟙 (P.X p)) (𝟙 (Z.X q)) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  induction x using BalancedTensor.induction_on with
  | hz => simp
  | ht m n => rfl
  | ha x y hx hy =>
    exact (map_add _ _ _).trans
      ((congrArg₂ (· + ·) hx hy).trans (map_add _ _ _).symm)

end LittleFinitistic.BimoduleTotal

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bimodule_BimoduleTensorAcross
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.ExternalTensor.Section4.SourceFiltration.inclusion2_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroCone_inclusion_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroTermSubsingleton _root_.OAI.ExternalTensor.Section4.forgetK_additive _root_.OAI.LittleFinitistic.BalancedTensor.tensorFinite _root_.OAI.LittleFinitistic.BalancedVertexFunctor.additive _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.ArrowVertex.arrow_id _root_.OAI.ExternalTensor.Section4.ArrowVertex.arrow_original _root_.OAI.ExternalTensor.Section4.ArrowVertex.iota_original _root_.OAI.ExternalTensor.Section4.ArrowVertex.left_mul _root_.OAI.ExternalTensor.Section4.ArrowVertex.map_left _root_.OAI.ExternalTensor.Section4.ArrowVertex.mem_space _root_.OAI.LittleFinitistic.BalancedAssociativity.forwardAt_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.forward_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.inverseAt_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.inverse_mk _root_.OAI.LittleFinitistic.BalancedTensor.FreeLeft.evaluation_single _root_.OAI.LittleFinitistic.BalancedTensor.FreeLeft.insertion_single _root_.OAI.LittleFinitistic.BalancedTensor.bimoduleAction_tmul_mk _root_.OAI.LittleFinitistic.BalancedTensor.leftAction_mk _root_.OAI.LittleFinitistic.BalancedTensor.mapRight_mk _root_.OAI.LittleFinitistic.BalancedTensor.rightAction_mk _root_.OAI.LittleFinitistic.BalancedTensor.tensorFunctorEquiv_mk _root_.OAI.LittleFinitistic.BalancedVertexImage.equiv_apply_val
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
variable {k B : Type u} [Field k] [Ring B] [Algebra k B]
variable {M M' M'' : ModuleCat.{u} (Enveloping k B)}
variable {N N' N'' : ModuleCat.{u} B}

/-- Tensor a bimodule map and an input map, retaining the outside B-action. -/
def tensorAcross (f : M ⟶ M') (g : N ⟶ N') :
    InputTensor k B M N →ₗ[B] InputTensor k B M' N' :=
  ((BimoduleBalancedTensor.functor k B (BalancedTensor.ScalarLeftModule k B N')).map f).hom.comp
    (inputModuleMap k B M g)

@[simp] theorem tensorAcross_mk (f : M ⟶ M') (g : N ⟶ N')
    (m : BimoduleBalancedTensor.Input k B M) (n : BalancedTensor.ScalarLeftModule k B N) :
    tensorAcross f g (BalancedTensor.mk k B _ _ m n) =
      BalancedTensor.mk k B (BimoduleBalancedTensor.Input k B M')
        (BalancedTensor.ScalarLeftModule k B N') (f.hom m) (g.hom n) := rfl

@[simp] theorem tensorAcross_comp (f : M ⟶ M') (f' : M' ⟶ M'')
    (g : N ⟶ N') (g' : N' ⟶ N'') :
    (tensorAcross f' g').comp (tensorAcross f g) = tensorAcross (f ≫ f') (g ≫ g') := by
  apply LinearMap.ext
  intro x
  induction x using BalancedTensor.induction_on with
  | hz => simp
  | ht m n => rfl
  | ha x y hx hy =>
    exact (map_add _ _ _).trans
      ((congrArg₂ (· + ·) hx hy).trans (map_add _ _ _).symm)

@[simp] theorem tensorAcross_id :
    tensorAcross (𝟙 M) (𝟙 N) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  induction x using BalancedTensor.induction_on with
  | hz => simp
  | ht m n => rfl
  | ha x y hx hy =>
    exact (map_add _ _ _).trans
      ((congrArg₂ (· + ·) hx hy).trans (map_add _ _ _).symm)

@[simp] theorem tensorAcross_zero_left (g : N ⟶ N') :
    tensorAcross (0 : M ⟶ M') g = 0 := by
  apply LinearMap.ext
  intro x
  induction x using BalancedTensor.induction_on with
  | hz => simp
  | ht m n =>
    exact LinearMap.congr_fun ((BalancedTensor.mk k B (BimoduleBalancedTensor.Input k B M')
      (BalancedTensor.ScalarLeftModule k B N')).map_zero) (g.hom n)
  | ha x y hx hy =>
    exact (map_add _ _ _).trans
      ((congrArg₂ (· + ·) hx hy).trans (map_add _ _ _).symm)

@[simp] theorem tensorAcross_zero_right (f : M ⟶ M') :
    tensorAcross f (0 : N ⟶ N') = 0 := by
  apply LinearMap.ext
  intro x
  induction x using BalancedTensor.induction_on with
  | hz => simp
  | ht m n =>
    exact (BalancedTensor.mk k B (BimoduleBalancedTensor.Input k B M')
      (BalancedTensor.ScalarLeftModule k B N') (f.hom m)).map_zero
  | ha x y hx hy =>
    exact (map_add _ _ _).trans
      ((congrArg₂ (· + ·) hx hy).trans (map_add _ _ _).symm)

variable {P : BiComplex k B} {Z Z' : CochainComplex (ModuleCat.{u} B) ℤ}
variable {a b q r : ℤ}

theorem tensorAcross_eq_termMap (f : P.X a ⟶ P.X b) (g : Z.X q ⟶ Z'.X r) :
    tensorAcross f g = termMap f g := by
  apply LinearMap.ext
  intro x
  induction x using BalancedTensor.induction_on with
  | hz => simp
  | ht m n => rfl
  | ha x y hx hy =>
    exact (map_add _ _ _).trans
      ((congrArg₂ (· + ·) hx hy).trans (map_add _ _ _).symm)
end LittleFinitistic.BimoduleTotal

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bimodule_BimoduleTotalFunctor
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.ExternalTensor.Section4.SourceFiltration.inclusion2_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroCone_inclusion_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroTermSubsingleton _root_.OAI.ExternalTensor.Section4.forgetK_additive _root_.OAI.LittleFinitistic.BalancedTensor.tensorFinite _root_.OAI.LittleFinitistic.BalancedVertexFunctor.additive _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.ArrowVertex.arrow_id _root_.OAI.ExternalTensor.Section4.ArrowVertex.arrow_original _root_.OAI.ExternalTensor.Section4.ArrowVertex.iota_original _root_.OAI.ExternalTensor.Section4.ArrowVertex.left_mul _root_.OAI.ExternalTensor.Section4.ArrowVertex.map_left _root_.OAI.ExternalTensor.Section4.ArrowVertex.mem_space _root_.OAI.LittleFinitistic.BalancedAssociativity.forwardAt_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.forward_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.inverseAt_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.inverse_mk _root_.OAI.LittleFinitistic.BalancedTensor.FreeLeft.evaluation_single _root_.OAI.LittleFinitistic.BalancedTensor.FreeLeft.insertion_single _root_.OAI.LittleFinitistic.BalancedTensor.bimoduleAction_tmul_mk _root_.OAI.LittleFinitistic.BalancedTensor.leftAction_mk _root_.OAI.LittleFinitistic.BalancedTensor.mapRight_mk _root_.OAI.LittleFinitistic.BalancedTensor.rightAction_mk _root_.OAI.LittleFinitistic.BalancedTensor.tensorFunctorEquiv_mk _root_.OAI.LittleFinitistic.BalancedVertexImage.equiv_apply_val _root_.OAI.LittleFinitistic.BimoduleTotal.tensorAcross_comp _root_.OAI.LittleFinitistic.BimoduleTotal.tensorAcross_id _root_.OAI.LittleFinitistic.BimoduleTotal.tensorAcross_mk _root_.OAI.LittleFinitistic.BimoduleTotal.tensorAcross_zero_left _root_.OAI.LittleFinitistic.BimoduleTotal.tensorAcross_zero_right _root_.OAI.LittleFinitistic.BimoduleTotal.termMap_comp _root_.OAI.LittleFinitistic.BimoduleTotal.termMap_id
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

abbrev vectorTotal := ComplexTensor.finiteTotal k B (right k B P) Z p hp

theorem matrix_smul (n : ℤ) (b : B) (x : TotalTerm k B P p Z n) :
    ComplexTensor.matrix k B (right k B P) Z p n (b • x) =
      b • (show TotalTerm k B P p Z (n+1) from
        ComplexTensor.matrix k B (right k B P) Z p n x) := by
  funext j
  change ComplexTensor.matrix k B (right k B P) Z p n (b • x) j =
    b • (show Term k B P Z (p j) ((n+1) + -(p j)) from
      ComplexTensor.matrix k B (right k B P) Z p n x j)
  erw [ComplexTensor.matrix_apply, ComplexTensor.matrix_apply]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  unfold ComplexTensor.entry
  split_ifs with h
  · exact horizontal_smul k B P Z n (p i) (p j) h b (x i)
  · simp
    rfl

theorem differential_smul (n m : ℤ) (b : B) (x : TotalTerm k B P p Z n) :
    ((vectorTotal k B P p hp Z).d n m).hom (b • x) =
      b • (show TotalTerm k B P p Z m from ((vectorTotal k B P p hp Z).d n m).hom x) := by
  by_cases h : n+1=m
  · subst m
    simp only [vectorTotal, ComplexTensor.finiteTotal, FiniteColumnComplex.total,
      FiniteColumnComplex.complex_d_hom]
    change (FiniteColumnComplex.diagonal _ n (b • x) +
      ComplexTensor.matrix k B (right k B P) Z p n (b • x)) =
      b • (show TotalTerm k B P p Z (n+1) from
        FiniteColumnComplex.diagonal _ n x + ComplexTensor.matrix k B (right k B P) Z p n x)
    funext i
    exact (congrArg₂ HAdd.hAdd
      (column_d_smul k B P Z (p i) n (n+1) b (x i))
      (congrFun (matrix_smul k B P p Z n b x) i)).trans
      (smul_add b
        (show Term k B P Z (p i) ((n+1) + -(p i)) from
          ((ComplexTensor.column k B (right k B P) Z (p i)).d n (n+1)).hom (x i))
        (show Term k B P Z (p i) ((n+1) + -(p i)) from
          ComplexTensor.matrix k B (right k B P) Z p n x i)).symm
  · have hz := (vectorTotal k B P p hp Z).shape n m h
    rw [hz]
    change (0 : TotalTerm k B P p Z m) = b • (0 : TotalTerm k B P p Z m)
    funext i
    exact (smul_zero b : b • (0 : Term k B P Z (p i) (m + -(p i))) = 0).symm

/-- The same signed finite tensor total, retaining the full left B action. -/
def total : CochainComplex (ModuleCat.{u} B) ℤ where
  X n := ModuleCat.of B (TotalTerm k B P p Z n)
  d n m := ModuleCat.ofHom
    { __ := ((vectorTotal k B P p hp Z).d n m).hom.toAddMonoidHom
      map_smul' := differential_smul k B P p hp Z n m }
  shape n m h := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact congrArg (fun f => f.hom x) ((vectorTotal k B P p hp Z).shape n m h)
  d_comp_d' n m t _ _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact congrArg (fun f => f.hom x) ((vectorTotal k B P p hp Z).d_comp_d n m t)

variable {Z} {Z' Z'' : CochainComplex (ModuleCat.{u} B) ℤ}

/-- The original input tensor map is B-linear in every degree. -/
def totalMap (f : Z ⟶ Z') : total k B P p hp Z ⟶ total k B P p hp Z' where
  f n := ModuleCat.ofHom
    { __ := ((ComplexTensor.finiteTotalMap k B (right k B P) p hp f).f n).hom.toAddMonoidHom
      map_smul' := by
        intro b x
        funext i
        change ((ComplexTensor.finiteTotalMap k B (right k B P) p hp f).f n).hom (b • x) i =
          b • (show Term k B P Z' (p i) (n + -(p i)) from
            ((ComplexTensor.finiteTotalMap k B (right k B P) p hp f).f n).hom x i)
        erw [ComplexTensor.finiteTotalMap_apply,ComplexTensor.finiteTotalMap_apply]
        exact inputMap_smul k B P f (p i) (n + -(p i)) b (x i) }
  comm' n m _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact congrArg (fun g => g.hom x)
      ((ComplexTensor.finiteTotalMap k B (right k B P) p hp f).comm n m)

/-- Tensoring with the fixed bimodule complex acts on every left-module complex. -/
def functor : CochainComplex (ModuleCat.{u} B) ℤ ⥤ CochainComplex (ModuleCat.{u} B) ℤ where
  obj Z := total k B P p hp Z
  map f := totalMap k B P p hp f
  map_id Z := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact congrArg (fun f => (f.f n).hom x)
      ((ComplexTensor.finiteTotalFunctor k B (right k B P) p hp).map_id Z)
  map_comp f g := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact congrArg (fun f => (f.f n).hom x)
      ((ComplexTensor.finiteTotalFunctor k B (right k B P) p hp).map_comp f g)

end LittleFinitistic.BimoduleTotal

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bimodule_BimoduleTotalDifferential
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.ExternalTensor.Section4.SourceFiltration.inclusion2_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroCone_inclusion_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroTermSubsingleton _root_.OAI.ExternalTensor.Section4.forgetK_additive _root_.OAI.LittleFinitistic.BalancedTensor.tensorFinite _root_.OAI.LittleFinitistic.BalancedVertexFunctor.additive _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
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

def horizontalBetween (n m a b : ℤ) (h : n+1=m) (hab : a+1=b) :
    Term k B P Z a (n + -a) →ₗ[B] Term k B P Z b (m + -b) :=
  termMap (P.d a b) (eqToHom (congrArg Z.X (show n + -a = m + -b by omega)))

def entryBetween (n m a b : ℤ) (h : n+1=m) :
    Term k B P Z a (n + -a) →ₗ[B] Term k B P Z b (m + -b) :=
  if hab : a+1=b then horizontalBetween k B P Z n m a b h hab else 0

variable {l : ℕ} (p : Fin l → ℤ) (hp : StrictMono p)

/-- The exact differential of the B-valued total, in arbitrary consecutive total degrees. -/
theorem total_d_apply (n m : ℤ) (h : n+1=m) (x : TotalTerm k B P p Z n) (j : Fin l) :
    ((total k B P p hp Z).d n m).hom x j =
      (show Term k B P Z (p j) (m + -(p j)) from
        ((ComplexTensor.column k B (right k B P) Z (p j)).d n m).hom (x j)) +
      ∑ i : Fin l, entryBetween k B P Z n m (p i) (p j) h (x i) := by
  subst m
  change ((ComplexTensor.finiteTotal k B (right k B P) Z p hp).d n (n+1)).hom x j = _
  simp only [ComplexTensor.finiteTotal, FiniteColumnComplex.total,
    FiniteColumnComplex.complex_d_hom]
  change (show Term k B P Z (p j) ((n+1) + -(p j)) from
      ((ComplexTensor.column k B (right k B P) Z (p j)).d n (n+1)).hom (x j)) +
    (show Term k B P Z (p j) ((n+1) + -(p j)) from
      ComplexTensor.matrix k B (right k B P) Z p n x j) = _
  erw [ComplexTensor.matrix_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  unfold entryBetween ComplexTensor.entry
  split_ifs with h
  · rfl
  · rfl
end LittleFinitistic.BimoduleTotal

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bimodule_BimoduleLeftTotalMap
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.ExternalTensor.Section4.SourceFiltration.inclusion2_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroCone_inclusion_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroTermSubsingleton _root_.OAI.ExternalTensor.Section4.forgetK_additive _root_.OAI.LittleFinitistic.BalancedTensor.tensorFinite _root_.OAI.LittleFinitistic.BalancedVertexFunctor.additive _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.ArrowVertex.arrow_id _root_.OAI.ExternalTensor.Section4.ArrowVertex.arrow_original _root_.OAI.ExternalTensor.Section4.ArrowVertex.iota_original _root_.OAI.ExternalTensor.Section4.ArrowVertex.left_mul _root_.OAI.ExternalTensor.Section4.ArrowVertex.map_left _root_.OAI.ExternalTensor.Section4.ArrowVertex.mem_space _root_.OAI.LittleFinitistic.BalancedAssociativity.forwardAt_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.forward_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.inverseAt_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.inverse_mk _root_.OAI.LittleFinitistic.BalancedTensor.FreeLeft.evaluation_single _root_.OAI.LittleFinitistic.BalancedTensor.FreeLeft.insertion_single _root_.OAI.LittleFinitistic.BalancedTensor.bimoduleAction_tmul_mk _root_.OAI.LittleFinitistic.BalancedTensor.leftAction_mk _root_.OAI.LittleFinitistic.BalancedTensor.mapRight_mk _root_.OAI.LittleFinitistic.BalancedTensor.rightAction_mk _root_.OAI.LittleFinitistic.BalancedTensor.tensorFunctorEquiv_mk _root_.OAI.LittleFinitistic.BalancedVertexImage.equiv_apply_val
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
variable {k B : Type u} [Field k] [Ring B] [Algebra k B]
variable {P P' P'' : BiComplex k B} (f : P ⟶ P')
variable (Z : CochainComplex (ModuleCat.{u} B) ℤ)

/-- The actual tensor map induced by a bimodule-complex morphism in each bidegree. -/
def leftTermMap (a q : ℤ) : Term k B P Z a q →ₗ[B] Term k B P' Z a q :=
  tensorAcross (f.f a) (𝟙 (Z.X q))

theorem leftTermMap_horizontal (n m a b : ℤ) (h : n+1=m) (hab : a+1=b) :
    (leftTermMap f Z b (m + -b)).comp (horizontalBetween k B P Z n m a b h hab) =
      (horizontalBetween k B P' Z n m a b h hab).comp (leftTermMap f Z a (n + -a)) := by
  unfold horizontalBetween leftTermMap
  rw [← tensorAcross_eq_termMap, ← tensorAcross_eq_termMap,
    tensorAcross_comp,tensorAcross_comp]
  simp only [Category.comp_id,Category.id_comp]
  rw [f.comm]

theorem leftTermMap_entry (n m a b : ℤ) (h : n+1=m) :
    (leftTermMap f Z b (m + -b)).comp (entryBetween k B P Z n m a b h) =
      (entryBetween k B P' Z n m a b h).comp (leftTermMap f Z a (n + -a)) := by
  unfold entryBetween
  split_ifs with hab
  · exact leftTermMap_horizontal f Z n m a b h hab
  · simp

theorem leftTermMap_vertical (n m a : ℤ) (x : Term k B P Z a (n + -a)) :
    leftTermMap f Z a (m + -a)
      (((ComplexTensor.column k B (right k B P) Z a).d n m).hom x) =
      ((ComplexTensor.column k B (right k B P') Z a).d n m).hom
        (leftTermMap f Z a (n + -a) x) := by
  let L := (leftTermMap f Z a (m + -a)).toAddMonoidHom.comp
    ((ComplexTensor.column k B (right k B P) Z a).d n m).hom.toAddMonoidHom
  let R := ((ComplexTensor.column k B (right k B P') Z a).d n m).hom.toAddMonoidHom.comp
    (leftTermMap f Z a (n + -a)).toAddMonoidHom
  induction x using BalancedTensor.induction_on with
  | hz => exact L.map_zero.trans R.map_zero.symm
  | ht x y =>
    rw [ComplexTensor.column_d,ComplexTensor.column_d]
    change leftTermMap f Z a (m + -a)
      ((-a).negOnePow • BalancedTensor.mk k B (BimoduleBalancedTensor.Input k B (P.X a))
        (ComplexTensor.leftTerm k B Z (m + -a)) x ((Z.d (n + -a) (m + -a)).hom y)) =
        (-a).negOnePow • BalancedTensor.mk k B (BimoduleBalancedTensor.Input k B (P'.X a))
        (ComplexTensor.leftTerm k B Z (m + -a)) ((f.f a).hom x) ((Z.d (n + -a) (m + -a)).hom y)
    simp only [Units.smul_def, map_zsmul]
    rfl
  | ha x y hx hy =>
    exact (L.map_add x y).trans
      ((congrArg₂ (· + ·) hx hy).trans (R.map_add x y).symm)

variable {l : ℕ} (p : Fin l → ℤ) (hp : StrictMono p)

def leftTotalMapF (n : ℤ) : TotalTerm k B P p Z n →ₗ[B] TotalTerm k B P' p Z n where
  toFun x i := leftTermMap f Z (p i) (n + -(p i)) (x i)
  map_add' x y := by ext i; exact map_add _ _ _
  map_smul' b x := by
    funext i
    exact (leftTermMap f Z (p i) (n + -(p i))).map_smul b (x i)

/-- Tensoring an actual bimodule chain map gives an actual B-linear total chain map. -/
def leftTotalMap : total k B P p hp Z ⟶ total k B P' p hp Z where
  f n := ModuleCat.ofHom (leftTotalMapF f Z p n)
  comm' n m h := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext j
    change ((total k B P' p hp Z).d n m).hom (leftTotalMapF f Z p n x) j =
      leftTermMap f Z (p j) (m + -(p j)) (((total k B P p hp Z).d n m).hom x j)
    erw [total_d_apply k B P' Z p hp n m h, total_d_apply k B P Z p hp n m h,
      map_add, map_sum]
    congr 1
    · exact (leftTermMap_vertical f Z n m (p j) (x j)).symm
    · apply Finset.sum_congr rfl
      intro i _
      exact (LinearMap.congr_fun (leftTermMap_entry f Z n m (p i) (p j) h) (x i)).symm

@[simp] theorem leftTotalMap_apply (n : ℤ) (x : TotalTerm k B P p Z n) (i : Fin l) :
    ((leftTotalMap f Z p hp).f n).hom x i = leftTermMap f Z (p i) (n + -(p i)) (x i) := rfl
end LittleFinitistic.BimoduleTotal

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bimodule_BimoduleLeftNaturality
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.ExternalTensor.Section4.SourceFiltration.inclusion2_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroCone_inclusion_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroTermSubsingleton _root_.OAI.ExternalTensor.Section4.forgetK_additive _root_.OAI.LittleFinitistic.BalancedTensor.tensorFinite _root_.OAI.LittleFinitistic.BalancedVertexFunctor.additive _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.ArrowVertex.arrow_id _root_.OAI.ExternalTensor.Section4.ArrowVertex.arrow_original _root_.OAI.ExternalTensor.Section4.ArrowVertex.iota_original _root_.OAI.ExternalTensor.Section4.ArrowVertex.left_mul _root_.OAI.ExternalTensor.Section4.ArrowVertex.map_left _root_.OAI.ExternalTensor.Section4.ArrowVertex.mem_space _root_.OAI.LittleFinitistic.BalancedAssociativity.forwardAt_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.forward_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.inverseAt_mk _root_.OAI.LittleFinitistic.BalancedAssociativity.inverse_mk _root_.OAI.LittleFinitistic.BalancedTensor.FreeLeft.evaluation_single _root_.OAI.LittleFinitistic.BalancedTensor.FreeLeft.insertion_single _root_.OAI.LittleFinitistic.BalancedTensor.bimoduleAction_tmul_mk _root_.OAI.LittleFinitistic.BalancedTensor.leftAction_mk _root_.OAI.LittleFinitistic.BalancedTensor.mapRight_mk _root_.OAI.LittleFinitistic.BalancedTensor.rightAction_mk _root_.OAI.LittleFinitistic.BalancedTensor.tensorFunctorEquiv_mk _root_.OAI.LittleFinitistic.BalancedVertexImage.equiv_apply_val
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
variable {k B : Type u} [Field k] [Ring B] [Algebra k B]
variable {P P' P'' : BiComplex k B}
variable {l : ℕ} (p : Fin l → ℤ) (hp : StrictMono p)
variable {Z Z' : CochainComplex (ModuleCat.{u} B) ℤ}

/-- Naturality of the actual bimodule-induced tensor map on arbitrary complexes. -/
theorem leftTotalMap_naturality (f : P ⟶ P') (g : Z ⟶ Z') :
    totalMap k B P p hp g ≫ leftTotalMap f Z' p hp =
      leftTotalMap f Z p hp ≫ totalMap k B P' p hp g := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  funext i
  change leftTermMap f Z' (p i) (n + -(p i))
    (((ComplexTensor.finiteTotalMap k B (right k B P) p hp g).f n).hom x i) =
      ((ComplexTensor.finiteTotalMap k B (right k B P') p hp g).f n).hom
        (leftTotalMapF f Z p n x) i
  erw [ComplexTensor.finiteTotalMap_apply,ComplexTensor.finiteTotalMap_apply]
  change leftTermMap f Z' (p i) (n + -(p i))
    (ComplexTensor.inputMap k B (right k B P) g (p i) (n + -(p i)) (x i)) =
      ComplexTensor.inputMap k B (right k B P') g (p i) (n + -(p i))
        (leftTermMap f Z (p i) (n + -(p i)) (x i))
  let L := (leftTermMap f Z' (p i) (n + -(p i))).toAddMonoidHom.comp
    (ComplexTensor.inputMap k B (right k B P) g (p i) (n + -(p i))).toAddMonoidHom
  let R := (ComplexTensor.inputMap k B (right k B P') g (p i) (n + -(p i))).toAddMonoidHom.comp
    (leftTermMap f Z (p i) (n + -(p i))).toAddMonoidHom
  induction x i using BalancedTensor.induction_on with
  | hz => exact L.map_zero.trans R.map_zero.symm
  | ht m n => rfl
  | ha x y hx hy =>
    exact (L.map_add x y).trans
      ((congrArg₂ (· + ·) hx hy).trans (R.map_add x y).symm)

/-- An augmentation of bimodule complexes induces this concrete natural transformation. -/
def leftTensorNat (f : P ⟶ P') : functor k B P p hp ⟶ functor k B P' p hp where
  app Z := leftTotalMap f Z p hp
  naturality {_ _} g := leftTotalMap_naturality p hp f g

@[simp] theorem leftTotalMap_id (Z : CochainComplex (ModuleCat.{u} B) ℤ) :
    leftTotalMap (𝟙 P) Z p hp = 𝟙 _ := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  funext i
  change tensorAcross (𝟙 (P.X (p i))) (𝟙 (Z.X (n + -(p i)))) (x i) = x i
  rw [tensorAcross_id,LinearMap.id_apply]

@[simp] theorem leftTotalMap_comp (f : P ⟶ P') (g : P' ⟶ P'')
    (Z : CochainComplex (ModuleCat.{u} B) ℤ) :
    leftTotalMap (f ≫ g) Z p hp = leftTotalMap f Z p hp ≫ leftTotalMap g Z p hp := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  funext i
  change tensorAcross ((f.f (p i)) ≫ g.f (p i)) (𝟙 (Z.X (n + -(p i)))) (x i) =
    tensorAcross (g.f (p i)) (𝟙 (Z.X (n + -(p i))))
      (tensorAcross (f.f (p i)) (𝟙 (Z.X (n + -(p i)))) (x i))
  have h := LinearMap.congr_fun (tensorAcross_comp (f.f (p i)) (g.f (p i))
    (𝟙 (Z.X (n + -(p i)))) (𝟙 (Z.X (n + -(p i))))) (x i)
  simpa only [Category.id_comp,LinearMap.comp_apply] using h.symm

end LittleFinitistic.BimoduleTotal

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bimodule_BimoduleSingleTerms
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.ExternalTensor.Section4.SourceFiltration.inclusion2_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroCone_inclusion_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroTermSubsingleton _root_.OAI.ExternalTensor.Section4.forgetK_additive _root_.OAI.LittleFinitistic.BalancedTensor.tensorFinite _root_.OAI.LittleFinitistic.BalancedVertexFunctor.additive _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
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

/-- The native degree-zero-module evaluation, retaining its original B action and differential. -/
abbrev moduleEvaluation :=
  ((BimoduleBalancedTensor.functor k B (BalancedTensor.ScalarLeftModule k B N)).mapHomologicalComplex
    (.up ℤ)).obj P

def singleTermIso (n a : ℤ) (h : a=n) :
    ModuleCat.of B (Term k B P (singleInput B N) a (n + -a)) ≅ (moduleEvaluation k B P N).X n :=
  (inputFunctor k B (P.X a)).mapIso
      (HomologicalComplex.singleObjXIsoOfEq (.up ℤ) 0 N (n + -a) (by omega)) ≪≫
    (BimoduleBalancedTensor.functor k B (BalancedTensor.ScalarLeftModule k B N)).mapIso (P.XIsoOfEq h)

end LittleFinitistic.BimoduleTotal

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bimodule_BimoduleDerivedInterval
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.ExternalTensor.Section4.SourceFiltration.inclusion2_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroCone_inclusion_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroTermSubsingleton _root_.OAI.ExternalTensor.Section4.forgetK_additive _root_.OAI.LittleFinitistic.BalancedVertexFunctor.additive _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
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
variable [HasDerivedCategory.{u+1} (ModuleCat.{u} B)]
variable (P : BiComplex k B)
variable [∀ n, Module.Projective Bᵐᵒᵖ (ComplexTensor.rightTerm k B (right k B P) n)]

omit [HasDerivedCategory.{u+1} (ModuleCat.{u} B)]
  [∀ n, Module.Projective Bᵐᵒᵖ (ComplexTensor.rightTerm k B (right k B P) n)] in
/-- Boundedness ensures this finite total contains every nonzero right degree. -/
theorem outside_interval_isZero (lo hi : ℤ)
    (hP : ∀ n, n < lo ∨ hi < n → IsZero (P.X n)) (n : ℤ)
    (hn : ∀ i, intervalDegrees lo hi i ≠ n) : IsZero (P.X n) := by
  apply hP n
  by_contra h
  have hbounds : lo ≤ n ∧ n ≤ hi := by omega
  obtain ⟨i,hi⟩ := intervalDegrees_covers lo hi n hbounds
  exact hn i hi
end LittleFinitistic.BimoduleTotal

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bimodule_BoundedBimoduleDerived
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.ExternalTensor.Section4.SourceFiltration.inclusion2_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroCone_inclusion_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroTermSubsingleton _root_.OAI.ExternalTensor.Section4.forgetK_additive _root_.OAI.LittleFinitistic.BalancedVertexFunctor.additive _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
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

/-- Exactly the bounded-right-projective data needed to compute tensor on every complex. -/
structure BoundedProjective (P : BiComplex k B) where
  lower : ℤ
  upper : ℤ
  bounded : ∀ n, n < lower ∨ upper < n → IsZero (P.X n)
  projective : ∀ n, Module.Projective Bᵐᵒᵖ (ComplexTensor.rightTerm k B (right k B P) n)

namespace BoundedProjective
variable {k B} {P : BiComplex k B} (data : BoundedProjective k B P)

abbrev degrees := intervalDegrees data.lower data.upper

theorem complete (n : ℤ) (hn : ∀ i, data.degrees i ≠ n) : IsZero (P.X n) :=
  outside_interval_isZero k B P data.lower data.upper data.bounded n hn

end BoundedProjective
end LittleFinitistic.BimoduleTotal

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bimodule_BimoduleAugmentedResolution
attribute [-instance] _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.ExternalTensor.Section4.SourceFiltration.inclusion2_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroCone_inclusion_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroTermSubsingleton _root_.OAI.ExternalTensor.Section4.forgetK_additive _root_.OAI.LittleFinitistic.BalancedVertexFunctor.additive _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
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

abbrev bimoduleStalk (X : ModuleCat.{u} (Enveloping k B)) : BiComplex k B :=
  (HomologicalComplex.single (ModuleCat (Enveloping k B)) (.up ℤ) 0).obj X

/-- Actual bounded right-projective resolution data, including the bimodule
augmentation and its quasi-isomorphism; no tensor comparison is assumed. -/
structure AugmentedProjective (P : BiComplex k B) (X : ModuleCat.{u} (Enveloping k B)) where
  data : BoundedProjective k B P
  augmentation : P ⟶ bimoduleStalk k B X
  quasiIso : QuasiIso augmentation

namespace AugmentedProjective
variable {k B} {P : BiComplex k B} {X : ModuleCat.{u} (Enveloping k B)}
variable (res : AugmentedProjective k B P X)

/-- The augmentation induces the concrete finite-total transformation. -/
def tensorAugmentation : functor k B P res.data.degrees
    (intervalDegrees_strictMono res.data.lower res.data.upper) ⟶
    functor k B (bimoduleStalk k B X) res.data.degrees
      (intervalDegrees_strictMono res.data.lower res.data.upper) :=
  leftTensorNat res.data.degrees (intervalDegrees_strictMono res.data.lower res.data.upper)
    res.augmentation

end AugmentedProjective
end LittleFinitistic.BimoduleTotal

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bimodule_BimoduleBarComparisonMap
attribute [-instance] _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.ExternalTensor.Section4.SourceFiltration.inclusion2_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroCone_inclusion_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroTermSubsingleton _root_.OAI.ExternalTensor.Section4.forgetK_additive _root_.OAI.LittleFinitistic.BalancedVertexFunctor.additive _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleCoefficients.towerLeft _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDTensor.scalarModuleTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Functor
namespace LittleFinitistic.BimoduleTotal
open ExternalTensor.Section4
universe u
variable {k B : Type u} [Field k] [Ring B] [Algebra k B]
variable {P : BiComplex k B} {X : ModuleCat.{u} (Enveloping k B)}
variable (res : AugmentedProjective k B P X)
variable (i₀ : Fin ((res.data.upper-res.data.lower).toNat+1)) (hi₀ : res.data.degrees i₀=0)

abbrev barModule := BimoduleBarComparison.Actions k B X
abbrev actualBarFunctor := DerivedBar.BimoduleTensor.tensorFunctor k B (barModule (X := X))

end LittleFinitistic.BimoduleTotal

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bimodule_BimoduleTensorVertexBridge
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.ExternalTensor.Section4.SourceFiltration.inclusion2_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroCone_inclusion_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroTermSubsingleton _root_.OAI.ExternalTensor.Section4.forgetK_additive _root_.OAI.LittleFinitistic.BalancedTensor.tensorFinite _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace LittleFinitistic.BimoduleTensorVertexBridge
open ExternalTensor.Section4
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B]
variable (N : Type u) [AddCommGroup N] [Module k N] [Module B N]

/-- The full B-valued tensor functor has exactly the previously constructed
vertex spaces, with scalar restriction accounted for explicitly. -/
def equiv (e : B) (M : ModuleCat.{u} (Enveloping k B)) :
    (LeftVertexHomology.vertex k B e).obj ((BimoduleBalancedTensor.functor k B N).obj M) ≃ₗ[k]
      BalancedVertexFunctor.Space k B e N M where
  toFun x := ⟨x.val, (VertexFunctor.mem_fixed (algebraMap k B) e (LeftVertexHomology.scalar_commute k B e)
      ((BimoduleBalancedTensor.functor k B N).obj M) x.val).1 x.property⟩
  invFun x := ⟨x.val, (VertexFunctor.mem_fixed (algebraMap k B) e (LeftVertexHomology.scalar_commute k B e)
      ((BimoduleBalancedTensor.functor k B N).obj M) x.val).2 x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c x := Subtype.ext (BimoduleBalancedTensor.algebraMap_smul k B M N c x.val)

/-- All induced differential and module maps are retained by the comparison. -/
def comparison (e : B) : BimoduleBalancedTensor.functor k B N ⋙
    LeftVertexHomology.vertex k B e ≅ BalancedVertexFunctor.functor k B e N :=
  NatIso.ofComponents (fun M => (equiv k B N e M).toModuleIso) (by
    intro M M' f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    rfl)

end LittleFinitistic.BimoduleTensorVertexBridge

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bimodule_BimoduleTotalCoefficient
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.ExternalTensor.Section4.SourceFiltration.inclusion2_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroCone_inclusion_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroTermSubsingleton _root_.OAI.ExternalTensor.Section4.forgetK_additive _root_.OAI.LittleFinitistic.BalancedTensor.tensorFinite _root_.OAI.LittleFinitistic.BalancedVertexFunctor.additive _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
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
variable (P : BiComplex k B) (Z : CochainComplex (ModuleCat.{u} B) ℤ)
variable {l : ℕ} (p : Fin l → ℤ) (hp : StrictMono p)

def coefficient (n a : ℤ) : TotalTerm k B P p Z n →ₗ[B] Term k B P Z a (n + -a) :=
  FiniteSupportReindex.coefficient (fun a => ModuleCat.of B (Term k B P Z a (n + -a))) p a

end LittleFinitistic.BimoduleTotal

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryBimoduleCoefficientEquiv
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.Multibar.patternTower _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.DerivedBar.termTower _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.ExternalTensor.Section4.rightModuleTower _root_.OAI.LittleFinitistic.BalancedTensor.scalarModuleTower _root_.OAI.LittleFinitistic.BalancedTensor.tensorFinite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.finite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.scalarTower _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDTensor.scalarModuleTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TensorComplex.scalarTower _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace LittleFinitistic.BimoduleComplexTensor
universe u
variable (k S A : Type u) [Field k] [Ring S] [Ring A] [Algebra k S] [Algebra k A]
variable {Q Q' : CochainComplex (ModuleCat.{u} (S ⊗[k] Aᵐᵒᵖ)) ℤ}
variable (e : Q ≅ Q') (Z : CochainComplex (ModuleCat.{u} A) ℤ)

def rightTermEquiv (p q : ℤ) : term k S A Q Z p q ≃ₗ[S] term k S A Q' Z p q :=
  LeftTensor.congr (BimoduleCoefficients.equiv k S A ((HomologicalComplex.eval _ _ p).mapIso e))
    (BimoduleCoefficients.equiv_left k S A ((HomologicalComplex.eval _ _ p).mapIso e))
    (LinearEquiv.refl A (ComplexTensor.leftTerm k A Z q))

/-- Both actual tensor maps respect an isomorphism of genuine bimodule complexes. -/
theorem rightTermEquiv_map (p p' q q' : ℤ) (g : Z.X q ⟶ Z.X q') :
    (rightTermEquiv k S A e Z p' q').toLinearMap.comp (map k S A Q Z (Q.d p p') g) =
    (map k S A Q' Z (Q'.d p p') g).comp (rightTermEquiv k S A e Z p q).toLinearMap := by
  apply LinearMap.restrictScalars_injective k
  apply BalancedTensor.ext
  intro x z
  exact congrArg (fun y => LeftTensor.mk k S A (BimoduleCoefficients k S A (Q'.X p'))
      (ComplexTensor.leftTerm k A Z q') y (g.hom z))
    (congrArg (fun f => f.hom x) (e.hom.comm p p')).symm

theorem rightTermEquiv_map_id (p q q' : ℤ) (g : Z.X q ⟶ Z.X q') :
    (rightTermEquiv k S A e Z p q').toLinearMap.comp (map k S A Q Z (𝟙 (Q.X p)) g) =
    (map k S A Q' Z (𝟙 (Q'.X p)) g).comp (rightTermEquiv k S A e Z p q).toLinearMap := by
  apply LinearMap.restrictScalars_injective k
  apply BalancedTensor.ext
  intro x z
  rfl
end LittleFinitistic.BimoduleComplexTensor

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryBimoduleTensorTotal
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.Multibar.patternTower _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.DerivedBar.termTower _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.ExternalTensor.Section4.rightModuleTower _root_.OAI.LittleFinitistic.BalancedTensor.scalarModuleTower _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDTensor.scalarModuleTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TensorComplex.scalarTower _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace LittleFinitistic.BimoduleComplexTensor
universe u
variable (k S A : Type u) [Field k] [Ring S] [Ring A] [Algebra k S] [Algebra k A]
variable (Q : CochainComplex (ModuleCat.{u} (S ⊗[k] Aᵐᵒᵖ)) ℤ)
variable (Z : CochainComplex (ModuleCat.{u} A) ℤ)
variable {l : ℕ} (p : Fin l → ℤ) (hp : StrictMono p)

include hp in
theorem differential_square (n : ℤ) :
    (differential k S A Q Z p (n+1)).comp (differential k S A Q Z p n) = 0 := by
  apply LinearMap.ext
  intro z
  apply (forgetTotalEquiv k S A Q Z p ((n+1)+1)).injective
  change forgetTotalEquiv k S A Q Z p ((n+1)+1)
      (differential k S A Q Z p (n+1) (differential k S A Q Z p n z)) = _
  rw [forget_differential k S A Q Z p hp,forget_differential k S A Q Z p hp,LinearMap.zero_apply,map_zero]
  exact congrArg (fun f => f (forgetTotalEquiv k S A Q Z p n z))
    ((FiniteColumnComplex.totalDifferential (ComplexTensor.columns k A (rightComplex k S A Q) Z p)
      (ComplexTensor.tensorHorizontal k A (rightComplex k S A Q) Z p hp)).square n)

/-- Actual signed finite tensor total in modules over the outside algebra. -/
def total : CochainComplex (ModuleCat.{u} S) ℤ :=
  CochainComplex.of (fun n => ModuleCat.of S (totalTerm k S A Q Z p n))
    (fun n => ModuleCat.ofHom (differential k S A Q Z p n))
    (fun n => ModuleCat.hom_ext (differential_square k S A Q Z p hp n))
end LittleFinitistic.BimoduleComplexTensor

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryBimoduleTotalForget
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.Multibar.patternTower _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.DerivedBar.termTower _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.ExternalTensor.Section4.rightModuleTower _root_.OAI.LittleFinitistic.BalancedTensor.scalarModuleTower _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDTensor.scalarModuleTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TensorComplex.scalarTower _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace LittleFinitistic.BimoduleComplexTensor
universe u
variable (k S A : Type u) [Field k] [Ring S] [Ring A] [Algebra k S] [Algebra k A]
variable (Q : CochainComplex (ModuleCat.{u} (S ⊗[k] Aᵐᵒᵖ)) ℤ)
variable (Z : CochainComplex (ModuleCat.{u} A) ℤ)
variable {l : ℕ} (p : Fin l → ℤ) (hp : StrictMono p)

abbrev forgetTotal : CochainComplex (ModuleCat.{u} k) ℤ :=
  ((ModuleCat.restrictScalars (algebraMap k S)).mapHomologicalComplex (.up ℤ)).obj (total k S A Q Z p hp)

def forgetTermIso (n : ℤ) : (forgetTotal k S A Q Z p hp).X n ≅
    (ComplexTensor.finiteTotal k A (rightComplex k S A Q) Z p hp).X n := by
  let e : (forgetTotal k S A Q Z p hp).X n ≃ₗ[k] totalTerm k S A Q Z p n :=
    { toFun := fun x => x
      invFun := fun x => x
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun r x => by
        have h (y : totalTerm k S A Q Z p n) : (algebraMap k S r) • y = r • y :=
          algebraMap_smul S r y
        exact h x }
  exact (e.trans (forgetTotalEquiv k S A Q Z p n)).toModuleIso

/-- The genuine outside-action total forgets to the actual previously verified k-total. -/
def forgetTotalIso : forgetTotal k S A Q Z p hp ≅
    ComplexTensor.finiteTotal k A (rightComplex k S A Q) Z p hp :=
  HomologicalComplex.Hom.isoOfComponents (forgetTermIso k S A Q Z p hp) (by
    intro n m h
    change n+1=m at h
    subst m
    have h₁ : (total k S A Q Z p hp).d n (n+1) = ModuleCat.ofHom (differential k S A Q Z p n) :=
      CochainComplex.of_d (fun n => ModuleCat.of S (totalTerm k S A Q Z p n))
        (fun n => ModuleCat.ofHom (differential k S A Q Z p n)) n
    have h₂ : (ComplexTensor.finiteTotal k A (rightComplex k S A Q) Z p hp).d n (n+1) =
        ModuleCat.ofHom ((FiniteColumnComplex.totalDifferential
          (ComplexTensor.columns k A (rightComplex k S A Q) Z p)
          (ComplexTensor.tensorHorizontal k A (rightComplex k S A Q) Z p hp)).d n) :=
      CochainComplex.of_d (fun n => ModuleCat.of k
        (FiniteColumnComplex.term (ComplexTensor.columns k A (rightComplex k S A Q) Z p) n))
        (fun n => ModuleCat.ofHom ((FiniteColumnComplex.totalDifferential
          (ComplexTensor.columns k A (rightComplex k S A Q) Z p)
          (ComplexTensor.tensorHorizontal k A (rightComplex k S A Q) Z p hp)).d n)) n
    change (forgetTermIso k S A Q Z p hp n).hom ≫ _ =
      (ModuleCat.restrictScalars (algebraMap k S)).map ((total k S A Q Z p hp).d n (n+1)) ≫
        (forgetTermIso k S A Q Z p hp (n+1)).hom
    rw [h₁,h₂]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    exact (forget_differential k S A Q Z p hp n z).symm)
end LittleFinitistic.BimoduleComplexTensor

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryBimoduleTotalMaps
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.Multibar.patternTower _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.DerivedBar.termTower _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.ExternalTensor.Section4.rightModuleTower _root_.OAI.LittleFinitistic.BalancedTensor.scalarModuleTower _root_.OAI.LittleFinitistic.BalancedTensor.tensorFinite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.finite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.scalarTower _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDTensor.scalarModuleTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TensorComplex.scalarTower _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace LittleFinitistic.BimoduleComplexTensor
universe u
variable (k S A : Type u) [Field k] [Ring S] [Ring A] [Algebra k S] [Algebra k A]
variable (Q : CochainComplex (ModuleCat.{u} (S ⊗[k] Aᵐᵒᵖ)) ℤ)
variable {Z Z' : CochainComplex (ModuleCat.{u} A) ℤ} (f : Z ⟶ Z')
variable {l : ℕ} (p : Fin l → ℤ) (hp : StrictMono p)

/-- The retained-action input map is exactly the prior tensor map after forgetting. -/
theorem forget_totalInputMap (n : ℤ) (z : totalTerm k S A Q Z p n) :
    forgetTotalEquiv k S A Q Z' p n (totalInputMap k S A Q f p n z) =
      ((ComplexTensor.finiteTotalMap k A (rightComplex k S A Q) p hp f).f n).hom
        (forgetTotalEquiv k S A Q Z p n z) := by
  funext i
  rw [ComplexTensor.finiteTotalMap_apply]
  change forgetEquiv k S A Q Z' (p i) (n + -(p i))
      (termInputMap k S A Q f (p i) (n + -(p i)) (z i)) =
    ComplexTensor.inputMap k A (rightComplex k S A Q) f (p i) (n + -(p i))
      (forgetEquiv k S A Q Z (p i) (n + -(p i)) (z i))
  let L := (forgetEquiv k S A Q Z' (p i) (n + -(p i))).toLinearMap.comp
    ((termInputMap k S A Q f (p i) (n + -(p i))).restrictScalars k)
  let R := (ComplexTensor.inputMap k A (rightComplex k S A Q) f (p i) (n + -(p i))).comp
    (forgetEquiv k S A Q Z (p i) (n + -(p i))).toLinearMap
  change L (z i) = R (z i)
  induction z i using BalancedTensor.induction_on with
  | hz => exact L.map_zero.trans R.map_zero.symm
  | ht x y => rfl
  | ha x y hx hy =>
    exact (L.map_add x y).trans ((congrArg₂ (· + ·) hx hy).trans (R.map_add x y).symm)

include hp in
theorem totalInputMap_comm (n : ℤ) :
    (differential k S A Q Z' p n).comp (totalInputMap k S A Q f p n) =
      (totalInputMap k S A Q f p (n+1)).comp (differential k S A Q Z p n) := by
  apply LinearMap.ext
  intro z
  apply (forgetTotalEquiv k S A Q Z' p (n+1)).injective
  change forgetTotalEquiv k S A Q Z' p (n+1)
      (differential k S A Q Z' p n (totalInputMap k S A Q f p n z)) =
    forgetTotalEquiv k S A Q Z' p (n+1)
      (totalInputMap k S A Q f p (n+1) (differential k S A Q Z p n z))
  rw [forget_differential k S A Q Z' p hp,forget_totalInputMap k S A Q f p hp,
    forget_totalInputMap k S A Q f p hp,forget_differential k S A Q Z p hp]
  have h := congrArg (fun g => g.hom (forgetTotalEquiv k S A Q Z p n z))
    ((ComplexTensor.finiteTotalMap k A (rightComplex k S A Q) p hp f).comm n (n+1))
  dsimp only [ComplexTensor.finiteTotal,FiniteColumnComplex.total] at h
  rw [FiniteColumnComplex.complex_d,FiniteColumnComplex.complex_d] at h
  exact h

/-- Actual chain maps of the outside-action tensor total. -/
def totalMap : total k S A Q Z p hp ⟶ total k S A Q Z' p hp where
  f n := ModuleCat.ofHom (totalInputMap k S A Q f p n)
  comm' n m h := by
    change n+1=m at h
    subst m
    have h₁ : (total k S A Q Z p hp).d n (n+1) = ModuleCat.ofHom (differential k S A Q Z p n) :=
      CochainComplex.of_d (fun n => ModuleCat.of S (totalTerm k S A Q Z p n))
        (fun n => ModuleCat.ofHom (differential k S A Q Z p n)) n
    have h₂ : (total k S A Q Z' p hp).d n (n+1) = ModuleCat.ofHom (differential k S A Q Z' p n) :=
      CochainComplex.of_d (fun n => ModuleCat.of S (totalTerm k S A Q Z' p n))
        (fun n => ModuleCat.ofHom (differential k S A Q Z' p n)) n
    rw [h₁,h₂]
    apply ModuleCat.hom_ext
    exact totalInputMap_comm k S A Q f p hp n

theorem forgetTotalIso_natural :
    ((ModuleCat.restrictScalars (algebraMap k S)).mapHomologicalComplex (.up ℤ)).map
      (totalMap k S A Q f p hp) ≫ (forgetTotalIso k S A Q Z' p hp).hom =
    (forgetTotalIso k S A Q Z p hp).hom ≫
      ComplexTensor.finiteTotalMap k A (rightComplex k S A Q) p hp f := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  exact forget_totalInputMap k S A Q f p hp n z
end LittleFinitistic.BimoduleComplexTensor

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryBimoduleTotalFunctor
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.Multibar.patternTower _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.DerivedBar.termTower _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.ExternalTensor.Section4.rightModuleTower _root_.OAI.LittleFinitistic.BalancedTensor.scalarModuleTower _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDTensor.scalarModuleTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TensorComplex.scalarTower _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace LittleFinitistic.BimoduleComplexTensor
universe u
variable (k S A : Type u) [Field k] [Ring S] [Ring A] [Algebra k S] [Algebra k A]
variable (Q : CochainComplex (ModuleCat.{u} (S ⊗[k] Aᵐᵒᵖ)) ℤ)
variable {l : ℕ} (p : Fin l → ℤ) (hp : StrictMono p)

/-- The actual tensor total is a functor retaining its outside action on every complex. -/
def totalFunctor : CochainComplex (ModuleCat.{u} A) ℤ ⥤ CochainComplex (ModuleCat.{u} S) ℤ where
  obj Z := total k S A Q Z p hp
  map f := totalMap k S A Q f p hp
  map_id Z := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    funext i
    change termInputMap k S A Q (𝟙 Z) (p i) (n + -(p i)) (z i) = z i
    rw [termInputMap_id]
    rfl
  map_comp f g := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    funext i
    change termInputMap k S A Q (f ≫ g) (p i) (n + -(p i)) (z i) =
      termInputMap k S A Q g (p i) (n + -(p i)) (termInputMap k S A Q f (p i) (n + -(p i)) (z i))
    rw [termInputMap_comp]
    rfl

/-- The genuine outside-action tensor preserves arbitrary quasi-isomorphisms when its right terms
are projective. There are no restrictions on either input complex. -/
theorem totalFunctor_quasiIso
    [∀ i, Module.Projective Aᵐᵒᵖ (ComplexTensor.rightTerm k A (rightComplex k S A Q) (p i))]
    {Z Z' : CochainComplex (ModuleCat.{u} A) ℤ} (f : Z ⟶ Z') [QuasiIso f] :
    QuasiIso ((totalFunctor k S A Q p hp).map f) := by
  apply (RestrictionHomology.quasiIso_iff (algebraMap k S) _).mp
  let g := ((ModuleCat.restrictScalars (algebraMap k S)).mapHomologicalComplex (.up ℤ)).map
    (totalMap k S A Q f p hp)
  have := ComplexTensor.finiteTotalMap_quasiIso k A (rightComplex k S A Q) f p hp
  have hg : QuasiIso (g ≫ (forgetTotalIso k S A Q Z' p hp).hom) := by
    dsimp only [g]
    rw [forgetTotalIso_natural]
    infer_instance
  exact (quasiIso_iff_comp_right g (forgetTotalIso k S A Q Z' p hp).hom).mp hg
end LittleFinitistic.BimoduleComplexTensor

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryBimoduleDerivedTensor
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace LittleFinitistic.BimoduleComplexTensor
universe u
variable (k S A : Type u) [Field k] [Ring S] [Ring A] [Algebra k S] [Algebra k A]
variable (Q : CochainComplex (ModuleCat.{u} (S ⊗[k] Aᵐᵒᵖ)) ℤ)
variable {l : ℕ} (p : Fin l → ℤ) (hp : StrictMono p)
variable [HasDerivedCategory.{u+1} (ModuleCat.{u} A)]
variable [HasDerivedCategory.{u+1} (ModuleCat.{u} S)]
variable [∀ i, Module.Projective Aᵐᵒᵖ (ComplexTensor.rightTerm k A (rightComplex k S A Q) (p i))]

omit [HasDerivedCategory.{u+1} (ModuleCat.{u} A)] in
theorem total_inverts : (HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)).IsInvertedBy
    (totalFunctor k S A Q p hp ⋙ DerivedCategory.Q) := by
  intro Z Z' f hf
  let : QuasiIso f := hf
  let := totalFunctor_quasiIso k S A Q p hp f
  exact (inferInstance : IsIso (DerivedCategory.Q.map ((totalFunctor k S A Q p hp).map f)))

/-- Localization of the actual tensor total, retaining the outside action. -/
def derivedTotal : DerivedCategory (ModuleCat.{u} A) ⥤ DerivedCategory (ModuleCat.{u} S) :=
  Localization.lift (totalFunctor k S A Q p hp ⋙ DerivedCategory.Q)
    (total_inverts k S A Q p hp) DerivedCategory.Q

def derivedTotalComparison :
    DerivedCategory.Q ⋙ derivedTotal k S A Q p hp ≅ totalFunctor k S A Q p hp ⋙ DerivedCategory.Q :=
  Localization.fac (totalFunctor k S A Q p hp ⋙ DerivedCategory.Q)
    (total_inverts k S A Q p hp) DerivedCategory.Q
end LittleFinitistic.BimoduleComplexTensor

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryBimoduleTotalAssociativity
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.Multibar.patternTower _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.DerivedBar.termTower _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.ExternalTensor.Section4.rightModuleTower _root_.OAI.LittleFinitistic.BalancedTensor.scalarModuleTower _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDTensor.scalarModuleTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TensorComplex.scalarTower _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace LittleFinitistic.BimoduleComplexTensor
universe u
variable (k S A B N : Type u) [Field k] [Ring S] [Ring A] [Ring B]
  [Algebra k S] [Algebra k A] [Algebra k B]
variable [AddCommGroup N] [Module k N] [Module A N] [Module Bᵐᵒᵖ N]
  [IsScalarTower k A N] [IsScalarTower k Bᵐᵒᵖ N] [SMulCommClass A Bᵐᵒᵖ N]
variable (Q : CochainComplex (ModuleCat.{u} (S ⊗[k] Aᵐᵒᵖ)) ℤ)
variable (Z : CochainComplex (ModuleCat.{u} B) ℤ)
variable {l : ℕ} (p : Fin l → ℤ) (hp : StrictMono p)

attribute [local instance] OAI.LittleFinitistic.BimoduleComplexTensor.instSMulCommClassMulOpposite_solutions_1
/-- Full signed total associativity in S-modules, on every input complex Z. -/
def totalAssociativityIso :
    total k S B (middleBimoduleComplex k S A B N Q) Z p hp ≅
      total k S A Q (middleLeftComplex k A B N Z) p hp :=
  HomologicalComplex.Hom.isoOfComponents (fun n => (associativeTotalEquiv k S A B N Q Z p n).toModuleIso) (by
    intro n m h
    change n+1=m at h
    subst m
    have h₁ : (total k S B (middleBimoduleComplex k S A B N Q) Z p hp).d n (n+1) =
        ModuleCat.ofHom (differential k S B (middleBimoduleComplex k S A B N Q) Z p n) := CochainComplex.of_d
      (fun n => ModuleCat.of S (totalTerm k S B (middleBimoduleComplex k S A B N Q) Z p n))
      (fun n => ModuleCat.ofHom (differential k S B (middleBimoduleComplex k S A B N Q) Z p n)) n
    have h₂ : (total k S A Q (middleLeftComplex k A B N Z) p hp).d n (n+1) =
        ModuleCat.ofHom (differential k S A Q (middleLeftComplex k A B N Z) p n) := CochainComplex.of_d
      (fun n => ModuleCat.of S (totalTerm k S A Q (middleLeftComplex k A B N Z) p n))
      (fun n => ModuleCat.ofHom (differential k S A Q (middleLeftComplex k A B N Z) p n)) n
    rw [h₁,h₂]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    exact (associative_differential k S A B N Q Z p n z).symm)
end LittleFinitistic.BimoduleComplexTensor

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryBimoduleTotalCongruence
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.Multibar.patternTower _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.DerivedBar.termTower _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.ExternalTensor.Section4.rightModuleTower _root_.OAI.LittleFinitistic.BalancedTensor.scalarModuleTower _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDTensor.scalarModuleTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TensorComplex.scalarTower _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace LittleFinitistic.BimoduleComplexTensor
universe u
variable (k S A : Type u) [Field k] [Ring S] [Ring A] [Algebra k S] [Algebra k A]
variable {Q Q' : CochainComplex (ModuleCat.{u} (S ⊗[k] Aᵐᵒᵖ)) ℤ}
variable (e : Q ≅ Q') (Z : CochainComplex (ModuleCat.{u} A) ℤ)
variable {l : ℕ} (p : Fin l → ℤ) (hp : StrictMono p)

def rightTotalEquiv (n : ℤ) : totalTerm k S A Q Z p n ≃ₗ[S] totalTerm k S A Q' Z p n :=
  LinearEquiv.piCongrRight (fun i => rightTermEquiv k S A e Z (p i) (n + -(p i)))

theorem right_entry (n : ℤ) (i j : Fin l) :
    (rightTermEquiv k S A e Z (p j) ((n+1) + -(p j))).toLinearMap.comp
      (entry k S A Q Z p n i j) =
    (entry k S A Q' Z p n i j).comp
      (rightTermEquiv k S A e Z (p i) (n + -(p i))).toLinearMap := by
  unfold entry
  split_ifs with h
  · exact rightTermEquiv_map k S A e Z _ _ _ _ (eqToHom (congrArg Z.X (show n + -(p i) = (n+1) + -(p j) by omega)))
  · simp only [LinearMap.comp_zero,LinearMap.zero_comp]

theorem right_differential (n : ℤ) (z : totalTerm k S A Q Z p n) :
    rightTotalEquiv k S A e Z p (n+1) (differential k S A Q Z p n z) =
    differential k S A Q' Z p n (rightTotalEquiv k S A e Z p n z) := by
  funext j
  simp only [rightTotalEquiv,LinearEquiv.piCongrRight_apply,differential,
    LinearMap.pi_apply,LinearMap.add_apply,LinearMap.comp_apply,LinearMap.proj_apply,
    LinearMap.sum_apply,map_add,map_sum]
  apply congrArg₂ (· + ·)
  · change rightTermEquiv k S A e Z (p j) ((n+1) + -(p j))
        ((((-(p j)).negOnePow : ℤ)) • (map k S A Q Z (𝟙 _)
          (Z.d (n + -(p j)) ((n+1) + -(p j))) (z j))) =
      (((-(p j)).negOnePow : ℤ)) • (map k S A Q' Z (𝟙 _)
        (Z.d (n + -(p j)) ((n+1) + -(p j))))
        (rightTermEquiv k S A e Z (p j) (n + -(p j)) (z j))
    rw [map_zsmul]
    congr 1
    exact congrArg (fun f => f (z j)) (rightTermEquiv_map_id k S A e Z (p j) (n + -(p j)) ((n+1) + -(p j)) (Z.d (n + -(p j)) ((n+1) + -(p j))))
  · apply Finset.sum_congr rfl
    intro i _
    exact congrArg (fun f => f (z i)) (right_entry k S A e Z p n i j)

/-- Tensor total preserves actual isomorphisms of genuine bimodule complexes and their outside action. -/
def totalRightIso : total k S A Q Z p hp ≅ total k S A Q' Z p hp :=
  HomologicalComplex.Hom.isoOfComponents (fun n => (rightTotalEquiv k S A e Z p n).toModuleIso) (by
    intro n m h
    change n+1=m at h
    subst m
    have h₁ : (total k S A Q Z p hp).d n (n+1) = ModuleCat.ofHom (differential k S A Q Z p n) :=
      CochainComplex.of_d (fun n => ModuleCat.of S (totalTerm k S A Q Z p n))
        (fun n => ModuleCat.ofHom (differential k S A Q Z p n)) n
    have h₂ : (total k S A Q' Z p hp).d n (n+1) = ModuleCat.ofHom (differential k S A Q' Z p n) :=
      CochainComplex.of_d (fun n => ModuleCat.of S (totalTerm k S A Q' Z p n))
        (fun n => ModuleCat.ofHom (differential k S A Q' Z p n)) n
    rw [h₁,h₂]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    exact (right_differential k S A e Z p n z).symm)
end LittleFinitistic.BimoduleComplexTensor

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_ColumnFinite
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.ArrowVertex.vertex_additive _root_.OAI.ExternalTensor.Section4.SourceFiltration.inclusion2_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroCone_inclusion_isIso _root_.OAI.ExternalTensor.Section4.SourceFiltration.zeroTermSubsingleton _root_.OAI.LittleFinitistic.BalancedVertexFunctor.additive _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.additive _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.finite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.scalarTower _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideComm _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticPresentation.instFiniteAuxiliaryEquation _root_.OAI.LittleFinitistic.QuadraticPresentation.instFiniteAuxiliaryLetter _root_.OAI.LittleFinitistic.QuadraticPresentation.step_finite _root_.OAI.LittleFinitistic.QuadraticPresentation.word_finite _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated _root_.OAI.LittleFinitistic.cyclicRing_finiteInst
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

theorem sum_finite {I : Type} [Fintype I] (K : I → BiComplex k B)
    (n : ℤ) (hK : ∀ i, FiniteDimensional k ((termK k B n).obj (K i))) :
    FiniteDimensional k ((termK k B n).obj (⨁ K)) := by
  let (i : I) : FiniteDimensional k ((termK k B n).obj (K i)) := hK i
  apply finite_of_iso k ((termK k B n).mapBiproduct K ≪≫ ModuleCat.biproductIsoPi _)
  change Module.Finite k (∀ i, ((termK k B n).obj (K i)))
  infer_instance

end ExternalTensor.Section4

end

end OAI
end


