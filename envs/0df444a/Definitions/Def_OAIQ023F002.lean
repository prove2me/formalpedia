-- Prove2me | Definitions.Def_OAIQ023F002
-- name    : OAIQ023F002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T15:39:53.968219+00:00
-- url     : https://prove2.me/theorems/2e5c4f4a-0af4-46cb-8897-71a815b336f0
-- title:
--   Definitions bundle OAIQ023F002 of the split of OpenAI, An algebra of infinite little finitistic dimension (result family 198)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.LittleFinitistic.Main.exists_counterexample`, carved from OpenAI's openai/math development (OpenAI, *An algebra of infinite little finitistic dimension (result family 198)*, OpenAI Math Release, September 23, 2026, result family 198, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 389 declarations of OpenAI's Lean: 177 definitions, 11 inductive types or structures, 53 instances and 148 theorems. The definitions and types are `OAI.LittleFinitistic.BalancedTensor.Free.coefficientAction`, `OAI.LittleFinitistic.BalancedTensor.Free.evaluateBilinear`, `OAI.LittleFinitistic.BalancedTensor.FreeLeft.coefficientAction`, `OAI.LittleFinitistic.BalancedTensor.FreeLeft.evaluateBilinear`, `OAI.LittleFinitistic.BalancedTensor.ScalarLeftModule`, `OAI.LittleFinitistic.BalancedTensor.ScalarModule`, `OAI.LittleFinitistic.BalancedTensor.Tensor`, `OAI.LittleFinitistic.BalancedTensor.fromScalarModule`, `OAI.LittleFinitistic.BalancedTensor.lift`, `OAI.LittleFinitistic.BalancedTensor.mk`, `OAI.LittleFinitistic.BalancedTensor.relations`, `OAI.LittleFinitistic.BalancedTensor.toScalarModule`, `OAI.LittleFinitistic.BimoduleCoefficients`, `OAI.LittleFinitistic.BimoduleCoefficients.equiv`, `OAI.LittleFinitistic.BimoduleCoefficients.map`, `OAI.LittleFinitistic.BimoduleComplexTensor.rightComplex`, `OAI.LittleFinitistic.BimoduleTotal.CanonicalInput`, `OAI.LittleFinitistic.BimoduleTotal.forget`, `OAI.LittleFinitistic.BimoduleTotal.instHasDerivedCategoryModuleCat_solutions`, `OAI.LittleFinitistic.BimoduleTotal.instHasDerivedCategoryModuleCat_solutions_1`, `OAI.LittleFinitistic.BimoduleTotal.instHasDerivedCategoryModuleCat_solutions_2`, `OAI.LittleFinitistic.BimoduleTotal.instHasDerivedCategoryModuleCat_solutions_4`, `OAI.LittleFinitistic.BimoduleTotal.instHasDerivedCategoryModuleCat_solutions_5`, `OAI.LittleFinitistic.BimoduleTotal.intervalDegrees`, `OAI.LittleFinitistic.BimoduleTotal.piSingleEquiv`, `OAI.LittleFinitistic.BimoduleTotal.signedShift`, `OAI.LittleFinitistic.BimoduleTotal.signedShiftComm`, `OAI.LittleFinitistic.BimoduleTotal.signedShiftIso`, `OAI.LittleFinitistic.BimoduleTotal.singleInput`, `OAI.LittleFinitistic.BlockModule.First`, `OAI.LittleFinitistic.BlockModule.Second`, `OAI.LittleFinitistic.BlockModule.derivedFirst`, `OAI.LittleFinitistic.BlockModule.derivedFirstComparison`, `OAI.LittleFinitistic.BlockModule.derivedFirstComponent`, `OAI.LittleFinitistic.BlockModule.derivedFirstComponentFactors`, `OAI.LittleFinitistic.BlockModule.derivedFirstIso`, `OAI.LittleFinitistic.BlockModule.derivedFirstRetraction`, `OAI.LittleFinitistic.BlockModule.firstComplex`, `OAI.LittleFinitistic.BlockModule.firstComplexComponentIso`, `OAI.LittleFinitistic.BlockModule.firstComplexFunctor` and 148 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: `Finitistic_Bimodule_BimoduleAugmentationQuasiIso`, `Finitistic_Bimodule_BimoduleBarComparisonIso`, `Finitistic_Bimodule_BimoduleBarComparisonMap`, `Finitistic_Bimodule_BimoduleBarResolution`, `Finitistic_Bimodule_BimoduleBarStalk`, `Finitistic_Bimodule_BimoduleDerivedInterval`, `Finitistic_Bimodule_BimoduleResolutionBarAPI`, `Finitistic_Bimodule_BimoduleScalarEvaluation`, `Finitistic_Bimodule_BimoduleShiftCoherence`, `Finitistic_Bimodule_BimoduleSingleTerms`, `Finitistic_Bimodule_BimoduleTotalPresentation`, `Finitistic_Bimodule_BimoduleTotalUnderlying`, `Finitistic_Encoding_FiniteBasisIso`, `Finitistic_Encoding_PresentationReindex`, `Finitistic_Encoding_QuadraticEncoding`, `Finitistic_Encoding_QuadraticPresentation`, `Finitistic_Encoding_RelationBasisAction`, `Finitistic_Encoding_RelationMatrixSequence`, `Finitistic_Localization_BoundedHomotopy`, `Finitistic_Localization_ChainRepresentatives`, `Finitistic_Localization_DerivedTruncationCohomology`, `Finitistic_Localization_DiagramEvaluationSquares`, `Finitistic_Localization_DiagramLifting`, `Finitistic_Localization_EvaluationModule`, `Finitistic_Localization_FiniteProjectiveHomotopy`, `Finitistic_Localization_FiniteSumTransport`, `Finitistic_Localization_FiniteSupportReindex`, `Finitistic_Localization_FixedDiagram`, `Finitistic_Localization_FormalSummandAction`, `Finitistic_Localization_IntegerExtensionFunctor`, `Finitistic_Localization_OddDouble`, `Finitistic_Localization_ProjectiveComplexes`, `Finitistic_Localization_QuotientAction`, `Finitistic_Localization_SignedCochainShift`, `Finitistic_Localization_SingleDegreeNaturality`, `Finitistic_Localization_TensorEvaluationComparison`, `Finitistic_Localization_TensorEvaluationFunctor`, `Finitistic_Localization_TwoConeVerdier`, `Finitistic_Ordinary_OrdinaryAssociativeTensorModules`, `Finitistic_Ordinary_OrdinaryBimodule`, `Finitistic_Ordinary_OrdinaryBimoduleAssociativeTerms`, `Finitistic_Ordinary_OrdinaryBimoduleAssociativity`, `Finitistic_Ordinary_OrdinaryBimoduleCoefficientEquiv`, `Finitistic_Ordinary_OrdinaryBimoduleCoefficients`, `Finitistic_Ordinary_OrdinaryBimoduleTensorTerms`, `Finitistic_Ordinary_OrdinaryBimoduleTotalAssociativity`, `Finitistic_Ordinary_OrdinaryBlockComplexes`, `Finitistic_Ordinary_OrdinaryBlockDerived`, `Finitistic_Ordinary_OrdinaryBlockModules`, `Finitistic_Ordinary_OrdinaryComplexTensorMaps`, `Finitistic_Ordinary_OrdinaryConeCoordinates`, `Finitistic_Ordinary_OrdinaryConeQuasiIso`, `Finitistic_Ordinary_OrdinaryFiniteConeReindex`, `Finitistic_Ordinary_OrdinaryFinitePiSupport`, `Finitistic_Ordinary_OrdinaryFirstComponentExact`, `Finitistic_Ordinary_OrdinaryFirstDerivedCompatibility`, `Finitistic_Ordinary_OrdinaryFirstDerivedRetraction`, `Finitistic_Ordinary_OrdinaryFixedTensorFunctor`, `Finitistic_Ordinary_OrdinaryFreeTensor`, `Finitistic_Ordinary_OrdinaryFreeTensorExactness`, `Finitistic_Ordinary_OrdinaryProductComponent`, `Finitistic_Ordinary_OrdinaryProductProjective`, `Finitistic_Ordinary_OrdinaryProductSplitting`, `Finitistic_Ordinary_OrdinaryRestrictionHomology`, `Finitistic_Ordinary_OrdinaryRightProjective`, `Finitistic_Ordinary_OrdinaryShiftSign`, `Finitistic_Ordinary_OrdinaryTensorInputMaps`, `Finitistic_Ordinary_OrdinaryTensorMixedSign`, `Finitistic_Ordinary_OrdinaryTensorRightRestriction`, `Finitistic_Ordinary_OrdinaryTensorTotalAcyclic`, `Finitistic_Ordinary_OrdinaryTriangularExactness`, `Finitistic_Rectification_BiprodEvaluationSquare`, `Finitistic_Rectification_ColumnProperties`, `Finitistic_Rectification_GradedVertexAcyclic`, `Finitistic_Rectification_LeftVertexHomology`, `Finitistic_Rectification_RectificationAcyclic`, `Finitistic_Rectification_TensorProjection`, `Finitistic_Rectification_TotalInterchange`, `Finitistic_Rectification_VertexProjectives`, `Finitistic_Selection_CharacterModule`, `Finitistic_Selection_FinitePresentation`, `Finitistic_Selection_FiniteQuotient`, `Finitistic_Selection_GroupSelection`, `Finitistic_Tensor_BalancedFreeLeft`, `Finitistic_Tensor_BalancedTensor`, `Finitistic_Tensor_IdempotentTensor`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ023F007`, `OAIQ023F008` and `OAIQ023F009`.
-- source:
--   OpenAI, An algebra of infinite little finitistic dimension (result family 198), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 198; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-algebra-of-infinite-little-finitistic-dimension-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Lean.Elab.Tactic.Omega

section
-- module Solutions.OAIQ023_Fin.Finitistic_Tensor_BalancedTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped TensorProduct
namespace LittleFinitistic.BalancedTensor
universe u v w w' z
variable (k : Type u) [Field k] (A : Type v) [Ring A]
variable (M : Type w) [AddCommGroup M] [Module k M] [Module Aᵐᵒᵖ M]
variable (N : Type w') [AddCommGroup N] [Module k N] [Module A N]

/-- Balancing relations for a right A-module and a left A-module, over k. -/
def relations : Submodule k (M ⊗[k] N) := Submodule.span k
  (Set.range fun q : A × M × N =>
    (MulOpposite.op q.1 • q.2.1) ⊗ₜ[k] q.2.2 - q.2.1 ⊗ₜ[k] (q.1 • q.2.2))

/-- Tensor over the possibly noncommutative algebra A. -/
abbrev Tensor := (M ⊗[k] N) ⧸ relations k A M N

def mk : M →ₗ[k] N →ₗ[k] Tensor k A M N :=
  (TensorProduct.mk k M N).compr₂ (relations k A M N).mkQ

variable {k A M N}

theorem balance (a : A) (m : M) (n : N) :
    mk k A M N (MulOpposite.op a • m) n = mk k A M N m (a • n) := by
  apply sub_eq_zero.mp
  change (relations k A M N).mkQ ((MulOpposite.op a • m) ⊗ₜ[k] n) -
    (relations k A M N).mkQ (m ⊗ₜ[k] (a • n)) = 0
  rw [← map_sub]
  exact (Submodule.Quotient.mk_eq_zero _).mpr
    (Submodule.subset_span ⟨(a,m,n),rfl⟩)

variable {V : Type z} [AddCommGroup V] [Module k V]

/-- Universal property for k-bilinear maps satisfying the actual A-balancing equation. -/
def lift (f : M →ₗ[k] N →ₗ[k] V)
    (hf : ∀ (a : A) m n, f (MulOpposite.op a • m) n = f m (a • n)) : Tensor k A M N →ₗ[k] V :=
  (relations k A M N).liftQ (TensorProduct.lift f) (by
    rw [relations, Submodule.span_le]
    rintro _ ⟨⟨a,m,n⟩,rfl⟩
    change TensorProduct.lift f ((MulOpposite.op a • m) ⊗ₜ[k] n - m ⊗ₜ[k] (a • n)) = 0
    simp only [map_sub, TensorProduct.lift.tmul, hf, sub_self])

@[simp] theorem lift_mk (f : M →ₗ[k] N →ₗ[k] V)
    (hf : ∀ (a : A) m n, f (MulOpposite.op a • m) n = f m (a • n)) (m : M) (n : N) :
    lift f hf (mk k A M N m n) = f m n := rfl

end LittleFinitistic.BalancedTensor

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_TensorEvaluationFunctor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.BalancedTensor
universe u v w z
variable (k : Type u) [Field k] (A : Type v) [Ring A] [Algebra k A]

abbrev ScalarModule (M : ModuleCat.{w} Aᵐᵒᵖ) :=
  (ModuleCat.restrictScalars (algebraMap k Aᵐᵒᵖ)).obj M

instance scalarModuleTower (M : ModuleCat.{w} Aᵐᵒᵖ) :
    IsScalarTower k Aᵐᵒᵖ (ScalarModule k A M) where
  smul_assoc c a m := by
    change (c • a) • (m : M) = algebraMap k Aᵐᵒᵖ c • (a • (m : M))
    rw [Algebra.smul_def, mul_smul]

end LittleFinitistic.BalancedTensor

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_ColumnProperties
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

instance rightFiniteBiproducts : HasFiniteBiproducts (ModuleCat.{u} Bᵐᵒᵖ) :=
  HasFiniteBiproducts.of_hasFiniteProducts
instance rightBinaryBiproducts : HasBinaryBiproducts (ModuleCat.{u} Bᵐᵒᵖ) :=
  HasBinaryBiproducts.of_hasBinaryProducts

theorem sum_isZero {C : Type*} [Category C] [HasZeroMorphisms C]
    {I : Type} (K : I → C) [HasBiproduct K] (hK : ∀ i, IsZero (K i)) :
    IsZero (⨁ K) := by
  apply (IsZero.iff_id_eq_zero _).2
  apply biproduct.hom_ext
  intro i
  simp only [Category.id_comp, zero_comp]
  exact (hK i).eq_zero_of_tgt _

end ExternalTensor.Section4

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Encoding_QuadraticEncoding
attribute [-instance] _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts
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

/-- Coefficients of the finite quadratic relation list, including degrees zero and one. -/
structure Relations (k : Type u) (d t : ℕ) where
  constant : Fin t → k
  linear : Fin t → Fin d → k
  quadratic : Fin t → Fin d → Fin d → k

end LittleFinitistic.QuadraticEncoding

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_ChainRepresentatives
attribute [-instance] _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LittleFinitistic.ChainRepresentatives
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open HomologicalComplex

variable {k : Type*} [CommRing k]
variable {V : Type*} [Category V] [Preadditive V] [Linear k V]
variable {ι : Type*} {s : ComplexShape ι}

/-- Choosing chain representatives of a finite quadratic diagram supplies actual,
specified null-homotopies for all its relations. -/
theorem quadratic_chain_representatives (na nb nr : ℕ)
    (D₀ D₁ D₂ : HomologicalComplex V s)
    (a : Fin na → ((HomotopyCategory.quotient V s).obj D₀ ⟶
      (HomotopyCategory.quotient V s).obj D₁))
    (b : Fin nb → ((HomotopyCategory.quotient V s).obj D₁ ⟶
      (HomotopyCategory.quotient V s).obj D₂))
    (c : Fin nr → Fin na → Fin nb → k)
    (hc : ∀ t, ∑ i, ∑ j, c t i j • (a i ≫ b j) = 0) :
    ∃ (f : Fin na → (D₀ ⟶ D₁)) (g : Fin nb → (D₁ ⟶ D₂)),
      (∀ i, (HomotopyCategory.quotient V s).map (f i) = a i) ∧
      (∀ j, (HomotopyCategory.quotient V s).map (g j) = b j) ∧
      Nonempty (∀ t, Homotopy (∑ i, ∑ j, c t i j • (f i ≫ g j)) 0) := by
  classical
  let q := HomotopyCategory.quotient V s
  let f := fun i => q.preimage (a i)
  let g := fun j => q.preimage (b j)
  have hf (i) : q.map (f i) = a i := q.map_preimage _
  have hg (j) : q.map (g j) = b j := q.map_preimage _
  refine ⟨f,g,hf,hg,⟨fun t => ?_⟩⟩
  apply HomotopyCategory.homotopyOfEq
  change q.map (∑ i, ∑ j, c t i j • (f i ≫ g j)) = q.map 0
  simp only [Functor.map_sum,Functor.map_smul,Functor.map_comp,hf,hg,Functor.map_zero,hc]

end LittleFinitistic.ChainRepresentatives

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_RectificationAcyclic
attribute [-instance] _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LittleFinitistic.RectificationAcyclic
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex

variable {C : Type*} [Category C] [Abelian C]

/-- The ordinary cone of a quasi-isomorphism is acyclic. -/
theorem cone_acyclic {K L : CochainComplex C ℤ} (f : K ⟶ L) [QuasiIso f] :
    (mappingCone f).Acyclic := by
  let P := HomotopyCategory.subcategoryAcyclic C
  have hf : P.trW ((HomotopyCategory.quotient C (.up ℤ)).map f) := by
    rw [← HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic,
      HomotopyCategory.quotient_map_mem_quasiIso_iff,HomologicalComplex.mem_quasiIso_iff]
    infer_instance
  have hT := HomotopyCategory.mappingCone_triangleh_distinguished f
  have hz := (P.trW_iff_of_distinguished (mappingCone.triangleh f) hT).1 hf
  exact (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).1 hz

end LittleFinitistic.RectificationAcyclic

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Encoding_FiniteBasisIso
attribute [-instance] _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.FiniteBasisIso
universe u
variable {k V : Type u} [Field k] [AddCommGroup V] [Module k V]
variable {I : Type} [Fintype I] (b : Module.Basis I k V)
abbrev family : I → ModuleCat.{u} k := fun _ => ModuleCat.of k k

/-- An actual finite basis gives the scalar-column isomorphism, including the empty basis. -/
def iso : (⨁ (family (k := k) : I → _)) ≅ ModuleCat.of k V :=
  ModuleCat.biproductIsoPi _ ≪≫ b.equivFun.symm.toModuleIso

theorem pi_hom_proj (j : I) :
    (ModuleCat.biproductIsoPi (family (k := k) : I → _)).hom ≫
      ModuleCat.ofHom (LinearMap.proj j) = biproduct.π _ j := by
  rw [← ModuleCat.biproductIsoPi_inv_comp_π (family (k := k) : I → _) j]
  simp only [Iso.hom_inv_id_assoc]

theorem injection_apply (i : I) (c : k) :
    (biproduct.ι (family (k := k) : I → _) i ≫ (iso b).hom).hom c = c • b i := by
  apply b.equivFun.injective
  change b.equivFun (b.equivFun.symm ((ModuleCat.Hom.hom
    (biproduct.ι (family (k := k) : I → _) i ≫ (ModuleCat.biproductIsoPi _).hom)) c)) =
      b.equivFun (c • b i)
  rw [LinearEquiv.apply_symm_apply]
  funext j
  have h := congrArg (fun f : ModuleCat.of k k ⟶ ModuleCat.of k k => f.hom c)
    (congrArg (fun f => biproduct.ι (family (k := k) : I → _) i ≫ f)
      (pi_hom_proj (k := k) j))
  rw [show ((biproduct.ι (family (k := k) : I → _) i ≫
      (ModuleCat.biproductIsoPi _).hom).hom c) j =
      (biproduct.ι (family (k := k) : I → _) i ≫ biproduct.π _ j).hom c from h]
  classical
  by_cases hij : i=j
  · subst j; simp
  · simp [hij,Ne.symm hij]
end LittleFinitistic.FiniteBasisIso

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_TensorProjection
attribute [-instance] _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
namespace LittleFinitistic.TensorProjection
variable {k B M M' N : Type*} [Field k] [Ring B] [Algebra k B]
  [AddCommGroup M] [Module k M] [AddCommGroup M'] [Module k M']
  [AddCommGroup N] [Module k N] [Module Bᵐᵒᵖ N] [IsScalarTower k Bᵐᵒᵖ N]

variable (p : M →ₗ[k] M)

theorem range_fixed (hp : p.comp p = p) (x : p.range) : p x.val = x.val := by
  obtain ⟨m,hm⟩ := x.property
  have h := LinearMap.congr_fun hp m
  simpa only [LinearMap.comp_apply,hm] using h

end LittleFinitistic.TensorProjection

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Encoding_RelationMatrixSequence
attribute [-instance] _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace LittleFinitistic.RelationMatrixSequence
open QuadraticEncoding
universe u
variable {k : Type u} [Field k] {d t : ℕ} (P : Relations k d t)

theorem transported_zero {C : Type*} [Category C] [HasZeroMorphisms C]
    {X₁ X₂ X₃ Y₁ Y₂ : C} (e₁ : Y₁ ≅ X₁) (e₂ : Y₂ ≅ X₂)
    (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃) (h : f ≫ g = 0) :
    (e₁.hom ≫ f ≫ e₂.inv) ≫ (e₂.hom ≫ g) = 0 := by
  simp only [Category.assoc, Iso.inv_hom_id_assoc, h, comp_zero]

theorem transported_comp_hom {C : Type*} [Category C]
    {X₁ X₂ Y₁ Y₂ : C} (e₁ : Y₁ ≅ X₁) (e₂ : Y₂ ≅ X₂) (f : X₁ ⟶ X₂) :
    e₁.hom ≫ f = (e₁.hom ≫ f ≫ e₂.inv) ≫ e₂.hom := by
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

end LittleFinitistic.RelationMatrixSequence

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryConeQuasiIso
attribute [-instance] _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic
universe u v
variable {C : Type u} [Category.{v} C] [Abelian C]
variable {K L : CochainComplex C ℤ} (f : K ⟶ L)

/-- The actual native mapping cone detects quasi-isomorphisms. -/
theorem quasiIso_iff_mappingCone_acyclic : QuasiIso f ↔ (CochainComplex.mappingCone f).Acyclic := by
  rw [← HomologicalComplex.mem_quasiIso_iff,
    ← HomotopyCategory.quotient_map_mem_quasiIso_iff,
    HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
  exact ((HomotopyCategory.subcategoryAcyclic C).trW_iff_of_distinguished
    (CochainComplex.mappingCone.triangleh f) (HomotopyCategory.mappingCone_triangleh_distinguished f)).trans
    (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _)
end LittleFinitistic

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryConeCoordinates
attribute [-instance] _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory Limits
namespace LittleFinitistic.ConeCoordinates
universe u
variable {R : Type u} [Ring R]
variable {K L : CochainComplex (ModuleCat.{u} R) ℤ} (f : K ⟶ L)

/-- The native cone term in its actual two module coordinates. -/
def coordinateIso (n : ℤ) : (CochainComplex.mappingCone f).X n ≅
    ModuleCat.of R (K.X (n+1) × L.X n) :=
  HomologicalComplex.homotopyCofiber.XIsoBiprod f n (n+1) rfl ≪≫
    ModuleCat.biprodIsoProd (K.X (n+1)) (L.X n)

def coordinateEquiv (n : ℤ) : (CochainComplex.mappingCone f).X n ≃ₗ[R] (K.X (n+1) × L.X n) :=
  (coordinateIso f n).toLinearEquiv

theorem coordinate_fst (n : ℤ) :
    (coordinateIso f n).hom ≫ ModuleCat.ofHom (LinearMap.fst R (K.X (n+1)) (L.X n)) =
      HomologicalComplex.homotopyCofiber.fstX f n (n+1) rfl := by
  unfold coordinateIso
  erw [Iso.trans_hom,Category.assoc,← ModuleCat.biprodIsoProd_inv_comp_fst,Iso.hom_inv_id_assoc]
  rfl

theorem coordinate_snd (n : ℤ) :
    (coordinateIso f n).hom ≫ ModuleCat.ofHom (LinearMap.snd R (K.X (n+1)) (L.X n)) =
      HomologicalComplex.homotopyCofiber.sndX f n := by
  unfold coordinateIso
  erw [Iso.trans_hom,Category.assoc,← ModuleCat.biprodIsoProd_inv_comp_snd,Iso.hom_inv_id_assoc]
  apply HomologicalComplex.homotopyCofiber.ext_from_X f (n+1) n rfl
  · erw [← Category.assoc, HomologicalComplex.homotopyCofiber.inlX_XIsoBiprod_hom,
      biprod.inl_snd, HomologicalComplex.homotopyCofiber.inlX_sndX]
  · erw [← Category.assoc, HomologicalComplex.homotopyCofiber.inrX_XIsoBiprod_hom,
      biprod.inr_snd, HomologicalComplex.homotopyCofiber.inrX_sndX]

/-- The first coordinate of the native cone differential carries its negative sign. -/
theorem differential_fst (n : ℤ) (z : (CochainComplex.mappingCone f).X n) :
    (coordinateEquiv f (n+1) (((CochainComplex.mappingCone f).d n (n+1)).hom z)).1 =
      -((K.d (n+1) ((n+1)+1)).hom (coordinateEquiv f n z).1) := by
  have hh := HomologicalComplex.homotopyCofiber.d_fstX f n (n+1) ((n+1)+1) rfl rfl
  rw [← coordinate_fst,← coordinate_fst] at hh
  exact congrArg (fun g => g.hom z) hh

/-- The second coordinate contains the input map and the target differential. -/
theorem differential_snd (n : ℤ) (z : (CochainComplex.mappingCone f).X n) :
    (coordinateEquiv f (n+1) (((CochainComplex.mappingCone f).d n (n+1)).hom z)).2 =
      (f.f (n+1)).hom (coordinateEquiv f n z).1 +
      (L.d n (n+1)).hom (coordinateEquiv f n z).2 := by
  have hh := HomologicalComplex.homotopyCofiber.d_sndX f n (n+1) rfl
  rw [← coordinate_snd,← coordinate_snd,← coordinate_fst] at hh
  exact congrArg (fun g => g.hom z) hh
end LittleFinitistic.ConeCoordinates

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryTriangularExactness
attribute [-instance] _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
namespace LittleFinitistic.TriangularExactness
universe u v
variable {R : Type u} [Ring R] {l : ℕ}
variable (E F G : Fin l → Type v)
variable [∀ i, AddCommGroup (E i)] [∀ i, Module R (E i)]
variable [∀ i, AddCommGroup (F i)] [∀ i, Module R (F i)]
variable [∀ i, AddCommGroup (G i)] [∀ i, Module R (G i)]

/-- A finite upper triangular differential with exact diagonal complexes is exact.
The argument eliminates one coordinate at a time; the modules may be arbitrary. -/
theorem exact_of_diagonal
    (d : (∀ i, E i) →ₗ[R] (∀ i, F i)) (e : (∀ i, F i) →ₗ[R] (∀ i, G i))
    (d₀ : ∀ i, E i →ₗ[R] F i) (e₀ : ∀ i, F i →ₗ[R] G i)
    (hzero : e.comp d = 0)
    (hd : ∀ (i : Fin l) (x : E i) (j : Fin l), j.val < i.val → d (Pi.single i x) j = 0)
    (hdi : ∀ (i : Fin l) (x : E i), d (Pi.single i x) i = d₀ i x)
    (he : ∀ (i : Fin l) (z : ∀ j, F j), (∀ j : Fin l, j.val < i.val → z j = 0) →
      e z i = e₀ i (z i))
    (hex : ∀ i, Function.Exact (d₀ i) (e₀ i)) : Function.Exact d e := by
  classical
  intro z
  constructor
  · intro hz
    have step (n : ℕ) (hn : n ≤ l) :
        ∃ w : ∀ i, E i, ∀ j : Fin l, j.val < n → (z-d w) j = 0 := by
      induction n with
      | zero => exact ⟨0,fun j hj => by omega⟩
      | succ n ih =>
        obtain ⟨w,hw⟩ := ih (by omega)
        let i : Fin l := ⟨n,by omega⟩
        have hclosed : e (z-d w) = 0 := by
          rw [map_sub,hz]
          have hed : e (d w) = 0 := congrArg (fun f : (∀ i, E i) →ₗ[R] (∀ i, G i) => f w) hzero
          rw [hed,sub_self]
        have hei : e₀ i ((z-d w) i) = 0 := by
          rw [← he i (z-d w) (fun j hj => hw j hj)]
          exact congrArg (fun x => x i) hclosed
        obtain ⟨y,hy⟩ := (hex i _).mp hei
        refine ⟨w + Pi.single i y, ?_⟩
        intro j hj
        by_cases hji : j.val < n
        · have hj0 := hd i y j hji
          change z j - d (w + Pi.single i y) j = 0
          rw [map_add,Pi.add_apply,hj0,add_zero]
          exact hw j hji
        · have hij : j = i := Fin.ext (by dsimp [i]; omega)
          subst j
          change z i - d (w + Pi.single i y) i = 0
          rw [map_add,Pi.add_apply,hdi,hy]
          change z i - (d w i + (z i - d w i)) = 0
          abel
    obtain ⟨w,hw⟩ := step l (by rfl)
    refine ⟨w, ?_⟩
    ext i
    exact (sub_eq_zero.mp (hw i i.isLt)).symm
  · rintro ⟨w,rfl⟩
    exact congrArg (fun f : (∀ i, E i) →ₗ[R] (∀ i, G i) => f w) hzero
end LittleFinitistic.TriangularExactness

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryFiniteConeReindex
attribute [-instance] _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.FiniteColumnComplex
universe u
variable {R : Type u} [Ring R] {l : ℕ}
variable (K L : Fin l → CochainComplex (ModuleCat.{u} R) ℤ)
variable (f : ∀ i, K i ⟶ L i)

abbrev coneColumn (i : Fin l) := CochainComplex.mappingCone (f i)
end LittleFinitistic.FiniteColumnComplex

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Tensor_IdempotentTensor
attribute [-instance] _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
namespace LittleFinitistic.IdempotentTensor
universe u v w
variable {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A]
variable (e : A)

/-- The actual projective right ideal eA, presented as the fixed points of left multiplication. -/
def rightIdeal : Submodule Aᵐᵒᵖ A where
  carrier := {a | e*a=a}
  zero_mem' := mul_zero e
  add_mem' ha hb := by change e*(_+_)=_+_; rw [mul_add,ha,hb]
  smul_mem' b a ha := by
    change e*(a*b.unop)=a*b.unop
    rw [← mul_assoc,ha]

variable (N : Type w) [AddCommGroup N] [Module k N] [Module A N]
  [IsScalarTower k A N]

/-- The vertex part eN, without assuming e is central. -/
def leftSpace : Submodule k N where
  carrier := {n | e • n = n}
  zero_mem' := smul_zero e
  add_mem' ha hb := by change e • (_+_) = _+_; rw [smul_add,ha,hb]
  smul_mem' c n hn := by change e • (c • n) = c • n; rw [smul_comm e c,hn]

def productEval : rightIdeal e →ₗ[k] N →ₗ[k] leftSpace (k := k) e N where
  toFun a :=
    { toFun := fun n => ⟨a.val • n, by change e • (a.val • n) = a.val • n; rw [← mul_smul,a.property]⟩
      map_add' n m := Subtype.ext (smul_add a.val n m)
      map_smul' c n := Subtype.ext (smul_comm a.val c n) }
  map_add' a b := by ext n; exact add_smul a.val b.val n
  map_smul' c a := by ext n; exact smul_assoc c a.val n

end LittleFinitistic.IdempotentTensor

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryBimodule
attribute [-instance] _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace LittleFinitistic.OrdinarySimulation
universe u
variable {k B : Type u} [Field k] [Ring B] [Algebra k B]
abbrev Enveloping (k B : Type u) [Field k] [Ring B] [Algebra k B] := B ⊗[k] Bᵐᵒᵖ

end LittleFinitistic.OrdinarySimulation

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryShiftSign
attribute [-instance] _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.OrdinarySimulation
universe u v
variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- Multiplication by an integer unit is an actual isomorphism in any additive category. -/
def integerUnitIso (X : C) (u : ℤˣ) : X ≅ X where
  hom := u • 𝟙 X
  inv := u⁻¹ • 𝟙 X
  hom_inv_id := by
    simp only [Linear.units_smul_comp, Linear.comp_units_smul, Category.id_comp,
      smul_smul, inv_mul_cancel, one_smul]
  inv_hom_id := by
    simp only [Linear.units_smul_comp, Linear.comp_units_smul, Category.id_comp,
      smul_smul, mul_inv_cancel, one_smul]

end LittleFinitistic.OrdinarySimulation

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryFixedTensorFunctor
attribute [-instance] _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.BalancedTensor
universe u
variable (k A : Type u) [Field k] [Ring A] [Algebra k A]

abbrev ScalarLeftModule (N : ModuleCat.{u} A) :=
  (ModuleCat.restrictScalars (algebraMap k A)).obj N

instance scalarLeftTower (N : ModuleCat.{u} A) : IsScalarTower k A (ScalarLeftModule k A N) where
  smul_assoc r a n := by
    change (r • a) • (n : N) = algebraMap k A r • (a • (n : N))
    rw [Algebra.smul_def,mul_smul]

end LittleFinitistic.BalancedTensor

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryFreeTensor
attribute [-instance] _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
namespace LittleFinitistic.BalancedTensor.Free
universe u
variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable (I N : Type u) [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]

/-- A right-regular coefficient acts on the left tensor factor by its unop. -/
def coefficientAction : Aᵐᵒᵖ →ₗ[k] N →ₗ[k] N :=
  (Algebra.lsmul k k N).toLinearMap.comp (MulOpposite.opLinearEquiv k).symm.toLinearMap

/-- Coordinate evaluation of a free right module tensor N. -/
def evaluateBilinear : (I →₀ Aᵐᵒᵖ) →ₗ[k] N →ₗ[k] (I →₀ N) :=
  Finsupp.lsum k (fun i => (coefficientAction (k := k) (A := A) N).compr₂ (Finsupp.lsingle i))

@[simp] theorem evaluateBilinear_single (i : I) (x : Aᵐᵒᵖ) (n : N) :
    evaluateBilinear (k := k) I N (Finsupp.single i x) n = Finsupp.single i (x.unop • n) := by
  simp only [evaluateBilinear,Finsupp.lsum_single]
  rfl

end LittleFinitistic.BalancedTensor.Free

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryFreeTensorExactness
attribute [-instance] _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
namespace LittleFinitistic.BalancedTensor.Free
universe u
variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable (I : Type u)
variable {N N' N'' : Type u}
variable [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]
variable [AddCommGroup N'] [Module k N'] [Module A N'] [IsScalarTower k A N']
variable [AddCommGroup N''] [Module k N''] [Module A N''] [IsScalarTower k A N'']

/-- Direct sums preserve exactness, with a preimage supported on the given finite support. -/
theorem finsupp_exact (f : N →ₗ[A] N') (g : N' →ₗ[A] N'') (h : Function.Exact f g) :
    Function.Exact (Finsupp.mapRange.linearMap (f.restrictScalars k) : (I →₀ N) →ₗ[k] (I →₀ N'))
      (Finsupp.mapRange.linearMap (g.restrictScalars k)) := by
  classical
  intro z
  constructor
  · intro hz
    have hg (i : I) : g (z i) = 0 := congrArg (fun x : I →₀ N'' => x i) hz
    let y : I →₀ N := Finsupp.onFinset z.support
      (fun i => if hi : z i = 0 then 0 else Classical.choose ((h (z i)).mp (hg i))) (by
        intro i hi
        by_contra hn
        have hz0 : z i = 0 := by simpa only [Finsupp.mem_support_iff,not_not] using hn
        exact hi (by simp [hz0]))
    refine ⟨y, ?_⟩
    ext i
    change f (if hi : z i = 0 then 0 else Classical.choose ((h (z i)).mp (hg i))) = z i
    split_ifs with hi
    · rw [map_zero,hi]
    · exact Classical.choose_spec ((h (z i)).mp (hg i))
  · rintro ⟨y,rfl⟩
    ext i
    exact (h (f (y i))).mpr ⟨y i,rfl⟩

end LittleFinitistic.BalancedTensor.Free

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryComplexTensorMaps
attribute [-instance] _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.ComplexTensor
open BalancedTensor
universe u
variable (k A : Type u) [Field k] [Ring A] [Algebra k A]
variable (Q : CochainComplex (ModuleCat.{u} Aᵐᵒᵖ) ℤ)
variable (Z : CochainComplex (ModuleCat.{u} A) ℤ)

abbrev rightTerm (p : ℤ) := ScalarLeftModule k Aᵐᵒᵖ (Q.X p)
abbrev leftTerm (q : ℤ) := ScalarLeftModule k A (Z.X q)
end LittleFinitistic.ComplexTensor

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryTensorMixedSign
attribute [-instance] _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.ComplexTensor
universe u
variable (k A : Type u) [Field k] [Ring A] [Algebra k A]
variable (Q : CochainComplex (ModuleCat.{u} Aᵐᵒᵖ) ℤ)
variable (Z : CochainComplex (ModuleCat.{u} A) ℤ)

theorem transport_d {q q' r r' : ℤ} (hq : q=q') (hr : r=r') :
    eqToHom (congrArg Z.X hq) ≫ Z.d q' r' = Z.d q r ≫ eqToHom (congrArg Z.X hr) := by
  subst q'
  subst r'
  simp only [eqToHom_refl,Category.id_comp,Category.comp_id]

end LittleFinitistic.ComplexTensor

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryTensorTotalAcyclic
attribute [-instance] _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace LittleFinitistic
namespace OrdinarySimulation.TensorResolution
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B] (l : ℕ)

/-- Exactly the manuscript's finite interval [-l,0] of Q_T. -/
def finiteDegrees (i : Fin (l+1)) : ℤ := -(l:ℤ) + i.val

theorem finiteDegrees_strictMono : StrictMono (finiteDegrees l) := by
  intro i j hij
  change -(l:ℤ) + (i.val:ℤ) < -(l:ℤ) + (j.val:ℤ)
  change i.val < j.val at hij
  omega

end OrdinarySimulation.TensorResolution
end LittleFinitistic

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryTensorInputMaps
attribute [-instance] _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.ComplexTensor
open BalancedTensor
universe u
variable (k A : Type u) [Field k] [Ring A] [Algebra k A]
variable (Q : CochainComplex (ModuleCat.{u} Aᵐᵒᵖ) ℤ)
variable {Z Z' : CochainComplex (ModuleCat.{u} A) ℤ} (f : Z ⟶ Z')

theorem inputMap_transport {q q' : ℤ} (h : q=q') :
    eqToHom (congrArg Z.X h) ≫ f.f q' = f.f q ≫ eqToHom (congrArg Z'.X h) := by
  subst q'
  simp only [eqToHom_refl,Category.id_comp,Category.comp_id]

end LittleFinitistic.ComplexTensor

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bimodule_BimoduleTotalUnderlying
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
variable {l : ℕ}
  (p : Fin l → ℤ)
  (hp : StrictMono p)

abbrev forget := (ModuleCat.restrictScalars (algebraMap k B)).mapHomologicalComplex (.up ℤ)

variable (Z : CochainComplex (ModuleCat.{u} B) ℤ)

instance restrictPreservesHomology :
    (ModuleCat.restrictScalars (algebraMap k B)).PreservesHomology :=
  Functor.preservesHomology_of_map_exact _ (fun S hS => by
    rw [ShortComplex.moduleCat_exact_iff] at hS ⊢
    exact hS)

end LittleFinitistic.BimoduleTotal

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bimodule_BimoduleSingleTerms
attribute [-instance] _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology
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
variable (N : ModuleCat.{u} B)

abbrev singleInput := (HomologicalComplex.single (ModuleCat.{u} B) (.up ℤ) 0).obj N

variable {k B}
/-- A finite product with only one possibly nonzero factor is that actual factor. -/
def piSingleEquiv {l : ℕ} (V : Fin l → Type u) [∀ i, AddCommGroup (V i)] [∀ i, Module B (V i)]
    (i : Fin l) (hz : ∀ j, j ≠ i → Subsingleton (V j)) : (∀ j, V j) ≃ₗ[B] V i where
  toFun x := x i
  invFun x := Pi.single i x
  left_inv x := by
    funext j
    by_cases h : j=i
    · subst j; simp
    · let := hz j h
      exact Subsingleton.elim _ _
  right_inv x := by simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end LittleFinitistic.BimoduleTotal

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bimodule_BimoduleDerivedInterval
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

/-- A finite interval of actual right-complex degrees, including both endpoints. -/
def intervalDegrees (lo hi : ℤ) (i : Fin ((hi-lo).toNat+1)) : ℤ := lo + i.val

theorem intervalDegrees_strictMono (lo hi : ℤ) : StrictMono (intervalDegrees lo hi) := by
  intro i j hij
  change lo + (i.val : ℤ) < lo + (j.val : ℤ)
  change i.val < j.val at hij
  omega

/-- Every degree in the support interval really occurs in the finite total. -/
theorem intervalDegrees_covers (lo hi n : ℤ) (hn : lo ≤ n ∧ n ≤ hi) :
    ∃ i, intervalDegrees lo hi i = n := by
  refine ⟨⟨(n-lo).toNat,by omega⟩,?_⟩
  dsimp [intervalDegrees]
  omega

end LittleFinitistic.BimoduleTotal

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bimodule_BimoduleBarResolution
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
local instance instHasDerivedCategoryModuleCat_solutions : HasDerivedCategory.{u+1} (ModuleCat.{u} B) :=
  HasDerivedCategory.standard (ModuleCat.{u} B)
end LittleFinitistic.BimoduleTotal

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Tensor_BalancedFreeLeft
attribute [-instance] _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
namespace LittleFinitistic.BalancedTensor.FreeLeft
universe u
variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable (I M : Type u) [AddCommGroup M] [Module k M] [Module Aᵐᵒᵖ M]
  [IsScalarTower k Aᵐᵒᵖ M]

/-- A coefficient of a free left module acts on the right tensor factor. -/
def coefficientAction : A →ₗ[k] M →ₗ[k] M :=
  (Algebra.lsmul k k M).toLinearMap.comp (MulOpposite.opLinearEquiv k).toLinearMap

def evaluateBilinear : M →ₗ[k] (I →₀ A) →ₗ[k] (I →₀ M) :=
  (Finsupp.lsum k (fun i =>
    (coefficientAction (k := k) (A := A) M).compr₂ (Finsupp.lsingle i))).flip

@[simp] theorem evaluateBilinear_single (i : I) (a : A) (m : M) :
    evaluateBilinear (k := k) I M m (Finsupp.single i a) =
      Finsupp.single i (MulOpposite.op a • m) := by
  simp only [evaluateBilinear,LinearMap.flip_apply,Finsupp.lsum_single]
  rfl

end LittleFinitistic.BalancedTensor.FreeLeft

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_FiniteSupportReindex
attribute [-instance] _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.FiniteSupportReindex
universe u
variable {R : Type u} [Ring R]
variable (V : ℤ → ModuleCat.{u} R)
variable {l m : ℕ} (p : Fin l → ℤ) (q : Fin m → ℤ)

/-- Extend a finite family of actual components by zero in every other degree. -/
def coefficient (n : ℤ) : (∀ i, V (p i)) →ₗ[R] V n := by
  classical
  exact if h : ∃ i, p i = n then
    ((eqToHom (congrArg V h.choose_spec)).hom).comp (LinearMap.proj h.choose)
  else 0

@[simp] theorem coefficient_at (hp : Function.Injective p) (i : Fin l) (x : ∀ i, V (p i)) :
    coefficient V p (p i) x = x i := by
  classical
  unfold coefficient
  split_ifs with h
  · have transport (j : Fin l) (hji : j=i) (hpi : p j=p i) :
        (eqToHom (congrArg V hpi)).hom (x j) = x i := by
      subst j
      rfl
    exact transport h.choose (hp h.choose_spec) h.choose_spec
  · exact False.elim (h ⟨i,rfl⟩)

end LittleFinitistic.FiniteSupportReindex

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bimodule_BimoduleAugmentationQuasiIso
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

/-- An acyclic kernel in an actual short exact sequence makes the quotient map
an isomorphism on homology. -/
theorem shortExact_quasiIso_g (S : ShortComplex (CochainComplex (ModuleCat.{u} B) ℤ))
    (hS : S.ShortExact) (hK : S.X₁.Acyclic) : QuasiIso S.g := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have hz (a : ℤ) : IsZero (S.X₁.homology a) :=
    (exactAt_iff_isZero_homology _ _).mp (hK a)
  have : Mono (homologyMap S.g n) := (hS.homology_exact₂ n).mono_g_iff.mpr
    ((hz n).eq_of_src _ _)
  have : Epi (homologyMap S.g n) := (hS.homology_exact₃ n (n+1) rfl).epi_f_iff.mpr
    ((hz (n+1)).eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

end LittleFinitistic.BimoduleTotal

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_IntegerExtensionFunctor
attribute [-instance] _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option backward.isDefEq.respectTransparency false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.IntegerExtensionFunctor
universe u
variable {B : Type u} [Ring B]
variable (F : ModuleCat.{u} B ⥤ ModuleCat.{u} B) [F.Additive]
variable (Z : ChainComplex (ModuleCat.{u} B) ℕ)
local notation "c" => ComplexShape.down ℕ

/-- Additive functors preserve the zero components added by integer extension. -/
def termIso : (o : Option ℕ) → F.obj (HomologicalComplex.extend.X Z o) ≅
    HomologicalComplex.extend.X ((F.mapHomologicalComplex c).obj Z) o
  | none => (F.map_isZero (isZero_zero _)).iso (isZero_zero _)
  | some _ => Iso.refl _

theorem termIso_d (o o' : Option ℕ) :
    (termIso F Z o).hom ≫ HomologicalComplex.extend.d ((F.mapHomologicalComplex c).obj Z) o o' =
      F.map (HomologicalComplex.extend.d Z o o') ≫ (termIso F Z o').hom := by
  cases o <;> cases o' <;>
    simp [termIso,HomologicalComplex.extend.d,HomologicalComplex.extend.X] <;>
    erw [Functor.map_zero] <;> (try erw [comp_zero]) <;> (try erw [zero_comp])

variable {Z} {Z' : ChainComplex (ModuleCat.{u} B) ℕ}
theorem termIso_natural (f : Z ⟶ Z') (o : Option ℕ) :
    F.map (HomologicalComplex.extend.mapX f o) ≫ (termIso F Z' o).hom =
      (termIso F Z o).hom ≫
        HomologicalComplex.extend.mapX ((F.mapHomologicalComplex c).map f) o := by
  cases o <;> simp [termIso,HomologicalComplex.extend.mapX,HomologicalComplex.extend.X]
  all_goals erw [Functor.map_zero,comp_zero,zero_comp]

end LittleFinitistic.IntegerExtensionFunctor

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bimodule_BimoduleBarComparisonMap
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
local instance instHasDerivedCategoryModuleCat_solutions_1 : HasDerivedCategory.{u+1} (ModuleCat.{u} B) :=
  HasDerivedCategory.standard (ModuleCat.{u} B)
end LittleFinitistic.BimoduleTotal

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bimodule_BimoduleBarComparisonIso
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
local instance instHasDerivedCategoryModuleCat_solutions_2 : HasDerivedCategory.{u+1} (ModuleCat.{u} B) :=
  HasDerivedCategory.standard (ModuleCat.{u} B)
end LittleFinitistic.BimoduleTotal

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bimodule_BimoduleBarStalk
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
local instance instHasDerivedCategoryModuleCat_solutions_4 : HasDerivedCategory.{u+1} (ModuleCat.{u} B) :=
  HasDerivedCategory.standard (ModuleCat.{u} B)
end LittleFinitistic.BimoduleTotal

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bimodule_BimoduleResolutionBarAPI
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
variable {k B : Type u} [Field k] [Ring B] [Algebra k B]
local instance instHasDerivedCategoryModuleCat_solutions_5 : HasDerivedCategory.{u+1} (ModuleCat.{u} B) :=
  HasDerivedCategory.standard (ModuleCat.{u} B)
end LittleFinitistic.BimoduleTotal

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bimodule_BimoduleScalarEvaluation
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
variable (N : Type u) [AddCommGroup N] [Module k N] [Module B N] [hN : IsScalarTower k B N]
abbrev CanonicalInput := BalancedTensor.ScalarLeftModule k B (ModuleCat.of B N)

end LittleFinitistic.BimoduleTotal

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_SignedCochainShift
attribute [-instance] _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option backward.isDefEq.respectTransparency false

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.BimoduleTotal
universe u v
variable (C : Type u) [Category.{v} C] [Preadditive C]

def signedShiftIso (a s : ℤ) :
    shiftFunctor (CochainComplex C ℤ) s ⋙ shiftFunctor _ a ≅
      shiftFunctor (CochainComplex C ℤ) a ⋙ shiftFunctor _ s :=
  OrdinarySimulation.integerUnitIso _ (a*s).negOnePow ≪≫ shiftFunctorComm _ s a

theorem signedShiftIso_hom_f (a s n : ℤ) (K : CochainComplex C ℤ) :
    ((signedShiftIso C a s).hom.app K).f n =
      (a*s).negOnePow • (K.XIsoOfEq (show n+a+s=n+s+a by omega)).hom := by
  simp [signedShiftIso,OrdinarySimulation.integerUnitIso,
    CochainComplex.shiftFunctorComm_hom_app_f]

/-- The standard signed commutation structure for a cochain shift. -/
@[instance_reducible]
def signedShiftComm (a : ℤ) : (shiftFunctor (CochainComplex C ℤ) a).CommShift ℤ where
  commShiftIso s := signedShiftIso C a s
  commShiftIso_zero := by
    ext K n
    simp [signedShiftIso_hom_f,Functor.CommShift.isoZero,
      CochainComplex.shiftFunctorZero_hom_app_f,CochainComplex.shiftFunctorZero_inv_app_f,
      HomologicalComplex.XIsoOfEq]
  commShiftIso_add s t := by
    ext K n
    simp [signedShiftIso_hom_f,Functor.CommShift.isoAdd_hom_app,
      CochainComplex.shiftFunctorAdd_hom_app_f,CochainComplex.shiftFunctorAdd_inv_app_f,
      CochainComplex.shiftFunctor_map_f',HomologicalComplex.XIsoOfEq,
      Linear.units_smul_comp,Linear.comp_units_smul,smul_smul,
      ← Int.negOnePow_add,mul_add]
end LittleFinitistic.BimoduleTotal

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bimodule_BimoduleShiftCoherence
attribute [-instance] _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology
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
local instance signedShift (a : ℤ) :
    (shiftFunctor (CochainComplex (ModuleCat.{u} B) ℤ) a).CommShift ℤ :=
  signedShiftComm (ModuleCat.{u} B) a

end LittleFinitistic.BimoduleTotal

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryBimoduleCoefficients
attribute [-instance] _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace LittleFinitistic
universe u
/-- A genuine tensor-algebra module with both scalar restrictions recorded together. -/
def BimoduleCoefficients (k S A : Type u) [Field k] [Ring S] [Ring A] [Algebra k S] [Algebra k A]
    (M : ModuleCat.{u} (S ⊗[k] Aᵐᵒᵖ)) := M
namespace BimoduleCoefficients
variable (k S A : Type u) [Field k] [Ring S] [Ring A] [Algebra k S] [Algebra k A]
variable (M : ModuleCat.{u} (S ⊗[k] Aᵐᵒᵖ))
instance instAddCommGroupCarrierTensorProductMulOpposite : AddCommGroup (BimoduleCoefficients k S A M) := inferInstanceAs (AddCommGroup M)
instance instModuleTensorProductMulOppositeCarrier : Module (S ⊗[k] Aᵐᵒᵖ) (BimoduleCoefficients k S A M) := inferInstanceAs (Module (S ⊗[k] Aᵐᵒᵖ) M)
instance instModuleCarrierTensorProductMulOpposite : Module k (BimoduleCoefficients k S A M) := Module.compHom _ (algebraMap k (S ⊗[k] Aᵐᵒᵖ))
instance instModuleCarrierTensorProductMulOpposite_1 : Module S (BimoduleCoefficients k S A M) := Module.compHom _
  (Algebra.TensorProduct.includeLeft (R := k) (S := k) (A := S) (B := Aᵐᵒᵖ)).toRingHom
instance instModuleMulOppositeCarrierTensorProduct : Module Aᵐᵒᵖ (BimoduleCoefficients k S A M) := Module.compHom _
  (Algebra.TensorProduct.includeRight (R := k) (A := S) (B := Aᵐᵒᵖ)).toRingHom
instance towerLeft : IsScalarTower k S (BimoduleCoefficients k S A M) := by
  apply IsScalarTower.of_algebraMap_smul
  intro r m
  change (Algebra.TensorProduct.includeLeft (R := k) (S := k) (A := S) (B := Aᵐᵒᵖ) (algebraMap k S r)) • (m : M) =
    (algebraMap k (S ⊗[k] Aᵐᵒᵖ) r) • (m : M)
  rw [AlgHom.commutes]
instance towerRight : IsScalarTower k Aᵐᵒᵖ (BimoduleCoefficients k S A M) := by
  apply IsScalarTower.of_algebraMap_smul
  intro r m
  change (Algebra.TensorProduct.includeRight (R := k) (A := S) (B := Aᵐᵒᵖ) (algebraMap k Aᵐᵒᵖ r)) • (m : M) =
    (algebraMap k (S ⊗[k] Aᵐᵒᵖ) r) • (m : M)
  rw [AlgHom.commutes]
instance commute : SMulCommClass S Aᵐᵒᵖ (BimoduleCoefficients k S A M) where
  smul_comm s a m := by
    change (s ⊗ₜ[k] (1:Aᵐᵒᵖ)) • (((1:S) ⊗ₜ[k] a) • (m : M)) =
      ((1:S) ⊗ₜ[k] a) • ((s ⊗ₜ[k] (1:Aᵐᵒᵖ)) • (m : M))
    rw [← mul_smul,← mul_smul]
    simp only [Algebra.TensorProduct.tmul_mul_tmul,one_mul,mul_one]

variable {M} {M' : ModuleCat.{u} (S ⊗[k] Aᵐᵒᵖ)}
def map (f : M ⟶ M') : BimoduleCoefficients k S A M →ₗ[Aᵐᵒᵖ] BimoduleCoefficients k S A M' where
  __ := f.hom.toAddHom
  map_smul' a m := f.hom.map_smul (((1:S) ⊗ₜ[k] a)) m

theorem map_left (f : M ⟶ M') (s : S) (m : BimoduleCoefficients k S A M) :
    map k S A f (s • m) = s • map k S A f m :=
  f.hom.map_smul (s ⊗ₜ[k] (1:Aᵐᵒᵖ)) m
end BimoduleCoefficients
end LittleFinitistic

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryAssociativeTensorModules
attribute [-instance] _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
namespace LittleFinitistic
universe u

variable (k A B M N Z : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
variable [AddCommGroup M] [Module k M] [Module Aᵐᵒᵖ M] [IsScalarTower k Aᵐᵒᵖ M]
variable [AddCommGroup N] [Module k N] [Module A N] [Module Bᵐᵒᵖ N]
  [IsScalarTower k A N] [IsScalarTower k Bᵐᵒᵖ N] [SMulCommClass A Bᵐᵒᵖ N]
variable [AddCommGroup Z] [Module k Z] [Module B Z] [IsScalarTower k B Z]

namespace RightTensor

local instance instSMulCommClassMulOpposite : SMulCommClass Bᵐᵒᵖ A N := ⟨fun b a n => (smul_comm a b n).symm⟩

end RightTensor

end LittleFinitistic

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryBimoduleTensorTerms
attribute [-instance] _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology
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

abbrev rightComplex : CochainComplex (ModuleCat.{u} Aᵐᵒᵖ) ℤ :=
  ((ModuleCat.restrictScalars
    (Algebra.TensorProduct.includeRight (R := k) (A := S) (B := Aᵐᵒᵖ)).toRingHom).mapHomologicalComplex (.up ℤ)).obj Q

end LittleFinitistic.BimoduleComplexTensor

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryRestrictionHomology
attribute [-instance] _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.RestrictionHomology
universe u v
variable {R S : Type u} [Ring R] [Ring S] (f : R →+* S)

theorem mapsExact (K : ShortComplex (ModuleCat.{u} S)) (hK : K.Exact) :
    (K.map (ModuleCat.restrictScalars f)).Exact := by
  rw [ShortComplex.moduleCat_exact_iff] at hK ⊢
  exact hK

theorem preservesHomology : (ModuleCat.restrictScalars.{u} f).PreservesHomology :=
  CategoryTheory.Functor.preservesHomology_of_map_exact _ (mapsExact f)

theorem quasiIso_iff {I : Type v} {c : ComplexShape I}
    {K L : HomologicalComplex (ModuleCat.{u} S) c} (g : K ⟶ L) :
    QuasiIso (((ModuleCat.restrictScalars f).mapHomologicalComplex c).map g) ↔ QuasiIso g := by
  let := preservesHomology f
  exact HomologicalComplex.quasiIso_map_iff_of_preservesHomology g (ModuleCat.restrictScalars f)
end LittleFinitistic.RestrictionHomology

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bimodule_BimoduleTotalPresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.BimoduleTotalPresentation
open ExternalTensor.Section4
universe u
theorem addHom_smul_zero {R M N : Type*} [Semiring R]
    [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
    (f : M →+ N) (r : R) : f (r • 0) = r • f 0 := by simp

theorem addHom_smul_add {R M N : Type*} [Semiring R]
    [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
    (f : M →+ N) (r : R) (x y : M)
    (hx : f (r • x) = r • f x) (hy : f (r • y) = r • f y) :
    f (r • (x + y)) = r • f (x + y) := by
  simp only [smul_add, map_add, hx, hy]

end LittleFinitistic.BimoduleTotalPresentation

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Encoding_QuadraticPresentation
attribute [-instance] _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
namespace LittleFinitistic.QuadraticPresentation

variable (R : Type*) [CommRing R] (α : Type*)

def word (w : List α) : FreeAlgebra R α := (w.map (FreeAlgebra.ι R)).prod

@[simp] theorem word_nil : word R α [] = 1 := rfl
@[simp] theorem word_append (u v : List α) :
    word R α (u ++ v) = word R α u * word R α v := by
  simp [word]
@[simp] theorem word_singleton (a : α) : word R α [a] = FreeAlgebra.ι R a := by
  simp [word]

def coefficients (p : FreeAlgebra R α) : FreeMonoid α →₀ R :=
  (FreeAlgebra.equivMonoidAlgebraFreeMonoid p).coeff

theorem expansion (p : FreeAlgebra R α) :
    (coefficients R α p).sum (fun w c => c • word R α w.toList) = p := by
  have h := FreeAlgebra.equivMonoidAlgebraFreeMonoid.symm_apply_apply p
  change MonoidAlgebra.lift R (FreeAlgebra R α) (FreeMonoid α)
    (FreeMonoid.lift (FreeAlgebra.ι R))
    (FreeAlgebra.equivMonoidAlgebraFreeMonoid p) = p at h
  simpa only [MonoidAlgebra.lift_apply, FreeMonoid.lift_apply, coefficients, word] using h

variable {R α}

variable (R α)



abbrev Word (N : ℕ) := {w : List α // w.length ≤ N}
abbrev Letter (N : ℕ) := α ⊕ Word α N
abbrev Step (N : ℕ) := {s : List α × α // (s.1 ++ [s.2]).length ≤ N}

def wordPrefix {N : ℕ} (s : Step α N) : Word α N :=
  ⟨s.val.1, by have := s.property; simp only [List.length_append,
    List.length_singleton] at this; omega⟩
def extended {N : ℕ} (s : Step α N) : Word α N := ⟨s.val.1 ++ [s.val.2], s.property⟩

def inclusion (N : ℕ) : FreeAlgebra R α →ₐ[R] FreeAlgebra R (Letter α N) :=
  FreeAlgebra.lift R (fun a => FreeAlgebra.ι R (.inl a))

def eliminate (N : ℕ) : FreeAlgebra R (Letter α N) →ₐ[R] FreeAlgebra R α :=
  FreeAlgebra.lift R (Sum.elim (FreeAlgebra.ι R) (fun w => word R α w.val))

def encodeWord (N : ℕ) (w : FreeMonoid α) : FreeAlgebra R (Letter α N) :=
  if h : w.toList.length ≤ N then FreeAlgebra.ι R (.inr ⟨w.toList,h⟩) else 0

def linearize (N : ℕ) (p : FreeAlgebra R α) : FreeAlgebra R (Letter α N) :=
  (coefficients R α p).sum (fun w c => c • encodeWord R α N w)

theorem eliminate_linearize (N : ℕ) (p : FreeAlgebra R α)
    (h : ∀ w ∈ (coefficients R α p).support, w.toList.length ≤ N) :
    eliminate R α N (linearize R α N p) = p := by
  apply Eq.trans (b := (coefficients R α p).sum (fun w c => c • word R α w.toList)) _ (expansion R α p)
  simp only [linearize, Finsupp.sum, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro w hw
  simp [encodeWord, h w hw, eliminate]

variable {κ : Type*} (p : κ → FreeAlgebra R α) (N : ℕ)
abbrev EquationIndex := κ ⊕ (Unit ⊕ Step α N)

def relation : EquationIndex α N (κ := κ) → FreeAlgebra R (Letter α N)
  | .inl i => linearize R α N (p i)
  | .inr (.inl _) => FreeAlgebra.ι R (.inr ⟨[], Nat.zero_le N⟩) - 1
  | .inr (.inr s) => FreeAlgebra.ι R (.inr (extended α s)) -
      FreeAlgebra.ι R (.inr (wordPrefix α s)) * FreeAlgebra.ι R (.inl s.val.2)

def original : RingCon (FreeAlgebra R α) :=
  ringConGen (fun x y => ∃ i, x = p i ∧ y = 0)

def quadratic : RingCon (FreeAlgebra R (Letter α N)) :=
  ringConGen (fun x y => ∃ i, x = relation R α p N i ∧ y = 0)

abbrev Original := (original R α p).Quotient
abbrev Quadratic := (quadratic R α p N).Quotient

def originalMap : FreeAlgebra R α →ₐ[R] Original R α p := (original R α p).mkₐ R

def quadraticMap : FreeAlgebra R (Letter α N) →ₐ[R] Quadratic R α p N :=
  (quadratic R α p N).mkₐ R

theorem original_relation (i : κ) : originalMap R α p (p i) = 0 :=
  (original R α p).eq.mpr (RingConGen.Rel.of _ _ ⟨i,rfl,rfl⟩)

theorem quadratic_relation (i : EquationIndex α N (κ := κ)) :
    quadraticMap R α p N (relation R α p N i) = 0 :=
  (quadratic R α p N).eq.mpr (RingConGen.Rel.of _ _ ⟨i,rfl,rfl⟩)



def oldInNew : FreeAlgebra R α →ₐ[R] Quadratic R α p N :=
  (quadraticMap R α p N).comp (inclusion R α N)

/-- Every auxiliary prefix generator equals its original word in the quotient. -/
theorem auxiliary_eq_word (w : List α) (h : w.length ≤ N) :
    quadraticMap R α p N (FreeAlgebra.ι R (.inr ⟨w,h⟩)) =
      oldInNew R α p N (word R α w) := by
  induction w using List.reverseRecOn with
  | nil =>
    have hh := quadratic_relation R α p N (.inr (.inl ()))
    simpa only [relation, map_sub, map_one, sub_eq_zero, word_nil] using hh
  | append_singleton w a ih =>
    have hw : w.length ≤ N := by simp only [List.length_append, List.length_singleton] at h; omega
    have hh := quadratic_relation R α p N (.inr (.inr ⟨(w,a),h⟩))
    simp only [relation, map_sub, map_mul, sub_eq_zero] at hh
    change quadraticMap R α p N (FreeAlgebra.ι R (.inr ⟨w ++ [a],h⟩)) =
      quadraticMap R α p N (FreeAlgebra.ι R (.inr ⟨w,hw⟩)) *
      quadraticMap R α p N (FreeAlgebra.ι R (.inl a)) at hh
    rw [ih hw] at hh
    simpa [word_append, word_singleton, map_mul, oldInNew, inclusion] using hh

variable (bound : ∀ i w, w ∈ (coefficients R α (p i)).support → w.toList.length ≤ N)

include bound in
theorem eliminate_relation (i : EquationIndex α N (κ := κ)) :
    originalMap R α p (eliminate R α N (relation R α p N i)) = 0 := by
  rcases i with i | (u | s)
  · rw [relation, eliminate_linearize R α N (p i) (bound i)]
    exact original_relation R α p i
  · simp [relation, eliminate]
  · simp [relation, eliminate, extended, wordPrefix]

def toOriginal : Quadratic R α p N →ₐ[R] Original R α p :=
  (quadratic R α p N).liftₐ ((originalMap R α p).comp (eliminate R α N))
    (RingCon.ringConGen_le.mpr (by
      rintro x y ⟨i,rfl,rfl⟩
      exact (eliminate_relation R α p N bound i).trans (map_zero _).symm))

@[simp] theorem toOriginal_quotient (f : FreeAlgebra R (Letter α N)) :
    toOriginal R α p N bound (quadraticMap R α p N f) =
      originalMap R α p (eliminate R α N f) := rfl

end LittleFinitistic.QuadraticPresentation

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Selection_GroupSelection
attribute [-instance] _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Group identities used in Section 2 of v5s9.15. -/

open scoped commutatorElement

namespace LittleFinitistic

/-- The relators used for the off-diagonal generators in Section 2. The
presentation and its finite-presentation reduction are separate obligations. -/
structure SelectionGroupData (G : Type*) [Group G] where
  T : Fin 3 → G
  U : Fin 3 → ℤ → G
  V : Fin 3 → ℤ → G
  W : Fin 3 → Fin 3 → ℤ → G
  square_U : ∀ i a, U i a * U i a = 1
  commute_UU : ∀ i j a b, i ≠ j → Commute (U i a) (U j b)
  commute_VV : ∀ i j a b, i ≠ j → Commute (V i a) (V j b)
  commute_UV : ∀ i j a b, i ≠ j → Commute (U i a) (V j b)
  commute_WU : ∀ i j h a b, h ≠ i → Commute (W i j a) (U h b)
  commute_WV : ∀ i j h a b, h ≠ j → Commute (W i j a) (V h b)
  commutator_UW : ∀ i j a b, i ≠ j → ⁅U i a, W i j b⁆ = U j (a+b)
  commutator_WV : ∀ i j a b, i ≠ j → ⁅W i j a, V j b⁆ = V i (a+b)
  commute_TT : ∀ i j, Commute (T i) (T j)
  conj_TU : ∀ l i a, T l * U i a * (T l)⁻¹ = U i (a - if l=i then 1 else 0)
  conj_TV : ∀ l i a, T l * V i a * (T l)⁻¹ = V i (a + if l=i then 1 else 0)
  conj_TW : ∀ l i j a, T l * W i j a * (T l)⁻¹ =
    W i j (a + (if l=i then 1 else 0) - if l=j then 1 else 0)
  diagonal_W : ∀ i a, W i i a = 1

namespace Presentation

inductive Generator where
  | T : Fin 3 → Generator
  | U : Fin 3 → ℤ → Generator
  | V : Fin 3 → ℤ → Generator
  | W : Fin 3 → Fin 3 → ℤ → Generator

abbrev t (i : Fin 3) := FreeGroup.of (Generator.T i)
abbrev u (i : Fin 3) (a : ℤ) := FreeGroup.of (Generator.U i a)
abbrev v (i : Fin 3) (a : ℤ) := FreeGroup.of (Generator.V i a)
abbrev w (i j : Fin 3) (a : ℤ) := FreeGroup.of (Generator.W i j a)

/-- Explicit equation patterns of the paper's infinite presentation.
Diagonal W generators are set to one, so the total-index notation introduces
no additional group generators compared with the manuscript. -/
inductive Equation : FreeGroup Generator → FreeGroup Generator → Prop where
  | squareU (i a) : Equation (u i a * u i a) 1
  | commuteUU (i j a b) (h : i ≠ j) : Equation (u i a * u j b) (u j b * u i a)
  | commuteVV (i j a b) (h : i ≠ j) : Equation (v i a * v j b) (v j b * v i a)
  | commuteUV (i j a b) (h : i ≠ j) : Equation (u i a * v j b) (v j b * u i a)
  | commuteWU (i j h a b) (hhi : h ≠ i) : Equation (w i j a * u h b) (u h b * w i j a)
  | commuteWV (i j h a b) (hhj : h ≠ j) : Equation (w i j a * v h b) (v h b * w i j a)
  | commutatorUW (i j a b) (h : i ≠ j) : Equation ⁅u i a,w i j b⁆ (u j (a+b))
  | commutatorWV (i j a b) (h : i ≠ j) : Equation ⁅w i j a,v j b⁆ (v i (a+b))
  | commuteTT (i j) : Equation (t i * t j) (t j * t i)
  | conjTU (l i a) : Equation (t l * u i a * (t l)⁻¹) (u i (a-if l=i then 1 else 0))
  | conjTV (l i a) : Equation (t l * v i a * (t l)⁻¹) (v i (a+if l=i then 1 else 0))
  | conjTW (l i j a) : Equation (t l * w i j a * (t l)⁻¹)
      (w i j (a+(if l=i then 1 else 0)-if l=j then 1 else 0))
  | diagonalW (i a) : Equation (w i i a) 1

def relators : Set (FreeGroup Generator) := {r | ∃ a b, Equation a b ∧ r=a*b⁻¹}
abbrev AuxiliaryGroup := PresentedGroup relators

theorem equation_holds {a b : FreeGroup Generator} (h : Equation a b) :
    PresentedGroup.mk relators a = PresentedGroup.mk relators b :=
  PresentedGroup.mk_eq_mk_of_mul_inv_mem ⟨a,b,h,rfl⟩

def data : SelectionGroupData AuxiliaryGroup where
  T i := PresentedGroup.of (.T i)
  U i a := PresentedGroup.of (.U i a)
  V i a := PresentedGroup.of (.V i a)
  W i j a := PresentedGroup.of (.W i j a)
  square_U i a := by simpa [u, PresentedGroup.of] using equation_holds (.squareU i a)
  commute_UU i j a b h := by
    simpa [u, PresentedGroup.of, Commute, SemiconjBy] using equation_holds (.commuteUU i j a b h)
  commute_VV i j a b h := by
    simpa [v, PresentedGroup.of, Commute, SemiconjBy] using equation_holds (.commuteVV i j a b h)
  commute_UV i j a b h := by
    simpa [u,v, PresentedGroup.of, Commute, SemiconjBy] using equation_holds (.commuteUV i j a b h)
  commute_WU i j h a b hhi := by
    simpa [w,u, PresentedGroup.of, Commute, SemiconjBy] using equation_holds (.commuteWU i j h a b hhi)
  commute_WV i j h a b hhj := by
    simpa [w,v, PresentedGroup.of, Commute, SemiconjBy] using equation_holds (.commuteWV i j h a b hhj)
  commutator_UW i j a b h := by
    simpa [u,w, PresentedGroup.of] using equation_holds (.commutatorUW i j a b h)
  commutator_WV i j a b h := by
    simpa [w,v, PresentedGroup.of] using equation_holds (.commutatorWV i j a b h)
  commute_TT i j := by
    simpa [t, PresentedGroup.of, Commute, SemiconjBy] using equation_holds (.commuteTT i j)
  conj_TU l i a := by simpa [t,u,PresentedGroup.of] using equation_holds (.conjTU l i a)
  conj_TV l i a := by simpa [t,v,PresentedGroup.of] using equation_holds (.conjTV l i a)
  conj_TW l i j a := by simpa [t,w,PresentedGroup.of] using equation_holds (.conjTW l i j a)
  diagonal_W i a := by simpa [w,PresentedGroup.of] using equation_holds (.diagonalW i a)

def evaluate {G : Type*} [Group G] (D : SelectionGroupData G) : Generator → G
  | .T i => D.T i
  | .U i a => D.U i a
  | .V i a => D.V i a
  | .W i j a => D.W i j a

theorem evaluate_equation {G : Type*} [Group G] (D : SelectionGroupData G)
    {a b : FreeGroup Generator} (h : Equation a b) :
    FreeGroup.lift (evaluate D) a = FreeGroup.lift (evaluate D) b := by
  cases h with
  | squareU i a => simpa [u,evaluate] using D.square_U i a
  | commuteUU i j a b h => simpa [u,evaluate] using (D.commute_UU i j a b h).eq
  | commuteVV i j a b h => simpa [v,evaluate] using (D.commute_VV i j a b h).eq
  | commuteUV i j a b h => simpa [u,v,evaluate] using (D.commute_UV i j a b h).eq
  | commuteWU i j h a b hh => simpa [w,u,evaluate] using (D.commute_WU i j h a b hh).eq
  | commuteWV i j h a b hh => simpa [w,v,evaluate] using (D.commute_WV i j h a b hh).eq
  | commutatorUW i j a b h => simpa [u,w,evaluate] using D.commutator_UW i j a b h
  | commutatorWV i j a b h => simpa [w,v,evaluate] using D.commutator_WV i j a b h
  | commuteTT i j => simpa [t,evaluate] using (D.commute_TT i j).eq
  | conjTU l i a => simpa [t,u,evaluate] using D.conj_TU l i a
  | conjTV l i a => simpa [t,v,evaluate] using D.conj_TV l i a
  | conjTW l i j a => simpa [t,w,evaluate] using D.conj_TW l i j a
  | diagonalW i a => simpa [w,evaluate] using D.diagonal_W i a

def ofData {G : Type*} [Group G] (D : SelectionGroupData G) : AuxiliaryGroup →* G :=
  PresentedGroup.toGroup (f := evaluate D) (by
    intro r hr
    obtain ⟨a,b,h,rfl⟩ := hr
    rw [map_mul,map_inv,evaluate_equation D h,mul_inv_cancel])

@[simp] theorem ofData_of {G : Type*} [Group G] (D : SelectionGroupData G) (s : Generator) :
    ofData D (PresentedGroup.of s) = evaluate D s := PresentedGroup.toGroup.of _

def shiftData {G : Type*} [Group G] (D : SelectionGroupData G) (k : ℤ) :
    SelectionGroupData G where
  T := D.T
  U i a := D.U i (a+k)
  V := D.V
  W := D.W
  square_U i a := D.square_U i (a+k)
  commute_UU i j a b h := D.commute_UU i j (a+k) (b+k) h
  commute_VV := D.commute_VV
  commute_UV i j a b h := D.commute_UV i j (a+k) b h
  commute_WU i j h a b hh := D.commute_WU i j h a (b+k) hh
  commute_WV := D.commute_WV
  commutator_UW i j a b h := by
    simpa only [add_assoc,add_comm k b] using D.commutator_UW i j (a+k) b h
  commutator_WV := D.commutator_WV
  commute_TT := D.commute_TT
  conj_TU l i a := by
    simpa only [add_sub_assoc,sub_add_eq_add_sub] using D.conj_TU l i (a+k)
  conj_TV := D.conj_TV
  conj_TW := D.conj_TW
  diagonal_W := D.diagonal_W

def shiftHom (k : ℤ) : AuxiliaryGroup →* AuxiliaryGroup := ofData (shiftData data k)

@[simp] theorem shiftHom_T (k : ℤ) (i : Fin 3) : shiftHom k (data.T i) = data.T i := by
  simp [shiftHom,data,shiftData,evaluate]

@[simp] theorem shiftHom_U (k : ℤ) (i : Fin 3) (a : ℤ) :
    shiftHom k (data.U i a) = data.U i (a+k) := by
  simp [shiftHom,data,shiftData,evaluate]

@[simp] theorem shiftHom_V (k : ℤ) (i : Fin 3) (a : ℤ) :
    shiftHom k (data.V i a) = data.V i a := by
  simp [shiftHom,data,shiftData,evaluate]

@[simp] theorem shiftHom_W (k : ℤ) (i j : Fin 3) (a : ℤ) :
    shiftHom k (data.W i j a) = data.W i j a := by
  simp [shiftHom,data,shiftData,evaluate]

end Presentation

end LittleFinitistic

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Selection_FinitePresentation
attribute [-instance] _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open scoped commutatorElement
namespace LittleFinitistic.FinitePresentation

/-! Target: Group.IsFinitelyPresented Presentation.AuxiliaryGroup.
Section 2, Lemma group-finite-presentation. No finite-presentation hypothesis
is permitted on the target group. Diagonal W generators are redundant.
-/

section Orbit
variable {G : Type*} [Group G]

def orbit (t x : G) (r : ℤ) : G := t ^ r * x * (t ^ r)⁻¹

@[simp] theorem orbit_zero (t x : G) : orbit t x 0 = x := by simp [orbit]

theorem orbit_add (t x : G) (a b : ℤ) :
    orbit t (orbit t x b) a = orbit t x (a+b) := by
  simp only [orbit, zpow_add, mul_inv_rev]
  group

theorem orbit_commute (t q x : G) (h : Commute t q) (a : ℤ) :
    t * orbit q x a * t⁻¹ = orbit q (t*x*t⁻¹) a := by
  have hc := h.zpow_right a
  simp only [orbit]
  calc
    t * (q^a*x*(q^a)⁻¹) * t⁻¹ = (t*q^a)*x*(q^a)⁻¹*t⁻¹ := by group
    _ = (q^a*t)*x*(q^a)⁻¹*t⁻¹ := by rw [hc.eq]
    _ = q^a*(t*x)*((q^a)⁻¹*t⁻¹) := by group
    _ = q^a*(t*x)*(t⁻¹*(q^a)⁻¹) := by rw [hc.inv_inv.eq]
    _ = q^a*(t*x*t⁻¹)*(q^a)⁻¹ := by group

theorem orbit_covariance (t q x : G) (h : Commute t q) (d : ℤ)
    (hx : t*x*t⁻¹ = orbit q x d) (a : ℤ) :
    t * orbit q x a * t⁻¹ = orbit q x (a+d) := by
  rw [orbit_commute t q x h a, hx, orbit_add]

theorem family_zpow (t : G) (f : ℤ → G) (d : ℤ)
    (h : ∀ r, t*f r*t⁻¹ = f (r+d)) (n r : ℤ) :
    orbit t (f r) n = f (r+n*d) := by
  induction n using Int.induction_on with
  | zero => simp
  | succ n ih =>
      have he : (↑n + 1 : ℤ) = 1 + ↑n := by omega
      rw [he, ← orbit_add, ih]
      change t^ (1:ℤ) * _ * (t^(1:ℤ))⁻¹ = _
      simp only [zpow_one, h]
      congr 1
      ring
  | pred n ih =>
      have hi := h (r + (-↑n - 1)*d)
      have he : r + (-↑n - 1)*d+d = r+(-↑n)*d := by ring
      rw [he] at hi
      have he' : (-↑n - 1 : ℤ) = -1 + -↑n := by omega
      rw [he', ← orbit_add, ih, ← hi]
      simp only [orbit, zpow_neg_one, inv_inv]
      group

end Orbit

abbrev Lattice := Fin 3 → ℤ

def coord (i : Fin 3) (r : ℤ) : Lattice := fun h => if h=i then r else 0

def wtU (i : Fin 3) (n : Lattice) := -n i

def wtV (i : Fin 3) (n : Lattice) := n i

def wtW (i j : Fin 3) (n : Lattice) := n i-n j

/- Each theorem supplies the integral preimage in the corresponding table row. -/
theorem table_UU (i j : Fin 3) (hij : i ≠ j) (r s : ℤ) :
    ∃ n : Lattice, wtU i n = r ∧ wtU j n = s := by
  refine ⟨coord i (-r) + coord j (-s), ?_⟩
  simp [wtU, coord, hij, hij.symm]

theorem table_VV (i j : Fin 3) (hij : i ≠ j) (r s : ℤ) :
    ∃ n : Lattice, wtV i n = r ∧ wtV j n = s := by
  refine ⟨coord i r + coord j s, ?_⟩
  simp [wtV, coord, hij, hij.symm]

theorem table_UV (i j : Fin 3) (hij : i ≠ j) (r s : ℤ) :
    ∃ n : Lattice, wtU i n = r ∧ wtV j n = s := by
  refine ⟨coord i (-r) + coord j s, ?_⟩
  simp [wtU, wtV, coord, hij, hij.symm]

theorem table_WU (i j h : Fin 3) (hij : i ≠ j) (hhi : h ≠ i) (r s : ℤ) :
    ∃ n : Lattice, wtW i j n = r ∧ wtU h n = s := by
  by_cases hhj : h=j
  · subst h
    refine ⟨coord i (r-s) + coord j (-s), ?_⟩
    simp [wtW, wtU, coord, hij, hij.symm]
  · refine ⟨coord i r + coord h (-s), ?_⟩
    simp [wtW, wtU, coord, hij.symm, hhi, (Ne.symm hhi), (Ne.symm hhj)]

theorem table_WV (i j h : Fin 3) (hij : i ≠ j) (hhj : h ≠ j) (r s : ℤ) :
    ∃ n : Lattice, wtW i j n = r ∧ wtV h n = s := by
  by_cases hhi : h=i
  · subst h
    refine ⟨coord i s + coord j (s-r), ?_⟩
    simp [wtW, wtV, coord, hij, hij.symm]
  · refine ⟨coord i r + coord h s, ?_⟩
    simp [wtW, wtV, coord, hij.symm, hhi, (Ne.symm hhi), (Ne.symm hhj)]

theorem table_UW (i j : Fin 3) (hij : i ≠ j) (r s : ℤ) :
    ∃ n : Lattice, wtU i n = r ∧ wtW i j n = s := by
  refine ⟨coord i (-r) + coord j (-r-s), ?_⟩
  simp [wtU, wtW, coord, hij, hij.symm]

theorem table_WV_output (i j : Fin 3) (hij : i ≠ j) (r s : ℤ) :
    ∃ n : Lattice, wtW i j n = r ∧ wtV j n = s := by
  refine ⟨coord i (r+s) + coord j s, ?_⟩
  simp [wtW, wtV, coord, hij, hij.symm]


section Torus
variable {G : Type*} [Group G]

def torus (T : Fin 3 → G) (n : Lattice) : G := T 0 ^ n 0 * T 1 ^ n 1 * T 2 ^ n 2

theorem family_torus (T : Fin 3 → G) (f : ℤ → G) (d : Fin 3 → ℤ)
    (hf : ∀ l r, T l * f r * (T l)⁻¹ = f (r+d l)) (n : Lattice) (r : ℤ) :
    torus T n * f r * (torus T n)⁻¹ =
      f (r + n 0*d 0 + n 1*d 1 + n 2*d 2) := by
  have he : torus T n * f r * (torus T n)⁻¹ =
      orbit (T 0) (orbit (T 1) (orbit (T 2) (f r) (n 2)) (n 1)) (n 0) := by
    simp only [torus, orbit]
    group
  rw [he, family_zpow _ _ _ (hf 2), family_zpow _ _ _ (hf 1),
    family_zpow _ _ _ (hf 0)]
  congr 1
  ring

end Torus


/-- Intermediate data: covariance plus only zero-argument algebraic relations.
This is constructed below from a finite presented group, not postulated for it. -/
structure CovariantData (G : Type*) [Group G] where
  T : Fin 3 → G
  U : Fin 3 → ℤ → G
  V : Fin 3 → ℤ → G
  W : Fin 3 → Fin 3 → ℤ → G
  TT : ∀ i j, Commute (T i) (T j)
  TU : ∀ l i a, T l * U i a * (T l)⁻¹ = U i (a-if l=i then 1 else 0)
  TV : ∀ l i a, T l * V i a * (T l)⁻¹ = V i (a+if l=i then 1 else 0)
  TW : ∀ l i j a, T l * W i j a * (T l)⁻¹ =
    W i j (a+(if l=i then 1 else 0)-if l=j then 1 else 0)
  diagonal : ∀ i a, W i i a = 1
  square : ∀ i, U i 0 * U i 0 = 1
  UU : ∀ i j, i ≠ j → Commute (U i 0) (U j 0)
  VV : ∀ i j, i ≠ j → Commute (V i 0) (V j 0)
  UV : ∀ i j, i ≠ j → Commute (U i 0) (V j 0)
  WU : ∀ i j h, h ≠ i → Commute (W i j 0) (U h 0)
  WV : ∀ i j h, h ≠ j → Commute (W i j 0) (V h 0)
  UWout : ∀ i j, i ≠ j → ⁅U i 0,W i j 0⁆ = U j 0
  WVout : ∀ i j, i ≠ j → ⁅W i j 0,V j 0⁆ = V i 0

namespace CovariantData
variable {G : Type*} [Group G] (D : CovariantData G)

def act (n : Lattice) : G ≃* G := MulAut.conj (torus D.T n)

end CovariantData

/-- Finitely many seed values. Diagonal W seeds will be killed. -/
structure SeedValues (G : Type*) where
  T : Fin 3 → G
  u : Fin 3 → G
  v : Fin 3 → G
  w : Fin 3 → Fin 3 → G

structure SeedData (G : Type*) [Group G] extends SeedValues G where
  TT : ∀ i j, Commute (T i) (T j)
  Tu : ∀ l i, T l*u i*(T l)⁻¹ = orbit (T i) (u i) (if l=i then 1 else 0)
  Tv : ∀ l i, T l*v i*(T l)⁻¹ = orbit (T i) (v i) (if l=i then 1 else 0)
  Tw : ∀ l i j, T l*w i j*(T l)⁻¹ =
    orbit (T i) (w i j) ((if l=i then 1 else 0)-(if l=j then 1 else 0))
  diagonal : ∀ i, w i i = 1
  square : ∀ i, u i*u i = 1
  UU : ∀ i j, i ≠ j → Commute (u i) (u j)
  VV : ∀ i j, i ≠ j → Commute (v i) (v j)
  UV : ∀ i j, i ≠ j → Commute (u i) (v j)
  WU : ∀ i j h, h ≠ i → Commute (w i j) (u h)
  WV : ∀ i j h, h ≠ j → Commute (w i j) (v h)
  UWout : ∀ i j, i ≠ j → ⁅u i,w i j⁆ = u j
  WVout : ∀ i j, i ≠ j → ⁅w i j,v j⁆ = v i


inductive SeedGenerator where
  | T : Fin 3 → SeedGenerator
  | U : Fin 3 → SeedGenerator
  | V : Fin 3 → SeedGenerator
  | W : Fin 3 → Fin 3 → SeedGenerator
  deriving DecidableEq, Fintype

inductive Rule where
  | TT : Fin 3 → Fin 3 → Rule
  | Tu : Fin 3 → Fin 3 → Rule
  | Tv : Fin 3 → Fin 3 → Rule
  | Tw : Fin 3 → Fin 3 → Fin 3 → Rule
  | diagonal : Fin 3 → Rule
  | square : Fin 3 → Rule
  | UU : Fin 3 → Fin 3 → Rule
  | VV : Fin 3 → Fin 3 → Rule
  | UV : Fin 3 → Fin 3 → Rule
  | WU : Fin 3 → Fin 3 → Fin 3 → Rule
  | WV : Fin 3 → Fin 3 → Fin 3 → Rule
  | UWout : Fin 3 → Fin 3 → Rule
  | WVout : Fin 3 → Fin 3 → Rule
  deriving DecidableEq, Fintype

/-- Finite seed equation patterns. Vacuous index combinations give 1=1. -/
def equation {G : Type*} [Group G] (D : SeedValues G) : Rule → G × G
  | .TT i j => (D.T i*D.T j, D.T j*D.T i)
  | .Tu l i => (D.T l*D.u i*(D.T l)⁻¹, orbit (D.T i) (D.u i) (if l=i then 1 else 0))
  | .Tv l i => (D.T l*D.v i*(D.T l)⁻¹, orbit (D.T i) (D.v i) (if l=i then 1 else 0))
  | .Tw l i j => (D.T l*D.w i j*(D.T l)⁻¹,
      orbit (D.T i) (D.w i j) ((if l=i then 1 else 0)-(if l=j then 1 else 0)))
  | .diagonal i => (D.w i i, 1)
  | .square i => (D.u i*D.u i, 1)
  | .UU i j => if i≠j then (D.u i*D.u j, D.u j*D.u i) else (1,1)
  | .VV i j => if i≠j then (D.v i*D.v j, D.v j*D.v i) else (1,1)
  | .UV i j => if i≠j then (D.u i*D.v j, D.v j*D.u i) else (1,1)
  | .WU i j h => if h≠i then (D.w i j*D.u h, D.u h*D.w i j) else (1,1)
  | .WV i j h => if h≠j then (D.w i j*D.v h, D.v h*D.w i j) else (1,1)
  | .UWout i j => if i≠j then (⁅D.u i,D.w i j⁆, D.u j) else (1,1)
  | .WVout i j => if i≠j then (⁅D.w i j,D.v j⁆, D.v i) else (1,1)

def freeSeeds : SeedValues (FreeGroup SeedGenerator) where
  T i := FreeGroup.of (.T i)
  u i := FreeGroup.of (.U i)
  v i := FreeGroup.of (.V i)
  w i j := FreeGroup.of (.W i j)

def evalSeeds {G : Type*} (D : SeedValues G) : SeedGenerator → G
  | .T i => D.T i
  | .U i => D.u i
  | .V i => D.v i
  | .W i j => D.w i j

theorem equation_evaluate {G : Type*} [Group G] (D : SeedValues G) (r : Rule) :
    FreeGroup.lift (evalSeeds D) (equation freeSeeds r).1 = (equation D r).1 ∧
    FreeGroup.lift (evalSeeds D) (equation freeSeeds r).2 = (equation D r).2 := by
  cases r <;> dsimp only [equation] <;> (try split_ifs) <;> simp [orbit, freeSeeds, evalSeeds]

def relator (r : Rule) : FreeGroup SeedGenerator :=
  (equation freeSeeds r).1 * (equation freeSeeds r).2⁻¹

def finiteRelators : Set (FreeGroup SeedGenerator) := Set.range relator
abbrev Model := PresentedGroup finiteRelators

instance instFiniteElemFreeGroupSeedGeneratorFiniteRelators : Finite finiteRelators := Set.finite_range relator

def modelValues : SeedValues Model where
  T i := PresentedGroup.of (.T i)
  u i := PresentedGroup.of (.U i)
  v i := PresentedGroup.of (.V i)
  w i j := PresentedGroup.of (.W i j)

theorem model_equation (r : Rule) :
    (equation modelValues r).1 = (equation modelValues r).2 := by
  have hm : FreeGroup.lift (evalSeeds modelValues) = PresentedGroup.mk finiteRelators := by
    apply FreeGroup.ext_hom
    intro s
    cases s <;> rfl
  have h := PresentedGroup.mk_eq_mk_of_mul_inv_mem (rels := finiteRelators)
    (x := (equation freeSeeds r).1) (y := (equation freeSeeds r).2) ⟨r,rfl⟩
  obtain ⟨h₁,h₂⟩ := equation_evaluate modelValues r
  rw [hm] at h₁ h₂
  exact h₁.symm.trans (h.trans h₂)


section OriginalSeeds
variable {G : Type*} [Group G] (D : SelectionGroupData G)

@[simp] theorem selection_U_orbit (i : Fin 3) (a : ℤ) :
    orbit (D.T i) (D.U i 0) (-a) = D.U i a := by
  have h := family_zpow (D.T i) (D.U i) (-1)
    (fun r => by simpa only [ite_true, if_true, sub_eq_add_neg] using D.conj_TU i i r) (-a) 0
  simpa using h

@[simp] theorem selection_V_orbit (i : Fin 3) (a : ℤ) :
    orbit (D.T i) (D.V i 0) a = D.V i a := by
  have h := family_zpow (D.T i) (D.V i) 1
    (fun r => by simpa only [ite_true, if_true] using D.conj_TV i i r) a 0
  simpa using h

@[simp] theorem selection_W_orbit (i j : Fin 3) (a : ℤ) :
    orbit (D.T i) (D.W i j 0) a = D.W i j a := by
  by_cases hij : i=j
  · subst j
    simp [orbit, D.diagonal_W]
  · have h := family_zpow (D.T i) (D.W i j) 1
      (fun r => by simpa [hij] using D.conj_TW i i j r) a 0
    simpa using h

/-- The original presentation satisfies each of the finite seed equations. -/
def originalSeeds : SeedData G where
  T := D.T
  u i := D.U i 0
  v i := D.V i 0
  w i j := D.W i j 0
  TT := D.commute_TT
  Tu l i := by
    have h := D.conj_TU l i 0
    have hh := selection_U_orbit D i (-(if l=i then 1 else 0))
    simp only [neg_neg] at hh
    rw [hh]
    simpa using h
  Tv l i := by
    rw [selection_V_orbit]
    simpa using D.conj_TV l i 0
  Tw l i j := by
    rw [selection_W_orbit]
    simpa using D.conj_TW l i j 0
  diagonal i := D.diagonal_W i 0
  square i := D.square_U i 0
  UU i j h := D.commute_UU i j 0 0 h
  VV i j h := D.commute_VV i j 0 0 h
  UV i j h := D.commute_UV i j 0 0 h
  WU i j h hh := D.commute_WU i j h 0 0 hh
  WV i j h hh := D.commute_WV i j h 0 0 hh
  UWout i j h := by simpa using D.commutator_UW i j 0 0 h
  WVout i j h := by simpa using D.commutator_WV i j 0 0 h
end OriginalSeeds


@[simp] theorem map_orbit {G H : Type*} [Group G] [Group H] (f : G →* H)
    (t x : G) (a : ℤ) : f (orbit t x a) = orbit (f t) (f x) a := by simp [orbit]

end LittleFinitistic.FinitePresentation

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_QuotientAction
attribute [-instance] _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LittleFinitistic.QuotientAction
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits CategoryTheory.Preadditive
open QuadraticEncoding

variable {k : Type*} [Field k] {C : Type*} [Category C] [Preadditive C] [Linear k C]
variable {X₀ X₁ X₂ : C} {d t : ℕ} (P : Relations k d t)
  (s : X₀ ⟶ X₁) (s' : X₁ ⟶ X₂) [IsIso s] [IsIso s']
  (a : Fin d → (X₀ ⟶ X₁)) (b : Fin d → (X₁ ⟶ X₂))
  (hc : ∀ h, s ≫ b h = a h ≫ s')

noncomputable def normalized (h : Fin d) : End X₀ := a h ≫ inv s

include hc in
omit [Preadditive C] [IsIso s'] in
lemma normalized_product_comp (h l : Fin d) :
    (normalized s a h * normalized s a l) ≫ s ≫ s' = a l ≫ b h := by
  simp only [normalized,End.mul_def,assoc,IsIso.inv_hom_id_assoc]
  rw [← hc h]
  simp only [IsIso.inv_hom_id_assoc]

omit [Preadditive C] [IsIso s'] in
lemma normalized_comp (h : Fin d) : normalized s a h ≫ s ≫ s' = a h ≫ s' := by
  simp [normalized]

variable (hr : ∀ j,
    (∑ h, ∑ l, P.quadratic j h l • (a l ≫ b h)) +
    (∑ h, P.linear j h • (a h ≫ s')) + P.constant j • (s ≫ s') = 0)

include hc hr in
/-- Normalizing the invertible arrows recovers the original quadratic equations. -/
theorem normalized_relations (j : Fin t) :
    (∑ h, ∑ l, P.quadratic j h l • (normalized s a h * normalized s a l)) +
    (∑ h, P.linear j h • normalized s a h) + P.constant j • (1 : End X₀) = 0 := by
  apply (cancel_mono (s ≫ s')).mp
  dsimp only [End]
  simp only [Preadditive.add_comp,Preadditive.sum_comp,Linear.smul_comp,End.one_def,id_comp,zero_comp]
  simpa only [← End.mul_def,normalized_product_comp s s' a b hc,normalized_comp] using hr j

/-- The degree-at-most-two defining polynomial with the displayed coefficients. -/
def polynomial (j : Fin t) : FreeAlgebra k (Fin d) :=
  (∑ h, ∑ l, P.quadratic j h l • (FreeAlgebra.ι k h * FreeAlgebra.ι k l)) +
  (∑ h, P.linear j h • FreeAlgebra.ι k h) + P.constant j • 1

noncomputable def freeAction : FreeAlgebra k (Fin d) →ₐ[k] End X₀ :=
  FreeAlgebra.lift k (normalized s a)

include hc hr in
lemma freeAction_polynomial (j : Fin t) : freeAction s a (polynomial P j) = 0 := by
  simpa only [freeAction,polynomial,map_add,map_sum,map_smul,map_mul,map_one,
    FreeAlgebra.lift_ι_apply] using normalized_relations P s s' a b hc hr j

end LittleFinitistic.QuotientAction

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Encoding_PresentationReindex
attribute [-instance] _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LittleFinitistic.PresentationReindex
open QuadraticPresentation

variable {k : Type*} [Field k] {α β κ ι : Type*}

noncomputable def renameHom (e : α ≃ β) : FreeAlgebra k α →ₐ[k] FreeAlgebra k β :=
  FreeAlgebra.lift k (fun a => FreeAlgebra.ι k (e a))

@[simp] theorem rename_ι (e : α ≃ β) (a : α) :
    renameHom (k := k) e (FreeAlgebra.ι k a) = FreeAlgebra.ι k (e a) := by
  simp [renameHom]

noncomputable def rename (e : α ≃ β) : FreeAlgebra k α ≃ₐ[k] FreeAlgebra k β :=
  AlgEquiv.ofAlgHom (renameHom e) (renameHom e.symm)
    (by apply FreeAlgebra.hom_ext; funext a; simp)
    (by apply FreeAlgebra.hom_ext; funext a; simp)

@[simp] theorem rename_apply (e : α ≃ β) (p : FreeAlgebra k α) : rename e p = renameHom e p := rfl

@[simp] theorem rename_word (e : α ≃ β) (w : List α) :
    renameHom (k := k) e (word k α w) = word k β (w.map e) := by
  unfold word
  rw [map_list_prod]
  simp only [List.map_map,Function.comp_def,rename_ι]

variable (e : α ≃ β) (j : κ ≃ ι) (p : κ → FreeAlgebra k α)

noncomputable def renamedRelation (i : ι) : FreeAlgebra k β := rename e (p (j.symm i))

end LittleFinitistic.PresentationReindex

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Encoding_RelationBasisAction
attribute [-instance] _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped TensorProduct
namespace LittleFinitistic.RelationBasisAction
open QuadraticEncoding
universe u v
variable {k : Type u} [Field k] {R : Type v} [Ring R] [Algebra k R]
variable {d t : ℕ} (P : Relations k d t) (x : Fin d → R)

/-- The distinguished arrow acts by one, followed by the original generators. -/
def arrow : Fin (d+1) → R := Fin.cases 1 x

end LittleFinitistic.RelationBasisAction

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_BoundedHomotopy
attribute [-instance] _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory Limits ZeroObject Pretriangulated
namespace LittleFinitistic.BoundedHomotopy

variable (C : Type*) [Category* C] [Preadditive C]

/-- Strict boundedness of the underlying complex, at both ends. -/
def boundedComplex : ObjectProperty (CochainComplex C ℤ) :=
  fun X => ∃ a b : ℤ, X.IsStrictlyGE a ∧ X.IsStrictlyLE b

/-- Bounded representatives, with homotopy classes of chain maps. -/
def bounded : ObjectProperty (HomotopyCategory C (.up ℤ)) :=
  (boundedComplex C).strictMap (HomotopyCategory.quotient _ _)

@[simp] theorem bounded_quotient_obj_iff (X : CochainComplex C ℤ) :
    bounded C ((HomotopyCategory.quotient _ _).obj X) ↔ boundedComplex C X := by
  refine ⟨?_, fun h => ⟨_, h⟩⟩
  simp only [bounded, ObjectProperty.strictMap_iff]
  rintro ⟨Y, h, he⟩
  obtain rfl : Y = X := congr_arg CategoryTheory.Quotient.as he
  exact h

instance instContainsZeroHomotopyCategoryIntUpBoundedOfHasZeroObject [HasZeroObject C] : (bounded C).ContainsZero where
  exists_zero := ⟨(HomotopyCategory.quotient _ _).obj 0,
    Functor.map_isZero _ (isZero_zero _), by
      rw [bounded_quotient_obj_iff]
      exact ⟨0, 0, inferInstance, inferInstance⟩⟩

instance instIsStableUnderShiftHomotopyCategoryIntUpBounded : (bounded C).IsStableUnderShift ℤ where
  isStableUnderShiftBy n :=
    { le_shift := by
        intro X hX
        obtain ⟨X : CochainComplex _ _, rfl⟩ := X.quotient_obj_surjective
        rw [bounded_quotient_obj_iff] at hX
        obtain ⟨a, b, ha, hb⟩ := hX
        rw [ObjectProperty.prop_shift_iff, HomotopyCategory.shift_quotient_obj,
          bounded_quotient_obj_iff]
        exact ⟨a-n, b-n, X.isStrictlyGE_shift a n (a-n) (by omega),
          X.isStrictlyLE_shift b n (b-n) (by omega)⟩ }

variable {C}
theorem bounded_mappingCone [HasBinaryBiproducts C]
    {X Y : CochainComplex C ℤ} (f : X ⟶ Y)
    (hX : boundedComplex C X) (hY : boundedComplex C Y) :
    boundedComplex C (CochainComplex.mappingCone f) := by
  obtain ⟨a,b,ha,hb⟩ := hX
  obtain ⟨c,d,hc,hd⟩ := hY
  refine ⟨min (a-1) c, max b d, CochainComplex.isStrictlyGE_mappingCone f a c _
    (by omega) (by omega), ?_⟩
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  rw [CochainComplex.mappingCone.isZero_X_iff]
  exact ⟨X.isZero_of_isStrictlyLE b _ (by omega),
    Y.isZero_of_isStrictlyLE d _ (by omega)⟩

variable (C)
instance instIsTriangulatedClosed₃HomotopyCategoryIntUpBounded [HasZeroObject C] [HasBinaryBiproducts C] :
    (bounded C).IsTriangulatedClosed₃ where
  ext₃' T hT h₁ h₂ := by
    have h₁' : boundedComplex C T.obj₁.as := (bounded_quotient_obj_iff _ _).mp h₁
    have h₂' : boundedComplex C T.obj₂.as := (bounded_quotient_obj_iff _ _).mp h₂
    obtain ⟨f : T.obj₁.as ⟶ T.obj₂.as, hf⟩ :=
      (HomotopyCategory.quotient _ _).map_surjective T.mor₁
    refine ⟨_, ?_, ⟨Triangle.π₃.mapIso (isoTriangleOfIso₁₂ T _ hT
      (HomotopyCategory.mappingCone_triangleh_distinguished f)
      (Iso.refl _) (Iso.refl _) ?_)⟩⟩
    · exact (bounded_quotient_obj_iff _ _).mpr (bounded_mappingCone f h₁' h₂')
    · exact (Category.comp_id _).trans (hf.symm.trans (Category.id_comp _).symm)

instance instIsTriangulatedHomotopyCategoryIntUpBounded [HasZeroObject C] [HasBinaryBiproducts C] : (bounded C).IsTriangulated where
  toIsTriangulatedClosed₂ := .of_isTriangulatedClosed₃

/-- The homotopy category Kᵇ(C); boundedness is part of each object. -/
abbrev K := (bounded C).FullSubcategory

instance instIsTriangulatedK [HasZeroObject C] [HasBinaryBiproducts C] : IsTriangulated (K C) := inferInstance

end LittleFinitistic.BoundedHomotopy

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_DerivedTruncationCohomology
attribute [-instance] _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
namespace LittleFinitistic.DerivedTruncation
universe u v w
variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
open DerivedCategory

abbrev t := (DerivedCategory.TStructure.t : CategoryTheory.Triangulated.TStructure (DerivedCategory C))
abbrev lower (X : DerivedCategory C) := (t.truncLT 0).obj X
abbrev upper (X : DerivedCategory C) := (t.truncGE 0).obj X
abbrev inclusion (X : DerivedCategory C) := (t.truncLTι 0).app X
abbrev projection (X : DerivedCategory C) := (t.truncGEπ 0).app X
abbrev triangle (X : DerivedCategory C) := (t.triangleLTGE 0).obj X
instance lower_isLE_minus_one (X : DerivedCategory C) : (lower X).IsLE (-1) :=
  t.isLE_truncLT_obj X 0 (-1) (by omega)
lemma distinguished (X : DerivedCategory C) : triangle X ∈ distTriang _ :=
  t.triangleLTGE_distinguished 0 X

lemma lower_homology_isIso (X : DerivedCategory C) (n : ℤ) (hn : n < 0) :
    IsIso ((homologyFunctor C n).map (inclusion X)) := by
  have h₀ := DerivedCategory.isZero_of_isGE (upper X) 0 n hn
  have h₁ := DerivedCategory.isZero_of_isGE (upper X) 0 (n-1) (by omega)
  have : Mono ((homologyFunctor C n).map (inclusion X)) :=
    (HomologySequence.exact₁ (triangle X) (distinguished X) (n-1) n (by omega)).mono_g
      (h₁.eq_of_src _ _)
  have : Epi ((homologyFunctor C n).map (inclusion X)) :=
    (HomologySequence.exact₂ (triangle X) (distinguished X) n).epi_f (h₀.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

lemma upper_homology_isIso (X : DerivedCategory C) (n : ℤ) (hn : 0 ≤ n) :
    IsIso ((homologyFunctor C n).map (projection X)) := by
  have h₀ := DerivedCategory.isZero_of_isLE (lower X) (-1) n (by omega)
  have h₁ := DerivedCategory.isZero_of_isLE (lower X) (-1) (n+1) (by omega)
  have : Mono ((homologyFunctor C n).map (projection X)) :=
    (HomologySequence.exact₂ (triangle X) (distinguished X) n).mono_g (h₀.eq_of_src _ _)
  have : Epi ((homologyFunctor C n).map (projection X)) :=
    (HomologySequence.exact₃ (triangle X) (distinguished X) n (n+1) rfl).epi_f
      (h₁.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

def lowerHomologyIso (X : DerivedCategory C) (n : ℤ) (hn : n < 0) :
    (homologyFunctor C n).obj (lower X) ≅ (homologyFunctor C n).obj X := by
  haveI := lower_homology_isIso X n hn
  exact asIso ((homologyFunctor C n).map (inclusion X))

def upperHomologyIso (X : DerivedCategory C) (n : ℤ) (hn : 0 ≤ n) :
    (homologyFunctor C n).obj X ≅ (homologyFunctor C n).obj (upper X) := by
  haveI := upper_homology_isIso X n hn
  exact asIso ((homologyFunctor C n).map (projection X))

/-- The exact cohomological support hypothesis in Section 4. -/
def TwoDegrees (X : DerivedCategory C) : Prop :=
  ∀ n : ℤ, n ≠ 0 → n ≠ -3 → IsZero ((homologyFunctor C n).obj X)

lemma isLE_zero (X : DerivedCategory C) (hX : TwoDegrees X) : X.IsLE 0 := by
  rw [DerivedCategory.isLE_iff]
  intro n hn
  exact hX n (by omega) (by omega)
lemma isGE_neg_three (X : DerivedCategory C) (hX : TwoDegrees X) : X.IsGE (-3) := by
  rw [DerivedCategory.isGE_iff]
  intro n hn
  exact hX n (by omega) (by omega)
lemma lower_isGE (X : DerivedCategory C) (hX : TwoDegrees X) : (lower X).IsGE (-3) := by
  have := isGE_neg_three X hX
  infer_instance
lemma lower_isLE (X : DerivedCategory C) (hX : TwoDegrees X) : (lower X).IsLE (-3) := by
  rw [DerivedCategory.isLE_iff]
  intro n hn
  by_cases hn₀ : n < 0
  · exact (lowerHomologyIso X n hn₀).isZero_iff.mpr (hX n (by omega) (by omega))
  · exact DerivedCategory.isZero_of_isLE (lower X) (-1) n (by omega)
lemma upper_isLE (X : DerivedCategory C) (hX : TwoDegrees X) : (upper X).IsLE 0 := by
  have := isLE_zero X hX
  infer_instance

/-- An object concentrated in one degree is the stalk of its actual cohomology. -/
def singleIso (X : DerivedCategory C) (n : ℤ) [X.IsGE n] [X.IsLE n] :
    X ≅ (singleFunctor C n).obj ((homologyFunctor C n).obj X) := Classical.choice (by
  obtain ⟨Y,⟨e⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE X n
  let h : (homologyFunctor C n).obj X ≅ Y :=
    (homologyFunctor C n).mapIso e ≪≫ (singleFunctorCompHomologyFunctorIso C n).app Y
  exact ⟨e ≪≫ (singleFunctor C n).mapIso h.symm⟩)
end LittleFinitistic.DerivedTruncation

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_DiagramEvaluationSquares
attribute [-instance] _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory
namespace LittleFinitistic.DiagramEvaluationSquares
universe u v
variable {C : Type u} [Category.{v} C]

/-- Compose two isomorphisms of arrow diagrams, retaining the displayed arrow. -/
theorem compose {A₀ A₁ B₀ B₁ C₀ C₁ : C}
    (f : A₀ ⟶ A₁) (g : B₀ ⟶ B₁) (h : C₀ ⟶ C₁)
    (i₀ : A₀ ≅ B₀) (i₁ : A₁ ≅ B₁) (j₀ : B₀ ≅ C₀) (j₁ : B₁ ≅ C₁)
    (hi : f ≫ i₁.hom = i₀.hom ≫ g) (hj : g ≫ j₁.hom = j₀.hom ≫ h) :
    f ≫ (i₁ ≪≫ j₁).hom = (i₀ ≪≫ j₀).hom ≫ h := by
  simp only [Iso.trans_hom]
  rw [← Category.assoc,hi,Category.assoc,hj,← Category.assoc]
end LittleFinitistic.DiagramEvaluationSquares

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_DiagramLifting
attribute [-instance] _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
namespace LittleFinitistic.DiagramLifting
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

variable {C D : Type*} [Category C] [Category D]
variable (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W]
variable [W.HasRightCalculusOfFractions]

/-- Finitely many localized arrows admit one common source denominator. -/
theorem finite_roof (n : ℕ) (X : C) (Y : Fin n → C)
    (f : ∀ i, L.obj X ⟶ L.obj (Y i)) :
    ∃ (Z : C) (u : Z ⟶ X), W u ∧
      ∃ (g : ∀ i, Z ⟶ Y i), ∀ i, L.map u ≫ f i = L.map (g i) := by
  induction n generalizing X with
  | zero => exact ⟨X,𝟙 X,W.id_mem X,(fun i => Fin.elim0 i),fun i => Fin.elim0 i⟩
  | succ n ih =>
    obtain ⟨φ,hφ⟩ := Localization.exists_rightFraction L W (f 0)
    obtain ⟨Z,u,hu,g,hg⟩ := ih φ.X' (fun i => Y i.succ)
      (fun i => L.map φ.s ≫ f i.succ)
    refine ⟨Z,u ≫ φ.s,W.comp_mem _ _ hu φ.hs,Fin.cases (u ≫ φ.f) g,?_⟩
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.cases_zero,Functor.map_comp,assoc,hφ,φ.map_s_comp_map]
    · simpa only [Fin.cases_succ,Functor.map_comp,assoc] using hg j

section Zero
variable [HasZeroMorphisms C] [HasZeroMorphisms D] [L.PreservesZeroMorphisms]

/-- A finite family vanishing after localization is annihilated by one source denominator. -/
theorem finite_zero_refinement (n : ℕ) (X : C) (Y : Fin n → C)
    (f : ∀ i, X ⟶ Y i) (hf : ∀ i, L.map (f i) = 0) :
    ∃ (Z : C) (u : Z ⟶ X), W u ∧ ∀ i, u ≫ f i = 0 := by
  induction n generalizing X with
  | zero => exact ⟨X,𝟙 X,W.id_mem X,fun i => Fin.elim0 i⟩
  | succ n ih =>
    have h0 : L.map (f 0) = L.map (0 : X ⟶ Y 0) := by simpa using hf 0
    obtain ⟨X',u,hu,he⟩ := (MorphismProperty.map_eq_iff_precomp L W (f 0) 0).mp h0
    have he0 : u ≫ f 0 = 0 := by simpa using he
    obtain ⟨Z,v,hv,hg⟩ := ih X' (fun i => Y i.succ) (fun i => u ≫ f i.succ)
      (fun i => by simp [hf])
    refine ⟨Z,v ≫ u,W.comp_mem _ _ hv hu,?_⟩
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [assoc,he0]
    · simpa only [assoc] using hg j

end Zero

open scoped BigOperators
variable {k : Type*} [CommRing k] [Preadditive C] [Preadditive D]
variable [Linear k C] [Linear k D] [L.Additive] [L.Linear k]

/-- A finite three-vertex diagram with arbitrary homogeneous quadratic relations
lifts along a right-fraction localization. The displayed denominator maps give
an isomorphism from the localized lift to the original entire diagram. -/
theorem quadratic_diagram_lift (na nb nr : ℕ) (X₀ X₁ X₂ : C)
    (a : Fin na → (L.obj X₀ ⟶ L.obj X₁))
    (b : Fin nb → (L.obj X₁ ⟶ L.obj X₂))
    (r : Fin nr → Fin na → Fin nb → k)
    (hr : ∀ ρ, ∑ i, ∑ j, r ρ i j • (a i ≫ b j) = 0) :
    ∃ (D₀ D₁ : C) (u₀ : D₀ ⟶ X₀) (u₁ : D₁ ⟶ X₁), W u₀ ∧ W u₁ ∧
    ∃ (f : Fin na → (D₀ ⟶ D₁)) (g : Fin nb → (D₁ ⟶ X₂)),
      (∀ i, L.map u₀ ≫ a i = L.map (f i) ≫ L.map u₁) ∧
      (∀ j, L.map u₁ ≫ b j = L.map (g j)) ∧
      (∀ ρ, ∑ i, ∑ j, r ρ i j • (f i ≫ g j) = 0) := by
  classical
  obtain ⟨D₁,u₁,hu₁,g,hg⟩ := finite_roof L W nb X₁ (fun _ => X₂) b
  have : IsIso (L.map u₁) := Localization.inverts L W _ hu₁
  obtain ⟨D₀,u₀,hu₀,f,hf⟩ := finite_roof L W na X₀ (fun _ => D₁)
    (fun i => a i ≫ inv (L.map u₁))
  have hpath (i : Fin na) (j : Fin nb) :
      L.map (f i ≫ g j) = L.map u₀ ≫ (a i ≫ b j) := by
    rw [Functor.map_comp,← hf i,← hg j]
    simp only [assoc,IsIso.inv_hom_id_assoc]
  let relations : Fin nr → (D₀ ⟶ X₂) := fun ρ => ∑ i, ∑ j, r ρ i j • (f i ≫ g j)
  have hrel (ρ : Fin nr) : L.map (relations ρ) = 0 := by
    dsimp [relations]
    simp only [Functor.map_sum,Functor.map_smul,hpath]
    have h := congrArg (fun t => L.map u₀ ≫ t) (hr ρ)
    simpa only [Preadditive.comp_sum,Linear.comp_smul,comp_zero] using h
  obtain ⟨D₀',v,hv,hvrel⟩ := finite_zero_refinement L W nr D₀ (fun _ => X₂) relations hrel
  refine ⟨D₀',D₁,v ≫ u₀,u₁,W.comp_mem _ _ hv hu₀,hu₁,
    (fun i => v ≫ f i),g,?_,hg,?_⟩
  · intro i
    have hi := congrArg (fun t => t ≫ L.map u₁) (hf i)
    simp only [assoc,IsIso.inv_hom_id,comp_id] at hi
    simp only [Functor.map_comp,assoc]
    rw [← hi]
  · intro ρ
    have h := hvrel ρ
    dsimp [relations] at h
    simpa only [Preadditive.comp_sum,Linear.comp_smul,assoc] using h

include W in
/-- Every finite three-level quadratic diagram in the localized category,
including objects not literally presented as functor images, has an isomorphic lift. -/
theorem finite_quadratic_diagram_lifting (na nb nr : ℕ) (Y₀ Y₁ Y₂ : D)
    (a : Fin na → (Y₀ ⟶ Y₁)) (b : Fin nb → (Y₁ ⟶ Y₂))
    (r : Fin nr → Fin na → Fin nb → k)
    (hr : ∀ ρ, ∑ i, ∑ j, r ρ i j • (a i ≫ b j) = 0) :
    ∃ (X₀ X₁ X₂ : C) (e₀ : L.obj X₀ ≅ Y₀) (e₁ : L.obj X₁ ≅ Y₁)
      (e₂ : L.obj X₂ ≅ Y₂) (f : Fin na → (X₀ ⟶ X₁)) (g : Fin nb → (X₁ ⟶ X₂)),
      (∀ i, L.map (f i) ≫ e₁.hom = e₀.hom ≫ a i) ∧
      (∀ j, L.map (g j) ≫ e₂.hom = e₁.hom ≫ b j) ∧
      (∀ ρ, ∑ i, ∑ j, r ρ i j • (f i ≫ g j) = 0) := by
  classical
  have := Localization.essSurj L W
  let X₀ := L.objPreimage Y₀
  let X₁ := L.objPreimage Y₁
  let X₂ := L.objPreimage Y₂
  let e₀ : L.obj X₀ ≅ Y₀ := L.objObjPreimageIso Y₀
  let e₁ : L.obj X₁ ≅ Y₁ := L.objObjPreimageIso Y₁
  let e₂ : L.obj X₂ ≅ Y₂ := L.objObjPreimageIso Y₂
  let a' := fun i => e₀.hom ≫ a i ≫ e₁.inv
  let b' := fun j => e₁.hom ≫ b j ≫ e₂.inv
  have hr' (ρ : Fin nr) : ∑ i, ∑ j, r ρ i j • (a' i ≫ b' j) = 0 := by
    dsimp [a',b']
    simp only [assoc,Iso.inv_hom_id_assoc]
    have h := congrArg (fun t => e₀.hom ≫ t ≫ e₂.inv) (hr ρ)
    simpa only [Preadditive.comp_sum,Preadditive.sum_comp,Linear.comp_smul,
      Linear.smul_comp,assoc,comp_zero,zero_comp] using h
  obtain ⟨D₀,D₁,u₀,u₁,hu₀,hu₁,f,g,hf,hg,hrel⟩ :=
    quadratic_diagram_lift L W na nb nr X₀ X₁ X₂ a' b' r hr'
  refine ⟨D₀,D₁,X₂,(Localization.isoOfHom L W u₀ hu₀) ≪≫ e₀,
    (Localization.isoOfHom L W u₁ hu₁) ≪≫ e₁,e₂,f,g,?_,?_,hrel⟩
  · intro i
    have h := congrArg (fun t => t ≫ e₁.hom) (hf i)
    simpa only [a',Iso.trans_hom,Localization.isoOfHom_hom,assoc,
      Iso.inv_hom_id,comp_id] using h.symm
  · intro j
    have h := congrArg (fun t => t ≫ e₂.hom) (hg j)
    simpa only [b',Iso.trans_hom,Localization.isoOfHom_hom,assoc,
      Iso.inv_hom_id,comp_id] using h.symm
end LittleFinitistic.DiagramLifting

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_EvaluationModule
attribute [-instance] _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology
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
variable {Y : Type v} [AddCommGroup Y] [Module k Y]

/-- An arbitrary vector-space representation of the presented quadratic algebra. -/
structure Representation (P : Relations k d t) (Y : Type v)
    [AddCommGroup Y] [Module k Y] where
  generator : Fin d → Module.End k Y
  relation : ∀ j, (∑ h, ∑ l, P.quadratic j h l • (generator h * generator l)) +
    (∑ h, P.linear j h • generator h) + P.constant j • (1 : Module.End k Y) = 0

end LittleFinitistic.QuadraticEncoding

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_FiniteProjectiveHomotopy
attribute [-instance] _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology
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

lemma finite_of_iso {M N : ModuleCat.{v} R} (e : M ≅ N) [Module.Finite R M] : Module.Finite R N :=
  Module.Finite.of_surjective e.toLinearEquiv.toLinearMap e.toLinearEquiv.surjective

end LittleFinitistic.FiniteProjectiveHomotopy

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_FiniteSumTransport
attribute [-instance] _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.FiniteSumTransport
variable {C D E : Type*} [Category C] [Category D] [Category E]
  [Preadditive C] [Preadditive D] [Preadditive E]
  [HasFiniteBiproducts C] [HasFiniteBiproducts D]
variable (F : C ⥤ E) (G : D ⥤ E) [F.Additive] [G.Additive]
variable {I : Type} [Finite I] (X : I → C) (Y : I → D)
variable (α : ∀ i, F.obj (X i) ≅ G.obj (Y i))

def iso : F.obj (⨁ X) ≅ G.obj (⨁ Y) :=
  F.mapBiproduct X ≪≫ biproduct.mapIso α ≪≫ (G.mapBiproduct Y).symm

@[reassoc (attr := simp)]
theorem injection (i : I) :
    F.map (biproduct.ι X i) ≫ (iso F G X Y α).hom =
      (α i).hom ≫ G.map (biproduct.ι Y i) := by
  have hi : F.map (biproduct.ι X i) ≫ (F.mapBiproduct X).hom =
      biproduct.ι (fun j => F.obj (X j)) i := by
    apply (cancel_mono (F.mapBiproduct X).inv).1
    rw [Category.assoc,Iso.hom_inv_id,Category.comp_id]
    simp only [Functor.mapBiproduct_inv,biproduct.ι_desc]
  simp only [iso,Iso.trans_hom,Iso.symm_hom,← Category.assoc,hi]
  simp [biproduct.mapIso_hom]
  erw [Category.assoc, biproduct.ι_desc]
  rfl

/-- Coordinate isomorphisms commute with the supplied map from a finite sum. -/
theorem desc_square {U : C} {V : D} (β : F.obj U ≅ G.obj V)
    (f : ∀ i, X i ⟶ U) (g : ∀ i, Y i ⟶ V)
    (h : ∀ i, (α i).hom ≫ G.map (g i) = F.map (f i) ≫ β.hom) :
    (iso F G X Y α).hom ≫ G.map (biproduct.desc g) =
      F.map (biproduct.desc f) ≫ β.hom := by
  apply (cancel_epi (F.mapBiproduct X).inv).1
  apply biproduct.hom_ext'
  intro i
  simp only [Functor.mapBiproduct_inv,biproduct.ι_desc_assoc]
  rw [← Category.assoc,injection,Category.assoc,← Functor.map_comp,
    biproduct.ι_desc,h]
  rw [← Category.assoc,← Functor.map_comp,biproduct.ι_desc]

@[reassoc (attr := simp)]
theorem projection (i : I) :
    (iso F G X Y α).hom ≫ G.map (biproduct.π Y i) =
      F.map (biproduct.π X i) ≫ (α i).hom := by
  apply (cancel_epi (F.mapBiproduct X).inv).1
  apply biproduct.hom_ext'
  intro j
  simp only [Functor.mapBiproduct_inv,biproduct.ι_desc_assoc]
  rw [← Category.assoc,injection,Category.assoc,← Functor.map_comp,
    ← Category.assoc (F.map (biproduct.ι X j)),← Functor.map_comp]
  classical
  by_cases hji : j=i
  · subst j; simp
  · simp [hji]

/-- Entrywise coordinate squares identify the entire supplied finite matrix map. -/
theorem matrix_square {J : Type} [Finite J] (X' : J → C) (Y' : J → D)
    (β : ∀ j, F.obj (X' j) ≅ G.obj (Y' j))
    (f : (⨁ X) ⟶ (⨁ X')) (g : (⨁ Y) ⟶ (⨁ Y'))
    (h : ∀ i j, (α i).hom ≫ G.map (biproduct.ι Y i ≫ g ≫ biproduct.π Y' j) =
      F.map (biproduct.ι X i ≫ f ≫ biproduct.π X' j) ≫ (β j).hom) :
    (iso F G X Y α).hom ≫ G.map g = F.map f ≫ (iso F G X' Y' β).hom := by
  apply (cancel_epi (F.mapBiproduct X).inv).1
  apply biproduct.hom_ext'
  intro i
  simp only [Functor.mapBiproduct_inv,biproduct.ι_desc_assoc]
  apply (cancel_mono (G.mapBiproduct Y').hom).1
  apply biproduct.hom_ext
  intro j
  have hp : (G.mapBiproduct Y').hom ≫ biproduct.π (G.obj ∘ Y') j =
      G.map (biproduct.π Y' j) := by
    change (biproduct.lift (fun j => G.map (biproduct.π Y' j))) ≫
      biproduct.π (fun j => G.obj (Y' j)) j = _
    exact biproduct.lift_π _ j
  simp only [Category.assoc,hp,injection_assoc,projection]
  simpa only [Functor.map_comp,Category.assoc] using h i j
end LittleFinitistic.FiniteSumTransport

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_OddDouble
attribute [-instance] _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LittleFinitistic.OddDouble
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open CategoryTheory.Preadditive CategoryTheory.Pretriangulated
open CategoryTheory.Idempotents

variable {C : Type*} [Category C] [Preadditive C] [HasShift C ℤ]

noncomputable def sourceProjector (T : Triangle C) (u : T.obj₂ ⟶ T.obj₁) :=
  𝟙 T.obj₁ - T.mor₁ ≫ u

noncomputable def targetProjector (T : Triangle C) (u : T.obj₂ ⟶ T.obj₁) :=
  𝟙 T.obj₂ - u ≫ T.mor₁

variable (T : Triangle C) (u : T.obj₂ ⟶ T.obj₁)
variable (hu : T.mor₁ ≫ u ≫ T.mor₁ = T.mor₁)
include hu

theorem sourceProjector_idem : sourceProjector T u ≫ sourceProjector T u = sourceProjector T u := by
  unfold sourceProjector
  simp only [comp_sub,sub_comp,id_comp,comp_id,assoc,reassoc_of% hu]
  abel

theorem targetProjector_idem : targetProjector T u ≫ targetProjector T u = targetProjector T u := by
  unfold targetProjector
  simp only [comp_sub,sub_comp,id_comp,comp_id,assoc,hu]
  abel

theorem sourceProjector_comp : sourceProjector T u ≫ T.mor₁ = 0 := by
  simp only [sourceProjector,sub_comp,id_comp,assoc,hu,sub_self]

theorem comp_targetProjector : T.mor₁ ≫ targetProjector T u = 0 := by
  simp only [targetProjector,comp_sub,comp_id,hu,sub_self]

variable [HasZeroObject C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

local instance instHasFiniteBiproductsKaroubi_solutions : HasFiniteBiproducts (Karoubi C) := Karoubi.karoubi_hasFiniteBiproducts
local instance instHasBinaryBiproductsKaroubi_solutions : HasBinaryBiproducts (Karoubi C) := hasBinaryBiproducts_of_finite_biproducts (Karoubi C)

variable (hT : T ∈ distTriang C)
include hT

omit hu in
theorem targetProjector_comp_second : targetProjector T u ≫ T.mor₂ = T.mor₂ := by
  simp only [targetProjector,sub_comp,id_comp,assoc,comp_distTriang_mor_zero₁₂ T hT,
    comp_zero,sub_zero]

omit hu in
theorem third_comp_sourceProjector :
    T.mor₃ ≫ (sourceProjector T u)⟦(1 : ℤ)⟧' = T.mor₃ := by
  simp only [sourceProjector,Functor.map_sub,Functor.map_comp,comp_sub,
    ← assoc,comp_distTriang_mor_zero₃₁ T hT,zero_comp,sub_zero]
  rw [(shiftFunctor C (1 : ℤ)).map_id,comp_id]

/-- Splitting data for the cone of a morphism admitting a generalized inverse.
These are the five biproduct equations in the idempotent completion. -/
theorem cone_splitting :
    ∃ (s : T.obj₁⟦(1 : ℤ)⟧ ⟶ T.obj₃) (t : T.obj₃ ⟶ T.obj₂),
      (sourceProjector T u)⟦(1 : ℤ)⟧' ≫ s = s ∧
      s ≫ T.mor₃ = (sourceProjector T u)⟦(1 : ℤ)⟧' ∧
      t ≫ targetProjector T u = t ∧
      T.mor₂ ≫ t = targetProjector T u ∧
      s ≫ t = 0 ∧
      t ≫ T.mor₂ + T.mor₃ ≫ s = 𝟙 T.obj₃ := by
  let p := sourceProjector T u
  let q := targetProjector T u
  have hp : p ≫ p = p := sourceProjector_idem T u hu
  have hq : q ≫ q = q := targetProjector_idem T u hu
  have hpf : p ≫ T.mor₁ = 0 := sourceProjector_comp T u hu
  have hfq : T.mor₁ ≫ q = 0 := comp_targetProjector T u hu
  have hqg : q ≫ T.mor₂ = T.mor₂ := targetProjector_comp_second T u hT
  have hhp : T.mor₃ ≫ p⟦(1 : ℤ)⟧' = T.mor₃ := third_comp_sourceProjector T u hT
  have hp1 : p⟦(1 : ℤ)⟧' ≫ p⟦(1 : ℤ)⟧' = p⟦(1 : ℤ)⟧' := by
    rw [← Functor.map_comp,hp]
  obtain ⟨s₀,hs₀⟩ := T.coyoneda_exact₁ hT (p⟦(1 : ℤ)⟧') (by
    rw [← Functor.map_comp,hpf,Functor.map_zero])
  let s := p⟦(1 : ℤ)⟧' ≫ s₀
  have hps : p⟦(1 : ℤ)⟧' ≫ s = s := by
    dsimp [s]; rw [← assoc,hp1]
  have hsh : s ≫ T.mor₃ = p⟦(1 : ℤ)⟧' := by
    dsimp [s]; rw [assoc,← hs₀,hp1]
  have hdelta : (𝟙 T.obj₃ - T.mor₃ ≫ s) ≫ T.mor₃ = 0 := by
    rw [sub_comp,id_comp,assoc,hsh,hhp,sub_self]
  obtain ⟨t₀,ht₀⟩ := T.coyoneda_exact₃ hT _ hdelta
  let t := t₀ ≫ q
  have htq : t ≫ q = t := by dsimp [t]; rw [assoc,hq]
  have htg : t ≫ T.mor₂ = 𝟙 T.obj₃ - T.mor₃ ≫ s := by
    dsimp [t]; rw [assoc,hqg,← ht₀]
  have hgt : T.mor₂ ≫ t = q := by
    have hz : (T.mor₂ ≫ t - q) ≫ T.mor₂ = 0 := by
      rw [sub_comp,assoc,htg,comp_sub,comp_id,← assoc,
        comp_distTriang_mor_zero₂₃ T hT,zero_comp,hqg,sub_zero,sub_self]
    obtain ⟨v,hv⟩ := T.coyoneda_exact₂ hT _ hz
    have he := congrArg (fun z => z ≫ q) hv
    simp only [sub_comp,assoc,htq,hq,hfq,comp_zero] at he
    exact sub_eq_zero.mp he
  have hst : s ≫ t = 0 := by
    have hz : (s ≫ t) ≫ T.mor₂ = 0 := by
      rw [assoc,htg,comp_sub,comp_id,← assoc,hsh,hps,sub_self]
    obtain ⟨v,hv⟩ := T.coyoneda_exact₂ hT _ hz
    have he := congrArg (fun z => z ≫ q) hv
    simpa only [assoc,htq,hfq,comp_zero] using he
  exact ⟨s,t,hps,hsh,htq,hgt,hst,by rw [htg,sub_add_cancel]⟩

noncomputable def formalKernel : Karoubi C where
  X := T.obj₁⟦(1 : ℤ)⟧
  p := (sourceProjector T u)⟦(1 : ℤ)⟧'
  idem := by rw [← Functor.map_comp,sourceProjector_idem T u hu]

noncomputable def formalCokernel : Karoubi C where
  X := T.obj₂
  p := targetProjector T u
  idem := targetProjector_idem T u hu

/-- The cone of a regular morphism is the direct sum of its formal cokernel
and the shifted formal kernel in the idempotent completion. -/
theorem regular_cone_iso :
    Nonempty ((toKaroubi C).obj T.obj₃ ≅ formalCokernel T u hu ⊞ formalKernel T u hu) := by
  obtain ⟨s,t,hps,hsh,htq,hgt,hst,htotal⟩ := cone_splitting T u hu hT
  let Q := formalCokernel T u hu
  let P := formalKernel T u hu
  let S := (toKaroubi C).obj T.obj₃
  let gi : Q ⟶ S := ⟨T.mor₂,by
    change targetProjector T u ≫ T.mor₂ ≫ 𝟙 _ = T.mor₂
    rw [comp_id,targetProjector_comp_second T u hT]⟩
  let tr : S ⟶ Q := ⟨t,by
    change 𝟙 _ ≫ t ≫ targetProjector T u = t
    rw [id_comp,htq]⟩
  let hr : S ⟶ P := ⟨T.mor₃,by
    change 𝟙 _ ≫ T.mor₃ ≫ (sourceProjector T u)⟦(1 : ℤ)⟧' = T.mor₃
    rw [id_comp,third_comp_sourceProjector T u hT]⟩
  let si : P ⟶ S := ⟨s,by
    change (sourceProjector T u)⟦(1 : ℤ)⟧' ≫ s ≫ 𝟙 _ = s
    rw [comp_id,hps]⟩
  let bc : BinaryBicone Q P :=
    { pt := S
      fst := tr
      snd := hr
      inl := gi
      inr := si
      inl_fst := by apply Karoubi.hom_ext; exact hgt
      inl_snd := by apply Karoubi.hom_ext; exact comp_distTriang_mor_zero₂₃ T hT
      inr_fst := by apply Karoubi.hom_ext; exact hst
      inr_snd := by apply Karoubi.hom_ext; exact hsh }
  have hb : bc.IsBilimit := isBinaryBilimitOfTotal bc (by
    apply Karoubi.hom_ext
    exact htotal)
  exact ⟨biprod.uniqueUpToIso Q P hb⟩

omit hu hT

noncomputable def formalShift (P : Karoubi C) (n : ℤ) : Karoubi C where
  X := P.X⟦n⟧
  p := P.p⟦n⟧'
  idem := by rw [← Functor.map_comp,P.idem]

/-- The first odd double is the cone of the complementary idempotent. -/
theorem odd_double_one (U : Karoubi C) :
    ∃ S : C, Nonempty ((toKaroubi C).obj S ≅ U ⊞ formalShift U 1) := by
  let f := 𝟙 U.X - U.p
  have hf : f ≫ f = f := by
    dsimp [f]
    simp only [comp_sub,sub_comp,id_comp,comp_id,U.idem]
    abel
  obtain ⟨S,g,h,hT⟩ := distinguished_cocone_triangle f
  let T := Triangle.mk f g h
  have hu : T.mor₁ ≫ f ≫ T.mor₁ = T.mor₁ := by change f ≫ f ≫ f = f; rw [hf,hf]
  have hq : formalCokernel T f hu = U := by
    refine Karoubi.ext (P := formalCokernel T f hu) (Q := U) rfl ?_
    change (𝟙 U.X - f ≫ f) ≫ 𝟙 U.X = 𝟙 U.X ≫ U.p
    rw [hf,comp_id,id_comp]
    dsimp [f]
    abel
  have hp : formalKernel T f hu = formalShift U 1 := by
    refine Karoubi.ext (P := formalKernel T f hu) (Q := formalShift U 1) rfl ?_
    change (𝟙 U.X - f ≫ f)⟦(1 : ℤ)⟧' ≫ 𝟙 _ = 𝟙 _ ≫ U.p⟦(1 : ℤ)⟧'
    rw [comp_id,id_comp,hf]
    congr 1
    dsimp [f]
    abel
  refine ⟨S,?_⟩
  have hc := regular_cone_iso T f hu hT
  rw [hq,hp] at hc
  exact hc

noncomputable def formalShiftFunctor (n : ℤ) : Karoubi C ⥤ Karoubi C where
  obj P := formalShift P n
  map {P Q} f := ⟨f.f⟦n⟧',by
    change P.p⟦n⟧' ≫ f.f⟦n⟧' ≫ Q.p⟦n⟧' = f.f⟦n⟧'
    simp only [← Functor.map_comp,f.comm]⟩
  map_id _ := by apply Karoubi.hom_ext; rfl
  map_comp _ _ := by apply Karoubi.hom_ext; exact Functor.map_comp _ _ _

instance instAdditiveKaroubiFormalShiftFunctor (n : ℤ) : (formalShiftFunctor (C := C) n).Additive where
  map_add := by intros; apply Karoubi.hom_ext; exact Functor.map_add _

noncomputable def retractProjector {A P : Karoubi C} (i : P ⟶ A) (r : A ⟶ P)
    (hi : i ≫ r = 𝟙 P) : Karoubi C where
  X := A.X
  p := r.f ≫ i.f
  idem := by
    have h : i.f ≫ r.f = P.p := congrArg Karoubi.Hom.f hi
    calc
      (r.f ≫ i.f) ≫ (r.f ≫ i.f) = (r.f ≫ (i.f ≫ r.f)) ≫ i.f := by simp only [assoc]
      _ = (r.f ≫ P.p) ≫ i.f := by rw [h]
      _ = r.f ≫ i.f := by rw [Karoubi.comp_p]

noncomputable def retractProjectorIso {A P : Karoubi C} (i : P ⟶ A) (r : A ⟶ P)
    (hi : i ≫ r = 𝟙 P) : retractProjector i r hi ≅ P := by
  have h : i.f ≫ r.f = P.p := congrArg Karoubi.Hom.f hi
  exact
    { hom := ⟨r.f,by
        change (r.f ≫ i.f) ≫ r.f ≫ P.p = r.f
        simp only [assoc,h,Karoubi.comp_p]⟩
      inv := ⟨i.f,by
        change P.p ≫ i.f ≫ (r.f ≫ i.f) = i.f
        rw [← assoc,Karoubi.p_comp,← assoc,h,Karoubi.p_comp]⟩
      hom_inv_id := by apply Karoubi.hom_ext; rfl
      inv_hom_id := by apply Karoubi.hom_ext; exact h }

/-- The second cone realizes the third odd double, with three successive shifts. -/
theorem odd_double_three_nested (U : Karoubi C) :
    ∃ Z : C, Nonempty ((toKaroubi C).obj Z ≅
      U ⊞ formalShift (formalShift (formalShift U 1) 1) 1) := by
  classical
  obtain ⟨S,⟨e⟩⟩ := odd_double_one U
  let A := (toKaroubi C).obj S
  let F := formalShiftFunctor (C := C) 1
  let P := F.obj U
  let i₀ : U ⟶ A := biprod.inl ≫ e.inv
  let r₀ : A ⟶ U := e.hom ≫ biprod.fst
  let i₁ : P ⟶ A := biprod.inr ≫ e.inv
  let r₁ : A ⟶ P := e.hom ≫ biprod.snd
  have h₀ : i₀ ≫ r₀ = 𝟙 U := by simp only [i₀,r₀,assoc,Iso.inv_hom_id_assoc,biprod.inl_fst]
  have h₁ : i₁ ≫ r₁ = 𝟙 P := by
    change (biprod.inr ≫ e.inv) ≫ e.hom ≫ biprod.snd = 𝟙 (formalShift U 1)
    rw [assoc, e.inv_hom_id_assoc]
    exact biprod.inr_snd (X := U) (Y := formalShift U 1)
  have htotal : r₀ ≫ i₀ + r₁ ≫ i₁ = 𝟙 A := by
    change (e.hom ≫ biprod.fst) ≫ (biprod.inl ≫ e.inv) +
      (e.hom ≫ biprod.snd) ≫ (biprod.inr ≫ e.inv) = 𝟙 A
    calc
      _ = e.hom ≫ (biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr) ≫ e.inv := by
        simp only [comp_add,add_comp,assoc]
      _ = 𝟙 A := by rw [biprod.total,id_comp,e.hom_inv_id]
  let δ : F.obj A ⟶ A := F.map r₀ ≫ i₁
  let γ : A ⟶ F.obj A := r₁ ≫ F.map i₀
  have hδγ : δ ≫ γ = F.map (r₀ ≫ i₀) := by
    dsimp only [δ,γ]
    rw [assoc,← assoc i₁ r₁,h₁,id_comp,← F.map_comp]
  have hγδ : γ ≫ δ = r₁ ≫ i₁ := by
    dsimp only [δ,γ]
    rw [assoc,← assoc (F.map i₀) (F.map r₀),← F.map_comp,h₀,F.map_id,id_comp]
  have hreg : δ ≫ γ ≫ δ = δ := by
    rw [← assoc,hδγ]
    dsimp only [δ]
    rw [F.map_comp,assoc,← assoc (F.map i₀) (F.map r₀),← F.map_comp,h₀,F.map_id,id_comp]
  obtain ⟨Z,g,h,hT⟩ := distinguished_cocone_triangle δ.f
  let T := Triangle.mk δ.f g h
  have hu : T.mor₁ ≫ γ.f ≫ T.mor₁ = T.mor₁ := congrArg Karoubi.Hom.f hreg
  have hq : formalCokernel T γ.f hu = retractProjector i₀ r₀ h₀ := by
    refine Karoubi.ext (P := formalCokernel T γ.f hu)
      (Q := retractProjector i₀ r₀ h₀) rfl ?_
    change (𝟙 A.X - γ.f ≫ δ.f) ≫ 𝟙 A.X = 𝟙 A.X ≫ (r₀.f ≫ i₀.f)
    rw [comp_id,id_comp]
    have he : 𝟙 A - γ ≫ δ = r₀ ≫ i₀ := by rw [hγδ,← htotal]; abel
    have he' := congrArg (Karoubi.inclusionHom A A) he
    rw [map_sub] at he'
    exact he'
  have h₁' : F.map (F.map i₁) ≫ F.map (F.map r₁) = 𝟙 (F.obj (F.obj P)) := by
    rw [← F.map_comp,← F.map_comp,h₁,F.map_id,F.map_id]
  have hp : formalKernel T γ.f hu =
      retractProjector (F.map (F.map i₁)) (F.map (F.map r₁)) h₁' := by
    refine Karoubi.ext (P := formalKernel T γ.f hu)
      (Q := retractProjector (F.map (F.map i₁)) (F.map (F.map r₁)) h₁') rfl ?_
    change (𝟙 (F.obj A).X - δ.f ≫ γ.f)⟦(1 : ℤ)⟧' ≫ 𝟙 _ =
      𝟙 _ ≫ ((F.map (F.map r₁)).f ≫ (F.map (F.map i₁)).f)
    rw [comp_id,id_comp]
    have he : 𝟙 (F.obj A) - δ ≫ γ = F.map (r₁ ≫ i₁) := by
      rw [hδγ,← F.map_id,← F.map_sub]
      congr 1
      rw [← htotal]
      abel
    have hA : (F.obj A).p = 𝟙 (F.obj A).X := (shiftFunctor C (1 : ℤ)).map_id S
    have he' := congrArg (Karoubi.inclusionHom (F.obj A) (F.obj A)) he
    rw [map_sub] at he'
    change (F.obj A).p - δ.f ≫ γ.f = (F.map (r₁ ≫ i₁)).f at he'
    rw [hA] at he'
    rw [he']
    change (shiftFunctor C (1 : ℤ)).map ((shiftFunctor C (1 : ℤ)).map (r₁.f ≫ i₁.f)) = _
    simp only [Functor.map_comp]
    rfl
  obtain ⟨econe⟩ := regular_cone_iso T γ.f hu hT
  rw [hq,hp] at econe
  refine ⟨Z,⟨econe ≪≫ biprod.mapIso (retractProjectorIso i₀ r₀ h₀)
    (retractProjectorIso (F.map (F.map i₁)) (F.map (F.map r₁)) h₁')⟩⟩

noncomputable def formalIso {P Q : Karoubi C} (e : P.X ≅ Q.X)
    (he : P.p ≫ e.hom = e.hom ≫ Q.p) : P ≅ Q := by
  have hi : Q.p ≫ e.inv = e.inv ≫ P.p := by
    apply (cancel_epi e.hom).mp
    rw [← assoc,← he,assoc,e.hom_inv_id,comp_id,e.hom_inv_id_assoc]
  exact
    { hom := ⟨P.p ≫ e.hom,by
        simp only [assoc,reassoc_of% he,he,Q.idem]⟩
      inv := ⟨Q.p ≫ e.inv,by
        simp only [assoc,reassoc_of% hi,hi,P.idem]⟩
      hom_inv_id := by
        apply Karoubi.hom_ext
        change (P.p ≫ e.hom) ≫ (Q.p ≫ e.inv) = P.p
        rw [assoc,hi,← assoc e.hom e.inv,e.hom_inv_id,id_comp,P.idem]
      inv_hom_id := by
        apply Karoubi.hom_ext
        change (Q.p ≫ e.inv) ≫ (P.p ≫ e.hom) = Q.p
        rw [assoc,he,← assoc e.inv e.hom,e.inv_hom_id,id_comp,Q.idem] }

noncomputable def formalShiftAdd (P : Karoubi C) (n m : ℤ) :
    formalShift (formalShift P n) m ≅ formalShift P (n+m) :=
  formalIso ((shiftFunctorAdd C n m).app P.X).symm
    ((shiftFunctorAdd C n m).inv.naturality P.p)

/-- Both odd doubles in the manuscript are represented by actual objects. -/
theorem odd_double_three (U : Karoubi C) :
    ∃ Z : C, Nonempty ((toKaroubi C).obj Z ≅ U ⊞ formalShift U 3) := by
  obtain ⟨Z,⟨e⟩⟩ := odd_double_three_nested U
  exact ⟨Z,⟨e ≪≫ biprod.mapIso (Iso.refl U)
    (formalShiftAdd (formalShift U 1) 1 1 ≪≫ formalShiftAdd U 1 2)⟩⟩
end LittleFinitistic.OddDouble

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_FormalSummandAction
attribute [-instance] _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open CategoryTheory CategoryTheory.Category CategoryTheory.Preadditive
open CategoryTheory.Idempotents CategoryTheory.Limits

namespace LittleFinitistic.FormalSummandAction

universe u v w
variable {k : Type w} [CommRing k]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]

instance karoubiHomSMul (P Q : Karoubi C) : SMul k (P ⟶ Q) where
  smul r f := ⟨r • f.f, by rw [Linear.smul_comp,Linear.comp_smul,f.comm]⟩

@[simp] theorem smul_f (P Q : Karoubi C) (r : k) (f : P ⟶ Q) :
    (r • f).f = r • f.f := rfl

instance karoubiHomModule (P Q : Karoubi C) : Module k (P ⟶ Q) :=
  Function.Injective.module k (Karoubi.inclusionHom P Q)
    (fun _ _ h => Karoubi.hom_ext _ _ h) (fun _ _ => rfl)

instance karoubiLinear : Linear k (Karoubi C) where
  smul_comp _ _ _ _ _ _ := by apply Karoubi.hom_ext; exact Linear.smul_comp _ _ _ _ _ _
  comp_smul _ _ _ _ _ _ := by apply Karoubi.hom_ext; exact Linear.comp_smul _ _ _ _ _ _

variable {R : Type*} [Ring R] [Algebra k R]
variable {L : C} (θ : R →ₐ[k] End L) (e : R) (he : e * e = e)

/-- The formal image of the central selecting idempotent. -/
def summand : Karoubi C :=
  ⟨L,θ e,by change θ e * θ e = θ e; rw [← map_mul,he]⟩

variable (hc : ∀ r : R, e * r = r * e)

include he hc in
lemma sandwich (r : R) : e * r * e = e * r := by
  calc
    e * r * e = e * e * r := by rw [mul_assoc,← hc r,← mul_assoc]
    _ = e * r := by rw [he]

include he hc in
lemma compressed_mul (r s : R) : (e*r)*(e*s) = e*(r*s) := by
  rw [← mul_assoc,sandwich e he hc,mul_assoc]

/-- The action on the formal summand, with restriction along alpha. -/
def action (α : R →ₐ[k] R) : R →ₐ[k] End (summand θ e he) where
  toFun r := ⟨θ (e * α r),by
    change θ e ≫ θ (e * α r) ≫ θ e = θ (e * α r)
    change (θ e * θ (e * α r)) * θ e = θ (e * α r)
    rw [← map_mul,← map_mul]
    congr 1
    rw [← mul_assoc e e,he,sandwich e he hc]⟩
  map_one' := by apply Karoubi.hom_ext; change θ (e * α 1) = θ e; rw [map_one,mul_one]
  map_mul' r s := by
    apply Karoubi.hom_ext
    change θ (e * α (r*s)) = θ (e * α r) * θ (e * α s)
    rw [← map_mul θ,map_mul α,compressed_mul e he hc]
  map_zero' := by apply Karoubi.hom_ext; change θ (e * α 0) = 0; simp
  map_add' r s := by apply Karoubi.hom_ext; change θ (e * α (r+s)) = θ (e * α r) + θ (e * α s); simp [mul_add]
  commutes' r := by
    apply Karoubi.hom_ext
    change θ (e * α (algebraMap k R r)) = (algebraMap k (End (summand θ e he)) r).f
    rw [α.commutes]
    change θ (e * algebraMap k R r) = (r • (𝟙 (summand θ e he))).f
    rw [smul_f]
    change θ (e * algebraMap k R r) = r • θ e
    rw [hc,Algebra.algebraMap_eq_smul_one,smul_mul_assoc,one_mul,map_smul]

@[simp] theorem action_f (α : R →ₐ[k] R) (r : R) :
    ((action θ e he hc α r) : End (summand θ e he)).f = θ (e * α r * e) := by
  rw [sandwich e he hc]
  rfl

variable {D : Type*} [Category D] [Preadditive D] [Linear k D]

/-- A linear functor transports an algebra action on endomorphisms. -/
def mapAction (F : C ⥤ D) [F.Additive] [F.Linear k] {X : C}
    (ρ : R →ₐ[k] End X) : R →ₐ[k] End (F.obj X) where
  toFun r := F.map (ρ r)
  map_one' := by simp
  map_mul' r s := by simp [End.mul_def]
  map_zero' := by simp
  map_add' r s := by rw [map_add]; exact F.map_add
  commutes' r := by
    rw [ρ.commutes]
    change F.map (r • (𝟙 X)) = r • (𝟙 (F.obj X))
    rw [Functor.map_smul,F.map_id]

/-- Direct sum of two actions of the same algebra. -/
noncomputable def biprodAction [HasBinaryBiproducts C] {X Y : C}
    (ρ : R →ₐ[k] End X) (σ : R →ₐ[k] End Y) : R →ₐ[k] End (X ⊞ Y) where
  toFun r := biprod.map (ρ r) (σ r)
  map_one' := by apply biprod.hom_ext <;> simp
  map_mul' r s := by apply biprod.hom_ext <;> simp [End.mul_def]
  map_zero' := by apply biprod.hom_ext <;> simp
  map_add' r s := by
    rw [map_add,map_add]
    change biprod.map ((ρ r : X ⟶ X) + (ρ s : X ⟶ X))
      ((σ r : Y ⟶ Y) + (σ s : Y ⟶ Y)) =
      (biprod.map (ρ r) (σ r) : X ⊞ Y ⟶ X ⊞ Y) + biprod.map (ρ s) (σ s)
    apply biprod.hom_ext <;> simp only [biprod.map_fst,biprod.map_snd,
      Preadditive.add_comp]
    all_goals exact Preadditive.comp_add _ _ _ _ _ _
  commutes' r := by
    rw [ρ.commutes,σ.commutes]
    change biprod.map (r • (𝟙 X)) (r • (𝟙 Y)) = r • (𝟙 (X ⊞ Y))
    apply biprod.hom_ext <;> simp

/-- Conjugating an action along an isomorphism. -/
def transportAction {X Y : C} (i : X ≅ Y) (ρ : R →ₐ[k] End Y) :
    R →ₐ[k] End X where
  toFun r := i.hom ≫ ρ r ≫ i.inv
  map_one' := by simp
  map_mul' r s := by simp [End.mul_def]
  map_zero' := by simp
  map_add' r s := by
    rw [map_add]
    change i.hom ≫ ((ρ r : Y ⟶ Y) + (ρ s : Y ⟶ Y)) ≫ i.inv = _
    rw [add_comp,comp_add]
  commutes' r := by
    rw [ρ.commutes]
    change i.hom ≫ (r • (𝟙 Y)) ≫ i.inv = r • (𝟙 X)
    simp

/-- An action on an old object in the completion is an actual old action. -/
def oldAction {X : C} (ρ : R →ₐ[k] End ((toKaroubi C).obj X)) :
    R →ₐ[k] End X where
  toFun r := (ρ r).f
  map_one' := by rw [map_one]; rfl
  map_mul' r s := by rw [map_mul]; rfl
  map_zero' := by rw [map_zero]; rfl
  map_add' r s := by rw [map_add]; rfl
  commutes' r := by rw [ρ.commutes]; rfl

@[simp] theorem oldAction_lift {X : C} (ρ : R →ₐ[k] End ((toKaroubi C).obj X))
    (r : R) : (toKaroubi C).map (oldAction ρ r) = ρ r := by
  apply Karoubi.hom_ext
  rfl

variable [HasShift C ℤ] [HasZeroObject C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [∀ n : ℤ, (shiftFunctor C n).Linear k]

instance formalShiftLinear (n : ℤ) :
    (OddDouble.formalShiftFunctor (C := C) n).Linear k where
  map_smul := by
    intro X Y f r
    apply Karoubi.hom_ext
    exact Functor.map_smul (shiftFunctor C n) r f.f

local instance instHasFiniteBiproductsKaroubi_solutions : HasFiniteBiproducts (Karoubi C) := Karoubi.karoubi_hasFiniteBiproducts
local instance instHasBinaryBiproductsKaroubi_solutions : HasBinaryBiproducts (Karoubi C) :=
  hasBinaryBiproducts_of_finite_biproducts (Karoubi C)

/-- The selecting action on the odd double. -/
noncomputable def oddDoubleAction (α : R →ₐ[k] R) :
    R →ₐ[k] End (summand θ e he ⊞ OddDouble.formalShift (summand θ e he) 3) :=
  biprodAction (action θ e he hc α)
    (mapAction (OddDouble.formalShiftFunctor 3) (action θ e he hc α))

/-- The object and its unital action are both chosen before any evaluation module. -/
theorem fixed_old_object_with_action (α : R →ₐ[k] R) :
    ∃ (V₀ : C) (ρ₀ : R →ₐ[k] End V₀)
      (i : (toKaroubi C).obj V₀ ≅
        summand θ e he ⊞ OddDouble.formalShift (summand θ e he) 3),
      ∀ r : R, (toKaroubi C).map (ρ₀ r) ≫ i.hom =
        i.hom ≫ oddDoubleAction θ e he hc α r := by
  obtain ⟨V₀,⟨i⟩⟩ := OddDouble.odd_double_three (summand θ e he)
  let σ := oddDoubleAction θ e he hc α
  let τ := transportAction i σ
  refine ⟨V₀,oldAction τ,i,?_⟩
  intro r
  rw [oldAction_lift]
  change (i.hom ≫ σ r ≫ i.inv) ≫ i.hom = i.hom ≫ σ r
  simp

end LittleFinitistic.FormalSummandAction

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_FixedDiagram
attribute [-instance] _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LittleFinitistic.FixedDiagram
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits CategoryTheory.Idempotents
open FormalSummandAction

variable {k R : Type*} [CommRing k] [Ring R] [Algebra k R]
variable {C Q : Type*} [Category C] [Category Q] [Preadditive C] [Preadditive Q]
  [Linear k C] [Linear k Q]

/-- Algebra relations are the homogeneous quadratic diagram relations under any action. -/
theorem action_relations {X : Q} (ρ : R →ₐ[k] End X) (na nb nr : ℕ)
    (x : Fin na → R) (y : Fin nb → R) (c : Fin nr → Fin na → Fin nb → k)
    (hc : ∀ t, ∑ a, ∑ b, c t a b • (y b * x a) = 0) :
    ∀ t, ∑ a, ∑ b, c t a b • ((ρ (x a) : X ⟶ X) ≫ ρ (y b)) = 0 := by
  intro t
  have h := congrArg ρ (hc t)
  simpa only [map_sum,map_smul,map_mul,map_zero,End.mul_def] using h

variable (q : C ⥤ Q) (W : MorphismProperty C) [q.IsLocalization W]
  [W.HasRightCalculusOfFractions] [q.Additive] [q.Linear k]
variable [HasShift Q ℤ] [HasZeroObject Q]
  [∀ n : ℤ, (shiftFunctor Q n).Additive] [Pretriangulated Q]
  [∀ n : ℤ, (shiftFunctor Q n).Linear k]
local instance instHasFiniteBiproductsKaroubi_solutions : HasFiniteBiproducts (Karoubi Q) := Karoubi.karoubi_hasFiniteBiproducts
local instance instHasBinaryBiproductsKaroubi_solutions : HasBinaryBiproducts (Karoubi Q) :=
  hasBinaryBiproducts_of_finite_biproducts (Karoubi Q)

include W in
/-- Fixed source-category objects and arrows, with every quadratic relation exact,
represent the odd double of the selecting action in the localization. -/
theorem fixed_diagram {L : Q} (θ : R →ₐ[k] End L)
    (e : R) (he : e*e=e) (hec : ∀ r : R, e*r=r*e) (α : R →ₐ[k] R)
    (na nb nr : ℕ) (x : Fin na → R) (y : Fin nb → R)
    (c : Fin nr → Fin na → Fin nb → k)
    (hc : ∀ t, ∑ a, ∑ b, c t a b • (y b * x a) = 0) :
    ∃ (V₀ : Q) (ρ₀ : R →ₐ[k] End V₀)
      (i : (toKaroubi Q).obj V₀ ≅
        summand θ e he ⊞ OddDouble.formalShift (summand θ e he) 3)
      (D₀ D₁ D₂ : C) (φ₀ : q.obj D₀ ≅ V₀) (φ₁ : q.obj D₁ ≅ V₀)
      (φ₂ : q.obj D₂ ≅ V₀) (f : Fin na → (D₀ ⟶ D₁)) (g : Fin nb → (D₁ ⟶ D₂)),
      (∀ r : R, (toKaroubi Q).map (ρ₀ r) ≫ i.hom =
        i.hom ≫ oddDoubleAction θ e he hec α r) ∧
      (∀ a, q.map (f a) ≫ φ₁.hom = φ₀.hom ≫ ρ₀ (x a)) ∧
      (∀ b, q.map (g b) ≫ φ₂.hom = φ₁.hom ≫ ρ₀ (y b)) ∧
      (∀ t, ∑ a, ∑ b, c t a b • (f a ≫ g b) = 0) := by
  obtain ⟨V₀,ρ₀,i,hi⟩ := fixed_old_object_with_action θ e he hec α
  obtain ⟨D₀,D₁,D₂,φ₀,φ₁,φ₂,f,g,hf,hg,hrel⟩ :=
    DiagramLifting.finite_quadratic_diagram_lifting q W na nb nr V₀ V₀ V₀
      (fun a => ρ₀ (x a)) (fun b => ρ₀ (y b)) c (action_relations ρ₀ na nb nr x y c hc)
  exact ⟨V₀,ρ₀,i,D₀,D₁,D₂,φ₀,φ₁,φ₂,f,g,hi,hf,hg,hrel⟩
end LittleFinitistic.FixedDiagram

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_ProjectiveComplexes
attribute [-instance] _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory Limits
namespace LittleFinitistic.ProjectiveComplexes
universe u
variable (B : Type u) [Ring B]

/-- Right B-modules are left modules over the opposite ring. -/
abbrev RightModule := ModuleCat.{u} Bᵐᵒᵖ

def finiteProjective : ObjectProperty (RightModule B) :=
  fun M => Module.Finite Bᵐᵒᵖ M ∧ Module.Projective Bᵐᵒᵖ M

instance instIsClosedUnderIsomorphismsRightModuleFiniteProjective : (finiteProjective B).IsClosedUnderIsomorphisms where
  of_iso e h := by
    let := h.1
    let := h.2
    exact ⟨Module.Finite.equiv e.toLinearEquiv,
      Module.Projective.of_equiv e.toLinearEquiv⟩

instance instContainsZeroRightModuleFiniteProjective : (finiteProjective B).ContainsZero where
  exists_zero := ⟨ModuleCat.of Bᵐᵒᵖ PUnit, ModuleCat.isZero_of_subsingleton _,
    by constructor <;> infer_instance⟩

instance instIsClosedUnderBinaryProductsRightModuleFiniteProjective : (finiteProjective B).IsClosedUnderBinaryProducts where
  limitsOfShape_le := by
    rintro X ⟨p⟩
    let M := p.diag.obj (.mk .left)
    let N := p.diag.obj (.mk .right)
    have hM := p.prop_diag_obj (.mk .left)
    have hN := p.prop_diag_obj (.mk .right)
    let := hM.1
    let := hM.2
    let := hN.1
    let := hN.2
    have hp : finiteProjective B (ModuleCat.of Bᵐᵒᵖ (M × N)) :=
      ⟨inferInstance, inferInstance⟩
    apply (finiteProjective B).prop_of_iso _ hp
    exact IsLimit.conePointUniqueUpToIso (ModuleCat.binaryProductLimitCone M N).isLimit
      ((IsLimit.postcomposeHomEquiv (diagramIsoPair p.diag) _).2 p.isLimit)

instance instIsClosedUnderFiniteProductsRightModuleFiniteProjective : (finiteProjective B).IsClosedUnderFiniteProducts := .mk'

/-- The additive category of finitely generated projective right B-modules. -/
abbrev Proj := (finiteProjective B).FullSubcategory

instance instHasBinaryBiproductsProj : HasBinaryBiproducts (Proj B) := .of_hasBinaryProducts

/-- Section 3's K = Kᵇ(proj-B), with homotopy classes of chain maps. -/
abbrev K := BoundedHomotopy.K (Proj B)

end LittleFinitistic.ProjectiveComplexes

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_SingleDegreeNaturality
attribute [-instance] _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.DerivedTruncation
open DerivedCategory
universe u v w
variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
variable (n : ℤ)

variable (X : DerivedCategory C) [X.IsGE n] [X.IsLE n]

def cohomologyAutomorphism : (homologyFunctor C n).obj X ≅ (homologyFunctor C n).obj X :=
  (homologyFunctor C n).mapIso (singleIso X n) ≪≫
    (singleFunctorCompHomologyFunctorIso C n).app ((homologyFunctor C n).obj X)

/-- Normalize a single-degree identification to induce the identity on its actual cohomology. -/
def canonicalIso : X ≅ (singleFunctor C n).obj ((homologyFunctor C n).obj X) :=
  singleIso X n ≪≫ (singleFunctor C n).mapIso (cohomologyAutomorphism n X).symm

end LittleFinitistic.DerivedTruncation

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_TensorEvaluationComparison
attribute [-instance] _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.BalancedTensor
universe u v w z
variable {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A]
variable (M : Type w) [AddCommGroup M] [Module k M] [Module Aᵐᵒᵖ M]
  [IsScalarTower k Aᵐᵒᵖ M]
variable (N : Type z) [AddCommGroup N] [Module k N] [Module A N]

def fromScalarModule : ScalarModule k A (ModuleCat.of Aᵐᵒᵖ M) →ₗ[Aᵐᵒᵖ] M where
  toFun m := m
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def toScalarModule : M →ₗ[Aᵐᵒᵖ] ScalarModule k A (ModuleCat.of Aᵐᵒᵖ M) where
  toFun m := m
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end LittleFinitistic.BalancedTensor

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Localization_TwoConeVerdier
attribute [-instance] _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory Limits Pretriangulated Category
namespace LittleFinitistic.TwoConeVerdier

variable {C : Type*} [Category* C] [HasZeroObject C] [Preadditive C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C]

/-- Two specified cone triangles, with the first maps the denominators to invert. -/
structure ConePair (C : Type*) [Category* C] [HasShift C ℤ] [Preadditive C]
    [HasZeroObject C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] where
  first : Triangle C
  second : Triangle C
  first_distinguished : first ∈ distTriang C
  second_distinguished : second ∈ distTriang C

namespace ConePair
variable (T : ConePair C)

/-- Only the two cone objects are generators. -/
def generators : ObjectProperty C := fun X => X = T.first.obj₃ ∨ X = T.second.obj₃
instance instNonemptyGenerators : T.generators.Nonempty := ⟨T.first.obj₃, Or.inl rfl⟩

/-- The least thick subcategory containing these two cones. -/
abbrev S : ObjectProperty C := T.generators.triangEnvelope

/-- Exactly the maps whose cone lies in S. -/
abbrev Sigma : MorphismProperty C := T.S.trW

/-- The Verdier localization at the cone class. -/
abbrev Q := T.Sigma.Localization
abbrev q : C ⥤ T.Q := T.Sigma.Q

end ConePair
end LittleFinitistic.TwoConeVerdier

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryTensorRightRestriction
attribute [-instance] _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace LittleFinitistic.TwoSidedTensor
universe u
variable (k A B S M N : Type u) [Field k] [Ring A] [Ring B] [Ring S]
  [Algebra k A] [Algebra k B] [Algebra k S]
variable [AddCommGroup M] [Module k M] [Module Aᵐᵒᵖ M] [IsScalarTower k Aᵐᵒᵖ M]
  [Module S M] [IsScalarTower k S M] [SMulCommClass S Aᵐᵒᵖ M]
variable [AddCommGroup N] [Module k N] [Module A N] [Module Bᵐᵒᵖ N]
  [IsScalarTower k A N] [IsScalarTower k Bᵐᵒᵖ N] [SMulCommClass A Bᵐᵒᵖ N]

local instance instSMulCommClassMulOpposite : SMulCommClass Bᵐᵒᵖ A N := ⟨fun b a n => (smul_comm a b n).symm⟩

end LittleFinitistic.TwoSidedTensor

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryBimoduleAssociativity
attribute [-instance] _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace LittleFinitistic.BimoduleAssociativity
universe u
variable (k S A B M N Z : Type u) [Field k] [Ring S] [Ring A] [Ring B]
  [Algebra k S] [Algebra k A] [Algebra k B]
variable [AddCommGroup M] [Module k M] [Module S M] [Module Aᵐᵒᵖ M]
  [IsScalarTower k S M] [IsScalarTower k Aᵐᵒᵖ M] [SMulCommClass S Aᵐᵒᵖ M]
variable [AddCommGroup N] [Module k N] [Module A N] [Module Bᵐᵒᵖ N]
  [IsScalarTower k A N] [IsScalarTower k Bᵐᵒᵖ N] [SMulCommClass A Bᵐᵒᵖ N]
variable [AddCommGroup Z] [Module k Z] [Module B Z] [IsScalarTower k B Z]
local instance instSMulCommClassMulOpposite_solutions : SMulCommClass Bᵐᵒᵖ A N := ⟨fun b a n => (smul_comm a b n).symm⟩

end LittleFinitistic.BimoduleAssociativity

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryBimoduleAssociativeTerms
attribute [-instance] _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear
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
local instance instSMulCommClassMulOpposite_solutions : SMulCommClass Bᵐᵒᵖ A N := ⟨fun b a n => (smul_comm a b n).symm⟩

end LittleFinitistic.BimoduleComplexTensor

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryBimoduleCoefficientEquiv
attribute [-instance] _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace LittleFinitistic.BimoduleCoefficients
universe u
variable (k S A : Type u) [Field k] [Ring S] [Ring A] [Algebra k S] [Algebra k A]
variable {M N : ModuleCat.{u} (S ⊗[k] Aᵐᵒᵖ)}

def equiv (e : M ≅ N) : BimoduleCoefficients k S A M ≃ₗ[Aᵐᵒᵖ] BimoduleCoefficients k S A N where
  __ := map k S A e.hom
  invFun := map k S A e.inv
  left_inv x := congrArg (fun h => h.hom x) e.hom_inv_id
  right_inv x := congrArg (fun h => h.hom x) e.inv_hom_id

theorem equiv_left (e : M ≅ N) (s : S) (x : BimoduleCoefficients k S A M) :
    equiv k S A e (s • x) = s • equiv k S A e x := map_left k S A e.hom s x
end LittleFinitistic.BimoduleCoefficients

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryBimoduleTotalAssociativity
attribute [-instance] _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear
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
local instance instSMulCommClassMulOpposite_solutions_1 : SMulCommClass Bᵐᵒᵖ A N := ⟨fun b a n => (smul_comm a b n).symm⟩
end LittleFinitistic.BimoduleComplexTensor

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryBlockModules
attribute [-instance] _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
namespace LittleFinitistic.BlockModule
universe u
/-- A module supported on the first factor of the actual product algebra. -/
def First (_k _L _R Z : Type u) := Z
/-- A module supported on the second factor of the actual product algebra. -/
def Second (_k _L _R Z : Type u) := Z
variable (k L R Z : Type u) [Field k] [Ring L] [Ring R] [Algebra k L] [Algebra k R]
  [AddCommGroup Z] [Module k Z]
namespace First
instance instAddCommGroup : AddCommGroup (First k L R Z) := inferInstanceAs (AddCommGroup Z)
instance instModule : Module k (First k L R Z) := inferInstanceAs (Module k Z)
instance instModuleProd [Module L Z] : Module (L × R) (First k L R Z) := Module.compHom Z (RingHom.fst L R)
instance instIsScalarTowerProd [Module L Z] [IsScalarTower k L Z] : IsScalarTower k (L × R) (First k L R Z) where
  smul_assoc c d z := smul_assoc c d.1 (show Z from z)
end First
namespace Second
instance instAddCommGroup : AddCommGroup (Second k L R Z) := inferInstanceAs (AddCommGroup Z)
instance instModule : Module k (Second k L R Z) := inferInstanceAs (Module k Z)
instance instModuleProd [Module R Z] : Module (L × R) (Second k L R Z) := Module.compHom Z (RingHom.snd L R)
instance instIsScalarTowerProd [Module R Z] [IsScalarTower k R Z] : IsScalarTower k (L × R) (Second k L R Z) where
  smul_assoc c d z := smul_assoc c d.2 (show Z from z)
end Second
end LittleFinitistic.BlockModule

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryProductComponent
attribute [-instance] _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.ProductModules
universe u v
variable (L R : Type u) [Ring L] [Ring R]
variable (M : ModuleCat.{v} (L × R))

/-- The actual first central-idempotent summand of an arbitrary product-ring module. -/
def firstSpace : Submodule (L × R) M where
  carrier := {m | ((1,0) : L × R) • m = m}
  zero_mem' := smul_zero _
  add_mem' {x y} hx hy := by
    change ((1,0) : L × R) • (x+y) = x+y
    rw [smul_add,hx,hy]
  smul_mem' d x hx := by
    change ((1,0) : L × R) • (d • x) = d • x
    have he : ((1,0) : L × R) * d = d * (1,0) := by ext <;> simp
    rw [← mul_smul,he,mul_smul,hx]

def firstScalar (r : L) : firstSpace L R M →ₗ[ℤ] firstSpace L R M where
  toFun x := ⟨(r,(0:R)) • x.val, by
    change ((1,0) : L × R) • ((r,(0:R)) • x.val) = (r,(0:R)) • x.val
    rw [← mul_smul]
    have h : ((1,0) : L × R) * (r,(0:R)) = (r,(0:R)) := by ext <;> simp
    rw [h]⟩
  map_add' x y := Subtype.ext (smul_add _ _ _)
  map_smul' n x := by
    apply Subtype.ext
    exact smul_comm ((r,(0:R)) : L × R) n x.val

def firstAction : L →+* Module.End ℤ (firstSpace L R M) where
  toFun := firstScalar L R M
  map_one' := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change ((1,0) : L × R) • x.val = x.val
    exact x.property
  map_zero' := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change (0 : L × R) • x.val = 0
    exact zero_smul (L × R) x.val
  map_add' r s := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change ((r+s,(0:R)) : L × R) • x.val = (r,(0:R)) • x.val + (s,(0:R)) • x.val
    simpa only [Prod.mk_add_mk,add_zero] using add_smul ((r,(0:R)) : L × R) (s,(0:R)) x.val
  map_mul' r s := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change ((r*s,(0:R)) : L × R) • x.val = (r,(0:R)) • ((s,(0:R)) • x.val)
    rw [← mul_smul]
    have h : ((r,(0:R)) : L × R) * (s,0) = (r*s,0) := by ext <;> simp
    rw [h]

instance firstModule : Module L (firstSpace L R M) := Module.compHom _ (firstAction L R M)

abbrev firstObject : ModuleCat.{v} L := ModuleCat.of L (firstSpace L R M)

variable {M} {N : ModuleCat.{v} (L × R)}

def firstMap (f : M ⟶ N) : firstSpace L R M →ₗ[L] firstSpace L R N where
  toFun x := ⟨f.hom x.val, by
    change ((1,0) : L × R) • f.hom x.val = f.hom x.val
    rw [← f.hom.map_smul,x.property]⟩
  map_add' x y := Subtype.ext (f.hom.map_add _ _)
  map_smul' r x := Subtype.ext (f.hom.map_smul ((r,(0:R)) : L × R) x.val)

/-- The actual component functor, constructed on every module and map. -/
def firstFunctor : ModuleCat.{v} (L × R) ⥤ ModuleCat.{v} L where
  obj M := firstObject L R M
  map f := ModuleCat.ofHom (firstMap L R f)
  map_id M := by rfl
  map_comp f g := by rfl

end LittleFinitistic.ProductModules

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryProductProjective
attribute [-instance] _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.ProductModules
universe u v
variable (L R : Type u) [Ring L] [Ring R]

abbrev firstInflation : ModuleCat.{v} L ⥤ ModuleCat.{v} (L × R) :=
  ModuleCat.restrictScalars (RingHom.fst L R)

end LittleFinitistic.ProductModules

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryProductSplitting
attribute [-instance] _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.ProductModules
universe u v
variable (L R : Type u) [Ring L] [Ring R]

abbrev secondInflation : ModuleCat.{v} R ⥤ ModuleCat.{v} (L × R) :=
  ModuleCat.restrictScalars (RingHom.snd L R)

end LittleFinitistic.ProductModules

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryBlockComplexes
attribute [-instance] _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace LittleFinitistic.BlockModule
universe u
variable (k L R : Type u) [Field k] [Ring L] [Ring R] [Algebra k L] [Algebra k R]

abbrev firstComplex (Z : CochainComplex (ModuleCat.{u} L) ℤ) :=
  ((ProductModules.firstInflation L R).mapHomologicalComplex (.up ℤ)).obj Z
abbrev secondComplex (Z : CochainComplex (ModuleCat.{u} R) ℤ) :=
  ((ProductModules.secondInflation L R).mapHomologicalComplex (.up ℤ)).obj Z

variable {U V : Type u} [AddCommGroup U] [AddCommGroup V] [Module k U] [Module k V]

def firstMap [Module L U] [Module L V] (f : U →ₗ[L] V) : First k L R U →ₗ[L × R] First k L R V where
  __ := f.toAddHom
  map_smul' d x := f.map_smul d.1 x

def secondMap [Module R U] [Module R V] (f : U →ₗ[R] V) : Second k L R U →ₗ[L × R] Second k L R V where
  __ := f.toAddHom
  map_smul' d x := f.map_smul d.2 x
end LittleFinitistic.BlockModule

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryBlockDerived
attribute [-instance] _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.BlockModule
universe u
variable (L R : Type u) [Ring L] [Ring R]
variable [HasDerivedCategory.{u+1} (ModuleCat.{u} L)]
variable [HasDerivedCategory.{u+1} (ModuleCat.{u} (L × R))]

abbrev firstComplexFunctor := (ProductModules.firstInflation L R).mapHomologicalComplex (.up ℤ)

omit [HasDerivedCategory.{u+1} (ModuleCat.{u} L)] in
theorem first_inverts : (HomologicalComplex.quasiIso (ModuleCat.{u} L) (.up ℤ)).IsInvertedBy
    (firstComplexFunctor L R ⋙ DerivedCategory.Q) := by
  intro Z Z' f hf
  let : QuasiIso f := hf
  have : QuasiIso ((firstComplexFunctor L R).map f) :=
    (RestrictionHomology.quasiIso_iff (RingHom.fst L R) f).mpr inferInstance
  exact (inferInstance : IsIso (DerivedCategory.Q.map ((firstComplexFunctor L R).map f)))

/-- Native derived inflation on the first block of the product algebra. -/
def derivedFirst : DerivedCategory (ModuleCat.{u} L) ⥤ DerivedCategory (ModuleCat.{u} (L × R)) :=
  Localization.lift (firstComplexFunctor L R ⋙ DerivedCategory.Q) (first_inverts L R) DerivedCategory.Q

def derivedFirstComparison : DerivedCategory.Q ⋙ derivedFirst L R ≅ firstComplexFunctor L R ⋙ DerivedCategory.Q :=
  Localization.fac (firstComplexFunctor L R ⋙ DerivedCategory.Q) (first_inverts L R) DerivedCategory.Q
end LittleFinitistic.BlockModule

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryFinitePiSupport
attribute [-instance] _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
namespace LittleFinitistic.FinitePiSupport
universe u v w
variable {R : Type u} [Ring R] {ι : Type v} [DecidableEq ι]
variable (V : ι → Type w) [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
variable (i₀ : ι) (hV : ∀ i, i ≠ i₀ → Subsingleton (V i))

/-- A product with all but one coordinate zero is exactly its remaining coordinate. -/
def equivalence : (∀ i, V i) ≃ₗ[R] V i₀ :=
  LinearEquiv.ofBijective (LinearMap.proj i₀) ⟨by
    intro x y h
    funext i
    by_cases hi : i = i₀
    · subst i
      exact h
    · exact (hV i hi).elim _ _, by
    intro x
    refine ⟨fun i => if h : i = i₀ then h.symm ▸ x else 0, ?_⟩
    simp⟩

@[simp] theorem equivalence_apply (x : ∀ i, V i) : equivalence (R := R) V i₀ hV x = x i₀ := rfl
end LittleFinitistic.FinitePiSupport

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryFirstComponentExact
attribute [-instance] _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.ProductModules
universe u
variable (L R : Type u) [Ring L] [Ring R]

instance firstFunctor_additive : (firstFunctor.{u,u} L R).Additive where
  map_add := by intros; rfl

/-- Exactness on the first central-idempotent component follows by projecting a preimage. -/
theorem firstFunctor_mapsExact (K : ShortComplex (ModuleCat.{u} (L × R))) (hK : K.Exact) :
    (K.map (firstFunctor L R)).Exact := by
  rw [ShortComplex.moduleCat_exact_iff] at hK ⊢
  intro y hy
  obtain ⟨x,hx⟩ := hK y.val (congrArg Subtype.val hy)
  refine ⟨⟨((1,0) : L × R) • x,?_⟩,?_⟩
  · change ((1,0) : L × R) • (((1,0) : L × R) • x) = ((1,0) : L × R) • x
    rw [← mul_smul]
    have h : ((1,0) : L × R) * (1,0) = (1,0) := by ext <;> simp
    rw [h]
  · apply Subtype.ext
    change K.f.hom (((1,0) : L × R) • x) = y.val
    rw [K.f.hom.map_smul,hx,y.property]

instance firstFunctor_preservesHomology : (firstFunctor.{u,u} L R).PreservesHomology :=
  Functor.preservesHomology_of_map_exact _ (firstFunctor_mapsExact L R)

instance firstFunctor_preservesFiniteLimits : PreservesFiniteLimits (firstFunctor.{u,u} L R) :=
  Functor.preservesFiniteLimits_of_preservesHomology _

instance firstFunctor_preservesFiniteColimits : PreservesFiniteColimits (firstFunctor.{u,u} L R) :=
  Functor.preservesFiniteColimits_of_preservesHomology _

/-- Taking the first component of an inflated module recovers the original module. -/
def firstInflationComponentEquiv (M : ModuleCat.{u} L) :
    firstObject L R ((firstInflation L R).obj M) ≃ₗ[L] M where
  toFun x := x.val
  invFun x := ⟨x, one_smul L x⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- This recovery is natural in every module and linear map. -/
def firstInflationComponentIso : firstInflation.{u,u} L R ⋙ firstFunctor L R ≅ 𝟭 (ModuleCat.{u} L) :=
  NatIso.ofComponents (fun M => (firstInflationComponentEquiv L R M).toModuleIso)
    (by intros; rfl)
end LittleFinitistic.ProductModules

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryFirstDerivedCompatibility
attribute [-instance] _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.BlockModule
universe u
variable (L R : Type u) [Ring L] [Ring R]

/-- First-block inflation is exact for arbitrary, possibly noncommutative rings. -/
instance firstInflation_preservesFiniteLimits :
    PreservesFiniteLimits (ProductModules.firstInflation.{u,u} L R) := by
  let := RestrictionHomology.preservesHomology (RingHom.fst L R)
  exact Functor.preservesFiniteLimits_of_preservesHomology _

instance firstInflation_preservesFiniteColimits :
    PreservesFiniteColimits (ProductModules.firstInflation.{u,u} L R) := by
  let := RestrictionHomology.preservesHomology (RingHom.fst L R)
  exact Functor.preservesFiniteColimits_of_preservesHomology _

variable [HasDerivedCategory.{u+1} (ModuleCat.{u} L)]
variable [HasDerivedCategory.{u+1} (ModuleCat.{u} (L × R))]

instance derivedFirst_lifting : Localization.Lifting DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{u} L) (.up ℤ))
    (firstComplexFunctor L R ⋙ DerivedCategory.Q) (derivedFirst L R) :=
  ⟨derivedFirstComparison L R⟩

/-- The ordinary localization model is naturally the exact derived inflation. -/
def derivedFirstIso : derivedFirst L R ≅ (ProductModules.firstInflation L R).mapDerivedCategory :=
  Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{u} L) (.up ℤ))
    (firstComplexFunctor L R ⋙ DerivedCategory.Q)
    (firstComplexFunctor L R ⋙ DerivedCategory.Q)
    (derivedFirst L R) (ProductModules.firstInflation L R).mapDerivedCategory (Iso.refl _)

/-- The comparison agrees with both specified localization comparison maps. -/
@[reassoc (attr := simp)]
theorem derivedFirstIso_hom_app_Q (Z : CochainComplex (ModuleCat.{u} L) ℤ) :
    (derivedFirstIso L R).hom.app (DerivedCategory.Q.obj Z) ≫
      (ProductModules.firstInflation L R).mapDerivedCategoryFactors.hom.app Z =
    (derivedFirstComparison L R).hom.app Z := by
  simp only [derivedFirstIso, Localization.liftNatIso_hom,
    Localization.liftNatTrans_app, Iso.refl_hom, NatTrans.id_app, Category.id_comp]
  change ((derivedFirstComparison L R).hom.app Z ≫
    (ProductModules.firstInflation L R).mapDerivedCategoryFactors.inv.app Z) ≫
    (ProductModules.firstInflation L R).mapDerivedCategoryFactors.hom.app Z = _
  simp

/-- Transport the coherent integer shift structure of the exact derived functor. -/
instance derivedFirst_commShift : (derivedFirst L R).CommShift ℤ :=
  Functor.CommShift.ofIso (derivedFirstIso L R).symm ℤ

instance derivedFirstIso_inv_commShift : NatTrans.CommShift (derivedFirstIso L R).inv ℤ :=
  Functor.CommShift.ofIso_compatibility (derivedFirstIso L R).symm ℤ

instance derivedFirstIso_hom_commShift : NatTrans.CommShift (derivedFirstIso L R).hom ℤ := by
  let : NatTrans.CommShift (derivedFirstIso L R).symm.hom ℤ :=
    derivedFirstIso_inv_commShift L R
  exact NatTrans.CommShift.of_iso_inv (derivedFirstIso L R).symm ℤ

instance derivedFirst_isTriangulated : (derivedFirst L R).IsTriangulated :=
  Functor.isTriangulated_of_iso (derivedFirstIso L R).symm
end LittleFinitistic.BlockModule

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryFirstDerivedRetraction
attribute [-instance] _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.BlockModule
universe u
variable (L R : Type u) [Ring L] [Ring R]
variable [HasDerivedCategory.{u+1} (ModuleCat.{u} L)]
variable [HasDerivedCategory.{u+1} (ModuleCat.{u} (L × R))]

/-- The exact derived first-component functor on the whole product-ring derived category. -/
abbrev derivedFirstComponent := (ProductModules.firstFunctor.{u,u} L R).mapDerivedCategory

def firstComplexComponentIso : firstComplexFunctor L R ⋙
    (ProductModules.firstFunctor L R).mapHomologicalComplex (.up ℤ) ≅
      𝟭 (CochainComplex (ModuleCat.{u} L) ℤ) :=
  Functor.mapHomologicalComplexCompIso (ProductModules.firstInflationComponentIso L R) (.up ℤ) ≪≫
    Functor.mapHomologicalComplexIdIso (ModuleCat.{u} L) (.up ℤ)

/-- On chain representatives, the composite is the identity localization. -/
def derivedFirstComponentFactors : DerivedCategory.Q ⋙ derivedFirst L R ⋙
    derivedFirstComponent L R ≅ (DerivedCategory.Q : CochainComplex (ModuleCat.{u} L) ℤ ⥤ _) :=
  (Functor.associator ..).symm ≪≫
    Functor.isoWhiskerRight (derivedFirstComparison L R) _ ≪≫
    Functor.associator .. ≪≫
    Functor.isoWhiskerLeft _ (ProductModules.firstFunctor L R).mapDerivedCategoryFactors ≪≫
    (Functor.associator ..).symm ≪≫
    Functor.isoWhiskerRight (firstComplexComponentIso L R) _ ≪≫ Functor.leftUnitor _

/-- Taking the first component recovers every derived object, naturally. -/
def derivedFirstRetraction : derivedFirst L R ⋙ derivedFirstComponent L R ≅
    𝟭 (DerivedCategory (ModuleCat.{u} L)) := by
  letI : Localization.Lifting DerivedCategory.Q
      (HomologicalComplex.quasiIso (ModuleCat.{u} L) (.up ℤ)) DerivedCategory.Q
      (derivedFirst L R ⋙ derivedFirstComponent L R) := ⟨derivedFirstComponentFactors L R⟩
  exact Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{u} L) (.up ℤ))
    DerivedCategory.Q DerivedCategory.Q _ _ (Iso.refl _)

instance derivedFirst_additive : (derivedFirst L R).Additive :=
  Functor.additive_of_iso (derivedFirstIso L R).symm

end LittleFinitistic.BlockModule

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryRightProjective
attribute [-instance] _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
namespace LittleFinitistic.OrdinarySimulation
universe u v w

open CategoryTheory
variable {k B : Type u} [Field k] [Ring B] [Algebra k B]

/-- The actual underlying right-B complex of the genuine dg bimodule. -/
abbrev underlyingRightComplex (P : CochainComplex (ModuleCat.{u} (Enveloping k B)) ℤ) :
    CochainComplex (ModuleCat.{u} Bᵐᵒᵖ) ℤ :=
  ((ModuleCat.restrictScalars
    (Algebra.TensorProduct.includeRight (R := k) (A := B) (B := Bᵐᵒᵖ)).toRingHom).mapHomologicalComplex (.up ℤ)).obj P

end LittleFinitistic.OrdinarySimulation

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_BiprodEvaluationSquare
attribute [-instance] _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents
namespace LittleFinitistic.BiprodEvaluationSquare
universe u v w z
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]
variable {D : Type w} [Category.{z} D] [Preadditive D] [HasBinaryBiproducts D]
variable (F : C ⥤ D) [F.Additive] [PreservesBinaryBiproducts F]

/-- Transport both diagonal actions through additive evaluation and given summand isomorphisms. -/
theorem square {A B : C} {A' B' : D} (f : A ⟶ A) (g : B ⟶ B)
    (i : F.obj A ≅ A') (j : F.obj B ≅ B') (f' : A' ⟶ A') (g' : B' ⟶ B')
    (hf : F.map f ≫ i.hom = i.hom ≫ f') (hg : F.map g ≫ j.hom = j.hom ≫ g') :
    F.map (biprod.map f g) ≫ (F.mapBiprod A B ≪≫ biprod.mapIso i j).hom =
      (F.mapBiprod A B ≪≫ biprod.mapIso i j).hom ≫ biprod.map f' g' := by
  apply biprod.hom_ext
  · simp only [Iso.trans_hom,Functor.mapBiprod_hom,biprod.mapIso_hom,
      Category.assoc,biprod.map_fst,biprod.map_fst_assoc,biprod.lift_fst_assoc]
    rw [← Category.assoc,← Functor.map_comp,biprod.map_fst,Functor.map_comp,Category.assoc,hf]
  · simp only [Iso.trans_hom,Functor.mapBiprod_hom,biprod.mapIso_hom,
      Category.assoc,biprod.map_snd,biprod.map_snd_assoc,biprod.lift_snd_assoc]
    rw [← Category.assoc,← Functor.map_comp,biprod.map_snd,Functor.map_comp,Category.assoc,hg]

variable {k R : Type*} [CommRing k] [Ring R] [Algebra k R]
variable [Linear k C] [HasShift C ℤ] [HasZeroObject C]
  [∀ n : ℤ,(shiftFunctor C n).Additive] [Pretriangulated C]
  [∀ n : ℤ,(shiftFunctor C n).Linear k]
variable {L : C} (theta : R →ₐ[k] End L) (e : R) (he : e*e=e)
  (hc : ∀ r : R,e*r=r*e) (alpha : R →ₐ[k] R)
local instance instHasFiniteBiproductsKaroubi_solutions : HasFiniteBiproducts (Karoubi C) := Karoubi.karoubi_hasFiniteBiproducts
local instance instHasBinaryBiproductsKaroubi_solutions : HasBinaryBiproducts (Karoubi C) := hasBinaryBiproducts_of_finite_biproducts _

omit [HasBinaryBiproducts C] in
theorem action_formula (r : R) :
    FormalSummandAction.oddDoubleAction theta e he hc alpha r =
      biprod.map (FormalSummandAction.action theta e he hc alpha r)
        ((OddDouble.formalShiftFunctor 3).map (FormalSummandAction.action theta e he hc alpha r)) := rfl
end LittleFinitistic.BiprodEvaluationSquare

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_GradedVertexAcyclic
attribute [-instance] _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
namespace LittleFinitistic.GradedVertexAcyclic

theorem acyclic_of_iso {C : Type*} [Category C] [Abelian C]
    {X Y : CochainComplex C ℤ} (e : X ≅ Y) (hY : Y.Acyclic) : X.Acyclic := by
  intro n
  rw [exactAt_iff_isZero_homology]
  exact ((homologyFunctor C (.up ℤ) n).mapIso e).isZero_iff.mpr (hY n).isZero_homology

open ExternalTensor.Section4
universe u
end LittleFinitistic.GradedVertexAcyclic

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_LeftVertexHomology
attribute [-instance] _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory HomologicalComplex
namespace LittleFinitistic.LeftVertexHomology
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B]

lemma scalar_commute (e : B) (c : k) : e * algebraMap k B c = algebraMap k B c * e :=
  (Algebra.commutes c e).symm

end LittleFinitistic.LeftVertexHomology

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_TotalInterchange
attribute [-instance] _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option backward.isDefEq.respectTransparency false

namespace OAI
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open CochainComplex.HomComplex
noncomputable section
namespace LittleFinitistic.RectificationTotal
variable {C D : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C]
  [Category D] [Preadditive D] [HasBinaryBiproducts D]
variable (F : C ⥤ D) [F.Additive]

abbrev mapComplex := F.mapHomologicalComplex (ComplexShape.up ℤ)

variable {A B A' B' : CochainComplex C ℤ}

/-- The canonical additive comparison for one cone. -/
def coneInterchange (q : A ⟶ B) :
    (mapComplex F).obj (mappingCone q) ≅ mappingCone ((mapComplex F).map q) :=
  homotopyCofiber.mapHomologicalComplexObjIso q F

@[reassoc (attr := simp)]
theorem coneInterchange_inv_inl (q : A ⟶ B) (i j : ℤ) (hij : i + (-1) = j) :
    (mappingCone.inl ((mapComplex F).map q)).v i j hij ≫
      (coneInterchange F q).inv.f j = F.map ((mappingCone.inl q).v i j hij) := by
  exact homotopyCofiber.inlX_mapHomologicalComplexObjXIso_inv q F i j (by change j+1=i; omega)

@[reassoc (attr := simp)]
theorem coneInterchange_inv_inr (q : A ⟶ B) (i : ℤ) :
    (mappingCone.inr ((mapComplex F).map q)).f i ≫
      (coneInterchange F q).inv.f i = F.map ((mappingCone.inr q).f i) := by
  exact homotopyCofiber.inrX_mapHomologicalComplexObjXIso_inv q F i

@[reassoc (attr := simp)]
theorem coneInterchange_hom_inl (q : A ⟶ B) (i j : ℤ) (hij : i + (-1) = j) :
    F.map ((mappingCone.inl q).v i j hij) ≫ (coneInterchange F q).hom.f j =
      (mappingCone.inl ((mapComplex F).map q)).v i j hij := by
  rw [← coneInterchange_inv_inl F q i j hij, Category.assoc]
  rw [← comp_f, Iso.inv_hom_id, id_f, Category.comp_id]

@[reassoc (attr := simp)]
theorem coneInterchange_hom_inr (q : A ⟶ B) (i : ℤ) :
    F.map ((mappingCone.inr q).f i) ≫ (coneInterchange F q).hom.f i =
      (mappingCone.inr ((mapComplex F).map q)).f i := by
  rw [← coneInterchange_inv_inr F q i, Category.assoc]
  rw [← comp_f, Iso.inv_hom_id, id_f, Category.comp_id]

variable {L₀ L₁ L₂ : CochainComplex C ℤ}
variable (p : L₁ ⟶ L₀) (q : L₂ ⟶ L₁) (h : Homotopy (q ≫ p) 0)

/-- Apply the functor to the supplied null-homotopy, transporting only
functorial composition and zero equalities. -/
def mapNullHomotopy : Homotopy ((mapComplex F).map q ≫ (mapComplex F).map p) 0 :=
  (Homotopy.ofEq (by simp)).trans ((F.mapHomotopy h).trans (Homotopy.ofEq (by simp)))

omit [HasBinaryBiproducts C] [HasBinaryBiproducts D] in
@[simp] theorem mapNullHomotopy_hom (i j : ℤ) :
    (mapNullHomotopy F p q h).hom i j = F.map (h.hom i j) := by
  simp [mapNullHomotopy, Homotopy.trans, Homotopy.ofEq]

end LittleFinitistic.RectificationTotal

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Rectification_VertexProjectives
attribute [-instance] _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory Limits
namespace LittleFinitistic.VertexProjectives
universe u
variable {B : Type u} [Ring B]

/-- eB, represented in the opposite regular module to encode right linearity. -/
def ideal (e : B) : Submodule Bᵐᵒᵖ Bᵐᵒᵖ :=
  (LinearMap.mulRight Bᵐᵒᵖ (MulOpposite.op e)).range

theorem fixed (e : B) (he : e * e = e) (x : ideal e) :
    x.val * MulOpposite.op e = x.val := by
  obtain ⟨y,hy⟩ := x.property
  change y * MulOpposite.op e = x.val at hy
  rw [← hy, mul_assoc, ← MulOpposite.op_mul, he]

instance finite (e : B) : Module.Finite Bᵐᵒᵖ (ideal e) :=
  inferInstanceAs (Module.Finite Bᵐᵒᵖ (LinearMap.mulRight Bᵐᵒᵖ (MulOpposite.op e)).range)

theorem projective (e : B) (he : e * e = e) : Module.Projective Bᵐᵒᵖ (ideal e) := by
  apply Module.Projective.of_split (ideal e).subtype
    (LinearMap.mulRight Bᵐᵒᵖ (MulOpposite.op e)).rangeRestrict
  ext x
  exact fixed e he x

/-- The actual finitely generated projective right module eB. -/
def object (e : B) (he : e * e = e) : ProjectiveComplexes.Proj B :=
  ⟨ModuleCat.of Bᵐᵒᵖ (ideal e), finite e, projective e he⟩

/-- Left multiplication by an arrow a with target idempotent e'. -/
def arrow {e e' : B} (he : e * e = e) (he' : e' * e' = e')
    (a : B) (ha : e' * a = a) : object e he ⟶ object e' he' :=
  ObjectProperty.homMk (ModuleCat.ofHom
    (((LinearMap.mulRight Bᵐᵒᵖ (MulOpposite.op a)).comp (ideal e).subtype).codRestrict
      (ideal e') (fun x => ⟨x.val * MulOpposite.op a, by
        change (x.val * MulOpposite.op a) * MulOpposite.op e' = x.val * MulOpposite.op a
        rw [mul_assoc, ← MulOpposite.op_mul, ha]⟩)))

@[simp] theorem arrow_apply {e e' : B} (he : e * e = e) (he' : e' * e' = e')
    (a : B) (ha : e' * a = a) (x : ideal e) :
    ((arrow he he' a ha).hom.hom x).val = x.val * MulOpposite.op a := rfl

end LittleFinitistic.VertexProjectives

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Selection_FiniteQuotient
attribute [-instance] _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-!
Exact prerequisites for Section 2 of v5s9.15.

These are the variable-coefficient elementary-matrix calculations in the
finite-quotient construction, over the actual rings F₂[t]/(t^m - 1).
They do not establish the paper's main homological theorem.
-/

open Matrix Polynomial

namespace LittleFinitistic

noncomputable def cyclicPolynomial (m : ℕ) : Polynomial (ZMod 2) := X^m - C 1
abbrev CyclicRing (m : ℕ) := AdjoinRoot (cyclicPolynomial m)

end LittleFinitistic

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Selection_CharacterModule
attribute [-instance] _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open scoped BigOperators

namespace LittleFinitistic
namespace CharacterModule

open MonoidAlgebra

variable {H F : Type*} [Group H] [Group F] [Fintype H]
variable (ψ : H →* F) (χ : H →* ℂˣ)

/-- The unnormalized character projector. Its identity coefficient is one,
so normalization is unnecessary for constructing the nonzero test module. -/
noncomputable def projector : MonoidAlgebra ℂ F :=
  ∑ h : H, single (ψ h) ((χ h : ℂ)⁻¹)

variable (hc : ∀ h g, Commute (ψ h) g)

/-- All vectors on which the central subgroup acts by the selected character. -/
noncomputable def eigenspace : Submodule (MonoidAlgebra ℂ F) (MonoidAlgebra ℂ F) where
  carrier := {x | ∀ h, single (ψ h) (1 : ℂ) * x = (χ h : ℂ) • x}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb h
    simp [mul_add,ha h,hb h,smul_add]
  smul_mem' := by
    intro a x hx h
    change single (ψ h) (1 : ℂ) * (a*x) = (χ h : ℂ) • (a*x)
    rw [← mul_assoc, (MonoidAlgebra.single_commute (hc h) Commute.one_left a).eq,
      mul_assoc,hx h,mul_smul_comm]

omit [Fintype H] in
theorem eigenspace_finiteDimensional [Finite F] :
    FiniteDimensional ℂ (eigenspace ψ χ hc) := by
  have : FiniteDimensional ℂ (MonoidAlgebra ℂ F) :=
    Module.Finite.equiv (MonoidAlgebra.coeffLinearEquiv ℂ : MonoidAlgebra ℂ F ≃ₗ[ℂ] (F →₀ ℂ)).symm
  exact FiniteDimensional.of_injective ((eigenspace ψ χ hc).restrictScalars ℂ).subtype
    Subtype.val_injective

end CharacterModule
end LittleFinitistic

end OAI
end


