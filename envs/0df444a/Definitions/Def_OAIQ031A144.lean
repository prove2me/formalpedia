-- Prove2me | Definitions.Def_OAIQ031A144
-- name    : OAIQ031A144
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T15:21:51.484505+00:00
-- url     : https://prove2.me/theorems/f9813a34-670f-4e9a-8d61-d6c4538350d9
-- title:
--   Definitions bundle OAIQ031A144 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 15 declarations of OpenAI's Lean: 6 definitions, 1 instance and 8 theorems. The definitions and types are `OAI.ArExplicit.FiniteLeftModule.evaluatedResolutionFullEquiv`, `OAI.ArExplicit.FiniteLeftModule.evaluatedResolutionOut`, `OAI.ArExplicit.FiniteLeftModule.resolutionPairBicone`, `OAI.ArExplicit.FiniteLeftModule.resolutionPairBilimit`, `OAI.ArExplicit.FiniteLeftModule.resolutionPairIso`, `OAI.ArExplicit.T.sourceQuotientRestriction`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Bar_ModuleBarTwistExtAction`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/ModuleBarTwistExtAction.lean), [`AuslanderReiten_Coordinates_FiniteTensorComparison`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Coordinates/FiniteTensorComparison.lean), [`AuslanderReiten_Coordinates_FiniteTensorComparisonEquiv`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Coordinates/FiniteTensorComparisonEquiv.lean), [`AuslanderReiten_Resolutions_FiniteResolutionProduct`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Resolutions/FiniteResolutionProduct.lean), [`AuslanderReiten_Resolutions_FiniteResolutionProductInclusions`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Resolutions/FiniteResolutionProductInclusions.lean), [`AuslanderReiten_Tensor_TwistedTensorResolution`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/TwistedTensorResolution.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A102`, `OAIQ031A131`, `OAIQ031A132`, `OAIQ031A134` and `OAIQ031A135` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A149` and `OAIQ031A150`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A102
import Definitions.Def_OAIQ031A131
import Definitions.Def_OAIQ031A132
import Definitions.Def_OAIQ031A134
import Definitions.Def_OAIQ031A135

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_ModuleBarTwistExtAction
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open scoped ModuleCat.Algebra
namespace ArExplicit.ModuleBar
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
universe u
variable (k R M : Type u) [Field k] [Ring R] [Algebra k R]
  [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M] [CharP k 2]
variable (h : R ≃ₐ[k] R) (e : M ≃ₗ[k] M)
variable (he : ∀ a m, e (a • m) = h a • e m)

variable [HasDerivedCategory (ModuleCat.{u} R)]
variable (p : AbsoluteBar.Cochain3 k R) (hp : AbsoluteBar.IsCocycle3 k R p)

theorem extClass3_comp_extMk (n : ℕ)
    (f : (resolution k R M).complex.X n ⟶ ModuleCat.of R M)
    (hf : (resolution k R M).complex.d (n+1) n ≫ f=0) :
    (extClass3 k R M p hp).comp ((resolution k R M).extMk f (n+1) rfl hf)
      (by omega : 3+n=n+3) =
    (resolution k R M).extMk (cubicMap k R M p n ≫ f) (n+4) rfl
      (ResolutionProducts.cubicPrecomp_closed (resolution k R M) (cubicMap k R M p)
        (cubicMap_comm k R M p hp) f hf) := by
  rw [← cubicCocycle_endExt k R M p hp]
  exact ResolutionProducts.cubic_endExt_comp_extMk (k := k) (resolution k R M)
    (cubicMap k R M p) (cubicMap_comm k R M p hp) f hf

end ArExplicit.ModuleBar

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Coordinates_FiniteTensorComparison
attribute [-instance] _root_.OAI.ArExplicit.BalancedTensor.functor_linear _root_.OAI.ArExplicit.TriangularModule.instAddCommGroup _root_.OAI.ArExplicit.TriangularModule.instIsScalarTowerTriangular _root_.OAI.ArExplicit.TriangularModule.instModule _root_.OAI.ArExplicit.TriangularModule.instModuleTriangular _root_.OAI.ArExplicit.TriangularModule.instSMulTriangular _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
namespace ArExplicit.FiniteLeftModule
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [Module.Finite k R]
variable (τ : FrobeniusTrace k R) (X : FiniteLeftModule k R)
variable (M N : FiniteLeftModule k (R ⊗[k] Rᵐᵒᵖ))
variable [Module.Finite R (EnvelopingBimodule k R M.carrier)]
  [Module.Projective R (EnvelopingBimodule k R M.carrier)]
  [Module.Finite Rᵐᵒᵖ (EnvelopingBimodule k R M.carrier)]
  [Module.Projective Rᵐᵒᵖ (EnvelopingBimodule k R M.carrier)]
variable [Module.Finite R (EnvelopingBimodule k R N.carrier)]
  [Module.Projective R (EnvelopingBimodule k R N.carrier)]
  [Module.Finite Rᵐᵒᵖ (EnvelopingBimodule k R N.carrier)]
  [Module.Projective Rᵐᵒᵖ (EnvelopingBimodule k R N.carrier)]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower

def evaluatedResolutionOut :
    BalancedTensor.completeTensor (F := EnvelopingBimodule k R M.carrier) τ X ⟶
      (evaluated X M).completeCochain τ :=
  BalancedTensor.comparisonOut τ X (evaluated X M) (LinearEquiv.refl R _)

theorem evaluatedResolutionOut_natural (f : M.carrier ⟶ N.carrier)
    (L : FiniteLeftModule k R) (e : (evaluated X N).carrier ≃ₗ[R] L.carrier) :
    (HomotopyCategory.quotient _ _).map
      (BalancedTensor.complexMap (k := k) (EnvelopingBimodule.mapRight f)
        (EnvelopingBimodule.map_left_smul f) (X.completeCochain τ) ≫
          BalancedTensor.comparisonOut τ X L e) =
    (HomotopyCategory.quotient _ _).map
      (evaluatedResolutionOut τ X M ≫
        resolutionMap τ (e.toLinearMap.comp (evaluationMap X f.hom))) := by
  apply BalancedTensor.comparisonOut_natural τ X (evaluated X M)
    (LinearEquiv.refl R _) L (EnvelopingBimodule.mapRight f)
    (EnvelopingBimodule.map_left_smul f) e
    (e.toLinearMap.comp (evaluationMap X f.hom))
  intro x
  rfl

end ArExplicit.FiniteLeftModule

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Coordinates_FiniteTensorComparisonEquiv
attribute [-instance] _root_.OAI.ArExplicit.TriangularModule.instAddCommGroup _root_.OAI.ArExplicit.TriangularModule.instIsScalarTowerTriangular _root_.OAI.ArExplicit.TriangularModule.instModule _root_.OAI.ArExplicit.TriangularModule.instModuleTriangular _root_.OAI.ArExplicit.TriangularModule.instSMulTriangular _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CochainComplex.HomComplex
open scoped TensorProduct ModuleCat.Algebra
namespace ArExplicit.FiniteLeftModule
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [Module.Finite k R]
variable (τ : FrobeniusTrace k R) (X : FiniteLeftModule k R)
variable (M : FiniteLeftModule k (R ⊗[k] Rᵐᵒᵖ))
variable [Module.Finite R (EnvelopingBimodule k R M.carrier)]
  [Module.Projective R (EnvelopingBimodule k R M.carrier)]
  [Module.Finite Rᵐᵒᵖ (EnvelopingBimodule k R M.carrier)]
  [Module.Projective Rᵐᵒᵖ (EnvelopingBimodule k R M.carrier)]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower

def evaluatedResolutionFullEquiv (P : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    CohomologyClass P (BalancedTensor.completeTensor (F := EnvelopingBimodule k R M.carrier) τ X) n ≃ₗ[k]
      CohomologyClass P ((evaluated X M).completeCochain τ) n :=
  LinearEquiv.ofBijective (fullHomPostcompLinear k n (evaluatedResolutionOut τ X M))
    (BalancedTensor.comparisonOut_bijective τ X (evaluated X M) (LinearEquiv.refl _ _) P n)

@[simp] theorem evaluatedResolutionFullEquiv_apply (P : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ)
    (x : CohomologyClass P (BalancedTensor.completeTensor (F := EnvelopingBimodule k R M.carrier) τ X) n) :
    evaluatedResolutionFullEquiv τ X M P n x = fullHomPostcomp (evaluatedResolutionOut τ X M) n x := rfl

end ArExplicit.FiniteLeftModule

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Resolutions_FiniteResolutionProduct
attribute [-instance] _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.FiniteLeftModule
open CategoryTheory CategoryTheory.Limits
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [Module.Finite k R]
variable (τ : FrobeniusTrace k R)
local notation "Q" => HomotopyCategory.quotient (ModuleCat R) (ComplexShape.up ℤ)
variable {M N : FiniteLeftModule k R}

variable (M N)

abbrev resolutionPairBicone : BinaryBicone ((Q).obj (M.completeCochain τ))
    ((Q).obj (N.completeCochain τ)) where
  pt := (Q).obj ((pairModule M N).completeCochain τ)
  fst := (Q).map (resolutionMap (M := pairModule M N) (N := M) τ (pairFst M N))
  snd := (Q).map (resolutionMap (M := pairModule M N) (N := N) τ (pairSnd M N))
  inl := (Q).map (resolutionMap (M := M) (N := pairModule M N) τ (pairInl M N))
  inr := (Q).map (resolutionMap (M := N) (N := pairModule M N) τ (pairInr M N))
  inl_fst := by
    erw [← resolutionMap_comp]
    rw [show (pairFst M N).comp (pairInl M N) = LinearMap.id from by ext x; rfl, resolutionMap_id]
  inl_snd := by
    erw [← resolutionMap_comp]
    rw [show (pairSnd M N).comp (pairInl M N) = 0 from by ext x; rfl, homotopyResolutionMap_zero]
  inr_fst := by
    erw [← resolutionMap_comp]
    rw [show (pairFst M N).comp (pairInr M N) = 0 from by ext x; rfl, homotopyResolutionMap_zero]
  inr_snd := by
    erw [← resolutionMap_comp]
    rw [show (pairSnd M N).comp (pairInr M N) = LinearMap.id from by ext x; rfl, resolutionMap_id]

 theorem resolutionPairBicone_total :
    (resolutionPairBicone τ M N).fst ≫ (resolutionPairBicone τ M N).inl +
      (resolutionPairBicone τ M N).snd ≫ (resolutionPairBicone τ M N).inr =
      𝟙 (resolutionPairBicone τ M N).pt := by
  apply (resolutionHomotopyEquiv τ (pairModule M N) (pairModule M N)).injective
  rw [map_add, resolutionHomotopyEquiv_comp, resolutionHomotopyEquiv_comp,
    resolutionHomotopyEquiv_id]
  simp only [resolutionHomotopyEquiv_map, StableHom.comp_classOf]
  rw [← map_add]
  apply congrArg (StableHom.classOf R _ _)
  ext x
  exact Prod.ext (add_zero _) (zero_add _)

def resolutionPairBilimit : (resolutionPairBicone τ M N).IsBilimit :=
  isBinaryBilimitOfTotal _ (resolutionPairBicone_total τ M N)

instance resolutionPairHasBiproduct : HasBinaryBiproduct ((Q).obj (M.completeCochain τ))
    ((Q).obj (N.completeCochain τ)) :=
  hasBinaryBiproduct_of_total _ (resolutionPairBicone_total τ M N)

def resolutionPairIso : (Q).obj ((pairModule M N).completeCochain τ) ≅
    ((Q).obj (M.completeCochain τ) ⊞ (Q).obj (N.completeCochain τ)) :=
  biprod.uniqueUpToIso _ _ (resolutionPairBilimit τ M N)

@[simp] theorem resolutionPairIso_hom_fst :
    (resolutionPairIso τ M N).hom ≫ biprod.fst =
      (Q).map (resolutionMap (M := pairModule M N) (N := M) τ (pairFst M N)) :=
  by simp [resolutionPairIso]

@[simp] theorem resolutionPairIso_hom_snd :
    (resolutionPairIso τ M N).hom ≫ biprod.snd =
      (Q).map (resolutionMap (M := pairModule M N) (N := N) τ (pairSnd M N)) :=
  by simp [resolutionPairIso]

end ArExplicit.FiniteLeftModule

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Resolutions_FiniteResolutionProductInclusions
attribute [-instance] _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.FiniteLeftModule
open CategoryTheory CategoryTheory.Limits
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [Module.Finite k R]
variable (τ : FrobeniusTrace k R) (M N : FiniteLeftModule k R)
local notation "Q" => HomotopyCategory.quotient (ModuleCat R) (ComplexShape.up ℤ)

theorem resolutionPairInl :
    (Q).map (resolutionMap (M := M) (N := pairModule M N) τ (pairInl M N)) ≫
      (resolutionPairIso τ M N).hom = biprod.inl := by
  apply biprod.hom_ext
  · rw [Category.assoc, resolutionPairIso_hom_fst, biprod.inl_fst]
    exact (resolutionPairBicone τ M N).inl_fst
  · rw [Category.assoc, resolutionPairIso_hom_snd, biprod.inl_snd]
    exact (resolutionPairBicone τ M N).inl_snd

end ArExplicit.FiniteLeftModule

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_TwistedTensorResolution
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.Resolution.tInducedCochain_kprojective _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.instInjectiveA _root_.OAI.ArExplicit.instInjectiveMulOppositeA _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory
open scoped TensorProduct
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k) (H : kˣ)
attribute [local instance 2000] moduleCatBaseModule moduleCatBaseTower
attribute [local instance 2001] Semiring.toNonAssocSemiring
local notation "R" => T k q
local notation "Te" => AbsoluteBar.Enveloping k R

theorem source_exact (n : ℕ) :
    Function.Exact ((sourceData q H).d (n+1)) ((sourceData q H).d n) := by
  let (n : ℕ) : Module.Finite Te
      ((AbsoluteBar.twistedResolution k R (TrivialExtension.twist H)).complex.X n) :=
    AbsoluteBar.twistedFinite k R (TrivialExtension.twist H) n
  exact ExternalTensor.differential_exact k Te Te
    (AbsoluteBar.twistedResolution k R (TrivialExtension.twist H))
    (AbsoluteBar.twistedResolution k R (TrivialExtension.twist H)) n

def sourceQuotientRestriction : TwoCone.BaseCokernel (sourceData q H) 0 ≃ₗ[
    ExternalTensor.EnvelopingProduct k R R]
    (ExternalTensor.envelopingFunctor k R R).obj
      (ModuleCat.of (ExternalTensor.ProductEnveloping k R R)
        (TwoCone.BaseCokernel (productSourceData q H) 0)) := by
  unfold sourceData
  convert! (TwoCone.baseCokernelRestrictionEquiv (ExternalTensor.envelopingEquiv k R R).symm.toRingHom
    (productSourceData q H) 0).symm using 1
  all_goals try with_reducible_and_instances rfl

end ArExplicit.T

end

end OAI
end


