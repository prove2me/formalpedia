-- Prove2me | Definitions.Def_OAIQ031A142
-- name    : OAIQ031A142
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T15:19:35.896222+00:00
-- url     : https://prove2.me/theorems/70e039da-b213-4896-bc18-293c1115a2e5
-- title:
--   Definitions bundle OAIQ031A142 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 13 declarations of OpenAI's Lean: 2 definitions and 11 theorems. The definitions and types are `OAI.ArExplicit.BarBalanced.regularMap`, `OAI.ArExplicit.TwoCone.topCokernelProjection`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Bar_NativeBarCompositeValues`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/NativeBarCompositeValues.lean), [`AuslanderReiten_Bar_NativeBarFreeEndpoint`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/NativeBarFreeEndpoint.lean), [`AuslanderReiten_Cocycles_RawCocycleProducts`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cocycles/RawCocycleProducts.lean), [`AuslanderReiten_Complete_CompleteFunctorCokernelAction`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Complete/CompleteFunctorCokernelAction.lean), [`AuslanderReiten_Cones_TwoConeSkeleton`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/TwoConeSkeleton.lean), [`AuslanderReiten_Evaluation_CanonicalRegularMap`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Evaluation/CanonicalRegularMap.lean), [`AuslanderReiten_Tensor_BalancedTensorFiniteEvaluation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/BalancedTensorFiniteEvaluation.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A129`, `OAIQ031A132`, `OAIQ031A133`, `OAIQ031A134` and `OAIQ031A135` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A147`, `OAIQ031A148`, `OAIQ031A149` and `OAIQ031A150`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A129
import Definitions.Def_OAIQ031A132
import Definitions.Def_OAIQ031A133
import Definitions.Def_OAIQ031A134
import Definitions.Def_OAIQ031A135

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_NativeBarFreeEndpoint
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.EnvelopingBimodule.regular_projective _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.moduleCatBaseComm _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit.BarBalanced
open CategoryTheory
open scoped TensorProduct
universe u
variable (k R M : Type u) [Field k] [Ring R] [Algebra k R] [CharP k 2]
variable [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]

theorem nativeScalarValues (a b : R) (m : M) :
    type_of% (compValues ((canonicalComplexIso k R (ModuleCat.of R M)).hom.f 0)
      ((ModuleBar.coefficientScalarIso k R M).hom.f 0)
      (canonicalComplexIso_tensor k R M a b m)
      (ModuleBar.coefficientScalarIso_tmul k R M a (b • m))) :=
  compValues ((canonicalComplexIso k R (ModuleCat.of R M)).hom.f 0)
    ((ModuleBar.coefficientScalarIso k R M).hom.f 0)
    (canonicalComplexIso_tensor k R M a b m)
    (ModuleBar.coefficientScalarIso_tmul k R M a (b • m))

theorem nativeFreeValues (e : M ≃ₗ[k] k) (a b : R) (m : M) :
    type_of% (compValues
      ((canonicalComplexIso k R (ModuleCat.of R M)).hom.f 0 ≫
        (ModuleBar.coefficientScalarIso k R M).hom.f 0)
      (ModuleBar.freeCoordinate k R M e).toModuleIso.hom
      (nativeScalarValues k R M a b m)
      (ModuleBar.freeCoordinate_tmul k R M e a (b • m))) :=
  compValues
      ((canonicalComplexIso k R (ModuleCat.of R M)).hom.f 0 ≫
        (ModuleBar.coefficientScalarIso k R M).hom.f 0)
      (ModuleBar.freeCoordinate k R M e).toModuleIso.hom
      (nativeScalarValues k R M a b m)
      (ModuleBar.freeCoordinate_tmul k R M e a (b • m))

@[simp] theorem nativeFreeEndpoint_tensor (e : M ≃ₗ[k] k) (a b : R) (m : M) :
    type_of% (valueOfEq (nativeFreeEndpoint_component k R M e)
      (nativeFreeValues k R M e a b m)) :=
  valueOfEq (nativeFreeEndpoint_component k R M e) (nativeFreeValues k R M e a b m)

end ArExplicit.BarBalanced

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_NativeBarCompositeValues
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.EnvelopingBimodule.regular_projective _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.moduleCatBaseComm _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.BarBalanced
open CategoryTheory
universe u
variable (k R M : Type u) [Field k] [Ring R] [Algebra k R] [CharP k 2]
variable [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]

theorem nativeFreeEndpoint_definition (e : M ≃ₗ[k] k) :
    nativeFreeEndpoint k R M e = (nativeComplexIso k R M).hom.f 0 ≫
      (ModuleBar.freeCoordinate k R M e).toModuleIso.hom := rfl

theorem nativeComposite_tensor (e : M ≃ₗ[k] k) (a b : R) (m : M) :
    type_of% (valueOfMapEq (nativeFreeEndpoint_definition k R M e).symm
      (nativeFreeEndpoint_tensor k R M e a b m)) :=
  valueOfMapEq (nativeFreeEndpoint_definition k R M e).symm
    (nativeFreeEndpoint_tensor k R M e a b m)

end ArExplicit.BarBalanced

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cocycles_RawCocycleProducts
attribute [-instance] _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.CompleteComparison
open CategoryTheory HomologicalComplex
open CochainComplex CochainComplex.HomComplex
open scoped ModuleCat.Algebra
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [CharP k 2]
variable {K L M : CochainComplex (ModuleCat.{u} R) ℤ} {n m : ℤ}

@[simp]
theorem rawCokernelAtMap_mk (x : Cocycle K L n) (a b : ℤ) (hab : a=n+b)
    (z : K.X (-a)) :
    rawCokernelAtMap (k := k) x a b hab (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk ((x.val.v (-a) (-b) (by omega)).hom z) := by
  change rawCokernelAtEquiv L b
    (reversedCokernelMap (k := k) x a b hab
      ((rawCokernelAtEquiv K a).symm (Submodule.Quotient.mk z))) = _
  rw [rawCokernelAtEquiv_symm_mk, reversedCokernelMap_mk]
  change Submodule.Quotient.mk
    ((L.extendXIso negIndexEmbedding (i := -b) (i' := b) (neg_neg b)).hom.hom
      ((reversedComponent x.val a b hab).hom
        ((K.extendXIso negIndexEmbedding (i := -a) (i' := a) (neg_neg a)).inv.hom z))) = _
  simp [reversedComponent]

theorem rawCokernelAtMap_cover (x : Cocycle K L n) (a b : ℤ) (hab : a=n+b) :
    (rawCokernelAtInclusion L b).comp
      (rawCokernelAtMap (k := k) x (a+1) (b+1) (by omega)) =
    (x.val.v (-a) (-b) (by omega)).hom.comp (rawCokernelAtInclusion K a) := by
  apply LinearMap.ext
  intro z
  obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective
    (LinearMap.range (K.d (-(a+1+1)) (-(a+1))).hom) z
  simp only [LinearMap.comp_apply]
  erw [rawCokernelAtMap_mk]
  exact congrArg (fun f => f.hom z) (rawCocycleComponent_comm (k := k) x a b hab)

theorem rawSourceAt_product (x : Cocycle K L n) (y : Cocycle L M m) :
    rawSourceAt (cocycleProduct x y) =
      (rawSourceAt y).comp (rawCokernelAtMap (k := k) x (n+m) m rfl) := by
  apply LinearMap.ext
  intro z
  obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective
    (LinearMap.range (K.d (-(n+m+1)) (-(n+m))).hom) z
  simp only [LinearMap.comp_apply]
  erw [rawSourceAt_mk (k := k), rawCokernelAtMap_mk, rawSourceAt_mk (k := k)]
  change Submodule.Quotient.mk
    (((x.val.comp y.val rfl).v (-(n+m)) 0 (by omega)).hom z) = _
  rw [Cochain.comp_v _ _ rfl (-(n+m)) (-m) 0 (by omega) (by omega)]
  rfl

end ArExplicit.CompleteComparison

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Complete_CompleteFunctorCokernelAction
attribute [-instance] _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits HomologicalComplex
open CochainComplex.HomComplex
open scoped ModuleCat.Algebra
namespace ArExplicit.CompleteComparison
universe u
variable {k R : Type u} [Field k] [CharP k 2] [Ring R] [Algebra k R]
variable [HasDerivedCategory (ModuleCat.{u} R)]
variable (F : ModuleCat.{u} R ⥤ ModuleCat.{u} R) [F.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F] [F.PreservesProjectiveObjects]
variable (K : CochainComplex (ModuleCat.{u} R) ℤ)
variable (hK : TotallyAcyclicComplex (chainOfCochain K))
variable (hFK : TotallyAcyclicComplex (chainOfCochain (functorComplex F K)))

omit [HasDerivedCategory (ModuleCat.{u} R)] in
theorem rawFunctor_precomp_endpoint
    (a : K ⟶ functorComplex F K)
    (E : ModuleCat.of R (CochainCokernel K) ≅ F.obj (ModuleCat.of R (CochainCokernel K)))
    (ha : cochainCokernelMap a =
      (E ≪≫ (rawFunctorEndpointIso F K hK hFK).symm).hom.hom) :
    ModuleCat.ofHom (cokernelMap (extendMap a negIndexEmbedding) 0) ≫
      (completeFunctorEndpointIso F K hK hFK).hom =
    ((cochainCokernelLinearEquiv K).toModuleIso ≪≫ E ≪≫
      F.mapIso (cochainCokernelLinearEquiv K).symm.toModuleIso).hom := by
  have hh := cokernelMap_coordinates a
  rw [ha] at hh
  exact endpoint_before (cochainCokernelLinearEquiv K).toModuleIso
    (cochainCokernelLinearEquiv (functorComplex F K)).toModuleIso
    (completeFunctorEndpointIso F K hK hFK)
    (F.mapIso (cochainCokernelLinearEquiv K).toModuleIso) E _ hh

omit [HasDerivedCategory (ModuleCat.{u} R)] in
theorem rawFunctor_postcomp_endpoint
    (b : functorComplex F K ⟶ K)
    (E : ModuleCat.of R (CochainCokernel K) ≅ F.obj (ModuleCat.of R (CochainCokernel K)))
    (hb : cochainCokernelMap b =
      (rawFunctorEndpointIso F K hK hFK ≪≫ E.symm).hom.hom) :
    (completeFunctorEndpointIso F K hK hFK).inv ≫
      ModuleCat.ofHom (cokernelMap (extendMap b negIndexEmbedding) 0) =
    ((cochainCokernelLinearEquiv K).toModuleIso ≪≫ E ≪≫
      F.mapIso (cochainCokernelLinearEquiv K).symm.toModuleIso).inv := by
  have hh := cokernelMap_coordinates b
  rw [hb] at hh
  exact endpoint_after (cochainCokernelLinearEquiv K).toModuleIso
    (cochainCokernelLinearEquiv (functorComplex F K)).toModuleIso
    (completeFunctorEndpointIso F K hK hFK)
    (F.mapIso (cochainCokernelLinearEquiv K).toModuleIso) E _ hh

end ArExplicit.CompleteComparison

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_TwoConeSkeleton
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory

namespace ArExplicit.TwoCone

universe u
variable {R : Type u} [Ring R] (D : Data R)

def topCokernelProjection (n : ℕ) : Cokernel D n →ₗ[R] BaseCokernel D (n + 4) :=
  (negativeTopCokernelEquiv D n).toLinearMap.comp
    ((ConeCokernel.projection (skeletonD D n) (-(D.d (n + 4))) (topAttaching D n)).comp
      (skeletonCokernelCoordinates D n).toLinearMap)

end ArExplicit.TwoCone

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Evaluation_CanonicalRegularMap
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.moduleCatBaseComm _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.BarBalanced
open CategoryTheory
open scoped TensorProduct
universe u
variable (k R : Type u) [Field k] [Ring R] [Algebra k R]
attribute [local instance 2000] moduleCatBaseModule moduleCatBaseTower
variable (X : ModuleCat.{u} R) (M : ModuleCat.{u} (R ⊗[k] Rᵐᵒᵖ))
variable (f : M ⟶ AbsoluteBar.moduleObject k R 0)

def regularMap : (EnvelopingBimodule.evaluationFunctor k R X).obj M ⟶ X :=
  (EnvelopingBimodule.evaluationFunctor k R X).map f ≫ (nativeEndpointIso k R X).hom

end ArExplicit.BarBalanced

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_BalancedTensorFiniteEvaluation
attribute [-instance] _root_.OAI.ArExplicit.BalancedTensor.functor_linear _root_.OAI.ArExplicit.EnvelopingBimodule.regular_projective _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.moduleCatBaseComm _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
namespace ArExplicit.BalancedTensor
universe u
variable {k R F : Type u} [Field k] [Ring R] [Algebra k R]
variable [AddCommGroup F] [Module k F] [Module Rᵐᵒᵖ F] [Module R F]
variable [SMulCommClass k R F] [SMulCommClass R Rᵐᵒᵖ F]
variable (M : FiniteLeftModule k R)
variable (e : BalancedTensor k R F M.carrier ≃ₗ[R] M.carrier)

theorem nativeEvaluationIso_tmul (f : F) (m : M.carrier) :
    (nativeEvaluationIso M e).hom.hom
      (letI := moduleCatBaseModule (k := k) (R := R) M.carrier; tmul f m) = e (tmul f m) :=
  tensorEvaluationIso_tmul M.carrier e f m

end ArExplicit.BalancedTensor

end

end OAI
end


