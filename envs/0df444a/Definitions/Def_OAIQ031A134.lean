-- Prove2me | Definitions.Def_OAIQ031A134
-- name    : OAIQ031A134
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T15:11:39.982382+00:00
-- url     : https://prove2.me/theorems/8d6600e8-4a33-4c13-9048-0ef1bb4d74ee
-- title:
--   Definitions bundle OAIQ031A134 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 19 declarations of OpenAI's Lean: 9 definitions and 10 theorems. The definitions and types are `OAI.ArExplicit.BarBalanced.endpointWithCoefficients`, `OAI.ArExplicit.BarBalanced.instModuleCarrierEnvelopingModuleObjectOfNatNat_2`, `OAI.ArExplicit.BarBalanced.instModuleCarrierTensorProductMulOpposite_solutions`, `OAI.ArExplicit.BarBalanced.instModuleCarrier_solutions`, `OAI.ArExplicit.BarBalanced.instModuleCarrier_solutions_2`, `OAI.ArExplicit.BarBalanced.nativeRegularCoordinates`, `OAI.ArExplicit.CompleteComparison.rawCokernelAtMap`, `OAI.ArExplicit.FiniteLeftModule.pairInr`, `OAI.ArExplicit.TwoCone.SkeletonCokernel`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Cocycles_RawCocycleProducts`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cocycles/RawCocycleProducts.lean), [`AuslanderReiten_Cones_TwoConeSkeleton`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/TwoConeSkeleton.lean), [`AuslanderReiten_Evaluation_CanonicalRegularEndpoint`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Evaluation/CanonicalRegularEndpoint.lean), [`AuslanderReiten_Evaluation_RegularCoefficientNaturality`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Evaluation/RegularCoefficientNaturality.lean), [`AuslanderReiten_Evaluation_RegularEvaluatedAugmentation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Evaluation/RegularEvaluatedAugmentation.lean), [`AuslanderReiten_Evaluation_RegularEvaluationCoordinates`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Evaluation/RegularEvaluationCoordinates.lean), [`AuslanderReiten_Ext_ExternalRegularEvaluation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Ext/ExternalRegularEvaluation.lean), [`AuslanderReiten_Resolutions_FiniteResolutionProduct`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Resolutions/FiniteResolutionProduct.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A107`, `OAIQ031A119`, `OAIQ031A121`, `OAIQ031A122` and `OAIQ031A124` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A140`, `OAIQ031A141`, `OAIQ031A142`, `OAIQ031A143` and `OAIQ031A144`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A107
import Definitions.Def_OAIQ031A119
import Definitions.Def_OAIQ031A121
import Definitions.Def_OAIQ031A122
import Definitions.Def_OAIQ031A124

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

def rawCokernelAtMap (x : Cocycle K L n) (a b : ℤ) (hab : a=n+b) :
    RawCokernelAt K a →ₗ[R] RawCokernelAt L b :=
  (rawCokernelAtEquiv L b).toLinearMap.comp
    ((reversedCokernelMap (k := k) x a b hab).comp
      (rawCokernelAtEquiv K a).symm.toLinearMap)

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

abbrev SkeletonCokernel (n : ℕ) := skeletonTerm D n ⧸ LinearMap.range (skeletonD D n)

end ArExplicit.TwoCone

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Evaluation_CanonicalRegularEndpoint
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
variable (k R : Type u) [Field k] [Ring R] [Algebra k R]
attribute [local instance 2000] moduleCatBaseModule moduleCatBaseTower
variable (X : ModuleCat.{u} R)

@[simp] theorem nativeEndpointIso_tmul_value
    (m : EnvelopingBimodule k R (AbsoluteBar.moduleObject k R 0)) (x : X) :
    (nativeEndpointIso k R X).hom (BalancedTensor.tmul m x) = (show R from m.value) • x := by
  change canonicalEquiv k R X 0 (BalancedTensor.tmul m x) = _
  rw [canonicalEquiv_tmul]
  rfl

end ArExplicit.BarBalanced

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Evaluation_RegularCoefficientNaturality
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.EnvelopingBimodule.regular_projective _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.moduleCatBaseComm _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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
variable (X Y : ModuleCat.{u} R) [Module k X] [IsScalarTower k R X]
local instance instModuleCarrier_solutions : Module k Y := moduleCatBaseModule (k := k) (R := R) Y
local instance instIsScalarTowerCarrier_solutions : IsScalarTower k R Y := moduleCatBaseTower (k := k) (R := R) Y

local instance instModuleCarrierEnvelopingModuleObjectOfNatNat_rf1446c_1 : Module k (AbsoluteBar.moduleObject k R 0) :=
  moduleCatBaseModule (k := k) (R := R ⊗[k] Rᵐᵒᵖ) (AbsoluteBar.moduleObject k R 0)
def endpointWithCoefficients (e : X ≅ Y) :
    (EnvelopingBimodule.evaluationFunctor k R X).obj (AbsoluteBar.moduleObject k R 0) ⟶ Y :=
  (EnvelopingBimodule.evaluationCoefficientIso k R e).hom.app (AbsoluteBar.moduleObject k R 0) ≫
    (nativeEndpointIso k R Y).hom

theorem endpointWithCoefficients_tmul (e : X ≅ Y)
    (a : EnvelopingBimodule k R (AbsoluteBar.moduleObject k R 0)) (x : X) :
    endpointWithCoefficients k R X Y e (BalancedTensor.tmul a x) =
      e.hom ((show R from a.value) • x) := by
  change (nativeEndpointIso k R Y).hom
    ((EnvelopingBimodule.evaluationCoefficientIso k R e).hom.app
      (AbsoluteBar.moduleObject k R 0) (BalancedTensor.tmul a x)) = _
  rw [EnvelopingBimodule.evaluationCoefficientIso_tmul, nativeEndpointIso_tmul_value]
  exact (e.hom.hom.map_smul _ _).symm

end ArExplicit.BarBalanced

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Evaluation_RegularEvaluationCoordinates
attribute [-instance] _root_.OAI.ArExplicit.AbsoluteBar.twistInvPair _root_.OAI.ArExplicit.AbsoluteBar.twistInvPairSymm _root_.OAI.ArExplicit.AbsoluteBar.twistedBaseModule _root_.OAI.ArExplicit.AbsoluteBar.twistedModuleTower _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.EnvelopingBimodule.regular_projective _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.moduleCatBaseComm _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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
variable (X Y : ModuleCat.{u} R) [Module k X] [IsScalarTower k R X]
local instance instModuleCarrier_solutions_2 : Module k Y := moduleCatBaseModule (k := k) (R := R) Y
local instance instIsScalarTowerCarrier_solutions_2 : IsScalarTower k R Y := moduleCatBaseTower (k := k) (R := R) Y
variable (M : ModuleCat.{u} (R ⊗[k] Rᵐᵒᵖ))
variable [Module k M] [IsScalarTower k (R ⊗[k] Rᵐᵒᵖ) M]
local instance instModuleCarrierEnvelopingModuleObjectOfNatNat_2 : Module k (AbsoluteBar.moduleObject k R 0) :=
  moduleCatBaseModule (k := k) (R := R ⊗[k] Rᵐᵒᵖ) (AbsoluteBar.moduleObject k R 0)
local instance instIsScalarTowerTensorProductMulOppositeCarrierEnvelopingModuleObjectOfNatNat_2 : IsScalarTower k (R ⊗[k] Rᵐᵒᵖ) (AbsoluteBar.moduleObject k R 0) :=
  moduleCatBaseTower (k := k) (R := R ⊗[k] Rᵐᵒᵖ) (AbsoluteBar.moduleObject k R 0)
variable (e : M ≃ₗ[R ⊗[k] Rᵐᵒᵖ] AbsoluteBar.moduleObject k R 0)

def nativeRegularCoordinates :
    BalancedTensor k R (EnvelopingBimodule k R M) X ≃ₗ[R] X := by
  letI := AbsoluteBar.baseModule k R 0
  letI := AbsoluteBar.bimoduleTower k R 0
  exact (EnvelopingBimodule.tensorCongr e X).trans (zeroEvaluationEquiv k R X)

@[simp] theorem nativeRegularCoordinates_tmul
    (m : EnvelopingBimodule k R M) (x : X) :
    nativeRegularCoordinates k R X M e (BalancedTensor.tmul m x) =
      (show R from e m.value) • x := rfl

theorem regularCoordinates_factor (u : X ≅ Y) :
    (endpointWithCoefficients k R X Y u).hom.comp
      (EnvelopingBimodule.tensorMap X e.toModuleIso.hom) =
      u.hom.hom.comp (nativeRegularCoordinates k R X M e).toLinearMap := by
  apply LinearMap.restrictScalars_injective k
  apply BalancedTensor.hom_ext
  intro m x
  change endpointWithCoefficients k R X Y u
    (BalancedTensor.tmul (EnvelopingBimodule.map e.toModuleIso.hom m) x) = _
  rw [endpointWithCoefficients_tmul]
  rfl

end ArExplicit.BarBalanced

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Evaluation_RegularEvaluatedAugmentation
attribute [-instance] _root_.OAI.ArExplicit.AbsoluteBar.twistInvPair _root_.OAI.ArExplicit.AbsoluteBar.twistInvPairSymm _root_.OAI.ArExplicit.AbsoluteBar.twistedBaseModule _root_.OAI.ArExplicit.AbsoluteBar.twistedModuleTower _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.EnvelopingBimodule.regular_projective _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.moduleCatBaseComm _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.BarBalanced
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
universe u
variable (k R : Type u) [Field k] [Ring R] [Algebra k R]
variable (X Y : ModuleCat.{u} R) [Module k X] [IsScalarTower k R X]
variable (P Q : ModuleCat.{u} (R ⊗[k] Rᵐᵒᵖ))
local instance instModuleCarrier_solutions_3_rf1446c_1 : Module k Y := moduleCatBaseModule (k := k) (R := R) Y
local instance instModuleCarrierTensorProductMulOpposite_solutions : Module k Q := moduleCatBaseModule (k := k) (R := R ⊗[k] Rᵐᵒᵖ) Q
local instance instIsScalarTowerCarrier_solutions_3_rf1446c_1 : IsScalarTower k R Y := moduleCatBaseTower (k := k) (R := R) Y
local instance instIsScalarTowerTensorProductMulOppositeCarrier_solutions : IsScalarTower k (R ⊗[k] Rᵐᵒᵖ) Q :=
  moduleCatBaseTower (k := k) (R := R ⊗[k] Rᵐᵒᵖ) Q

variable (u : X ≅ Y) (f : P ⟶ Q)
variable (e : Q ≃ₗ[R ⊗[k] Rᵐᵒᵖ] AbsoluteBar.moduleObject k R 0)
variable (b : P ⟶ AbsoluteBar.moduleObject k R 0)

local instance instModuleCarrierEnvelopingModuleObjectOfNatNat_3_rf1446c_1 : Module k (AbsoluteBar.moduleObject k R 0) :=
  moduleCatBaseModule (k := k) (R := R ⊗[k] Rᵐᵒᵖ) (AbsoluteBar.moduleObject k R 0)
local instance instIsScalarTowerTensorProductMulOppositeCarrierEnvelopingModuleObjectOfNatNat_3_rf1446c_1 : IsScalarTower k (R ⊗[k] Rᵐᵒᵖ) (AbsoluteBar.moduleObject k R 0) :=
  moduleCatBaseTower (k := k) (R := R ⊗[k] Rᵐᵒᵖ) (AbsoluteBar.moduleObject k R 0)
theorem regularEvaluatedAugmentation (hb : f ≫ e.toModuleIso.hom = b) :
    (EnvelopingBimodule.evaluationFunctor k R X).map b ≫
      endpointWithCoefficients k R X Y u =
    (EnvelopingBimodule.evaluationFunctor k R X).map f ≫
      (nativeRegularCoordinates k R X Q e).toModuleIso.hom ≫ u.hom := by
  have he : (EnvelopingBimodule.evaluationFunctor k R X).map e.toModuleIso.hom ≫
      endpointWithCoefficients k R X Y u =
      (nativeRegularCoordinates k R X Q e).toModuleIso.hom ≫ u.hom :=
    ModuleCat.hom_ext (regularCoordinates_factor k R X Y Q e u)
  rw [← hb, (EnvelopingBimodule.evaluationFunctor k R X).map_comp, Category.assoc, he]
  rfl

end ArExplicit.BarBalanced

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Ext_ExternalRegularEvaluation
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.EnvelopingBimodule.regular_projective _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.moduleCatBaseComm _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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
variable (X : ModuleCat.{u} R)

@[simp] theorem nativeEndpointIso_tmul
    (m : EnvelopingBimodule k R (AbsoluteBar.moduleObject k R 0)) (x : X) :
    (nativeEndpointIso k R X).hom (BalancedTensor.tmul m x) = (show R from m.value) • x := by
  change canonicalEquiv k R X 0 (BalancedTensor.tmul m x) = _
  rw [canonicalEquiv_tmul]
  rfl


end ArExplicit.BarBalanced

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
variable {M N : FiniteLeftModule k R}

variable (M N)

def pairInr : N.carrier →ₗ[R] (pairModule M N).carrier := LinearMap.inr R _ _

end ArExplicit.FiniteLeftModule

end

end OAI
end


