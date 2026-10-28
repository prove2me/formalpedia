-- Prove2me | Definitions.Def_OAIQ031A155
-- name    : OAIQ031A155
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T15:37:40.081676+00:00
-- url     : https://prove2.me/theorems/1cbaff1a-1f1d-4f57-b0e6-c2ca4489823f
-- title:
--   Definitions bundle OAIQ031A155 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 12 declarations of OpenAI's Lean: 3 definitions and 9 theorems. The definitions and types are `OAI.ArExplicit.A.positiveTateModel`, `OAI.ArExplicit.A.rawPositiveModel`, `OAI.ArExplicit.A.tateModel`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Complete_ConcreteTateModel`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Complete/ConcreteTateModel.lean), [`AuslanderReiten_Cones_TwoConeSkeleton`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/TwoConeSkeleton.lean), [`AuslanderReiten_Coordinates_FiniteSourceCoordinates`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Coordinates/FiniteSourceCoordinates.lean), [`AuslanderReiten_Ext_ExternalNativeRegularAugmentation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Ext/ExternalNativeRegularAugmentation.lean), [`AuslanderReiten_Ext_ExternalRegularEvaluation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Ext/ExternalRegularEvaluation.lean), [`AuslanderReiten_Ext_TTensorGeneration`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Ext/TTensorGeneration.lean), [`AuslanderReiten_Resolutions_FiniteCoverProducts`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Resolutions/FiniteCoverProducts.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A151`, `OAIQ031A152` and `OAIQ031A153` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ031A157`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A151
import Definitions.Def_OAIQ031A152
import Definitions.Def_OAIQ031A153

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

@[simp]
theorem bottomCokernelInclusion_mk (n : ℕ) (a : D.term n) :
    bottomCokernelInclusion D n (Submodule.Quotient.mk a) =
      Submodule.Quotient.mk (a, (0, 0)) := rfl

end ArExplicit.TwoCone

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Ext_TTensorGeneration
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.instInjectiveA _root_.OAI.ArExplicit.instInjectiveMulOppositeA _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.Resolution
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k)
variable [HasDerivedCategory (ModuleCat.{u} (ArExplicit.T k q))]
variable (hq : q ≠ 0) (hq1 : 1+q ≠ 0) (h : NoPositivePowerOne q)
local notation "T₀" => ArExplicit.T k q
local notation "S₀" => ModuleCat.of T₀ (Simple q)

include hq hq1 h in
theorem tTensor_generation (n : ℕ) (z : tTensorCoefficients q (3*(n+1))) :
    ∃ u v : tTensorCoefficients q (3*n),
      z = ExternalTensor.coefficientFirst k T₀ T₀ S₀ S₀ S₀ S₀ (tExplicitP q) (3*n) u +
        ExternalTensor.coefficientSecond k T₀ T₀ S₀ S₀ S₀ S₀ (tExplicitP q) (3*n) v := by
  obtain ⟨⟨u,v⟩, huv⟩ := BinaryKoszul.row_surjective k n
    (tTensorCoefficientEquiv q hq hq1 h (n+1) z)
  refine ⟨(tTensorCoefficientEquiv q hq hq1 h n).symm u,
    (tTensorCoefficientEquiv q hq hq1 h n).symm v, ?_⟩
  apply (tTensorCoefficientEquiv q hq hq1 h (n+1)).injective
  rw [map_add, tTensorCoefficient_first, tTensorCoefficient_second,
    LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  exact huv.symm

end ArExplicit.Resolution

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Complete_ConcreteTateModel
attribute [-instance] _root_.OAI.ArExplicit.FiniteLeftModule.resolutionPairHasBiproduct _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
open CochainComplex CochainComplex.HomComplex
open scoped ModuleCat.Algebra
namespace ArExplicit.A
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k)
variable [HasDerivedCategory (ModuleCat.{u} (ArExplicit.T k q))]
variable [HasDerivedCategory (ModuleCat.{u} (ArExplicit.A k q))]
open CompleteComparison

def rawPositiveModel (hq : q ≠ 0) (hq1 : 1+q ≠ 0)
    (h : Resolution.NoPositivePowerOne q) :=
  ModuleBar.tensorPositiveModel k (ArExplicit.T k q) (ArExplicit.T k q)
    (Resolution.Simple q) (Resolution.Simple q)
    (CocycleData.p q) (CocycleData.p_isCocycle3 q)
    (CocycleData.p q) (CocycleData.p_isCocycle3 q)
    (Resolution.tExplicitP q) (Resolution.aFactorExtClass q)
    (Resolution.tExplicitP q) (Resolution.aFactorExtClass q)
    (Resolution.tTensor_generation q hq hq1 h) (Resolution.aEndHom_scalar q hq1)
    (simpleComplete q) (nonnegativeExtChart q hq1)
    (Resolution.tTensorCoefficientEquiv q hq hq1 h)
    (Resolution.tTensorCoefficient_zero_of_not_dvd q hq hq1 h)
    (Resolution.tTensorCoefficient_first q hq hq1 h)
    (Resolution.tTensorCoefficient_second q hq hq1 h)

def positiveTateModel (hq : q ≠ 0) (hq1 : 1+q ≠ 0) (h : Resolution.NoPositivePowerOne q) : FullTate.PositiveModel (k := k) (simpleComplete q)
    (firstFullClass q hq1) (secondFullClass q hq1) :=
  rawPositiveModel q hq hq1 h

def tateModel (hq : q ≠ 0) (hq1 : 1+q ≠ 0) (h : Resolution.NoPositivePowerOne q) : TateKoszul.Model
    (fun a => fullHomRightMultiply (k := k) (K := simpleComplete q) (n := a) (firstFullClass q hq1))
    (fun a => fullHomRightMultiply (k := k) (K := simpleComplete q) (n := a) (secondFullClass q hq1)) :=
  FullTate.model (AFrobeniusTrace k q) (A_trace_symmetric k q)
    ((simpleFiniteModule q).completeCochain_totallyAcyclic (AFrobeniusTrace k q)).to_chain
    (positiveTateModel q hq hq1 h)

end ArExplicit.A

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Coordinates_FiniteSourceCoordinates
attribute [-instance] _root_.OAI.ArExplicit.FiniteLeftModule.resolutionPairHasBiproduct _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.FiniteLeftModule
open CategoryTheory
open CochainComplex CochainComplex.HomComplex CompleteComparison
open scoped ModuleCat.Algebra
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [Module.Finite k R] [CharP k 2]
variable (τ : FrobeniusTrace k R) (S M N L : FiniteLeftModule k R) (n : ℤ)

variable {S M N L n}
theorem HasSourceCoordinates.connecting_product
    (f : M.carrier →ₗ[R] N.carrier) (g : N.carrier →ₗ[R] L.carrier)
    (hf : Function.Injective f) (hg : Function.Surjective g) (hex : Function.Exact f g)
    (u : CohomologyClass (S.completeCochain τ) (L.completeCochain τ) n)
    (s : RawCokernelAt (S.completeCochain τ) n →ₗ[R] L.carrier)
    (A : (S.completeCochain τ).X (-n) →ₗ[R] N.carrier)
    (t : RawCokernelAt (S.completeCochain τ) (n+1) →ₗ[R] M.carrier)
    (hs : HasSourceCoordinates τ S L n u s)
    (hA : SourceQuotientSquare τ S N L n g s A)
    (ht : SourceInclusionSquare τ S M N n f A t) :
    HasSourceCoordinates τ S M (n+1)
      (fullHomProduct u ((fullHomShiftedHomotopyEquiv k _ _ 1).symm
        (resolutionConnecting τ f g hf hg hex))) t :=
  resolutionConnecting_product_source τ f g hf hg hex n u s hs A t hA ht

end ArExplicit.FiniteLeftModule

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Ext_ExternalRegularEvaluation
attribute [-instance] _root_.OAI.ArExplicit.AbsoluteBar.twistInvPair _root_.OAI.ArExplicit.AbsoluteBar.twistInvPairSymm _root_.OAI.ArExplicit.AbsoluteBar.twistedBaseModule _root_.OAI.ArExplicit.AbsoluteBar.twistedModuleTower _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.EnvelopingBimodule.regular_projective _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.moduleCatBaseComm _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit.ExternalBalanced
open CategoryTheory
open scoped TensorProduct
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
attribute [local instance 2000] moduleCatBaseModule moduleCatBaseTower
variable (X : ModuleCat.{u} A) (Y : ModuleCat.{u} B)
local notation "UA" => AbsoluteBar.moduleObject k A 0
local notation "UB" => AbsoluteBar.moduleObject k B 0
local notation "XY" => ExternalTensor.moduleObject k A B X Y
local notation "E" => EnvelopingBimodule.evaluationFunctor k (A ⊗[k] B) XY

theorem productRegularEndpoint_pure (a : EnvelopingBimodule k A UA)
    (b : EnvelopingBimodule k B UB) (x : X) (y : Y) :
    type_of% (productRegularEndpointPureProof k A B X Y a b x y) :=
  productRegularEndpointPureProof k A B X Y a b x y


theorem regularEndpoint_pure_eq
    (left : EnvelopingBimodule k A UA) (right : EnvelopingBimodule k B UB)
    (first : X) (second : Y) :
    type_of% ((factorRegularEndpoint_pure k A B X Y left right first second).trans
      (productRegularEndpoint_pure k A B X Y left right first second).symm) :=
  (factorRegularEndpoint_pure k A B X Y left right first second).trans
    (productRegularEndpoint_pure k A B X Y left right first second).symm

theorem regularEndpoint_eq_aux :
    type_of% (regularEndpoint_ext k A B X Y
      (factorRegularEndpoint k A B X Y) (productRegularEndpoint k A B X Y)
      (regularEndpoint_pure_eq k A B X Y)) :=
  regularEndpoint_ext k A B X Y
    (factorRegularEndpoint k A B X Y) (productRegularEndpoint k A B X Y)
    (regularEndpoint_pure_eq k A B X Y)

theorem regularEndpoint_eq :
    totalEndpointMap k A B X Y (BarBalanced.nativeEndpointIso k A X).hom
      (BarBalanced.nativeEndpointIso k B Y).hom =
    (E).map (barTensorZeroEquiv k A B).toModuleIso.hom ≫
      (BarBalanced.nativeEndpointIso k (A ⊗[k] B) XY).hom :=
  regularEndpoint_eq_aux k A B X Y

end ArExplicit.ExternalBalanced

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Ext_ExternalNativeRegularAugmentation
attribute [-instance] _root_.OAI.ArExplicit.AbsoluteBar.twistInvPair _root_.OAI.ArExplicit.AbsoluteBar.twistInvPairSymm _root_.OAI.ArExplicit.AbsoluteBar.twistedBaseModule _root_.OAI.ArExplicit.AbsoluteBar.twistedModuleTower _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.moduleCatBaseComm _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.ExternalBalanced
open CategoryTheory
open scoped TensorProduct
universe u
variable (k A B M N : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
variable [CharP k 2] [AddCommGroup M] [AddCommGroup N] [Module A M] [Module B N]
variable [Module k M] [Module k N] [IsScalarTower k A M] [IsScalarTower k B N]
local notation "Ae" => A ⊗[k] Aᵐᵒᵖ
local notation "Be" => B ⊗[k] Bᵐᵒᵖ

attribute [local instance] OAI.ArExplicit.ExternalBalanced.instModuleCarrierTensorProductCanonicalTensorObject
theorem nativeTotalBarIso_regularAugmentation :
    (nativeTotalBarIso k A B M N).hom.f 0 ≫
      (ExternalTensor.augmentation k A B (ModuleBar.nativeResolution k A M)
        (ModuleBar.nativeResolution k B N)).f 0 =
    (eval k A B M N).map
      ((ExternalTensor.envelopingFunctor k A B).map
        ((ExternalTensor.augmentation k Ae Be (AbsoluteBar.resolution k A)
          (AbsoluteBar.resolution k B)).f 0) ≫ (barTensorZeroEquiv k A B).toModuleIso.hom) ≫
      (BarBalanced.nativeEndpointIso k (A ⊗[k] B)
        (ExternalTensor.canonicalTensorObject k A B M N)).hom := by
  rw [nativeTotalBarIso_augmentation, regularEndpoint_eq]
  conv_rhs => erw [Functor.map_comp]
  erw [Category.assoc]
  rfl

end ArExplicit.ExternalBalanced

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Resolutions_FiniteCoverProducts
attribute [-instance] _root_.OAI.ArExplicit.FiniteLeftModule.resolutionPairHasBiproduct _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit
open CategoryTheory
open CochainComplex CochainComplex.HomComplex CompleteComparison
open scoped ModuleCat.Algebra
universe u
variable {k R : Type u} [Field k] [CharP k 2] [Ring R] [Algebra k R]
variable [Module.Finite k R]

namespace FiniteCoverTower
variable (τ : FrobeniusTrace k R) (T : FiniteCoverTower (k := k) (R := R))

variable (S : FiniteLeftModule k R)
variable (u₀ : CohomologyClass (S.completeCochain τ) ((T.obj 0).completeCochain τ) 0)

variable (s : ∀ n : ℕ, RawCokernelAt (S.completeCochain τ) (n : ℤ) →ₗ[R] (T.obj n).carrier)
variable (A : ∀ n : ℕ, (S.completeCochain τ).X (-(n : ℤ)) →ₗ[R] (T.middle n).carrier)
variable (hzero : FiniteLeftModule.HasSourceCoordinates τ S (T.obj 0) 0 u₀ (s 0))
variable (hquotient : ∀ n : ℕ, FiniteLeftModule.SourceQuotientSquare τ S
  (T.middle n) (T.obj n) (n : ℤ) (T.quotient n) (s n) (A n))
variable (hinclusion : ∀ n : ℕ, FiniteLeftModule.SourceInclusionSquare τ S
  (T.obj (n+1)) (T.middle n) (n : ℤ) (T.inclusion n) (A n) (s (n+1)))

include hzero hquotient hinclusion in

theorem coverClassFrom_source (n : ℕ) :
    FiniteLeftModule.HasSourceCoordinates τ S (T.obj n) (n : ℤ)
      (T.coverClassFrom τ S u₀ n) (s n) := by
  induction n with
  | zero => exact hzero
  | succ n ih =>
    exact FiniteLeftModule.HasSourceCoordinates.connecting_product τ
      (T.inclusion n) (T.quotient n) (T.injective n) (T.surjective n) (T.exact n)
      (T.coverClassFrom τ S u₀ n) (s n) (A n) (s (n+1)) ih (hquotient n) (hinclusion n)

end FiniteCoverTower
end ArExplicit

end

end OAI
end


