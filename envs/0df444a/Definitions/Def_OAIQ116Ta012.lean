-- Prove2me | Definitions.Def_OAIQ116Ta012
-- name    : OAIQ116Ta012
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T02:14:07.423596+00:00
-- url     : https://prove2.me/theorems/aa6a30ef-ac2f-43a6-a21f-f34405f1b992
-- title:
--   Definitions bundle OAIQ116Ta012 of the split of OpenAI, A counterexample to Tachikawa's second conjecture
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Tachikawa.main_theorem`, carved from OpenAI's openai/math development (OpenAI, *A counterexample to Tachikawa's second conjecture*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 167 declarations of OpenAI's Lean: 83 definitions, 23 instances and 61 theorems. The definitions and types are `OAI.Tachikawa.Construction.XInverseTwistIso`, `OAI.Tachikawa.Construction.eTwist`, `OAI.Tachikawa.Construction.sFinite`, `OAI.Tachikawa.Construction.sResolution`, `OAI.Tachikawa.Enveloping.CoindGoodTerms`, `OAI.Tachikawa.Enveloping.coindCokerTensorIso`, `OAI.Tachikawa.Enveloping.coindComplex`, `OAI.Tachikawa.Enveloping.coindComplexShort`, `OAI.Tachikawa.Enveloping.coindComplexUnit`, `OAI.Tachikawa.Enveloping.coindComplexπ`, `OAI.Tachikawa.Enveloping.coindIterateTensorIso`, `OAI.Tachikawa.Enveloping.coindReplacement`, `OAI.Tachikawa.Enveloping.coindTensorEquiv`, `OAI.Tachikawa.Enveloping.coindTensorIso`, `OAI.Tachikawa.Enveloping.coindTensorUnderlying`, `OAI.Tachikawa.Enveloping.coindTermTensorIso`, `OAI.Tachikawa.Enveloping.cokerComplex`, `OAI.Tachikawa.Enveloping.fiber`, `OAI.Tachikawa.Enveloping.fiberInclusion`, `OAI.Tachikawa.Enveloping.fiberThird`, `OAI.Tachikawa.Enveloping.leftProdEquiv`, `OAI.Tachikawa.Enveloping.ordinaryAlpha`, `OAI.Tachikawa.Enveloping.ordinaryBeta`, `OAI.Tachikawa.Enveloping.ordinaryEndEquiv`, `OAI.Tachikawa.Enveloping.ordinaryOuterObj`, `OAI.Tachikawa.Enveloping.regularOuterEquiv`, `OAI.Tachikawa.Enveloping.regularOuterIso`, `OAI.Tachikawa.Enveloping.regularOuterUnderlying`, `OAI.Tachikawa.Enveloping.restrictedSingleMap`, `OAI.Tachikawa.Enveloping.rightFreeEvaluate`, `OAI.Tachikawa.Enveloping.rightFreeExtend`, `OAI.Tachikawa.Enveloping.rightFreeFunctor`, `OAI.Tachikawa.Enveloping.rightFreeHomEquiv`, `OAI.Tachikawa.Enveloping.rightFreeObj`, `OAI.Tachikawa.Enveloping.rightFreeResolution`, `OAI.Tachikawa.Enveloping.rightFreeRestrictionUnderlying`, `OAI.Tachikawa.Enveloping.rightFreeUnderlying`, `OAI.Tachikawa.Enveloping.rightProdEquiv`, `OAI.Tachikawa.Enveloping.tensorAugmentationEquiv`, `OAI.Tachikawa.Enveloping.tensorCompleteLift` and 43 more.
--
--   **Sources.** They come from these modules of lean/OAI/RingTheory, in whole or in part: `Tachikawa_Coinduction`, `Tachikawa_CompleteTensor`, `Tachikawa_Cone`, `Tachikawa_Coresolution`, `Tachikawa_Delta`, `Tachikawa_DerivedDescent`, `Tachikawa_FiniteCoinduction`, `Tachikawa_Induction`, `Tachikawa_Nakayama`, `Tachikawa_OuterExt`, `Tachikawa_Perfect`, `Tachikawa_ReverseResolution`, `Tachikawa_RightInduction`, `Tachikawa_Socle`, `Tachikawa_Triangular`, `Tachikawa_TwistHom`, `Tachikawa_Twisting`.
--
--   **Imports.** It imports the bundles `OAIQ116Ta017`, `OAIQ116Ta007`, `OAIQ116Ta008` and `OAIQ116Ta009` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ116Ta014` and `OAIQ116Ta015`; the statement `OAI.Tachikawa.Construction.XInverseTwist_weight`.
-- source:
--   OpenAI, A counterexample to Tachikawa's second conjecture, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-counterexample-to-Tachikawas-second-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/RingTheory at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ116Ta017
import Definitions.Def_OAIQ116Ta007
import Definitions.Def_OAIQ116Ta008
import Definitions.Def_OAIQ116Ta009

section
-- module Solutions.OAIQ116_Tach.Tachikawa_CompleteTensor
attribute [-instance] _root_.OAI.Tachikawa.DownHom.instAddCommGroupCochain _root_.OAI.Tachikawa.DownHom.instModuleCochain _root_.OAI.Tachikawa.Enveloping.coindEndo_finite _root_.OAI.Tachikawa.Enveloping.coindObj_finite _root_.OAI.Tachikawa.Enveloping.dualRegularLeftInjective _root_.OAI.Tachikawa.Enveloping.eval_finite _root_.OAI.Tachikawa.Enveloping.inducedRegularComplex_finite _root_.OAI.Tachikawa.Enveloping.inducedRegularComplex_finiteAlg _root_.OAI.Tachikawa.Enveloping.inducedRegularComplex_leftProjective _root_.OAI.Tachikawa.Enveloping.inducedRegularComplex_projective _root_.OAI.Tachikawa.Enveloping.instAddCommGroupCarrierMulOppositeRightObj _root_.OAI.Tachikawa.Enveloping.instAddCommGroupRightIndType _root_.OAI.Tachikawa.Enveloping.instAdditiveModuleCatAlgRightIndFunctor _root_.OAI.Tachikawa.Enveloping.instAdditiveModuleCatMulOppositeAlgCoindFunctor _root_.OAI.Tachikawa.Enveloping.instEpiModuleCatAlgCoindπ _root_.OAI.Tachikawa.Enveloping.instFiniteAlgCarrierXNatModuleCatComplexRegularResolution _root_.OAI.Tachikawa.Enveloping.instFiniteDimensionalCarrierAlgCoindObjOfMulOpposite _root_.OAI.Tachikawa.Enveloping.instFiniteDimensionalCarrierAlgRegular _root_.OAI.Tachikawa.Enveloping.instFiniteDimensionalCarrierAlgTwistedRegular _root_.OAI.Tachikawa.Enveloping.instIsScalarTowerCarrierMulOppositeRightObj _root_.OAI.Tachikawa.Enveloping.instIsScalarTowerMulOppositeCarrierRightObj _root_.OAI.Tachikawa.Enveloping.instIsScalarTowerMulOppositeRightIndType _root_.OAI.Tachikawa.Enveloping.instIsScalarTowerRightIndType _root_.OAI.Tachikawa.Enveloping.instLinearModuleCatAlgEvaluation _root_.OAI.Tachikawa.Enveloping.instModuleCarrierMulOppositeRightObj _root_.OAI.Tachikawa.Enveloping.instModuleCarrierMulOppositeRightObj_1 _root_.OAI.Tachikawa.Enveloping.instModuleMulOppositeRightIndType _root_.OAI.Tachikawa.Enveloping.instModuleRightIndType _root_.OAI.Tachikawa.Enveloping.instModuleRightIndType_1 _root_.OAI.Tachikawa.Enveloping.instMonoFunctorModuleCatAlgCoindUnitNat _root_.OAI.Tachikawa.Enveloping.instMonoModuleCatAlgCoindUnit _root_.OAI.Tachikawa.Enveloping.instPreservesFiniteColimitsModuleCatAlgLeftFunctor _root_.OAI.Tachikawa.Enveloping.instPreservesFiniteColimitsModuleCatAlgMulOppositeRightFunctor _root_.OAI.Tachikawa.Enveloping.instPreservesFiniteLimitsModuleCatAlgLeftFunctor _root_.OAI.Tachikawa.Enveloping.instPreservesFiniteLimitsModuleCatAlgMulOppositeRightFunctor _root_.OAI.Tachikawa.Enveloping.instSMulCommClassMulOppositeCarrierRightObj _root_.OAI.Tachikawa.Enveloping.instSMulCommClassMulOppositeRightIndType _root_.OAI.Tachikawa.Enveloping.leftFunctor_reflectsIsomorphisms _root_.OAI.Tachikawa.Enveloping.regular_left_projective _root_.OAI.Tachikawa.Enveloping.regular_right_projective _root_.OAI.Tachikawa.Enveloping.rightFunctor_finite _root_.OAI.Tachikawa.Enveloping.rightFunctor_reflectsIsomorphisms _root_.OAI.Tachikawa.HomBimodule.instEpiModuleCatAlgPostMap _root_.OAI.Tachikawa.HomBimodule.instFiniteDimensionalCarrierAlgObj _root_.OAI.Tachikawa.LeftCoinduced.coextend_additive _root_.OAI.Tachikawa.LeftCoinduced.coextend_preservesInjective _root_.OAI.Tachikawa.OuterTensor.restrictionPreservesHomology _root_.OAI.Tachikawa.TotalDualPairing.instTensorSignsNatUp_solutions _root_.OAI.Tachikawa.TotalMap.sourceHasCoproduct _root_.OAI.Tachikawa.Triangular.instAddCommGroupOff _root_.OAI.Tachikawa.Triangular.instIsScalarTowerMulOppositeProdOff _root_.OAI.Tachikawa.Triangular.instIsScalarTowerProdOff _root_.OAI.Tachikawa.Triangular.instModuleMulOppositeProdOff _root_.OAI.Tachikawa.Triangular.instModuleOff _root_.OAI.Tachikawa.Triangular.instModuleProdOff _root_.OAI.Tachikawa.Triangular.instSMulCommClassProdMulOppositeOff _root_.OAI.Tachikawa.downIntTensorSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace Tachikawa.Enveloping
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  (M : ModuleCat.{0} (Alg k S R))

lemma tensorComplex_exact [FiniteDimensional k (Obj M)] [Module.Projective Rᵐᵒᵖ (Obj M)]
    (P : ChainComplex (ModuleCat.{0} R) ℤ) (hP : ComplexExact P) :
    ComplexExact (tensorComplex M P) := by
  let : Module.Finite Rᵐᵒᵖ (Obj M) := Module.Finite.of_restrictScalars_finite k _ _
  intro j
  exact BalancedTensor.mapRight_exact (P.d (j+1) j).hom (P.d j (j-1)).hom (hP j)

variable [FiniteDimensional k R] [FiniteDimensional k (Obj M)]
  [Module.Projective Rᵐᵒᵖ (Obj M)]
  (N : FiniteModule k R) (t : SymmetrizingForm (k := k) (R := R))

lemma tensor_augmentation_exact : Function.Exact
    ((tensorComplex M (N.complete t)).d 1 0)
    ((tensorFunctor M).map (ModuleCat.ofHom N.cover.map)) := by
  let : Module.Finite Rᵐᵒᵖ (Obj M) := Module.Finite.of_restrictScalars_finite k _ _
  apply BalancedTensor.mapRight_exact
  change Function.Exact ((N.complete t).d (0+1) 0) N.cover.map
  rw [N.complete_d]
  exact N.pos_augmentation_exact

def tensorAugmentationEquiv : CokerAt (tensorComplex M (N.complete t)) 0 ≃ₗ[S]
    (tensorFunctor M).obj N.obj :=
  CokerAt.augmentationEquiv _ _ 0
    ((tensorFunctor M).map (ModuleCat.ofHom N.cover.map)).hom
    (tensor_augmentation_exact M N t)
    (tensor_map_surjective M (X := (N.complete t).X 0) (Y := N.obj)
      (ModuleCat.ofHom N.cover.map) N.cover.surjective)

end Tachikawa.Enveloping



namespace Tachikawa.Enveloping
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]

variable [FiniteDimensional k R] (M : ModuleCat (Alg k R R))
  [FiniteDimensional k (Obj M)] [Module.Projective R (Obj M)]
  [Module.Projective Rᵐᵒᵖ (Obj M)]
  (N : FiniteModule k R) (t : SymmetrizingForm (k := k) (R := R))
  (v : N.obj ⟶ (tensorFunctor M).obj N.obj)

lemma exists_tensorCompleteLift : ∃ l : N.complete t ⟶ tensorComplex M (N.complete t),
    l.f 0 ≫ (tensorFunctor M).map (ModuleCat.ofHom N.cover.map) =
      ModuleCat.ofHom N.cover.map ≫ v := by
  let u := (tensorAugmentationEquiv M N t).symm.toLinearMap.comp
    (v.hom.comp (N.cokerEquiv t).toLinearMap)
  obtain ⟨l,hl⟩ := exists_complete_lift (N.complete t) (tensorComplex M (N.complete t))
    (N.complete_totallyAcyclic t) (tensorComplex_exact M _ (N.complete_exact t))
    (N.complete_projective t) (tensorComplex_finite M _ (N.complete_finite t))
    (tensorComplex_projective M _ (N.complete_finite t) (N.complete_projective t)) u
  refine ⟨l,?_⟩
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have hx := congrArg (tensorAugmentationEquiv M N t)
    (LinearMap.congr_fun hl (CokerAt.π (N.complete t) 0 x))
  change (tensorAugmentationEquiv M N t) (CokerAt.π _ 0 (l.f 0 x)) =
    (tensorAugmentationEquiv M N t) ((tensorAugmentationEquiv M N t).symm
      (v ((N.cokerEquiv t) (CokerAt.π _ 0 x)))) at hx
  rw [LinearEquiv.apply_symm_apply] at hx
  exact hx

def tensorCompleteLift : N.complete t ⟶ tensorComplex M (N.complete t) :=
  (exists_tensorCompleteLift M N t v).choose

end Tachikawa.Enveloping



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Twisting
attribute [-instance] _root_.OAI.Tachikawa.DownHom.instAddCommGroupCochain _root_.OAI.Tachikawa.DownHom.instModuleCochain _root_.OAI.Tachikawa.Enveloping.coindEndo_finite _root_.OAI.Tachikawa.Enveloping.coindObj_finite _root_.OAI.Tachikawa.Enveloping.dualRegularLeftInjective _root_.OAI.Tachikawa.Enveloping.eval_finite _root_.OAI.Tachikawa.Enveloping.inducedRegularComplex_finite _root_.OAI.Tachikawa.Enveloping.inducedRegularComplex_finiteAlg _root_.OAI.Tachikawa.Enveloping.inducedRegularComplex_leftProjective _root_.OAI.Tachikawa.Enveloping.inducedRegularComplex_projective _root_.OAI.Tachikawa.Enveloping.instAddCommGroupCarrierMulOppositeRightObj _root_.OAI.Tachikawa.Enveloping.instAddCommGroupRightIndType _root_.OAI.Tachikawa.Enveloping.instAdditiveModuleCatAlgRightIndFunctor _root_.OAI.Tachikawa.Enveloping.instAdditiveModuleCatMulOppositeAlgCoindFunctor _root_.OAI.Tachikawa.Enveloping.instEpiModuleCatAlgCoindπ _root_.OAI.Tachikawa.Enveloping.instFiniteDimensionalCarrierAlgCoindObjOfMulOpposite _root_.OAI.Tachikawa.Enveloping.instIsScalarTowerCarrierMulOppositeRightObj _root_.OAI.Tachikawa.Enveloping.instIsScalarTowerMulOppositeCarrierRightObj _root_.OAI.Tachikawa.Enveloping.instIsScalarTowerMulOppositeRightIndType _root_.OAI.Tachikawa.Enveloping.instIsScalarTowerRightIndType _root_.OAI.Tachikawa.Enveloping.instLinearModuleCatAlgEvaluation _root_.OAI.Tachikawa.Enveloping.instModuleCarrierMulOppositeRightObj _root_.OAI.Tachikawa.Enveloping.instModuleCarrierMulOppositeRightObj_1 _root_.OAI.Tachikawa.Enveloping.instModuleMulOppositeRightIndType _root_.OAI.Tachikawa.Enveloping.instModuleRightIndType _root_.OAI.Tachikawa.Enveloping.instModuleRightIndType_1 _root_.OAI.Tachikawa.Enveloping.instMonoFunctorModuleCatAlgCoindUnitNat _root_.OAI.Tachikawa.Enveloping.instMonoModuleCatAlgCoindUnit _root_.OAI.Tachikawa.Enveloping.instPreservesFiniteColimitsModuleCatAlgLeftFunctor _root_.OAI.Tachikawa.Enveloping.instPreservesFiniteColimitsModuleCatAlgMulOppositeRightFunctor _root_.OAI.Tachikawa.Enveloping.instPreservesFiniteLimitsModuleCatAlgLeftFunctor _root_.OAI.Tachikawa.Enveloping.instPreservesFiniteLimitsModuleCatAlgMulOppositeRightFunctor _root_.OAI.Tachikawa.Enveloping.instSMulCommClassMulOppositeCarrierRightObj _root_.OAI.Tachikawa.Enveloping.instSMulCommClassMulOppositeRightIndType _root_.OAI.Tachikawa.Enveloping.leftFunctor_reflectsIsomorphisms _root_.OAI.Tachikawa.Enveloping.regular_left_projective _root_.OAI.Tachikawa.Enveloping.regular_right_projective _root_.OAI.Tachikawa.Enveloping.rightFunctor_finite _root_.OAI.Tachikawa.Enveloping.rightFunctor_reflectsIsomorphisms _root_.OAI.Tachikawa.HomBimodule.instEpiModuleCatAlgPostMap _root_.OAI.Tachikawa.HomBimodule.instFiniteDimensionalCarrierAlgObj _root_.OAI.Tachikawa.LeftCoinduced.coextend_additive _root_.OAI.Tachikawa.LeftCoinduced.coextend_preservesInjective _root_.OAI.Tachikawa.OuterTensor.restrictionPreservesHomology _root_.OAI.Tachikawa.SymmetrizingForm.twist_isEquivalence _root_.OAI.Tachikawa.SymmetrizingForm.twist_preserves_projective _root_.OAI.Tachikawa.TotalDualPairing.instTensorSignsNatUp_solutions _root_.OAI.Tachikawa.TotalMap.sourceHasCoproduct _root_.OAI.Tachikawa.Triangular.instAddCommGroupOff _root_.OAI.Tachikawa.Triangular.instIsScalarTowerMulOppositeProdOff _root_.OAI.Tachikawa.Triangular.instIsScalarTowerProdOff _root_.OAI.Tachikawa.Triangular.instModuleMulOppositeProdOff _root_.OAI.Tachikawa.Triangular.instModuleOff _root_.OAI.Tachikawa.Triangular.instModuleProdOff _root_.OAI.Tachikawa.Triangular.instProjectiveCarrierOneFree _root_.OAI.Tachikawa.Triangular.instSMulCommClassProdMulOppositeOff _root_.OAI.Tachikawa.downIntTensorSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace Tachikawa.Enveloping
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]

variable [FiniteDimensional k R]

instance instProjectiveObjXNatModuleCatAlgComplexRegularResolution (n : ℕ) : Module.Projective R
    (Obj ((regularResolution (k := k) (R := R)).complex.X n)) :=
  projective_left _

instance instProjectiveMulOppositeObjXNatModuleCatAlgComplexRegularResolution (n : ℕ) : Module.Projective Rᵐᵒᵖ
    (Obj ((regularResolution (k := k) (R := R)).complex.X n)) :=
  projective_right _

end Tachikawa.Enveloping



namespace Tachikawa.Enveloping
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R] (σ : R ≃ₐ[k] R)

def twistedRightEquiv : Obj (twistedRegular σ) ≃ₗ[Rᵐᵒᵖ] R where
  toFun := fun x => σ.symm (show R from x)
  invFun := fun x => σ x
  left_inv x := σ.apply_symm_apply x
  right_inv x := σ.symm_apply_apply x
  map_add' x y := map_add σ.symm x y
  map_smul' r x := by
    change σ.symm (1 * ((show R from x) * σ r.unop)) = σ.symm (show R from x) * r.unop
    rw [one_mul,map_mul,AlgEquiv.symm_apply_apply]

instance instProjectiveObjTwistedRegular : Module.Projective R (Obj (twistedRegular σ)) :=
  Module.Projective.of_equiv (twistedLeftEquiv σ).symm
instance instProjectiveMulOppositeObjTwistedRegular : Module.Projective Rᵐᵒᵖ (Obj (twistedRegular σ)) := by
  let : Module.Projective Rᵐᵒᵖ R :=
    Module.Projective.of_equiv (MulOpposite.opLinearEquiv Rᵐᵒᵖ).symm
  exact Module.Projective.of_equiv (twistedRightEquiv σ).symm

lemma twisted_left_smul (a : R) (x : Obj (twistedRegular σ)) :
    (show R from a • x) = a * (show R from x) := by
  change a * ((show R from x) * σ 1) = _
  rw [map_one,mul_one]
lemma twisted_right_smul (a : Rᵐᵒᵖ) (x : Obj (twistedRegular σ)) :
    (show R from a • x) = (show R from x) * σ a.unop := by
  change 1 * ((show R from x) * σ a.unop) = _
  rw [one_mul]

end Tachikawa.Enveloping



namespace Tachikawa.Enveloping
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
  (σ : R ≃ₐ[k] R)

abbrev twistedTensorFunctor : ModuleCat.{0} R ⥤ ModuleCat.{0} R :=
  BalancedTensor.functor (k := k) (R := R) (S := R) (M := Obj (twistedRegular σ))

lemma twistedTensor_move_general (X : ModuleCat R) (r : R) (x : X) :
    BalancedTensor.mk (k := k) (R := R) (S := R)
      (M := Obj (twistedRegular σ)) (N := X) (show Obj (twistedRegular σ) from r) x =
    BalancedTensor.mk (show Obj (twistedRegular σ) from (1:R)) (σ.symm r • x) := by
  have hb := BalancedTensor.balance (k := k) (S := R)
    (M := Obj (twistedRegular σ)) (N := X) (σ.symm r)
    (show Obj (twistedRegular σ) from (1:R)) x
  have hm : MulOpposite.op (σ.symm r) • (show Obj (twistedRegular σ) from (1:R)) =
      (show Obj (twistedRegular σ) from r) := by
    change 1 * (1 * σ (σ.symm r)) = r
    rw [σ.apply_symm_apply,one_mul,one_mul]
  rw [hm] at hb
  exact hb

def twistedTensorMap (X : ModuleCat R) :
    (twistedTensorFunctor σ).obj X ⟶ (SymmetrizingForm.twistFunctor σ).obj X :=
  ModuleCat.ofHom (Y := (SymmetrizingForm.twistFunctor σ).obj X)
    (BalancedTensor.lift (k := k) (R := R) (S := R)
      (M := Obj (twistedRegular σ)) (N := X)
      (P := (SymmetrizingForm.twistFunctor σ).obj X)
      { toFun := fun m =>
          { toFun := fun x => σ.symm (show R from m) • x
            map_add' := fun x y => smul_add _ x y
            map_smul' := fun c x => by
              change σ.symm (show R from m) • ((algebraMap k R c) • x) =
                σ.symm (algebraMap k R c) • (σ.symm (show R from m) • x)
              rw [σ.symm.commutes,IsScalarTower.algebraMap_smul R,
                IsScalarTower.algebraMap_smul R]
              exact smul_comm _ _ _ }
        map_add' := fun m n => by ext x; exact (congrArg (fun r => r • x) (map_add σ.symm _ _)).trans (add_smul _ _ _)
        map_smul' := fun r m => by
          ext x
          change σ.symm (show R from r • m) • x = σ.symm r • (σ.symm (show R from m) • x)
          rw [twisted_left_smul,map_mul,mul_smul] }
      (by
        intro r m x
        change σ.symm (show R from MulOpposite.op r • m) • x = σ.symm (show R from m) • (r • x)
        rw [twisted_right_smul,map_mul,σ.symm_apply_apply,mul_smul]
        rfl))

def twistedTensorInv (X : ModuleCat R) :
    (SymmetrizingForm.twistFunctor σ).obj X ⟶ (twistedTensorFunctor σ).obj X :=
  ModuleCat.ofHom (X := (SymmetrizingForm.twistFunctor σ).obj X)
    { toFun := fun x => BalancedTensor.mk (show Obj (twistedRegular σ) from (1:R)) (show X from x)
      map_add' := fun x y => map_add _ x y
      map_smul' := fun r x => by
        change BalancedTensor.mk (show Obj (twistedRegular σ) from (1:R)) (σ.symm r • (show X from x)) =
          r • BalancedTensor.mk (show Obj (twistedRegular σ) from (1:R)) (show X from x)
        rw [← twistedTensor_move_general]
        have hm : r • (show Obj (twistedRegular σ) from (1:R)) =
            (show Obj (twistedRegular σ) from r) := by
          change r * (1 * σ 1) = r
          rw [map_one,mul_one,mul_one]
        conv_lhs => rw [← hm]
        rw [LinearMap.map_smul]
        rfl }

def twistedTensorIso (X : ModuleCat R) :
    (twistedTensorFunctor σ).obj X ≅ (SymmetrizingForm.twistFunctor σ).obj X where
  hom := twistedTensorMap σ X
  inv := twistedTensorInv σ X
  hom_inv_id := by
    apply ModuleCat.hom_ext
    apply BalancedTensor.hom_ext (k := k) (R := R) (S := R)
    intro m x
    change BalancedTensor.mk (k := k) (R := R) (S := R) (N := X)
      (show Obj (twistedRegular σ) from (1:R))
      (σ.symm (show R from m) • x) = BalancedTensor.mk m x
    exact (twistedTensor_move_general σ X (show R from m) x).symm
  inv_hom_id := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change σ.symm (1:R) • (show X from x) = x
    rw [map_one,one_smul]

def twistedTensorNatIso : twistedTensorFunctor σ ≅ SymmetrizingForm.twistFunctor σ :=
  NatIso.ofComponents (twistedTensorIso σ) (by
    intro X Y f
    apply ModuleCat.hom_ext
    apply BalancedTensor.hom_ext
    intro m x
    change σ.symm (show R from m) • f x = f (σ.symm (show R from m) • x)
    exact (f.hom.map_smul _ _).symm)

end Tachikawa.Enveloping

end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Coresolution
attribute [-instance] _root_.OAI.Tachikawa.AlgebraInduction.instPreservesFiniteColimitsModuleCatRes _root_.OAI.Tachikawa.AlgebraInduction.instPreservesFiniteLimitsModuleCatRes _root_.OAI.Tachikawa.DownHom.instAddCommGroupCochain _root_.OAI.Tachikawa.Enveloping.instAddCommGroupCarrierMulOppositeRightObj _root_.OAI.Tachikawa.Enveloping.instModuleCarrierMulOppositeRightObj_1 _root_.OAI.Tachikawa.LeftCoinduced.coextend_additive _root_.OAI.Tachikawa.LeftCoinduced.coextend_preservesInjective _root_.OAI.Tachikawa.OuterTensor.restrictionPreservesHomology _root_.OAI.Tachikawa.TotalDualPairing.instTensorSignsNatUp_solutions _root_.OAI.Tachikawa.TotalMap.sourceHasCoproduct _root_.OAI.Tachikawa.downIntTensorSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
set_option backward.isDefEq.respectTransparency false


noncomputable section



namespace Tachikawa.SymmetrizingForm
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R] (σ : R ≃ₐ[k] R)

variable {J : Type} {c : ComplexShape J}

def inverseTwistComplex {P Q : HomologicalComplex (ModuleCat R) c}
    (f : P ⟶ ((twistFunctor σ).mapHomologicalComplex c).obj Q) :
    ((twistFunctor σ.symm).mapHomologicalComplex c).obj P ⟶ Q where
  f j := inverseTwistHom σ (f.f j)
  comm' i j _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact congrArg (fun h => h x) (f.comm i j)

end Tachikawa.SymmetrizingForm



namespace Tachikawa.SymmetrizingForm
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R] (σ : R ≃ₐ[k] R)

instance twist_preserves_injective : (twistFunctor σ).PreservesInjectiveObjects := inferInstance

end Tachikawa.SymmetrizingForm
namespace Tachikawa
open CategoryTheory HomologicalComplex
variable {C D : Type*} [Category C] [Abelian C] [Category D] [Abelian D]
  (F : C ⥤ D) [F.Additive] [F.PreservesInjectiveObjects] [F.PreservesHomology]
  {Y : C} (P : InjectiveResolution Y)

@[simp] lemma mappedCoresolution_ι_zero : (mappedCoresolution F P).ι.f 0 = F.map (P.ι.f 0) := by
  change (𝟙 (F.obj Y)) ≫ F.map (P.ι.f 0) = F.map (P.ι.f 0)
  exact Category.id_comp _

end Tachikawa
namespace Tachikawa.SymmetrizingForm
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R] (σ : R ≃ₐ[k] R)
  {X : ModuleCat R} (P : InjectiveResolution X)
  (e : (twistFunctor σ).obj X ≅ X) (he : ∀ x, e.hom x = x)
  (e' : (twistFunctor σ.symm).obj X ≅ X) (he' : ∀ x, e'.hom x = x)

include he in
lemma twistIso_inv_apply (x : X) : e.inv x = x := by
  have h := congrArg (fun f => f x) e.inv_hom_id
  change e.hom (e.inv x) = x at h
  rw [he] at h
  exact h

def inverseCoresolutionHom
    (l : InjectiveResolution.Hom P (mappedCoresolution (twistFunctor σ) P) e.inv) :
    InjectiveResolution.Hom (mappedCoresolution (twistFunctor σ.symm) P) P e'.hom where
  hom := inverseTwistComplex σ l.hom
  ι_f_zero_comp_hom_f_zero := by
    rw [mappedCoresolution_ι_zero]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change X at x
    have h := congrArg (fun f => f (show X from x)) l.ι_f_zero_comp_hom_f_zero
    rw [mappedCoresolution_ι_zero] at h
    change l.hom.f 0 (P.ι.f 0 x) = P.ι.f 0 (e.inv x) at h
    change l.hom.f 0 (P.ι.f 0 x) = P.ι.f 0 (e'.hom x)
    rw [twistIso_inv_apply σ e he] at h
    exact h.trans (congrArg (fun y : X => P.ι.f 0 y) (he' x)).symm

end Tachikawa.SymmetrizingForm



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_TwistHom
attribute [-instance] _root_.OAI.Tachikawa.AlgebraInduction.instPreservesFiniteColimitsModuleCatRes _root_.OAI.Tachikawa.AlgebraInduction.instPreservesFiniteLimitsModuleCatRes _root_.OAI.Tachikawa.DownHom.instAddCommGroupCochain _root_.OAI.Tachikawa.DownHom.instModuleCochain _root_.OAI.Tachikawa.Enveloping.dualRegularLeftInjective _root_.OAI.Tachikawa.Enveloping.inducedRegularComplex_leftProjective _root_.OAI.Tachikawa.Enveloping.instAddCommGroupCarrierMulOppositeRightObj _root_.OAI.Tachikawa.Enveloping.instModuleCarrierMulOppositeRightObj _root_.OAI.Tachikawa.Enveloping.instModuleCarrierMulOppositeRightObj_1 _root_.OAI.Tachikawa.Enveloping.regular_left_projective _root_.OAI.Tachikawa.Enveloping.regular_right_projective _root_.OAI.Tachikawa.LeftCoinduced.coextend_additive _root_.OAI.Tachikawa.LeftCoinduced.coextend_preservesInjective _root_.OAI.Tachikawa.OuterTensor.algebraTwist_preserves_projective _root_.OAI.Tachikawa.OuterTensor.restrictionPreservesHomology _root_.OAI.Tachikawa.TotalDualPairing.instTensorSignsNatUp_solutions _root_.OAI.Tachikawa.TotalMap.sourceHasCoproduct _root_.OAI.Tachikawa.downIntTensorSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
set_option backward.isDefEq.respectTransparency false


noncomputable section



namespace Tachikawa.FiniteModule
open CategoryTheory CategoryTheory.Abelian
open scoped ModuleCat.Algebra
open SymmetrizingForm
variable {k R : Type} [Field k] [Ring R] [Algebra k R] [FiniteDimensional k R]
  (M : FiniteModule k R) (t : SymmetrizingForm (k := k) (R := R))

variable (σ : R ≃ₐ[k] R) (e : (twistFunctor σ).obj M.obj ≅ M.obj)

def positiveTwistLift : ProjectiveResolution.Hom M.projectiveResolution
    (mappedResolution (twistFunctor σ) M.projectiveResolution) e.inv where
  hom := ProjectiveResolution.lift e.inv _ _
  hom_f_zero_comp_π_f_zero := ProjectiveResolution.lift_commutes_zero _ _ _

def negativeTwistLift : InjectiveResolution.Hom (M.coresolution t)
    (mappedCoresolution (twistFunctor σ) (M.coresolution t)) e.inv where
  hom := InjectiveResolution.desc e.inv _ _
  ι_f_zero_comp_hom_f_zero := InjectiveResolution.desc_commutes_zero _ _ _

def completeTwistComponent : ∀ j : ℤ, (M.complete t).X j ⟶
    (twistFunctor σ).obj ((M.complete t).X j)
  | .ofNat n => (M.positiveTwistLift σ e).hom.f n
  | .negSucc n => (M.negativeTwistLift t σ e).hom.f n

lemma completeTwistComponent_comm (j : ℤ) :
    M.completeTwistComponent t σ e (j+1) ≫ (twistFunctor σ).map (M.differential t j) =
      M.differential t j ≫ M.completeTwistComponent t σ e j := by
  cases j with
  | ofNat n =>
    have h := (M.positiveTwistLift σ e).hom.comm (n+1) n
    rw [M.projectiveResolution_d] at h
    change _ ≫ (twistFunctor σ).map (M.projectiveResolution.complex.d (n+1) n) = _ at h
    rw [M.projectiveResolution_d] at h
    exact h
  | negSucc n =>
    cases n with
    | zero =>
      have hp := (M.positiveTwistLift σ e).hom_f_zero_comp_π_f_zero
      have hi := (M.negativeTwistLift t σ e).ι_f_zero_comp_hom_f_zero
      change (M.positiveTwistLift σ e).hom.f 0 ≫ (twistFunctor σ).map (M.projectiveResolution.π.f 0) =
        M.projectiveResolution.π.f 0 ≫ e.inv at hp
      rw [M.projectiveResolution_π] at hp
      rw [mappedCoresolution_ι_zero,M.coresolution_ι] at hi
      change ModuleCat.ofHom (M.embed t) ≫ (M.negativeTwistLift t σ e).hom.f 0 =
        e.inv ≫ (twistFunctor σ).map (ModuleCat.ofHom (M.embed t)) at hi
      change (M.positiveTwistLift σ e).hom.f 0 ≫
        (twistFunctor σ).map (ModuleCat.ofHom M.cover.map ≫ ModuleCat.ofHom (M.embed t)) =
        (ModuleCat.ofHom M.cover.map ≫ ModuleCat.ofHom (M.embed t)) ≫
          (M.negativeTwistLift t σ e).hom.f 0
      erw [Functor.map_comp,← Category.assoc,hp,Category.assoc,← hi,Category.assoc]
      try rfl
    | succ n =>
      have h := (M.negativeTwistLift t σ e).hom.comm n (n+1)
      rw [M.coresolution_d] at h
      change _ ≫ (twistFunctor σ).map ((M.coresolution t).cocomplex.d n (n+1)) = _ at h
      rw [M.coresolution_d] at h
      exact h

def completeTwistLift : M.complete t ⟶
    ((twistFunctor σ).mapHomologicalComplex (.down ℤ)).obj (M.complete t) where
  f := M.completeTwistComponent t σ e
  comm' i j hij := by
    have hi : i=j+1 := by change j+1=i at hij; omega
    subst i
    change _ ≫ (twistFunctor σ).map ((M.complete t).d (j+1) j) = _
    rw [M.complete_d]
    exact M.completeTwistComponent_comm t σ e j

end Tachikawa.FiniteModule



namespace Tachikawa.FiniteModule
open CategoryTheory CategoryTheory.Abelian
open scoped ModuleCat.Algebra
open SymmetrizingForm
variable {k R : Type} [Field k] [Ring R] [Algebra k R] [FiniteDimensional k R]
  (M : FiniteModule k R) (t : SymmetrizingForm (k := k) (R := R)) (σ : R ≃ₐ[k] R)
  (e : (twistFunctor σ).obj M.obj ≅ M.obj)

def completeTwistHom : completeHom (k := k) (M.complete t) M.obj ⟶
    completeHom (k := k) (M.complete t) M.obj :=
  completeFunctorHom (k := k) (twistFunctor σ) (M.complete t) (M.complete t) M.obj
    (M.completeTwistLift t σ e) ≫ completeHomMap (M.complete t) e.hom

end Tachikawa.FiniteModule



namespace Tachikawa.Enveloping
open CategoryTheory
open scoped ModuleCat.Algebra
open SymmetrizingForm
variable {k R : Type} [Field k] [Ring R] [Algebra k R] [FiniteDimensional k R]
  (N : FiniteModule k R) (t : SymmetrizingForm (k := k) (R := R))
  (σ : R ≃ₐ[k] R) (e : (twistFunctor σ).obj N.obj ≅ N.obj)

def tensorTwistLift : N.complete t ⟶ tensorComplex (twistedRegular σ) (N.complete t) :=
  N.completeTwistLift t σ e ≫
    ((twistedTensorNatIso σ).inv.mapHomologicalComplex (.down ℤ)).app (N.complete t)

end Tachikawa.Enveloping

end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_OuterExt
attribute [-instance] _root_.OAI.Tachikawa.LeftCoinduced.coextend_additive _root_.OAI.Tachikawa.LeftCoinduced.coextend_preservesInjective _root_.OAI.Tachikawa.downIntTensorSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
set_option backward.isDefEq.respectTransparency false


noncomputable section



namespace Tachikawa.OuterTensor
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct ModuleCat.Algebra
variable {k A B : Type} [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
  (σ : A ≃ₐ[k] A) (τ : B ≃ₐ[k] B)

variable {M : ModuleCat A} {N : ModuleCat B}
  (P : ProjectiveResolution M) (Q : ProjectiveResolution N)
  (e : (algebraTwist σ).obj M ≅ M) (f : (algebraTwist τ).obj N ≅ N)
  (lP : ProjectiveResolution.Hom P (mappedResolution (algebraTwist σ) P) e.inv)
  (lQ : ProjectiveResolution.Hom Q (mappedResolution (algebraTwist τ) Q) f.inv)

def tensorTwistObjIso :
    (algebraTwist (Algebra.TensorProduct.congr σ τ)).obj (((bifunctor k A B).obj M).obj N) ≅
      (((bifunctor k A B).obj M).obj N) :=
  (twistObjIso σ τ M N).symm ≪≫
    { hom := morphism e.hom f.hom
      inv := morphism e.inv f.inv
      hom_inv_id := by rw [morphism_comp,e.hom_inv_id,f.hom_inv_id,morphism_id]
      inv_hom_id := by rw [morphism_comp,e.inv_hom_id,f.inv_hom_id,morphism_id] }

end Tachikawa.OuterTensor



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Nakayama
attribute [-instance] _root_.OAI.Tachikawa.DownHom.instAddCommGroupCochain _root_.OAI.Tachikawa.DownHom.instModuleCochain _root_.OAI.Tachikawa.Enveloping.instAddCommGroupCarrierMulOppositeRightObj _root_.OAI.Tachikawa.Enveloping.instModuleCarrierMulOppositeRightObj_1 _root_.OAI.Tachikawa.LeftCoinduced.coextend_additive _root_.OAI.Tachikawa.LeftCoinduced.coextend_preservesInjective _root_.OAI.Tachikawa.downIntTensorSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace Tachikawa
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable {P Q Z : Type} [AddCommGroup P] [Module R P]
  [AddCommGroup Q] [Module R Q] [AddCommGroup Z] [Module R Z]
  [Module k Z] [IsScalarTower k R Z]

namespace Nakayama

instance injective [Module.Finite R P] [Module.Projective R P] :
    Module.Injective R (Nakayama k R P) where
  out {X Y} _ _ _ _ f hf g := by
    let : Module k X := Module.compHom X (algebraMap k R)
    let : Module k Y := Module.compHom Y (algebraMap k R)
    let : IsScalarTower k R X := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    let : IsScalarTower k R Y := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    let fp : (P →ₗ[R] X) →ₗ[k] (P →ₗ[R] Y) := LinearMap.compRight k f
    have hinj : Function.Injective fp := by
      intro a b h
      ext p
      exact hf (LinearMap.congr_fun h p)
    obtain ⟨l, hl⟩ := fp.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hinj)
    let ψ := homDualEquiv (k := k) g
    refine ⟨coevaluation (ψ.comp l), ?_⟩
    intro x
    have hnat := coevaluation_natural_right f (ψ.comp l)
    have hh : (ψ.comp l).comp fp = ψ := by
      rw [LinearMap.comp_assoc, hl, LinearMap.comp_id]
    have hcomp : (coevaluation (ψ.comp l)).comp f = g := by
      rw [hnat]
      change coevaluation ((ψ.comp l).comp fp) = g
      rw [hh]
      exact coevaluation_homDualEquiv g
    exact LinearMap.congr_fun hcomp x

end Nakayama
end Tachikawa



namespace Tachikawa
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
namespace Nakayama

lemma complex_exact {P : ChainComplex (ModuleCat R) ℤ} (hP : TotallyAcyclic P) :
    ComplexExact (complex (k := k) P) := by
  intro j
  let f := homPrecomp (k := k) (Z := R) (P.d j (j-1)).hom
  let g := homPrecomp (k := k) (Z := R) (P.d (j+1) j).hom
  have hex : Function.Exact f g := by
    intro a
    change a.comp (P.d (j+1) j).hom = 0 ↔ ∃ b : P.X (j-1) →ₗ[R] R, b.comp (P.d j (j-1)).hom = a
    constructor
    · exact hP.2 j a
    · rintro ⟨b, rfl⟩
      rw [LinearMap.comp_assoc]
      have hh := ModuleCat.hom_ext_iff.mp (P.d_comp_d (j+1) j (j-1))
      change (P.d j (j-1)).hom.comp (P.d (j+1) j).hom = 0 at hh
      rw [hh, LinearMap.comp_zero]
  change Function.Exact g.dualMap f.dualMap
  exact exact_dual f g hex

variable {P Q Z : Type} [AddCommGroup P] [Module R P]
  [AddCommGroup Q] [Module R Q] [AddCommGroup Z] [Module R Z]

lemma map_exact (f : P →ₗ[R] Q) (g : Q →ₗ[R] Z)
    (h : Function.Exact f g) (hg : Function.Surjective g) :
    Function.Exact (map (k := k) f) (map g) := by
  exact exact_dual _ _ (homPrecomp_exact (k := k) f g h hg)

end Nakayama
end Tachikawa



namespace Tachikawa
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
namespace Nakayama
variable {P Q T Z : Type} [AddCommGroup P] [Module R P]
  [AddCommGroup Q] [Module R Q] [AddCommGroup T] [Module R T]
  [AddCommGroup Z] [Module R Z] [Module k Z] [IsScalarTower k R Z]
  [Module.Finite R P] [Module.Projective R P]
  [Module.Finite R Q] [Module.Projective R Q]
  [Module.Finite R T] [Module.Projective R T]

variable (C : ChainComplex (ModuleCat R) ℤ)

def cokerEquiv : CokerAt (complex (k := k) C) 0 ≃ₗ[R] Nakayama k R (CokerAt C 0) := by
  change (Nakayama k R (C.X 0) ⧸ LinearMap.range (map (k := k) (C.d 1 0).hom)) ≃ₗ[R] Nakayama k R (CokerAt C 0)
  let g := map (k := k) (CokerAt.π C 0)
  have he : Function.Exact (map (k := k) (C.d 1 0).hom) g :=
    map_exact _ _ (fun x => Submodule.Quotient.mk_eq_zero _) (CokerAt.π_surjective C 0)
  have hh : LinearMap.range (map (k := k) (C.d 1 0).hom) = LinearMap.ker g := by
    ext x
    exact (he x).symm
  exact (Submodule.quotEquivOfEq _ _ hh).trans (g.quotKerEquivOfSurjective (map_surjective _ (CokerAt.π_surjective C 0)))

def injectiveTail (hC : TotallyAcyclic C)
    (fin : ∀ j, Module.Finite R (C.X j))
    (proj : ∀ j, Module.Projective R (C.X j)) :
    InjectiveResolution (ModuleCat.of R (CokerAt (complex (k := k) C) 0)) := by
  let I := complex (k := k) C
  let X (n : ℕ) := I.X (-(n : ℤ)-1)
  let d (n : ℕ) : X n ⟶ X (n+1) := I.d (-(n : ℤ)-1) (-((n+1 : ℕ) : ℤ)-1)
  let ε : ModuleCat.of R (CokerAt I 0) ⟶ X 0 := ModuleCat.ofHom (CokerAt.ι I 0)
  have hI : ComplexExact I := complex_exact hC
  apply coresolutionOfExact _ X d ε
  · intro n
    exact hI.adjacent I _ _ _ (by omega) (by omega)
  · intro x
    constructor
    · intro hx
      change I.d (-1) (-2) x = 0 at hx
      obtain ⟨y, hy⟩ := (hI.adjacent I 0 (-1) (-2) (by omega) (by omega) x).mp hx
      exact ⟨CokerAt.π I 0 y, hy⟩
    · rintro ⟨y, rfl⟩
      obtain ⟨z, rfl⟩ := CokerAt.π_surjective I 0 y
      exact (hI.adjacent I 0 (-1) (-2) (by omega) (by omega)).apply_apply_eq_zero z
  · exact CokerAt.ι_injective I 0 (hI 0)
  · intro n
    let := fin (-(n : ℤ)-1)
    let := proj (-(n : ℤ)-1)
    change Injective (ModuleCat.of R (Nakayama k R (C.X (-(n : ℤ)-1))))
    let : Module.Injective R (Nakayama k R (C.X (-(n : ℤ)-1))) := Nakayama.injective
    exact Module.injective_object_of_injective_module R _

end Nakayama
end Tachikawa



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Socle
attribute [-instance] _root_.OAI.Tachikawa.Construction.instFiniteCSubtypeMemSubmoduleCe _root_.OAI.Tachikawa.Construction.instFiniteCSubtypeMemSubmoduleCf _root_.OAI.Tachikawa.Construction.instFiniteMulOppositeC _root_.OAI.Tachikawa.Construction.instFiniteMulOppositeCSubtypeMemSubmoduleEC _root_.OAI.Tachikawa.Construction.instFiniteMulOppositeCSubtypeMemSubmoduleFC _root_.OAI.Tachikawa.Construction.instProjectiveMulOppositeC _root_.OAI.Tachikawa.DownHom.instAddCommGroupCochain _root_.OAI.Tachikawa.DownHom.instModuleCochain _root_.OAI.Tachikawa.Enveloping.instAddCommGroupCarrierMulOppositeRightObj _root_.OAI.Tachikawa.Enveloping.instModuleCarrierMulOppositeRightObj_1 _root_.OAI.Tachikawa.LeftCoinduced.coextend_additive _root_.OAI.Tachikawa.LeftCoinduced.coextend_preservesInjective _root_.OAI.Tachikawa.downIntTensorSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace Tachikawa
open scoped TensorProduct
namespace Construction
variable {k : Type*} [Field k] (q : k)

instance instInjectiveE : Module.Injective (E q) (E q) := (formE q).injective

end Construction
end Tachikawa



namespace Tachikawa.Construction
open CategoryTheory CategoryTheory.Abelian
open scoped TensorProduct ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q : k)

abbrev sFinite : FiniteModule k (T q) :=
  ⟨C.simpleObj q, Module.Finite.of_restrictScalars_finite k (T q) _⟩
abbrev sResolution := (sFinite q).projectiveResolution

end Tachikawa.Construction



namespace Tachikawa.Construction
open CategoryTheory CategoryTheory.Abelian HomologicalComplex
open scoped ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q H : k) (hH : H ≠ 0)
  (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0)

instance simpleTwist_preserves_projective : (C.tTwist q H hH).PreservesProjectiveObjects := by
  have : (C.tTwist q H hH).IsEquivalence :=
    ModuleCat.restrictScalars_isEquivalence_of_ringEquiv
      (TrivialExtension.scaleDual (R := C k q) H hH).symm.toRingEquiv
  infer_instance

end Tachikawa.Construction



namespace Tachikawa.Construction
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian HomologicalComplex
open scoped TensorProduct ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q H : k) (hH : H ≠ 0)
  (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0)

abbrev eTwist := OuterTensor.algebraTwist (sigma q H hH)

end Tachikawa.Construction



namespace Tachikawa.Construction
open CategoryTheory CategoryTheory.Abelian
open scoped TensorProduct ModuleCat.Algebra
variable {k : Type} [Field k] (q H : k) (hH : H ≠ 0)

variable [CharP k 2]

def XInverseTwistIso : (SymmetrizingForm.twistFunctor (sigma q H hH).symm).obj
    (ModuleCat.of (E q) (X q)) ≅ ModuleCat.of (E q) (X q) where
  hom := ModuleCat.ofHom
    (X := (SymmetrizingForm.twistFunctor (sigma q H hH).symm).obj (ModuleCat.of (E q) (X q)))
    (Y := ModuleCat.of (E q) (X q))
    { toFun := id
      map_add' _ _ := rfl
      map_smul' a x := by
        change characterE q (sigma q H hH a) * (show k from x) = characterE q a * (show k from x)
        rw [characterE_sigma] }
  inv := ModuleCat.ofHom
    (X := ModuleCat.of (E q) (X q))
    (Y := (SymmetrizingForm.twistFunctor (sigma q H hH).symm).obj (ModuleCat.of (E q) (X q)))
    { toFun := id
      map_add' _ _ := rfl
      map_smul' a x := by
        change characterE q a * (show k from x) = characterE q (sigma q H hH a) * (show k from x)
        rw [characterE_sigma] }

end Tachikawa.Construction

end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_ReverseResolution
attribute [-instance] _root_.OAI.Tachikawa.DownHom.instAddCommGroupCochain _root_.OAI.Tachikawa.Enveloping.instAddCommGroupCarrierMulOppositeRightObj _root_.OAI.Tachikawa.Enveloping.instIsScalarTowerCarrierMulOppositeRightObj _root_.OAI.Tachikawa.Enveloping.instModuleCarrierMulOppositeRightObj_1 _root_.OAI.Tachikawa.LeftCoinduced.coextend_additive _root_.OAI.Tachikawa.LeftCoinduced.coextend_preservesInjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



noncomputable section



namespace Tachikawa.OuterTensor
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ModuleCat.Algebra
variable {k A B : Type} [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]

instance instAdditiveModuleCatTensorProductObjFunctorFlipBifunctor (N : ModuleCat B) : ((bifunctor k A B).flip.obj N).Additive where
  map_add {_X _Y} f f' := ModuleCat.hom_ext (map_add_left f f' (𝟙 N))

lemma exact_map_right (N : ModuleCat B) (S : ShortComplex (ModuleCat A)) (hS : S.Exact) :
    (S.map ((bifunctor k A B).flip.obj N)).Exact := by
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hS ⊢
  exact Module.Flat.rTensor_exact N (show Function.Exact (S.f.hom.restrictScalars k)
    (S.g.hom.restrictScalars k) from hS)

instance instPreservesFiniteLimitsModuleCatTensorProductObjFunctorFlipBifunctor (N : ModuleCat B) : PreservesFiniteLimits ((bifunctor k A B).flip.obj N) := by
  apply (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono _).mpr
  intro S hS
  refine ⟨exact_map_right N S hS.exact, ?_⟩
  rw [ModuleCat.mono_iff_injective]
  exact Module.Flat.rTensor_preserves_injective_linearMap (M := N)
    (S.f.hom.restrictScalars k) ((ModuleCat.mono_iff_injective S.f).mp hS.mono_f)

instance instPreservesFiniteColimitsModuleCatTensorProductObjFunctorFlipBifunctor (N : ModuleCat B) : PreservesFiniteColimits ((bifunctor k A B).flip.obj N) := by
  apply (Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi _).mpr
  intro S hS
  refine ⟨exact_map_right N S hS.exact, ?_⟩
  rw [ModuleCat.epi_iff_surjective]
  exact LinearMap.rTensor_surjective N ((ModuleCat.epi_iff_surjective S.g).mp hS.epi_g)

end Tachikawa.OuterTensor



namespace Tachikawa.OuterTensor
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct ModuleCat.Algebra
variable {k A B : Type} [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]

lemma total_finite (P : ChainComplex (ModuleCat.{0} A) ℕ)
    (Q : ChainComplex (ModuleCat.{0} B) ℕ)
    (hP : ∀ i, FiniteDimensional k (P.X i)) (hQ : ∀ j, FiniteDimensional k (Q.X j))
    (n : ℕ) : Module.Finite (A ⊗[k] B)
      ((mapBifunctor P Q (bifunctor k A B) (.down ℕ)).X n) := by
  let : Finite {ij : ℕ × ℕ // ij.1+ij.2=n} := by
    let f : {ij : ℕ × ℕ // ij.1+ij.2=n} → Fin (n+1) × Fin (n+1) := fun t =>
      (⟨t.val.1, by omega⟩, ⟨t.val.2, by omega⟩)
    exact Finite.of_injective f (by intro x y h; apply Subtype.ext; exact Prod.ext (congrArg (fun z => z.1.val) h) (congrArg (fun z => z.2.val) h))
  let F := fun ij : {ij : ℕ × ℕ // ij.1+ij.2=n} =>
    ((bifunctor k A B).obj (P.X ij.val.1)).obj (Q.X ij.val.2)
  let (i : ℕ) : FiniteDimensional k (P.X i) := hP i
  let (j : ℕ) : FiniteDimensional k (Q.X j) := hQ j
  have (t : {ij : ℕ × ℕ // ij.1+ij.2=n}) : Module.Finite (A ⊗[k] B) (F t) := objFinite _ _
  change Module.Finite (A ⊗[k] B) (∐ F : ModuleCat (A ⊗[k] B))
  exact Module.Finite.equiv ((biproduct.isoCoproduct F).symm ≪≫ ModuleCat.biproductIsoPi F).toLinearEquiv.symm

end Tachikawa.OuterTensor



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_RightInduction
attribute [-instance] _root_.OAI.Tachikawa.DownHom.instAddCommGroupCochain _root_.OAI.Tachikawa.Enveloping.coindEndo_finite _root_.OAI.Tachikawa.Enveloping.coindObj_finite _root_.OAI.Tachikawa.Enveloping.eval_finite _root_.OAI.Tachikawa.Enveloping.instAdditiveModuleCatMulOppositeAlgCoindFunctor _root_.OAI.Tachikawa.Enveloping.instEpiModuleCatAlgCoindπ _root_.OAI.Tachikawa.Enveloping.instFiniteDimensionalCarrierAlgCoindObjOfMulOpposite _root_.OAI.Tachikawa.Enveloping.instLinearModuleCatAlgEvaluation _root_.OAI.Tachikawa.Enveloping.instMonoFunctorModuleCatAlgCoindUnitNat _root_.OAI.Tachikawa.Enveloping.instMonoModuleCatAlgCoindUnit _root_.OAI.Tachikawa.Enveloping.rightFunctor_finite _root_.OAI.Tachikawa.HomBimodule.instFiniteDimensionalCarrierAlgObj _root_.OAI.Tachikawa.LeftCoinduced.coextend_additive _root_.OAI.Tachikawa.LeftCoinduced.coextend_preservesInjective _root_.OAI.Tachikawa.Triangular.instAddCommGroupOff _root_.OAI.Tachikawa.Triangular.instIsScalarTowerMulOppositeProdOff _root_.OAI.Tachikawa.Triangular.instIsScalarTowerProdOff _root_.OAI.Tachikawa.Triangular.instModuleMulOppositeProdOff _root_.OAI.Tachikawa.Triangular.instModuleOff _root_.OAI.Tachikawa.Triangular.instModuleProdOff _root_.OAI.Tachikawa.Triangular.instSMulCommClassProdMulOppositeOff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace Tachikawa.Enveloping
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k U R : Type} [Field k] [Ring U] [Ring R] [Algebra k U] [Algebra k R]

instance instModuleMulOppositeCarrierRightObj (M : ModuleCat (Alg k U R)) : Module Rᵐᵒᵖ (RightObj M) :=
  inferInstanceAs (Module Rᵐᵒᵖ ((rightFunctor (k := k) (R := U) (S := R)).obj M))

end Tachikawa.Enveloping



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Coinduction
attribute [-instance] _root_.OAI.Tachikawa.DownHom.instAddCommGroupCochain _root_.OAI.Tachikawa.DownHom.instModuleCochain _root_.OAI.Tachikawa.Enveloping.eval_finite _root_.OAI.Tachikawa.Enveloping.instLinearModuleCatAlgEvaluation _root_.OAI.Tachikawa.HomBimodule.instFiniteDimensionalCarrierAlgObj _root_.OAI.Tachikawa.Triangular.instAddCommGroupOff _root_.OAI.Tachikawa.Triangular.instIsScalarTowerMulOppositeProdOff _root_.OAI.Tachikawa.Triangular.instIsScalarTowerProdOff _root_.OAI.Tachikawa.Triangular.instModuleMulOppositeProdOff _root_.OAI.Tachikawa.Triangular.instModuleOff _root_.OAI.Tachikawa.Triangular.instModuleProdOff _root_.OAI.Tachikawa.Triangular.instProjectiveCarrierOneFree _root_.OAI.Tachikawa.Triangular.instSMulCommClassProdMulOppositeOff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace Tachikawa.Enveloping
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]

instance instAdditiveModuleCatAlgCoindEndo : (coindEndo (k := k) (R := R) (S := S)).Additive := inferInstanceAs
  ((rightFunctor (k := k) (R := R) (S := S) ⋙ coindFunctor).Additive)

instance instAdditiveModuleCatAlgCoindCoker : (coindCoker (k := k) (R := R) (S := S)).Additive := by
  constructor
  intro X Y f g
  dsimp only [coindCoker]
  let π := cokernel.π (coindUnitNat (k := k) (R := R) (S := S))
  let : Epi (π.app X) := inferInstance
  apply (cancel_epi (π.app X)).1
  erw [← π.naturality, Functor.map_add, Preadditive.add_comp,
    Preadditive.comp_add, ← π.naturality, ← π.naturality]

instance instAdditiveModuleCatAlgCoindIterate (n : ℕ) : (coindIterate (k := k) (R := R) (S := S) n).Additive := by
  induction n with
  | zero => exact inferInstanceAs ((𝟭 (ModuleCat (Alg k R S))).Additive)
  | succ n ih => exact inferInstanceAs ((coindIterate (k := k) (R := R) (S := S) n ⋙ coindCoker).Additive)




end Tachikawa.Enveloping



namespace Tachikawa.Enveloping
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]

def rightFreeFunctor : ModuleCat R ⥤ ModuleCat (Alg k R S) :=
  (OuterTensor.bifunctor k R Sᵐᵒᵖ).flip.obj (rightRegularObj (S := S))

instance instAdditiveModuleCatAlgRightFreeFunctor : (rightFreeFunctor (k := k) (R := R) (S := S)).Additive := inferInstanceAs
  (((OuterTensor.bifunctor k R Sᵐᵒᵖ).flip.obj (rightRegularObj (S := S))).Additive)

abbrev rightFreeObj (L : ModuleCat R) := (rightFreeFunctor (k := k) (S := S)).obj L
variable (L : ModuleCat R) (Q : ModuleCat (Alg k R S))

def rightFreeEvaluate (f : rightFreeObj (k := k) (S := S) L ⟶ Q) : L →ₗ[R] Obj Q where
  toFun x := f (x ⊗ₜ[k] (rightRegularOne (S := S)))
  map_add' x y := by erw [TensorProduct.add_tmul,map_add]; rfl
  map_smul' r x := by
    change f ((r • x) ⊗ₜ[k] (rightRegularOne (S := S))) =
      ((r ⊗ₜ[k] (1:Sᵐᵒᵖ)) : Alg k R S) • f (x ⊗ₜ[k] (rightRegularOne (S := S)))
    have h := f.hom.map_smul ((r ⊗ₜ[k] (1:Sᵐᵒᵖ)) : Alg k R S)
      (x ⊗ₜ[k] (rightRegularOne (S := S)))
    change f ((r • x) ⊗ₜ[k] ((1:Sᵐᵒᵖ) • rightRegularOne)) = _ at h
    simpa only [one_smul] using h

def rightFreeExtend (g : L →ₗ[R] Obj Q) : rightFreeObj (k := k) (S := S) L ⟶ Q :=
  ModuleCat.ofHom (X := rightFreeObj (k := k) (S := S) L) (Y := Q)
  { toFun := TensorProduct.lift (rightFreeBilinear L Q g)
    map_add' := map_add _
    map_smul' a x := by
      change TensorProduct.lift (rightFreeBilinear L Q g)
          ((OuterTensor.action k R Sᵐᵒᵖ L (rightRegularObj (S := S)) a) x) =
        a • TensorProduct.lift (rightFreeBilinear L Q g) x
      induction a using OAI.tensorInductionOn with
      | add a b ha hb => erw [map_add,LinearMap.add_apply,map_add,ha,hb,add_smul]
      | tmul r s =>
        induction x using OAI.tensorInductionOn with
        | add x y hx hy => rw [map_add,map_add,hx,hy,map_add,smul_add]
        | tmul x t =>
          change (s*(show Sᵐᵒᵖ from t)) • g (r • x) = (r ⊗ₜ[k] s) • ((show Sᵐᵒᵖ from t) • g x)
          rw [tmul_smul Q r s ((show Sᵐᵒᵖ from t) • g x)]
          rw [g.map_smul,mul_smul,smul_comm r s,smul_comm r (show Sᵐᵒᵖ from t)] }

lemma rightFreeEvaluate_extend (g : L →ₗ[R] Obj Q) :
    rightFreeEvaluate L Q (rightFreeExtend L Q g) = g := by
  ext x
  change (1:Sᵐᵒᵖ) • g x = g x
  rw [one_smul]

lemma rightFreeExtend_evaluate (f : rightFreeObj (k := k) (S := S) L ⟶ Q) :
    rightFreeExtend L Q (rightFreeEvaluate L Q f) = f := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext; intro z
  induction z using OAI.tensorInductionOn with
  | add x y hx hy => erw [map_add,map_add,hx,hy]
  | tmul x s =>
    change (((1:R) ⊗ₜ[k] (show Sᵐᵒᵖ from s)) : Alg k R S) • f (x ⊗ₜ[k] (rightRegularOne (S := S))) =
      f (x ⊗ₜ[k] s)
    erw [← f.hom.map_smul]
    congr 1
    change ((1:R) • x) ⊗ₜ[k] ((show Sᵐᵒᵖ from s) • rightRegularOne) = x ⊗ₜ[k] s
    rw [one_smul]
    congr 1
    exact mul_one (show Sᵐᵒᵖ from s)

def rightFreeHomEquiv : (rightFreeObj (k := k) (S := S) L ⟶ Q) ≃ₗ[k] (L →ₗ[R] Obj Q) where
  toFun := rightFreeEvaluate L Q
  invFun := rightFreeExtend L Q
  left_inv := rightFreeExtend_evaluate L Q
  right_inv := rightFreeEvaluate_extend L Q
  map_add' f g := by ext x; rfl
  map_smul' c f := by ext x; rfl

lemma rightFreeEvaluate_natural {L' : ModuleCat R} (a : L' ⟶ L)
    (f : rightFreeObj (k := k) (S := S) L ⟶ Q) :
    rightFreeEvaluate L' Q ((rightFreeFunctor (k := k) (S := S)).map a ≫ f) =
      (rightFreeEvaluate L Q f).comp a.hom := by
  ext x
  rfl

end Tachikawa.Enveloping



namespace Tachikawa.Enveloping
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
variable [FiniteDimensional k R]

def rightFreeUnderlying (M : ModuleCat R) :
    rightFreeObj (k := k) (S := S) M ≃ₗ[k] (M ⊗[k] rightRegularObj (S := S)) :=
  moduleCatUnderlyingEquiv (k := k) (R := Alg k R S)
    (OuterTensor.Obj k R Sᵐᵒᵖ M (rightRegularObj (S := S)))

def rightFreeRestrictionUnderlying (M : ModuleCat R) :
    (rightFunctor (k := k) (S := S)).obj (rightFreeObj M) ≃ₗ[k]
      (M ⊗[k] rightRegularObj (S := S)) :=
  (moduleCatUnderlyingEquiv (k := k) (R := Sᵐᵒᵖ)
    (Obj (rightFreeObj (k := k) (S := S) M))).trans
    (rightFreeUnderlying M)

def coindTensorUnderlying (M : ModuleCat R) :
    rightFreeObj (k := k) (S := S) ((LeftCoinduced.J (k := k)).obj M) ≃ₗ[k]
      (coindEndo (k := k)).obj (rightFreeObj (k := k) (S := S) M) :=
  (rightFreeUnderlying _).trans
    ((TensorProduct.congr (LeftCoinduced.underlying M) (LinearEquiv.refl k _)).trans
      ((rTensorHomEquivHomRTensor k R M (rightRegularObj (S := S))).trans
        (((rightFreeRestrictionUnderlying M).symm.congrRight).trans
          (coindUnderlying _).symm)))

lemma coindTensorUnderlying_tmul (M : ModuleCat R)
    (φ : (LeftCoinduced.J (k := k)).obj M) (s : rightRegularObj (S := S)) (r : R) :
    (coindUnderlying _ (coindTensorUnderlying (S := S) M (φ ⊗ₜ[k] s))) r =
      (LeftCoinduced.underlying M φ r) ⊗ₜ[k] s := by
  change rTensorHomEquivHomRTensor k R M (rightRegularObj (S := S))
    ((LeftCoinduced.underlying M φ) ⊗ₜ[k] s) r = _
  rw [rTensorHomEquivHomRTensor_apply]
  rfl

def coindTensorEquiv (M : ModuleCat R) :
    rightFreeObj (k := k) (S := S) ((LeftCoinduced.J (k := k)).obj M) ≃ₗ[Alg k R S]
      (coindEndo (k := k)).obj (rightFreeObj (k := k) (S := S) M) where
  __ := (coindTensorUnderlying M).toAddEquiv
  map_smul' a z := by
    apply (coindUnderlying _).injective
    change (coindUnderlying _ (coindTensorUnderlying M (OuterTensor.action k R Sᵐᵒᵖ _ _ a z))) =
      (action (k := k) (R := R) (S := S)
        (Coind (k := k) (R := R) ((rightFunctor (k := k)).obj (rightFreeObj M))) a)
          (coindUnderlying _ (coindTensorUnderlying M z))
    induction a using OAI.tensorInductionOn with
    | add a b ha hb =>
      erw [map_add,LinearMap.add_apply,map_add,map_add,map_add,LinearMap.add_apply,ha,hb]
      rfl
    | tmul a b =>
      induction z using OAI.tensorInductionOn with
      | add x y hx hy =>
        let forward := (coindUnderlying ((rightFunctor (k := k)).obj
          (rightFreeObj (S := S) M))).toLinearMap.comp (coindTensorUnderlying M).toLinearMap
        let outer := OuterTensor.action k R Sᵐᵒᵖ
          ((LeftCoinduced.J (k := k)).obj M) (rightRegularObj (S := S)) (a ⊗ₜ[k] b)
        let target := action (k := k) (R := R) (S := S)
          (Coind (k := k) (R := R) ((rightFunctor (k := k)).obj (rightFreeObj (S := S) M)))
            (a ⊗ₜ[k] b)
        change forward (outer (x+y)) = target (forward (x+y))
        change forward (outer x) = target (forward x) at hx
        change forward (outer y) = target (forward y) at hy
        exact (congrArg forward (outer.map_add x y)).trans
          ((forward.map_add _ _).trans
            ((congrArg₂ (· + ·) hx hy).trans
              ((target.map_add _ _).symm.trans
                (congrArg target (forward.map_add x y).symm))))
      | tmul φ s =>
        apply LinearMap.ext
        intro r
        rw [show OuterTensor.action k R Sᵐᵒᵖ _ _ (a ⊗ₜ[k] b) (φ ⊗ₜ[k] s) =
          (a • φ) ⊗ₜ[k] (b • s) from rfl,coindTensorUnderlying_tmul]
        change (LeftCoinduced.underlying M (a • φ) r) ⊗ₜ[k] (b • s) =
          b • (coindUnderlying _ (coindTensorUnderlying M (φ ⊗ₜ[k] s)) (r*a))
        rw [coindTensorUnderlying_tmul]
        change ((LeftCoinduced.underlying M φ) (r*a)) ⊗ₜ[k] (b • s) =
          ((1:R) • ((LeftCoinduced.underlying M φ) (r*a))) ⊗ₜ[k] (b • s)
        rw [one_smul]

def coindTensorIso (M : ModuleCat R) :
    rightFreeObj (k := k) (S := S) ((LeftCoinduced.J (k := k)).obj M) ≅
      (coindEndo (k := k)).obj (rightFreeObj (k := k) (S := S) M) :=
  (coindTensorEquiv M).toModuleIso

lemma coindTensor_unit (M : ModuleCat R) :
    (rightFreeFunctor (k := k) (S := S)).map ((LeftCoinduced.unit (k := k)).app M) ≫
      (coindTensorIso M).hom = coindUnit (rightFreeObj M) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  induction z using OAI.tensorInductionOn with
  | add x y hx hy => erw [map_add,map_add,hx,hy]
  | tmul x s =>
    apply (coindUnderlying _).injective
    apply LinearMap.ext
    intro r
    change coindUnderlying _ (coindTensorUnderlying M
      (((LeftCoinduced.unit (k := k)).app M x) ⊗ₜ[k] s)) r = _
    rw [coindTensorUnderlying_tmul]
    change (r • x) ⊗ₜ[k] s = (r • x) ⊗ₜ[k] ((1:Sᵐᵒᵖ) • s)
    rw [one_smul]

end Tachikawa.Enveloping



namespace Tachikawa.Enveloping
open CategoryTheory CategoryTheory.Abelian
open scoped TensorProduct ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  [FiniteDimensional k R] [FiniteDimensional k S]

lemma regular_coind_ext_zero (N : ModuleCat Rᵐᵒᵖ) (n : ℕ) :
    Subsingleton (Ext (regular (k := k) (R := R))
      (coindObj (k := k) (R := R) N) (n+1)) := by
  let : Module.Projective Rᵐᵒᵖ R :=
    Module.Projective.of_equiv (MulOpposite.opLinearEquiv Rᵐᵒᵖ).symm
  let : Module.Projective Rᵐᵒᵖ (Obj (regular (k := k) (R := R))) :=
    Module.Projective.of_equiv (regularRightEquiv (k := k) (R := R)).symm
  let M := regularFinite (k := k) (R := R)
  let : Module.Projective Rᵐᵒᵖ (Obj M.obj) :=
    show Module.Projective Rᵐᵒᵖ (Obj (regular (k := k) (R := R))) from inferInstance
  exact coind_ext_zero M N n

end Tachikawa.Enveloping



namespace Tachikawa.Enveloping
open CategoryTheory CategoryTheory.Abelian
open scoped TensorProduct ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  [FiniteDimensional k R]

omit [FiniteDimensional k R] in
lemma rightFree_map_exact {A B C : ModuleCat R} (f : A ⟶ B) (g : B ⟶ C)
    (h : Function.Exact f g) :
    Function.Exact ((rightFreeFunctor (k := k) (S := S)).map f)
      ((rightFreeFunctor (k := k) (S := S)).map g) :=
  Module.Flat.rTensor_exact (rightRegularObj (S := S))
    (show Function.Exact (f.hom.restrictScalars k) (g.hom.restrictScalars k) from h)

omit [FiniteDimensional k R] in
lemma rightFree_map_surjective {A B : ModuleCat R} (f : A ⟶ B) (h : Function.Surjective f) :
    Function.Surjective ((rightFreeFunctor (k := k) (S := S)).map f) :=
  LinearMap.rTensor_surjective (rightRegularObj (S := S))
    (show Function.Surjective (f.hom.restrictScalars k) from h)

variable (M : FiniteModule k R)

def rightFreeResolution : ProjectiveResolution (rightFreeObj (k := k) (S := S) M.obj) := by
  let F := rightFreeFunctor (k := k) (R := R) (S := S)
  apply resolutionOfExact _ (fun n => F.obj (ModuleCat.of R (M.posTerm n)))
    (fun n => F.map (ModuleCat.ofHom (M.posDifferential n)))
    (F.map (ModuleCat.ofHom M.cover.map))
  · intro n
    exact rightFree_map_exact _ _ (M.pos_exact n)
  · exact rightFree_map_exact _ _ M.pos_augmentation_exact
  · exact rightFree_map_surjective _ M.cover.surjective
  · intro n
    let : Module.Projective (Alg k R S) (F.obj (ModuleCat.of R (M.posTerm n))) :=
      OuterTensor.projective k R Sᵐᵒᵖ (ModuleCat.of R (M.posTerm n))
        (rightRegularObj (S := S))
    infer_instance

lemma rightFreeResolution_d (n : ℕ) :
    (rightFreeResolution (S := S) M).complex.d (n+1) n =
      (rightFreeFunctor (k := k) (S := S)).map (ModuleCat.ofHom (M.posDifferential n)) := by
  dsimp [rightFreeResolution, resolutionOfExact]
  exact ChainComplex.of_d _ _ _

lemma rightFree_ext_zero (Q : ModuleCat (Alg k R S)) [Module.Injective R (Obj Q)] (n : ℕ) :
    Subsingleton (Ext (rightFreeObj (k := k) (S := S) M.obj) Q (n+1)) := by
  let P := M.projectiveResolution
  let T := rightFreeResolution (S := S) M
  have hd (i : ℕ) : P.complex.d (i+1) i = ModuleCat.ofHom (M.posDifferential i) := by
    dsimp [P, FiniteModule.projectiveResolution, resolutionOfExact]
    exact ChainComplex.of_d _ _ _
  let : Injective (ModuleCat.of R (Obj Q)) := Module.injective_object_of_injective_module R (Obj Q)
  let : Subsingleton (Ext M.obj (ModuleCat.of R (Obj Q)) (n+1)) :=
    Ext.subsingleton_of_injective _ _ n
  apply ext_subsingleton_of_boundaries T n
  intro f hf
  let f' : P.complex.X (n+1) ⟶ ModuleCat.of R (Obj Q) :=
    ModuleCat.ofHom (rightFreeEvaluate (P.complex.X (n+1)) Q f)
  have hf' : P.complex.d (n+2) (n+1) ≫ f' = 0 := by
    rw [hd]
    apply ModuleCat.hom_ext
    change (rightFreeEvaluate _ Q f).comp (M.posDifferential (n+1)) = 0
    rw [rightFreeResolution_d] at hf
    exact congrArg (rightFreeEvaluate (ModuleCat.of R (M.posTerm (n+2))) Q) hf
  obtain ⟨g,hg⟩ := boundaries_of_ext_subsingleton P n f' hf'
  let g' : T.complex.X n ⟶ Q := rightFreeExtend _ Q g.hom
  refine ⟨g', ?_⟩
  apply (rightFreeHomEquiv _ Q).injective
  change rightFreeEvaluate _ Q (T.complex.d (n+1) n ≫ g') = rightFreeEvaluate _ Q f
  erw [rightFreeResolution_d, rightFreeEvaluate_natural]
  rw [show rightFreeEvaluate _ Q g' = g.hom from rightFreeEvaluate_extend _ _ _]
  rw [hd] at hg
  exact ModuleCat.hom_ext_iff.mp hg

end Tachikawa.Enveloping



namespace Tachikawa.Enveloping
open CategoryTheory CategoryTheory.Abelian
open scoped TensorProduct ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R] [FiniteDimensional k R]

def ordinaryOuterObj : ModuleCat (Alg k R R) :=
  rightFreeObj (k := k) (S := R) (dualLeftObj (k := k) (R := R))

lemma outer_dual_ext_zero (n : ℕ) :
    Subsingleton (Ext (ordinaryOuterObj (k := k) (R := R)) (dualRegularObj (k := k) (R := R)) (n+1)) :=
  rightFree_ext_zero (dualLeftFinite (k := k) (R := R)) (dualRegularObj (k := k) (R := R)) n

end Tachikawa.Enveloping

end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Induction
attribute [-instance] _root_.OAI.Tachikawa.DownHom.instAddCommGroupCochain _root_.OAI.Tachikawa.DownHom.instModuleCochain _root_.OAI.Tachikawa.Enveloping.eval_finite _root_.OAI.Tachikawa.Enveloping.instLinearModuleCatAlgEvaluation _root_.OAI.Tachikawa.HomBimodule.instFiniteDimensionalCarrierAlgObj _root_.OAI.Tachikawa.Triangular.instAddCommGroupOff _root_.OAI.Tachikawa.Triangular.instIsScalarTowerMulOppositeProdOff _root_.OAI.Tachikawa.Triangular.instIsScalarTowerProdOff _root_.OAI.Tachikawa.Triangular.instModuleMulOppositeProdOff _root_.OAI.Tachikawa.Triangular.instModuleOff _root_.OAI.Tachikawa.Triangular.instModuleProdOff _root_.OAI.Tachikawa.Triangular.instSMulCommClassProdMulOppositeOff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace Tachikawa.Enveloping
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R] [FiniteDimensional k R]

def ordinaryEndEquiv : ordinaryOuterObj (k := k) (R := R) ≃ₗ[k] (R →ₗ[k] R) :=
  (rightFreeUnderlying (dualLeftObj (k := k) (R := R))).trans
    ((dualOuterUnderlying (rightRegularObj (S := R))).trans (rightRegularEndUnderlying (k := k) (R := R)).congrRight)

lemma ordinaryEndEquiv_tmul (φ : dualLeftObj (k := k) (R := R))
    (s : rightRegularObj (S := R)) (a : R) :
    ordinaryEndEquiv (k := k) (R := R) (φ ⊗ₜ[k] s) a =
      (show Module.Dual k R from φ) a • (show Rᵐᵒᵖ from s).unop := by
  change rightRegularEndUnderlying (k := k) (R := R) (dualOuterUnderlying (rightRegularObj (S := R)) (φ ⊗ₜ[k] s) a) = _
  rw [dualOuterUnderlying_tmul, map_smul]
  rfl

lemma ordinaryEndEquiv_left (a : R) (z : ordinaryOuterObj (k := k) (R := R)) :
    ordinaryEndEquiv (((a ⊗ₜ[k] (1:Rᵐᵒᵖ)) : Alg k R R) • z) =
      (ordinaryEndEquiv z).comp (LinearMap.mulRight k a) := by
  induction z using OAI.tensorInductionOn with
  | add x y hx hy =>
    erw [smul_add,map_add,map_add,hx,hy,LinearMap.add_comp]
  | tmul φ s =>
    apply LinearMap.ext; intro c
    change ordinaryEndEquiv ((a • φ) ⊗ₜ[k] ((1:Rᵐᵒᵖ) • s)) c = ordinaryEndEquiv (φ ⊗ₜ[k] s) (c*a)
    rw [one_smul,ordinaryEndEquiv_tmul,ordinaryEndEquiv_tmul]
    rfl

lemma ordinaryEndEquiv_right (a : R) (z : ordinaryOuterObj (k := k) (R := R)) :
    ordinaryEndEquiv (((1:R) ⊗ₜ[k] MulOpposite.op a : Alg k R R) • z) =
      (LinearMap.mulRight k a).comp (ordinaryEndEquiv z) := by
  induction z using OAI.tensorInductionOn with
  | add x y hx hy =>
    erw [smul_add,map_add,map_add,hx,hy,LinearMap.comp_add]
  | tmul φ s =>
    apply LinearMap.ext; intro c
    change ordinaryEndEquiv (((1:R) • φ) ⊗ₜ[k] (MulOpposite.op a • s)) c = (ordinaryEndEquiv (φ ⊗ₜ[k] s) c)*a
    rw [one_smul,ordinaryEndEquiv_tmul,ordinaryEndEquiv_tmul]
    change (show Module.Dual k R from φ) c • ((show Rᵐᵒᵖ from s).unop * a) =
      ((show Module.Dual k R from φ) c • (show Rᵐᵒᵖ from s).unop)*a
    exact Algebra.smul_mul_assoc _ _ _ |>.symm




def ordinaryAlpha (f : regular (k := k) (R := R) ⟶ ordinaryOuterObj (k := k) (R := R)) :
    R →ₗ[k] (R →ₗ[k] R) :=
  ordinaryEndEquiv.toLinearMap.comp ((f.hom.restrictScalars k).comp regularUnderlyingEquiv.symm.toLinearMap)

lemma ordinaryAlpha_left (f : regular (k := k) (R := R) ⟶ ordinaryOuterObj (k := k) (R := R))
    (a b : R) : ordinaryAlpha f (a*b) = (ordinaryAlpha f b).comp (LinearMap.mulRight k a) := by
  have h := f.hom.map_smul (a ⊗ₜ[k] (1:Rᵐᵒᵖ)) (regularUnderlyingEquiv.symm b)
  have hpre : (a ⊗ₜ[k] (1:Rᵐᵒᵖ)) • (regularUnderlyingEquiv (k := k) (R := R)).symm b =
      regularUnderlyingEquiv.symm (a*b) := by change a*(b*1)=a*b; rw [mul_one]
  rw [hpre] at h
  exact (congrArg ordinaryEndEquiv h).trans (ordinaryEndEquiv_left _ _)

lemma ordinaryAlpha_right (f : regular (k := k) (R := R) ⟶ ordinaryOuterObj (k := k) (R := R))
    (a b : R) : ordinaryAlpha f (a*b) = (LinearMap.mulRight k b).comp (ordinaryAlpha f a) := by
  have h := f.hom.map_smul ((1:R) ⊗ₜ[k] MulOpposite.op b) (regularUnderlyingEquiv.symm a)
  have hpre : ((1:R) ⊗ₜ[k] MulOpposite.op b) • (regularUnderlyingEquiv (k := k) (R := R)).symm a =
      regularUnderlyingEquiv.symm (a*b) := by change 1*(a*b)=a*b; rw [one_mul]
  rw [hpre] at h
  exact (congrArg ordinaryEndEquiv h).trans (ordinaryEndEquiv_right _ _)

def ordinaryBeta (f : ordinaryOuterObj (k := k) (R := R) ⟶ dualRegularObj (k := k) (R := R)) :
    (R →ₗ[k] R) →ₗ[k] Module.Dual k R :=
  dualRegularUnderlying.toLinearMap.comp ((f.hom.restrictScalars k).comp ordinaryEndEquiv.symm.toLinearMap)

lemma ordinaryBeta_end (f : ordinaryOuterObj (k := k) (R := R) ⟶ dualRegularObj (k := k) (R := R))
    (z : ordinaryOuterObj (k := k) (R := R)) :
    ordinaryBeta f (ordinaryEndEquiv z) = dualRegularUnderlying (f z) := by
  simp only [ordinaryBeta,LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.symm_apply_apply]
  rfl

lemma ordinaryBeta_left (f : ordinaryOuterObj (k := k) (R := R) ⟶ dualRegularObj (k := k) (R := R))
    (a : R) (F : R →ₗ[k] R) :
    ordinaryBeta f (F.comp (LinearMap.mulRight k a)) =
      (ordinaryBeta f F).comp (LinearMap.mulRight k a) := by
  obtain ⟨z,rfl⟩ := ordinaryEndEquiv (k := k) (R := R) |>.surjective F
  rw [← ordinaryEndEquiv_left,ordinaryBeta_end,ordinaryBeta_end]
  rw [f.hom.map_smul,dualRegularUnderlying_left]

lemma ordinaryBeta_right (f : ordinaryOuterObj (k := k) (R := R) ⟶ dualRegularObj (k := k) (R := R))
    (a : R) (F : R →ₗ[k] R) :
    ordinaryBeta f ((LinearMap.mulRight k a).comp F) =
      (ordinaryBeta f F).comp (LinearMap.mulLeft k a) := by
  obtain ⟨z,rfl⟩ := ordinaryEndEquiv (k := k) (R := R) |>.surjective F
  rw [← ordinaryEndEquiv_right,ordinaryBeta_end,ordinaryBeta_end]
  rw [f.hom.map_smul,dualRegularUnderlying_right]

lemma ordinaryBeta_alpha
    (a : regular (k := k) (R := R) ⟶ ordinaryOuterObj (k := k) (R := R))
    (b : ordinaryOuterObj (k := k) (R := R) ⟶ dualRegularObj (k := k) (R := R)) (x : R) :
    ordinaryBeta b (ordinaryAlpha a x) =
      dualRegularUnderlying ((a ≫ b) (regularUnderlyingEquiv.symm x)) :=
  ordinaryBeta_end b _

end Tachikawa.Enveloping



namespace Tachikawa
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k : Type} [Field k] (q : k)

lemma characterBimoduleMap_apply (x : B q) :
    Enveloping.dualRegularUnderlying (characterBimoduleMap q
      (Enveloping.regularUnderlyingEquiv.symm x)) = characterMapB q x := rfl

variable [CharP k 2]

lemma ordinary_morphism_factorization_pf_zero
    (a : Enveloping.regular (k := k) (R := B q) ⟶ Enveloping.ordinaryOuterObj (k := k) (R := B q))
    (b : Enveloping.ordinaryOuterObj (k := k) (R := B q) ⟶ Enveloping.dualRegularObj (k := k) (R := B q)) :
    Enveloping.dualRegularUnderlying ((a ≫ b) (Enveloping.regularUnderlyingEquiv.symm 1)) (pf q) = 0 := by
  rw [← Enveloping.ordinaryBeta_alpha]
  exact ordinary_factorization_pf_zero q (Enveloping.ordinaryAlpha a)
    (Enveloping.ordinaryAlpha_left a) (Enveloping.ordinaryAlpha_right a)
    (Enveloping.ordinaryBeta b) (Enveloping.ordinaryBeta_left b) (Enveloping.ordinaryBeta_right b)

end Tachikawa



namespace Tachikawa.Construction
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k : Type} [Field k] (q : k)

lemma sigma_inclusionB (H : k) (hH : H ≠ 0) (a : B q) :
    sigma q H hH (inclusionB q a) = inclusionB q a := by
  induction a using OAI.tensorInductionOn with
  | add x y hx hy => simp only [map_add,hx,hy]
  | tmul x y =>
    change TrivialExtension.scaleDual H hH (inclusionC q x) ⊗ₜ[k]
      TrivialExtension.scaleDual H hH (inclusionC q y) = _
    have h (x : C k q) : TrivialExtension.scaleDual H hH (inclusionC q x) = inclusionC q x := by
      apply TrivSqZeroExt.ext
      · rfl
      · exact smul_zero _
    rw [h,h]
    rfl

end Tachikawa.Construction



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Perfect
attribute [-instance] _root_.OAI.Tachikawa.DownHom.instAddCommGroupCochain _root_.OAI.Tachikawa.Enveloping.eval_finite _root_.OAI.Tachikawa.Enveloping.instLinearModuleCatAlgEvaluation _root_.OAI.Tachikawa.HomBimodule.instFiniteDimensionalCarrierAlgObj _root_.OAI.Tachikawa.Triangular.instAddCommGroupOff _root_.OAI.Tachikawa.Triangular.instIsScalarTowerMulOppositeProdOff _root_.OAI.Tachikawa.Triangular.instIsScalarTowerProdOff _root_.OAI.Tachikawa.Triangular.instModuleMulOppositeProdOff _root_.OAI.Tachikawa.Triangular.instModuleOff _root_.OAI.Tachikawa.Triangular.instModuleProdOff _root_.OAI.Tachikawa.Triangular.instSMulCommClassProdMulOppositeOff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace Tachikawa.Enveloping
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]

lemma restrictedOuterRegular_action (φ : R →ₐ[k] S) (a : Alg k R R)
    (z : ((AlgebraInduction.res φ).obj (ModuleCat.of S S)) ⊗[k]
      ((AlgebraInduction.res φ.op).obj (ModuleCat.of Sᵐᵒᵖ Sᵐᵒᵖ))) :
    TensorProduct.congr (resRegularUnderlying φ) (resRegularUnderlying φ.op)
      ((OuterTensor.action k R Rᵐᵒᵖ _ _ a) z) =
    envelopingMap φ a *
      TensorProduct.congr (resRegularUnderlying φ) (resRegularUnderlying φ.op) z := by
  induction a using OAI.tensorInductionOn with
  | add a b ha hb => rw [map_add,LinearMap.add_apply,map_add,ha,hb,map_add,add_mul]
  | tmul a b =>
    induction z using OAI.tensorInductionOn with
    | add x y hx hy => rw [map_add,map_add,hx,hy,map_add,mul_add]
    | tmul x y =>
      change (φ a * (show S from x)) ⊗ₜ[k] (φ.op b * (show Sᵐᵒᵖ from y)) =
        (φ a ⊗ₜ[k] φ.op b) * ((show S from x) ⊗ₜ[k] (show Sᵐᵒᵖ from y))
      exact (Algebra.TensorProduct.tmul_mul_tmul _ _ _ _).symm

end Tachikawa.Enveloping



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_DerivedDescent
attribute [-instance] _root_.OAI.Tachikawa.DownHom.instAddCommGroupCochain _root_.OAI.Tachikawa.Enveloping.eval_finite _root_.OAI.Tachikawa.Enveloping.instLinearModuleCatAlgEvaluation _root_.OAI.Tachikawa.HomBimodule.instFiniteDimensionalCarrierAlgObj _root_.OAI.Tachikawa.Triangular.instAddCommGroupOff _root_.OAI.Tachikawa.Triangular.instIsScalarTowerMulOppositeProdOff _root_.OAI.Tachikawa.Triangular.instIsScalarTowerProdOff _root_.OAI.Tachikawa.Triangular.instModuleMulOppositeProdOff _root_.OAI.Tachikawa.Triangular.instModuleOff _root_.OAI.Tachikawa.Triangular.instModuleProdOff _root_.OAI.Tachikawa.Triangular.instSMulCommClassProdMulOppositeOff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace Tachikawa.Enveloping
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]

abbrev coindComplex (P : CochainComplex (ModuleCat (Alg k R S)) ℤ) :=
  ((coindEndo (k := k)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P

abbrev cokerComplex (P : CochainComplex (ModuleCat (Alg k R S)) ℤ) :=
  ((coindCoker (k := k)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P

def coindComplexUnit (P : CochainComplex (ModuleCat (Alg k R S)) ℤ) : P ⟶ coindComplex P where
  f i := coindUnit (P.X i)
  comm' i j _ := (coindUnitNat.naturality (P.d i j)).symm

def coindComplexπ (P : CochainComplex (ModuleCat (Alg k R S)) ℤ) : coindComplex P ⟶ cokerComplex P where
  f i := coindπ (P.X i)
  comm' i j _ := ((cokernel.π (coindUnitNat (k := k))).naturality (P.d i j)).symm

def coindComplexShort (P : CochainComplex (ModuleCat (Alg k R S)) ℤ) :
    ShortComplex (CochainComplex (ModuleCat (Alg k R S)) ℤ) :=
  ShortComplex.mk (coindComplexUnit P) (coindComplexπ P) (by
    apply HomologicalComplex.Hom.ext
    funext i
    exact coindUnit_π (P.X i))

lemma coindComplexShort_exact (P : CochainComplex (ModuleCat (Alg k R S)) ℤ) :
    (coindComplexShort P).ShortExact := by
  apply shortExact_of_degreewise_shortExact
  intro i
  exact coindShort_exact (P.X i)

end Tachikawa.Enveloping



namespace Tachikawa
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open scoped ModuleCat.Algebra
attribute [instance] IndReplacement.quasiIso

end Tachikawa



namespace Tachikawa.Enveloping
open CategoryTheory HomologicalComplex
open scoped TensorProduct ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  [FiniteDimensional k R] (φ : R →ₐ[k] S)

def restrictedSingleMap {U : ModuleCat.{0} (Alg k S S)} {N : ModuleCat.{0} (Alg k R R)}
    (b : (AlgebraInduction.res (envelopingMap φ)).obj U ⟶ N) :
    ((AlgebraInduction.res (envelopingMap φ)).mapHomologicalComplex (.up ℤ)).obj
      ((CochainComplex.singleFunctor _ 0).obj U) ⟶ (CochainComplex.singleFunctor _ 0).obj N :=
  (singleMapHomologicalComplex (AlgebraInduction.res (envelopingMap φ)) (.up ℤ) 0).hom.app U ≫
    (CochainComplex.singleFunctor _ 0).map b

end Tachikawa.Enveloping



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_FiniteCoinduction
attribute [-instance] _root_.OAI.Tachikawa.DownHom.instAddCommGroupCochain _root_.OAI.Tachikawa.Enveloping.eval_finite _root_.OAI.Tachikawa.Enveloping.instLinearModuleCatAlgEvaluation _root_.OAI.Tachikawa.HomBimodule.instFiniteDimensionalCarrierAlgObj _root_.OAI.Tachikawa.Triangular.instAddCommGroupOff _root_.OAI.Tachikawa.Triangular.instIsScalarTowerMulOppositeProdOff _root_.OAI.Tachikawa.Triangular.instIsScalarTowerProdOff _root_.OAI.Tachikawa.Triangular.instModuleMulOppositeProdOff _root_.OAI.Tachikawa.Triangular.instModuleOff _root_.OAI.Tachikawa.Triangular.instModuleProdOff _root_.OAI.Tachikawa.Triangular.instSMulCommClassProdMulOppositeOff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace Tachikawa.Enveloping
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
variable [FiniteDimensional k R]

instance rightFree_preservesFiniteColimits : PreservesFiniteColimits (rightFreeFunctor (k := k) (R := R) (S := S)) :=
  inferInstanceAs (PreservesFiniteColimits ((OuterTensor.bifunctor k R Sᵐᵒᵖ).flip.obj (rightRegularObj (S := S))))
instance rightFree_preservesFiniteLimits : PreservesFiniteLimits (rightFreeFunctor (k := k) (R := R) (S := S)) :=
  inferInstanceAs (PreservesFiniteLimits ((OuterTensor.bifunctor k R Sᵐᵒᵖ).flip.obj (rightRegularObj (S := S))))

def coindCokerTensorIso (M : ModuleCat R) :
    rightFreeObj (k := k) (S := S) ((LeftCoinduced.C (k := k)).obj M) ≅
      (coindCoker (k := k)).obj (rightFreeObj (k := k) (S := S) M) := by
  let F := rightFreeFunctor (k := k) (R := R) (S := S)
  have h := LeftCoinduced.short_exact (k := k) M
  let := h.mono_f
  let := h.epi_g
  have hF : ((LeftCoinduced.short (k := k) M).map F).ShortExact := h.map F
  refine CokernelCofork.mapIsoOfIsColimit hF.gIsCokernel
    (coindShort_exact (rightFreeObj (k := k) (S := S) M)).gIsCokernel ?_
  refine Arrow.isoMk (Iso.refl _) (coindTensorIso M) ?_
  simpa only [F, LeftCoinduced.short, coindShort, ShortComplex.map, Arrow.mk,
    Iso.refl_hom, Category.id_comp] using (coindTensor_unit (k := k) (S := S) M).symm

def coindIterateTensorIso (M : ModuleCat R) : ∀ n : ℕ,
    rightFreeObj (k := k) (S := S) ((LeftCoinduced.iterate (k := k) n).obj M) ≅
      (coindIterate (k := k) n).obj (rightFreeObj (k := k) (S := S) M)
  | 0 => Iso.refl _
  | n+1 => coindCokerTensorIso ((LeftCoinduced.iterate (k := k) n).obj M) ≪≫
      (coindCoker (k := k)).mapIso (coindIterateTensorIso M n)

def coindTermTensorIso (M : ModuleCat R) (n : ℕ) :
    rightFreeObj (k := k) (S := S)
      ((LeftCoinduced.J (k := k)).obj ((LeftCoinduced.iterate (k := k) n).obj M)) ≅
      coindTerm (rightFreeObj (k := k) (S := S) M) n :=
  coindTensorIso ((LeftCoinduced.iterate (k := k) n).obj M) ≪≫
    (coindEndo (k := k)).mapIso (coindIterateTensorIso M n)

end Tachikawa.Enveloping



namespace Tachikawa.Enveloping
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]

def regularOuterUnderlying :
    rightFreeObj (k := k) (S := S) (leftRegularObj (R := R)) ≃ₗ[k] Alg k R S :=
  (rightFreeUnderlying _).trans
    (TensorProduct.congr (leftRegularUnderlying (k := k) (R := R))
      (rightRegularUnderlying (k := k) (S := S)))

def regularOuterEquiv :
    rightFreeObj (k := k) (S := S) (leftRegularObj (R := R)) ≃ₗ[Alg k R S] Alg k R S where
  __ := (regularOuterUnderlying (k := k) (R := R) (S := S)).toAddEquiv
  map_smul' a z := by
    change regularOuterUnderlying (OuterTensor.action k R Sᵐᵒᵖ _ _ a z) =
      a * regularOuterUnderlying z
    induction a using OAI.tensorInductionOn with
    | add a b ha hb => erw [map_add,LinearMap.add_apply,map_add,ha,hb,add_mul]
    | tmul a b =>
      induction z using OAI.tensorInductionOn with
      | add x y hx hy => erw [map_add,map_add,hx,hy,map_add,mul_add]
      | tmul x y =>
        change (a*(show R from x)) ⊗ₜ[k] (b*(show Sᵐᵒᵖ from y)) =
          (a ⊗ₜ[k] b) * ((show R from x) ⊗ₜ[k] (show Sᵐᵒᵖ from y))
        exact (Algebra.TensorProduct.tmul_mul_tmul _ _ _ _).symm

def regularOuterIso :
    rightFreeObj (k := k) (S := S) (leftRegularObj (R := R)) ≅ ModuleCat.of (Alg k R S) (Alg k R S) :=
  (regularOuterEquiv (k := k) (R := R) (S := S)).toModuleIso

lemma finiteProjective_inAdd_outer (M : ModuleCat (Alg k R S))
    [Module.Finite (Alg k R S) M] [Module.Projective (Alg k R S) M] :
    InAdd (rightFreeObj (k := k) (S := S) (leftRegularObj (R := R))) M := by
  obtain ⟨n,⟨r⟩⟩ := finiteProjective_inAdd M
  let e := biproduct.mapIso (fun _ : Fin n => (regularOuterIso (k := k) (R := R) (S := S)).symm)
  exact ⟨n,⟨r.trans e.retract⟩⟩

end Tachikawa.Enveloping



namespace Tachikawa.Enveloping
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]

attribute [instance] CoindReplacement.quasiIso

def coindReplacement : (n : ℕ) → (P : CochainComplex (ModuleCat (Alg k R S)) ℤ) → CoindReplacement P
  | 0, P => ⟨P,𝟙 P,inferInstance⟩
  | n+1, P =>
    let t := coindReplacement n (cokerComplex P)
    { complex := mappingCocone (coindComplexπ P ≫ t.map)
      map := shortExactReplacementMap (coindComplexShort P) t.map
      quasiIso := by
        exact @shortExactReplacementMap_quasiIso _ _ _ (coindComplexShort P)
          (coindComplexShort_exact P) _ t.map t.quasiIso }

def CoindGoodTerms (W : ModuleCat (Alg k R S)) :
    ℕ → CochainComplex (ModuleCat (Alg k R S)) ℤ → Prop
  | 0, P => ∀ i, InAdd W (P.X i)
  | n+1, P => (∀ i, InAdd W ((coindComplex P).X i)) ∧ CoindGoodTerms W n (cokerComplex P)

lemma coindReplacement_terms (W : ModuleCat (Alg k R S)) (n : ℕ)
    (P : CochainComplex (ModuleCat (Alg k R S)) ℤ) (h : CoindGoodTerms W n P) :
    ∀ i, InAdd W ((coindReplacement n P).complex.X i) := by
  induction n generalizing P with
  | zero => exact h
  | succ n ih =>
    exact mappingCocone_inAdd _ h.1 (ih (cokerComplex P) h.2)

end Tachikawa.Enveloping



namespace Tachikawa.Enveloping
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]

lemma coindReplacement_bounded (n : ℕ)
    (P : CochainComplex (ModuleCat (Alg k R S)) ℤ) (l u : ℤ)
    (hP : ∀ i, i < l ∨ u < i → IsZero (P.X i)) :
    ∀ i, i < l ∨ u + n < i → IsZero ((coindReplacement n P).complex.X i) := by
  induction n generalizing P with
  | zero => simpa only [coindReplacement, Nat.cast_zero, add_zero] using hP
  | succ n ih =>
    intro i hi
    apply mappingCocone_isZero_X
    · exact (coindEndo (k := k)).map_isZero (hP i (by omega))
    · apply ih (cokerComplex P)
      · intro j hj
        exact (coindCoker (k := k)).map_isZero (hP j hj)
      · omega

end Tachikawa.Enveloping



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Delta
attribute [-instance] _root_.OAI.Tachikawa.DownHom.instAddCommGroupCochain _root_.OAI.Tachikawa.Triangular.instAddCommGroupOff _root_.OAI.Tachikawa.Triangular.instIsScalarTowerMulOppositeProdOff _root_.OAI.Tachikawa.Triangular.instIsScalarTowerProdOff _root_.OAI.Tachikawa.Triangular.instModuleMulOppositeProdOff _root_.OAI.Tachikawa.Triangular.instModuleOff _root_.OAI.Tachikawa.Triangular.instModuleProdOff _root_.OAI.Tachikawa.Triangular.instSMulCommClassProdMulOppositeOff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace Tachikawa
open CategoryTheory
open scoped ModuleCat.Algebra

namespace Enveloping
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  [FiniteDimensional k R] [FiniteDimensional k S]

def leftProdEquiv (M N : ModuleCat (Alg k R S)) :
    Obj (ModuleCat.of (Alg k R S) (M × N)) ≃ₗ[R] (Obj M × Obj N) where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def rightProdEquiv (M N : ModuleCat (Alg k R S)) :
    Obj (ModuleCat.of (Alg k R S) (M × N)) ≃ₗ[Sᵐᵒᵖ] (Obj M × Obj N) where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable (U V Y : FiniteModule k (Alg k R S)) (g : U.obj ⟶ Y.obj) (h : V.obj ⟶ Y.obj)

omit [FiniteDimensional k R] [FiniteDimensional k S] in
lemma fiberProjection_surjective : Function.Surjective (fiberProjection U V Y g h) := by
  intro y
  obtain ⟨z,hz⟩ := Y.cover.surjective y
  refine ⟨(0,(0,z)),?_⟩
  change g 0 + (h 0 + Y.cover.map z) = y
  rw [map_zero,map_zero,zero_add,zero_add,hz]

def fiber : FiniteModule k (Alg k R S) where
  obj := ModuleCat.of (Alg k R S) (LinearMap.ker (fiberProjection U V Y g h).hom)
  finite := by
    let : IsNoetherianRing (Alg k R S) := IsNoetherianRing.of_finite k (Alg k R S)
    let : Module.Finite (Alg k R S) (fiberMiddle U V Y) := by
      change Module.Finite (Alg k R S) (U.obj × (V.obj × (Fin Y.cover.rank → Alg k R S)))
      infer_instance
    exact Module.Finite.of_injective (LinearMap.ker (fiberProjection U V Y g h).hom).subtype
      Subtype.val_injective

def fiberInclusion : (fiber U V Y g h).obj ⟶ fiberMiddle U V Y :=
  ModuleCat.ofHom (LinearMap.ker (fiberProjection U V Y g h).hom).subtype

lemma fiberInclusion_injective : Function.Injective (fiberInclusion U V Y g h) :=
  Subtype.val_injective

lemma fiber_exact : Function.Exact (fiberInclusion U V Y g h) (fiberProjection U V Y g h) := by
  intro x
  exact ⟨fun hx => ⟨⟨x,hx⟩,rfl⟩,fun ⟨y,hy⟩ => hy ▸ y.property⟩

lemma fiber_left_projective [Module.Projective R (Obj U.obj)]
    [Module.Projective R (Obj V.obj)] [Module.Projective R (Obj Y.obj)] :
    Module.Projective R (Obj (fiber U V Y g h).obj) := by
  let : Module.Projective R (Obj (fiberCover Y)) := freeLeftProjective _
  let : Module.Projective R (Obj (ModuleCat.of (Alg k R S) (V.obj × fiberCover Y))) :=
    Module.Projective.of_equiv (leftProdEquiv V.obj (fiberCover Y)).symm
  let : Module.Projective R (Obj (fiberMiddle U V Y)) :=
    Module.Projective.of_equiv (leftProdEquiv U.obj
      (ModuleCat.of (Alg k R S) (V.obj × fiberCover Y))).symm
  exact projective_kernel_of_surjective (leftMap (fiberInclusion U V Y g h))
    (leftMap (fiberProjection U V Y g h)) (fiberInclusion_injective U V Y g h)
    (fiberProjection_surjective U V Y g h) (fiber_exact U V Y g h)

lemma fiber_right_projective [Module.Projective Sᵐᵒᵖ (Obj U.obj)]
    [Module.Projective Sᵐᵒᵖ (Obj V.obj)] [Module.Projective Sᵐᵒᵖ (Obj Y.obj)] :
    Module.Projective Sᵐᵒᵖ (Obj (fiber U V Y g h).obj) := by
  let : Module.Projective Sᵐᵒᵖ (Obj (fiberCover Y)) := freeRightProjective _
  let : Module.Projective Sᵐᵒᵖ (Obj (ModuleCat.of (Alg k R S) (V.obj × fiberCover Y))) :=
    Module.Projective.of_equiv (rightProdEquiv V.obj (fiberCover Y)).symm
  let : Module.Projective Sᵐᵒᵖ (Obj (fiberMiddle U V Y)) :=
    Module.Projective.of_equiv (rightProdEquiv U.obj
      (ModuleCat.of (Alg k R S) (V.obj × fiberCover Y))).symm
  exact projective_kernel_of_surjective (rightMap (fiberInclusion U V Y g h))
    (rightMap (fiberProjection U V Y g h)) (fiberInclusion_injective U V Y g h)
    (fiberProjection_surjective U V Y g h) (fiber_exact U V Y g h)

end Enveloping
end Tachikawa



namespace Tachikawa.Enveloping
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
variable (U V Y : FiniteModule k (Alg k R S))

def fiberThird : fiberMiddle U V Y ⟶ fiberCover Y :=
  ModuleCat.ofHom ((LinearMap.snd (Alg k R S) V.obj (fiberCover Y)).comp
    (LinearMap.snd (Alg k R S) U.obj (V.obj × fiberCover Y)))

end Tachikawa.Enveloping



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Triangular
attribute [-instance] _root_.OAI.Tachikawa.DownHom.instAddCommGroupCochain _root_.OAI.Tachikawa.DownHom.instModuleCochain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace Tachikawa.Triangular
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]

instance instFiniteDimensionalAlgOfCarrierAlg (F : ModuleCat (Enveloping.Alg k R R)) [FiniteDimensional k R]
    [FiniteDimensional k F] : FiniteDimensional k (Alg F) := by
  let : FiniteDimensional k (Off F) := inferInstanceAs (FiniteDimensional k F)
  exact inferInstanceAs (FiniteDimensional k ((R × R) × Off F))

variable (F : ModuleCat (Enveloping.Alg k R R))
lemma off_mul (a b : Alg F) :
    off F (a*b) = lower F a • off F b + MulOpposite.op (upper F b) • off F a := rfl

def e₀ : Alg F := TrivSqZeroExt.inl (1,0)
def e₁ : Alg F := TrivSqZeroExt.inl (0,1)

end Tachikawa.Triangular



namespace Tachikawa.Triangular
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable (F : ModuleCat (Enveloping.Alg k R R)) (L N : ModuleCat R)
  (α : Enveloping.evalType L F →ₗ[R] N)

def Triple (F : ModuleCat (Enveloping.Alg k R R)) (L N : ModuleCat R)
    (_α : Enveloping.evalType L F →ₗ[R] N) : Type := L × N
instance instAddCommGroupTriple : AddCommGroup (Triple F L N α) := inferInstanceAs (AddCommGroup (L × N))
instance instModuleAlgTriple : Module (Alg F) (Triple F L N α) where
  smul a x := (upper F a • x.1, α (BalancedTensor.mk (off F a) x.1) + lower F a • x.2)
  one_smul x := by
    change L × N at x
    apply Prod.ext
    · exact one_smul R x.1
    · change α (BalancedTensor.mk (0 : Enveloping.Obj F) x.1) + (1:R) • x.2 = x.2
      simp
  mul_smul a b x := by
    change L × N at x
    apply Prod.ext
    · exact mul_smul (upper F a) (upper F b) x.1
    · change α (BalancedTensor.mk (off F (a*b)) x.1) + lower F (a*b) • x.2 =
        α (BalancedTensor.mk (off F a) (upper F b • x.1)) +
          lower F a • (α (BalancedTensor.mk (off F b) x.1) + lower F b • x.2)
      rw [off_mul, map_mul, BalancedTensor.mk_add_left,
        BalancedTensor.mk_smul_left, BalancedTensor.balance, α.map_add,
        α.map_smul, smul_add, mul_smul]
      abel
  smul_zero a := by
    apply Prod.ext
    · exact smul_zero (upper F a)
    · change α (BalancedTensor.mk (off F a) (0 : L)) + lower F a • (0 : N) = 0
      simp
  smul_add a x y := by
    change L × N at x y
    apply Prod.ext
    · exact smul_add (upper F a) x.1 y.1
    · change α (BalancedTensor.mk (off F a) (x.1+y.1)) + lower F a • (x.2+y.2) = _
      rw [(BalancedTensor.mk (off F a)).map_add, α.map_add, smul_add]
      change _ = (α (BalancedTensor.mk (off F a) x.1) + lower F a • x.2) +
        (α (BalancedTensor.mk (off F a) y.1) + lower F a • y.2)
      abel
  add_smul a b x := by
    change L × N at x
    apply Prod.ext
    · exact add_smul (upper F a) (upper F b) x.1
    · change α (BalancedTensor.mk (off F (a+b)) x.1) + lower F (a+b) • x.2 = _
      rw [(off F).map_add, map_add (lower F), BalancedTensor.mk_add_left, α.map_add, add_smul]
      change _ = (α (BalancedTensor.mk (off F a) x.1) + lower F a • x.2) +
        (α (BalancedTensor.mk (off F b) x.1) + lower F b • x.2)
      abel
  zero_smul x := by
    change L × N at x
    apply Prod.ext
    · exact zero_smul R x.1
    · change α (BalancedTensor.mk (0 : Enveloping.Obj F) x.1) + (0:R) • x.2 = 0
      simp

def tripleObj : ModuleCat (Alg F) := ModuleCat.of (Alg F) (Triple F L N α)

@[simp] lemma triple_smul_fst (a : Alg F) (x : Triple F L N α) :
    (a • x).1 = upper F a • x.1 := rfl
@[simp] lemma triple_smul_snd (a : Alg F) (x : Triple F L N α) :
    (a • x).2 = α (BalancedTensor.mk (off F a) x.1) + lower F a • x.2 := rfl

end Tachikawa.Triangular



namespace Tachikawa.Triangular
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable {F : ModuleCat (Enveloping.Alg k R R)} {L N L' N' : ModuleCat R}
  {α : Enveloping.evalType L F →ₗ[R] N} {β : Enveloping.evalType L' F →ₗ[R] N'}

lemma e₀_smul_triple (x : Triple F L N α) : e₀ F • x = (x.1,0) := by
  apply Prod.ext
  · change (1:R) • x.1 = x.1
    exact one_smul R x.1
  · change α (BalancedTensor.mk (0 : Enveloping.Obj F) x.1) + (0:R) • x.2 = 0
    simp
lemma e₁_smul_triple (x : Triple F L N α) : e₁ F • x = (0,x.2) := by
  apply Prod.ext
  · change (0:R) • x.1 = 0
    exact zero_smul R x.1
  · change α (BalancedTensor.mk (0 : Enveloping.Obj F) x.1) + (1:R) • x.2 = x.2
    simp
lemma diagonal_smul_triple (r : R) (x : Triple F L N α) :
    (TrivSqZeroExt.inl (r,r) : Alg F) • x = (r • x.1,r • x.2) := by
  apply Prod.ext
  · rfl
  · change α (BalancedTensor.mk (0 : Enveloping.Obj F) x.1) + r • x.2 = r • x.2
    simp

def tripleMap (g : L →ₗ[R] L') (h : N →ₗ[R] N')
    (hc : h.comp α = β.comp (BalancedTensor.mapRight (M := Enveloping.Obj F) g)) :
    Triple F L N α →ₗ[Alg F] Triple F L' N' β where
  toFun x := (g x.1,h x.2)
  map_add' x y := Prod.ext (g.map_add _ _) (h.map_add _ _)
  map_smul' a x := by
    apply Prod.ext
    · exact g.map_smul _ _
    · change h (α (BalancedTensor.mk (off F a) x.1) + lower F a • x.2) =
        β (BalancedTensor.mk (off F a) (g x.1)) + lower F a • h x.2
      rw [h.map_add,h.map_smul]
      have he := LinearMap.congr_fun hc (BalancedTensor.mk (off F a) x.1)
      exact congrArg (· + lower F a • h x.2) he

variable (f : Triple F L N α →ₗ[Alg F] Triple F L' N' β)

lemma hom_fst_e₁ (y : N) : (f (0,y)).1 = 0 := by
  have h := congrArg Prod.fst (f.map_smul (e₁ F) (show Triple F L N α from (0,y)))
  rw [e₁_smul_triple,e₁_smul_triple] at h
  exact h
lemma hom_snd_e₀ (x : L) : (f (x,0)).2 = 0 := by
  have h := congrArg Prod.snd (f.map_smul (e₀ F) (show Triple F L N α from (x,0)))
  rw [e₀_smul_triple,e₀_smul_triple] at h
  exact h

def homUpper : L →ₗ[R] L' where
  toFun x := (f (x,0)).1
  map_add' x y := by
    have he := congrArg Prod.fst
      (f.map_add (show Triple F L N α from (x,0)) (show Triple F L N α from (y,0)))
    change (f (x+y,(0:N)+0)).1 = (f (x,0)).1 + (f (y,0)).1 at he
    simpa only [add_zero] using he
  map_smul' r x := by
    have h := congrArg Prod.fst (f.map_smul (TrivSqZeroExt.inl (r,r))
      (show Triple F L N α from (x,0)))
    rw [diagonal_smul_triple,diagonal_smul_triple,smul_zero] at h
    exact h

def homLower : N →ₗ[R] N' where
  toFun y := (f (0,y)).2
  map_add' x y := by
    have he := congrArg Prod.snd
      (f.map_add (show Triple F L N α from (0,x)) (show Triple F L N α from (0,y)))
    change (f ((0:L)+0,x+y)).2 = (f (0,x)).2 + (f (0,y)).2 at he
    simpa only [zero_add] using he
  map_smul' r y := by
    have h := congrArg Prod.snd (f.map_smul (TrivSqZeroExt.inl (r,r))
      (show Triple F L N α from (0,y)))
    rw [diagonal_smul_triple,diagonal_smul_triple,smul_zero] at h
    exact h

lemma hom_pair (x : L) (y : N) : f (x,y) = (homUpper f x,homLower f y) := by
  have h := f.map_add (show Triple F L N α from (x,0)) (show Triple F L N α from (0,y))
  change f (x+0,0+y) = f (x,0)+f (0,y) at h
  rw [add_zero,zero_add] at h
  rw [h]
  apply Prod.ext
  · change (f (x,0)).1 + (f (0,y)).1 = (f (x,0)).1
    rw [hom_fst_e₁,add_zero]
  · change (f (x,0)).2 + (f (0,y)).2 = (f (0,y)).2
    rw [hom_snd_e₀,zero_add]

@[ext] lemma triple_hom_ext {f g : Triple F L N α →ₗ[Alg F] Triple F L' N' β}
    (h₀ : homUpper f = homUpper g) (h₁ : homLower f = homLower g) : f = g := by
  apply LinearMap.ext
  intro x
  change f (x.1,x.2) = g (x.1,x.2)
  rw [hom_pair f x.1 x.2,hom_pair g x.1 x.2,h₀,h₁]

end Tachikawa.Triangular



namespace Tachikawa.Triangular
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable (F : ModuleCat (Enveloping.Alg k R R))

abbrev tensorObj (L : ModuleCat R) := ModuleCat.of R (Enveloping.evalType L F)
abbrev tensorMap {L L' : ModuleCat R} (f : L ⟶ L') : tensorObj F L ⟶ tensorObj F L' :=
  ModuleCat.ofHom (BalancedTensor.mapRight (M := Enveloping.Obj F) f.hom)

def D₀Obj (L : ModuleCat R) : ModuleCat (Alg F) :=
  tripleObj F L (tensorObj F L) LinearMap.id
def D₁Obj (L : ModuleCat R) : ModuleCat (Alg F) :=
  tripleObj F (zeroObj (R := R)) L 0

def D₀Map {L L' : ModuleCat R} (f : L ⟶ L') : D₀Obj F L ⟶ D₀Obj F L' :=
  ModuleCat.ofHom (tripleMap f.hom (tensorMap F f).hom (by simp))
def D₁Map {L L' : ModuleCat R} (f : L ⟶ L') : D₁Obj F L ⟶ D₁Obj F L' :=
  ModuleCat.ofHom (tripleMap 0 f.hom (by simp))

def D₀ : ModuleCat R ⥤ ModuleCat (Alg F) where
  obj := D₀Obj F
  map := D₀Map F
  map_id L := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Prod.ext
    · rfl
    · exact LinearMap.congr_fun (BalancedTensor.mapRight_id (k := k) (R := R) (S := R)
        (M := Enveloping.Obj F) (N := L)) x.2
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Prod.ext
    · rfl
    · exact LinearMap.congr_fun (BalancedTensor.mapRight_comp f.hom g.hom) x.2

def D₁ : ModuleCat R ⥤ ModuleCat (Alg F) where
  obj := D₁Obj F
  map := D₁Map F
  map_id L := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Prod.ext
    · exact Subsingleton.elim _ _
    · rfl
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Prod.ext
    · rfl
    · rfl

instance instAdditiveModuleCatAlgD₀ : (D₀ F).Additive where
  map_add {_ _ f g} := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Prod.ext
    · rfl
    · exact LinearMap.congr_fun (BalancedTensor.mapRight_add f.hom g.hom) x.2
instance instAdditiveModuleCatAlgD₁ : (D₁ F).Additive where
  map_add {_ _ f g} := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Prod.ext
    · exact Subsingleton.elim _ _
    · rfl

variable {F} {L L' : ModuleCat R}

def cross₁₀ : (D₁Obj F L ⟶ D₀Obj F L') ≃ₗ[k] (L ⟶ tensorObj F L') where
  toFun f := ModuleCat.ofHom (homLower f.hom)
  invFun h := ModuleCat.ofHom (tripleMap 0 h.hom (by
    rw [LinearMap.comp_zero,BalancedTensor.mapRight_zero,LinearMap.comp_zero]))
  left_inv f := by
    apply ModuleCat.hom_ext
    apply triple_hom_ext
    · apply Subsingleton.elim
    · rfl
  right_inv f := rfl
  map_add' f g := by rfl
  map_smul' c f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change ((algebraMap k (Alg F) c) • f.hom (0,x)).2 = c • (f.hom (0,x)).2
    change ((TrivSqZeroExt.inl (algebraMap k R c,algebraMap k R c)) •
      f.hom (0,x)).2 = c • (f.hom (0,x)).2
    erw [diagonal_smul_triple]
    exact IsScalarTower.algebraMap_smul R c (f.hom (0,x)).2

end Tachikawa.Triangular



namespace Tachikawa.Triangular
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable (F : ModuleCat (Enveloping.Alg k R R)) (ι : Type) [Fintype ι]

def freeTensorEval : Enveloping.evalType (freeObj (R := R) ι) F →ₗ[R] (ι → Enveloping.Obj F) :=
  (BalancedTensor.rightFreeEval (k := k) (R := R) (S := R) (M := Enveloping.Obj F) ι).comp
    (BalancedTensor.mapRight (M := Enveloping.Obj F) (freeUnderlying (R := R) ι).toLinearMap)

def freeTensorInv : (ι → Enveloping.Obj F) →ₗ[R] Enveloping.evalType (freeObj (R := R) ι) F :=
  (BalancedTensor.mapRight (M := Enveloping.Obj F) (freeUnderlying (R := R) ι).symm.toLinearMap).comp
    (BalancedTensor.rightFreeInv (k := k) (R := R) (S := R) (M := Enveloping.Obj F) ι)

omit [Fintype ι] in
lemma freeTensorEval_mk (m : Enveloping.Obj F) (x : freeObj (R := R) ι) (i : ι) :
    freeTensorEval F ι (BalancedTensor.mk m x) i = MulOpposite.op (x i) • m := rfl

lemma freeTensorEval_inv (x : ι → Enveloping.Obj F) : freeTensorEval F ι (freeTensorInv F ι x) = x := by
  dsimp only [freeTensorEval,freeTensorInv,LinearMap.comp_apply]
  have h := LinearMap.congr_fun (BalancedTensor.mapRight_split (k := k) (S := R)
    (M := Enveloping.Obj F) (freeUnderlying (R := R) ι).symm.toLinearMap
      (freeUnderlying (R := R) ι).toLinearMap (by rfl))
      (BalancedTensor.rightFreeInv (k := k) (R := R) (S := R) (M := Enveloping.Obj F) ι x)
  dsimp only [LinearMap.comp_apply,LinearMap.id_apply] at h
  rw [h]
  exact BalancedTensor.rightFreeEval_inv ι x

lemma freeTensorInv_eval (x : Enveloping.evalType (freeObj (R := R) ι) F) :
    freeTensorInv F ι (freeTensorEval F ι x) = x := by
  dsimp only [freeTensorEval,freeTensorInv,LinearMap.comp_apply]
  rw [BalancedTensor.rightFreeInv_eval]
  exact LinearMap.congr_fun (BalancedTensor.mapRight_split _ _ (by rfl)) x

def freeTensorEquiv : Enveloping.evalType (freeObj (R := R) ι) F ≃ₗ[R] (ι → Enveloping.Obj F) :=
  { freeTensorEval F ι with
    invFun := freeTensorInv F ι
    left_inv := freeTensorInv_eval F ι
    right_inv := freeTensorEval_inv F ι }




def D₀FreeInclusion : D₀Obj F (freeObj (R := R) ι) →ₗ[Alg F] (ι → Alg F) where
  toFun x i := ⟨(x.1 i,0), show Off F from freeTensorEval F ι x.2 i⟩
  map_add' x y := by
    funext i
    apply TrivSqZeroExt.ext
    · apply Prod.ext
      · rfl
      · exact (zero_add (0 : R)).symm
    · exact congrFun ((freeTensorEval F ι).map_add x.2 y.2) i
  map_smul' a x := by
    funext i
    apply TrivSqZeroExt.ext
    · apply Prod.ext
      · rfl
      · change (0:R) = lower F a * 0
        simp
    · change freeTensorEval F ι
        (BalancedTensor.mk (k := k) (R := R) (S := R) (M := Enveloping.Obj F)
          (N := freeObj (R := R) ι) (off F a) x.1 + lower F a •
          (show Enveloping.evalType (freeObj (R := R) ι) F from x.2)) i =
        lower F a • freeTensorEval F ι x.2 i +
          MulOpposite.op (x.1 i) • off F a
      rw [map_add, map_smul, Pi.add_apply, Pi.smul_apply, freeTensorEval_mk]
      exact add_comm _ _

def D₀FreeProjection : (ι → Alg F) →ₗ[Alg F] D₀Obj F (freeObj (R := R) ι) where
  toFun a := (fun i => upper F (a i), freeTensorInv F ι (fun i => off F (a i)))
  map_add' a b := by
    apply Prod.ext
    · funext i
      exact map_add (upper F) (a i) (b i)
    · exact (freeTensorInv F ι).map_add _ _
  map_smul' a z := by
    apply Prod.ext
    · funext i
      exact map_mul (upper F) a (z i)
    · apply (freeTensorEquiv F ι).injective
      change freeTensorEval F ι
        (freeTensorInv F ι (fun i => off F (a * z i))) =
        freeTensorEval F ι
          (BalancedTensor.mk (k := k) (R := R) (S := R) (M := Enveloping.Obj F)
            (N := freeObj (R := R) ι) (off F a) (fun i => upper F (z i)) +
            lower F a • freeTensorInv F ι (fun i => off F (z i)))
      rw [freeTensorEval_inv,map_add,map_smul,freeTensorEval_inv]
      funext i
      exact (off_mul F a (z i)).trans (add_comm _ _)

def D₁FreeProjection : (ι → Alg F) →ₗ[Alg F] D₁Obj F (freeObj (R := R) ι) where
  toFun a := (0,fun i => lower F (a i))
  map_add' a b := by
    apply Prod.ext
    · exact Subsingleton.elim _ _
    · funext i
      exact map_add (lower F) (a i) (b i)
  map_smul' a z := by
    apply Prod.ext
    · exact Subsingleton.elim _ _
    · funext i
      change lower F (a*z i) = ((0 : freeObj (R := R) ι) + lower F a •
        (show freeObj (R := R) ι from fun i => lower F (z i))) i
      rw [zero_add]
      exact map_mul (lower F) a (z i)

end Tachikawa.Triangular



namespace Tachikawa.Triangular
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable (F : ModuleCat.{0} (Enveloping.Alg k R R))
abbrev D₀Complex (P : ChainComplex (ModuleCat.{0} R) ℤ) :=
  ((D₀ F).mapHomologicalComplex (.down ℤ)).obj P
abbrev D₁Complex (P : ChainComplex (ModuleCat.{0} R) ℤ) :=
  ((D₁ F).mapHomologicalComplex (.down ℤ)).obj P

lemma cross₁₀_pre {L M N : ModuleCat.{0} R} (d : L ⟶ M)
    (f : D₁Obj F M ⟶ D₀Obj F N) :
    cross₁₀ (D₁Map F d ≫ f) = d ≫ cross₁₀ f := rfl
lemma cross₁₀_post {L M N : ModuleCat.{0} R} (d : M ⟶ N)
    (f : D₁Obj F L ⟶ D₀Obj F M) :
    cross₁₀ (f ≫ D₀Map F d) = cross₁₀ f ≫ (Enveloping.tensorFunctor F).map d := rfl

variable (P : ChainComplex (ModuleCat.{0} R) ℤ) (hP : TotallyAcyclic P)
  (N : ModuleCat.{0} R)
include hP

variable {P}
def crossMap {Q : ChainComplex (ModuleCat.{0} R) ℤ}
    (u : P ⟶ Enveloping.tensorComplex F Q) : D₁Complex F P ⟶ D₀Complex F Q where
  f j := cross₁₀.symm (u.f j)
  comm' i j hij := by
    apply cross₁₀.injective
    change cross₁₀ (cross₁₀.symm (u.f i) ≫ D₀Map F (Q.d i j)) =
      cross₁₀ (D₁Map F (P.d i j) ≫ cross₁₀.symm (u.f j))
    rw [cross₁₀_pre,cross₁₀_post]
    erw [LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply]
    exact u.comm i j

end Tachikawa.Triangular

end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Cone
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace Tachikawa.Triangular
open CategoryTheory
open DownHom
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [CharP k 2] [Ring R] [Algebra k R]
variable (F : ModuleCat.{0} (Enveloping.Alg k R R))
  {P : ChainComplex (ModuleCat.{0} R) ℤ}
  (u : P ⟶ Enveloping.tensorComplex F P)
abbrev cone := CompleteCone.complex (crossMap F u)

end Tachikawa.Triangular



end

end OAI
end


