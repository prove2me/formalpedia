-- Prove2me | Definitions.Def_OAIQ116Ta016
-- name    : OAIQ116Ta016
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T02:50:26.825985+00:00
-- url     : https://prove2.me/theorems/a0c2e5e8-ff22-4bee-8189-d3380c93988d
-- title:
--   Definitions bundle OAIQ116Ta016 of the split of OpenAI, A counterexample to Tachikawa's second conjecture
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Tachikawa.main_theorem`, carved from OpenAI's openai/math development (OpenAI, *A counterexample to Tachikawa's second conjecture*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 67 declarations of OpenAI's Lean: 47 definitions, 1 instance and 19 theorems. The definitions and types are `OAI.Tachikawa.Construction.FAction`, `OAI.Tachikawa.Construction.FFirst`, `OAI.Tachikawa.Construction.FHom`, `OAI.Tachikawa.Construction.FHomInclusion`, `OAI.Tachikawa.Construction.FHomPair`, `OAI.Tachikawa.Construction.FHomProjection`, `OAI.Tachikawa.Construction.FSecond`, `OAI.Tachikawa.Construction.VAction`, `OAI.Tachikawa.Construction.XExtKunneth`, `OAI.Tachikawa.Construction.completeYHomologyEquiv`, `OAI.Tachikawa.Construction.completeYStableEquiv`, `OAI.Tachikawa.Construction.concreteF`, `OAI.Tachikawa.Construction.concreteFst`, `OAI.Tachikawa.Construction.concreteInclusion`, `OAI.Tachikawa.Construction.concreteLift`, `OAI.Tachikawa.Construction.concreteMiddle`, `OAI.Tachikawa.Construction.concreteProjection`, `OAI.Tachikawa.Construction.concreteSnd`, `OAI.Tachikawa.Construction.concreteVZero`, `OAI.Tachikawa.Construction.delta`, `OAI.Tachikawa.Construction.finiteX`, `OAI.Tachikawa.Construction.middleHom`, `OAI.Tachikawa.Construction.middleHpair`, `OAI.Tachikawa.Construction.middleHpairX`, `OAI.Tachikawa.Construction.normalizedMap`, `OAI.Tachikawa.Construction.positiveSelfHomExt`, `OAI.Tachikawa.Construction.selfHom`, `OAI.Tachikawa.Construction.selfHomDual`, `OAI.Tachikawa.Construction.selfHomZeroEquiv`, `OAI.Tachikawa.Construction.stableXEndEquiv`, `OAI.Tachikawa.Construction.xComplete`, `OAI.Tachikawa.Construction.xTwistHom`, `OAI.Tachikawa.Construction.zeroHomEquiv`, `OAI.Tachikawa.OuterTensor.extKunneth`, `OAI.Tachikawa.SourceField.sourceAlgebra`, `OAI.Tachikawa.SourceField.sourceAug`, `OAI.Tachikawa.SourceField.sourceCone`, `OAI.Tachikawa.SourceField.sourceConeModule`, `OAI.Tachikawa.SourceField.sourceDelta`, `OAI.Tachikawa.SourceField.sourceF` and 7 more.
--
--   **Sources.** They come from these modules of lean/OAI/RingTheory, in whole or in part: [`Tachikawa_Coresolution`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RingTheory/Tachikawa/Coresolution.lean), [`Tachikawa_Counterexample`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RingTheory/Tachikawa/Counterexample.lean), [`Tachikawa_Delta`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RingTheory/Tachikawa/Delta.lean), [`Tachikawa_HomProfile`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RingTheory/Tachikawa/HomProfile.lean), [`Tachikawa_OuterExt`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RingTheory/Tachikawa/OuterExt.lean), [`Tachikawa_Socle`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RingTheory/Tachikawa/Socle.lean), [`Tachikawa_StableLift`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RingTheory/Tachikawa/StableLift.lean).
--
--   **Imports.** It imports the bundles `OAIQ116Ta014` and `OAIQ116Ta015` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI.Tachikawa.Construction.xTwistHom_positive`, `OAI.Tachikawa.SourceField.sourceCone_closed_boundary` and `OAI.Tachikawa.SourceField.sourceDelta_bijective`; the proofs of `OAI.Tachikawa.Construction.XInverseTwist_weight`, `OAI.Tachikawa.Construction.xTwistHom_positive`, `OAI.Tachikawa.SourceField.sourceCone_closed_boundary`, `OAI.Tachikawa.SourceField.sourceDelta_bijective` and `OAI.Tachikawa.main_theorem`.
-- source:
--   OpenAI, A counterexample to Tachikawa's second conjecture, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-counterexample-to-Tachikawas-second-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/RingTheory at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ116Ta014
import Definitions.Def_OAIQ116Ta015

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Coresolution
attribute [-instance] _root_.OAI.Tachikawa.DownHom.instAddCommGroupCochain _root_.OAI.Tachikawa.Enveloping.instAddCommGroupCarrierMulOppositeRightObj _root_.OAI.Tachikawa.Enveloping.instModuleCarrierMulOppositeRightObj_1 _root_.OAI.Tachikawa.LeftCoinduced.coextend_additive _root_.OAI.Tachikawa.LeftCoinduced.coextend_preservesInjective _root_.OAI.Tachikawa.OuterTensor.restrictionPreservesHomology _root_.OAI.Tachikawa.TotalDualPairing.instIsIsoHomologicalComplexNatModuleCatUpComparison _root_.OAI.Tachikawa.TotalDualPairing.instTensorSignsNatUp_solutions _root_.OAI.Tachikawa.TotalMap.sourceHasCoproduct _root_.OAI.Tachikawa.downIntTensorSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
set_option backward.isDefEq.respectTransparency false


noncomputable section



namespace Tachikawa
open CategoryTheory CategoryTheory.Abelian
open scoped ModuleCat.Algebra
variable (k R : Type) [Field k] [Ring R] [Algebra k R]
  (P : ChainComplex (ModuleCat R) ℕ) (N : ModuleCat R)

variable {k R} {M : ModuleCat R} (Q : ProjectiveResolution M)

lemma resolutionCyclesToExt_surjective (n : ℕ) :
    Function.Surjective (resolutionCyclesToExt N Q n (k := k)) := by
  intro x
  obtain ⟨f,hf,rfl⟩ := Q.extMk_surjective x (n+1) rfl
  exact ⟨⟨f,(resolutionHom_memZ k R Q.complex N n f).mpr hf⟩,rfl⟩

lemma resolutionCyclesToExt_ker (n : ℕ) :
    LinearMap.ker (resolutionCyclesToExt N Q (n+1) (k := k)) =
      LinearMap.range (VectorSplit.boundary (resolutionHom k R Q.complex N) (n+1)) := by
  ext z
  change Q.extMk z.val (n+2) rfl
    ((resolutionHom_memZ k R Q.complex N (n+1) z.val).mp z.property) = 0 ↔ _
  erw [Q.extMk_eq_zero_iff _ _ _ _ n rfl]
  have hp : (ComplexShape.up ℕ).prev (n+1) = n :=
    (ComplexShape.up ℕ).prev_eq' rfl
  change (∃ g : Q.complex.X n ⟶ N, Q.complex.d (n+1) n ≫ g = z.val) ↔
    ∃ g : (resolutionHom k R Q.complex N).X ((ComplexShape.up ℕ).prev (n+1)),
      VectorSplit.boundary _ (n+1) g = z
  simp only [← Subtype.val_inj]
  change (∃ g : Q.complex.X n ⟶ N, Q.complex.d (n+1) n ≫ g = z.val) ↔
    ∃ g : Q.complex.X ((ComplexShape.up ℕ).prev (n+1)) ⟶ N,
      Q.complex.d (n+1) ((ComplexShape.up ℕ).prev (n+1)) ≫ g = z.val
  rw [hp]

end Tachikawa



namespace Tachikawa
open CategoryTheory CategoryTheory.Abelian CochainComplex.HomComplex
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
  {M N : ModuleCat R} (Q : ProjectiveResolution M)

lemma resolutionCyclesToExt_ker_all (n : ℕ) :
    LinearMap.ker (resolutionCyclesToExt N Q n (k := k)) =
      LinearMap.range (VectorSplit.boundary (resolutionHom k R Q.complex N) n) := by
  cases n with
  | succ n => exact resolutionCyclesToExt_ker N Q n
  | zero =>
    rw [resolutionBoundary_zero, LinearMap.range_zero]
    ext z
    change Q.extMk z.val 1 rfl ((resolutionHom_memZ k R Q.complex N 0 z.val).mp z.property) = 0 ↔ z = 0
    refine (extMk_zeroDegree_eq_zero Q z.val _).trans ?_
    constructor
    · intro h
      exact Subtype.ext h
    · intro h
      subst z
      rfl

def resolutionHomologyExtAll (n : ℕ) :
    VectorSplit.H (resolutionHom k R Q.complex N) n ≃ₗ[k] Ext M N n := by
  change (VectorSplit.Z (resolutionHom k R Q.complex N) n ⧸
    LinearMap.range (VectorSplit.boundary (resolutionHom k R Q.complex N) n)) ≃ₗ[k] _
  rw [← resolutionCyclesToExt_ker_all Q n]
  exact (resolutionCyclesToExt N Q n).quotKerEquivOfSurjective
    (resolutionCyclesToExt_surjective N Q n)

end Tachikawa



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_OuterExt
attribute [-instance] _root_.OAI.Tachikawa.DownHom.instAddCommGroupCochain _root_.OAI.Tachikawa.Enveloping.inducedRegularCochain_projective _root_.OAI.Tachikawa.Enveloping.instAddCommGroupCarrierMulOppositeRightObj _root_.OAI.Tachikawa.Enveloping.instModuleCarrierMulOppositeRightObj_1 _root_.OAI.Tachikawa.LeftCoinduced.coextend_additive _root_.OAI.Tachikawa.LeftCoinduced.coextend_preservesInjective _root_.OAI.Tachikawa.OuterTensor.instAdditiveModuleCatTensorProductObjFunctorFlipBifunctor _root_.OAI.Tachikawa.OuterTensor.instPreservesFiniteColimitsModuleCatTensorProductObjFunctorFlipBifunctor _root_.OAI.Tachikawa.OuterTensor.instPreservesFiniteLimitsModuleCatTensorProductObjFunctorFlipBifunctor _root_.OAI.Tachikawa.Triangular.instProjectiveCarrierOneFree _root_.OAI.Tachikawa.VectorSplit.tensorFunctor_linear _root_.OAI.Tachikawa.downIntTensorSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
set_option backward.isDefEq.respectTransparency false


noncomputable section



namespace Tachikawa.OuterTensor
open CategoryTheory CategoryTheory.Abelian HomologicalComplex
open scoped TensorProduct ModuleCat.Algebra
variable {k A B : Type} [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B] [CharP k 2]
  {M U : ModuleCat A} {N V : ModuleCat B}
  (P : ProjectiveResolution M) (Q : ProjectiveResolution N)
  [∀ n, Module.Finite A (P.complex.X n)] [∀ n, Module.Finite B (Q.complex.X n)]
  [∀ n, FiniteDimensional k (P.complex.X n)] [∀ n, FiniteDimensional k (Q.complex.X n)]

def extKunneth (n : ℕ) :
    Ext (((bifunctor k A B).obj M).obj N) (((bifunctor k A B).obj U).obj V) n ≃ₗ[k]
      (∀ t : TotalDualPairing.Diag n, Ext M U t.val.1 ⊗[k] Ext N V t.val.2) := by
  let S := tensorResolution (k := k) P Q
  let H := resolutionHom k (A ⊗[k] B) S.complex (((bifunctor k A B).obj U).obj V)
  let e₁ := (resolutionHomologyExtAll (N := ((bifunctor k A B).obj U).obj V) S n (k := k)).symm
  let e₂ := (VectorSplit.homologyIsoH H n).symm.toLinearEquiv
  let e₃ := ((homologyFunctor (ModuleCat k) (.up ℕ) n).mapIso
    (homTotalIso P.complex Q.complex U V).symm).toLinearEquiv
  let e₄ := (VectorSplit.tensorHomologyIso (resolutionHom k A P.complex U)
    (resolutionHom k B Q.complex V) (.up ℕ) n).toLinearEquiv
  let e₅ := coproductPiEquiv (fun t : TotalDualPairing.Diag n =>
    ModuleCat.of k (VectorSplit.H (resolutionHom k A P.complex U) t.val.1 ⊗[k]
      VectorSplit.H (resolutionHom k B Q.complex V) t.val.2))
  let e₆ := LinearEquiv.piCongrRight (fun t : TotalDualPairing.Diag n =>
    TensorProduct.congr (resolutionHomologyExtAll (N := U) P t.val.1 (k := k))
      (resolutionHomologyExtAll (N := V) Q t.val.2 (k := k)))
  exact e₁.trans (e₂.trans (e₃.trans (e₄.trans (e₅.trans e₆))))

end Tachikawa.OuterTensor



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Socle
attribute [-instance] _root_.OAI.Tachikawa.AlgebraInduction.resFinite _root_.OAI.Tachikawa.Construction.instFiniteCSubtypeMemSubmoduleCe _root_.OAI.Tachikawa.Construction.instFiniteCSubtypeMemSubmoduleCf _root_.OAI.Tachikawa.Construction.instFiniteDimensionalCarrierBBRegularLeftObj _root_.OAI.Tachikawa.Construction.instFiniteDimensionalCarrierEXObj _root_.OAI.Tachikawa.Construction.instFiniteMulOppositeC _root_.OAI.Tachikawa.Construction.instFiniteMulOppositeCSubtypeMemSubmoduleEC _root_.OAI.Tachikawa.Construction.instFiniteMulOppositeCSubtypeMemSubmoduleFC _root_.OAI.Tachikawa.Construction.instProjectiveMulOppositeC _root_.OAI.Tachikawa.DownHom.instAddCommGroupCochain _root_.OAI.Tachikawa.DownHom.instModuleCochain _root_.OAI.Tachikawa.Enveloping.coindEndo_finite _root_.OAI.Tachikawa.Enveloping.coindObj_finite _root_.OAI.Tachikawa.Enveloping.eval_finite _root_.OAI.Tachikawa.Enveloping.inducedRegularComplex_finite _root_.OAI.Tachikawa.Enveloping.instAddCommGroupCarrierMulOppositeRightObj _root_.OAI.Tachikawa.Enveloping.instFiniteCarrierDualLeftObjOfFiniteDimensional _root_.OAI.Tachikawa.Enveloping.instFiniteDimensionalCarrierAlgCoindObjOfMulOpposite _root_.OAI.Tachikawa.Enveloping.instFiniteDimensionalCarrierDualLeftObj _root_.OAI.Tachikawa.Enveloping.instModuleCarrierMulOppositeRightObj_1 _root_.OAI.Tachikawa.Enveloping.rightFunctor_finite _root_.OAI.Tachikawa.HomBimodule.instFiniteDimensionalCarrierAlgObj _root_.OAI.Tachikawa.LeftCoinduced.C_finite _root_.OAI.Tachikawa.LeftCoinduced.J_finite _root_.OAI.Tachikawa.LeftCoinduced.coextend_additive _root_.OAI.Tachikawa.LeftCoinduced.coextend_preservesInjective _root_.OAI.Tachikawa.LeftCoinduced.iterate_finite _root_.OAI.Tachikawa.Triangular.instFiniteCarrierOneFree _root_.OAI.Tachikawa.Triangular.instFiniteDimensionalAlgOfCarrierAlg _root_.OAI.Tachikawa.Triangular.instFiniteDimensionalCarrierAlgD₀ObjOfAlg _root_.OAI.Tachikawa.Triangular.instFiniteDimensionalCarrierAlgD₁Obj _root_.OAI.Tachikawa.downIntTensorSigns _root_.OAI.Tachikawa.freeEndo_finite _root_.OAI.Tachikawa.freeKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace Tachikawa.Construction
open CategoryTheory CategoryTheory.Abelian
open scoped TensorProduct ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q : k)

def XExtKunneth (n : ℕ) :
    Ext (XTensorObj q) (XTensorObj q) n ≃ₗ[k]
      (∀ t : TotalDualPairing.Diag n,
        Ext (C.simpleObj q) (C.simpleObj q) t.val.1 ⊗[k]
        Ext (C.simpleObj q) (C.simpleObj q) t.val.2) :=
  OuterTensor.extKunneth (sResolution q) (sResolution q) n

lemma XExtThree_nontrivial (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) :
    Nontrivial (Ext (XTensorObj q) (XTensorObj q) 3) := by
  let t : TotalDualPairing.Diag 3 := ⟨(3,0),rfl⟩
  let e := (TensorProduct.congr (C.simpleExtMultiple q hq hp 1)
    (C.simpleExtZeroEquiv q)).trans (TensorProduct.lid k k)
  have ht : Nontrivial (Ext (C.simpleObj q) (C.simpleObj q) t.val.1 ⊗[k]
      Ext (C.simpleObj q) (C.simpleObj q) t.val.2) := e.symm.injective.nontrivial
  let := ht
  have hpi : Nontrivial (∀ t : TotalDualPairing.Diag 3,
      Ext (C.simpleObj q) (C.simpleObj q) t.val.1 ⊗[k]
      Ext (C.simpleObj q) (C.simpleObj q) t.val.2) :=
    Function.Surjective.nontrivial (Function.surjective_eval t)
  let := hpi
  exact (XExtKunneth q 3).symm.injective.nontrivial

lemma XTensor_nonprojective (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) :
    ¬ Module.Projective (E q) (XTensorObj q) := by
  intro h
  let := h
  let := XExtThree_nontrivial q hq hp
  have := Ext.subsingleton_of_projective (XTensorObj q) (XTensorObj q) 2
  exact not_subsingleton (Ext (XTensorObj q) (XTensorObj q) 3) ⟨Subsingleton.elim⟩

end Tachikawa.Construction



namespace Tachikawa.Construction
open CategoryTheory CategoryTheory.Abelian
open scoped ModuleCat.Algebra TensorProduct
variable {k : Type} [Field k] [CharP k 2] (q : k)

lemma X_nonprojective (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) :
    ¬ Module.Projective (E q) (X q) := by
  intro h
  let := h
  have := Module.Projective.of_equiv (XTensorEquiv q).symm
  exact XTensor_nonprojective q hq hp this

end Tachikawa.Construction



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_StableLift
attribute [-instance] _root_.OAI.Tachikawa.DownHom.instAddCommGroupCochain _root_.OAI.Tachikawa.DownHom.instModuleCochain _root_.OAI.Tachikawa.Enveloping.instLinearModuleCatAlgEvaluation _root_.OAI.Tachikawa.Triangular.instAddCommGroupOff _root_.OAI.Tachikawa.Triangular.instAddCommGroupTriple _root_.OAI.Tachikawa.Triangular.instAdditiveModuleCatAlgD₀ _root_.OAI.Tachikawa.Triangular.instAdditiveModuleCatAlgD₁ _root_.OAI.Tachikawa.Triangular.instFiniteDimensionalAlgOfCarrierAlg _root_.OAI.Tachikawa.Triangular.instFiniteDimensionalCarrierAlgD₀ObjOfAlg _root_.OAI.Tachikawa.Triangular.instFiniteDimensionalCarrierAlgD₁Obj _root_.OAI.Tachikawa.Triangular.instFiniteDimensionalTripleOfCarrier _root_.OAI.Tachikawa.Triangular.instIsScalarTowerAlgTriple _root_.OAI.Tachikawa.Triangular.instIsScalarTowerMulOppositeProdOff _root_.OAI.Tachikawa.Triangular.instIsScalarTowerProdOff _root_.OAI.Tachikawa.Triangular.instModuleAlgTriple _root_.OAI.Tachikawa.Triangular.instModuleMulOppositeProdOff _root_.OAI.Tachikawa.Triangular.instModuleOff _root_.OAI.Tachikawa.Triangular.instModuleProdOff _root_.OAI.Tachikawa.Triangular.instModuleTriple _root_.OAI.Tachikawa.Triangular.instProjectiveCarrierOneFree _root_.OAI.Tachikawa.Triangular.instSMulCommClassProdMulOppositeOff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace Tachikawa
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  [FiniteDimensional k R] [FiniteDimensional k S]
  (t : SymmetrizingForm (k := k) (R := R)) (u : SymmetrizingForm (k := k) (R := S))
  (X : ModuleCat.{0} R) (Z : ModuleCat.{0} S) [FiniteDimensional k X]

include t u in

theorem evaluation_nonzero_of_syzygy_composition
    (U M T : FiniteModule k (Enveloping.Alg k S R))
    [Module.Projective Rᵐᵒᵖ (Enveloping.Obj U.obj)]
    [Module.Projective Rᵐᵒᵖ (Enveloping.Obj M.obj)]
    (e : T.obj ≃ₗ[Enveloping.Alg k S R] HomBimodule.obj (k := k) X Z)
    (g : U.obj →ₗ[Enveloping.Alg k S R] M.obj)
    (phi : M.obj →ₗ[Enveloping.Alg k S R] T.syzygy.obj)
    (hn : phi.comp g ∉ projectiveFactors (k := k)) :
    (Enveloping.evalMap X (ModuleCat.ofHom (X := U.obj) (Y := M.obj) g)).hom
      ∉ projectiveFactors (k := k) := by
  let tau := Enveloping.envelopingForm u t
  let : Module.Injective (Enveloping.Alg k S R) (Enveloping.Alg k S R) := tau.injective
  let PU := ModuleCat.of (Enveloping.Alg k S R)
    (Fin (Module.finrank k U) → Enveloping.Alg k S R)
  let PM := ModuleCat.of (Enveloping.Alg k S R)
    (Fin (Module.finrank k M) → Enveloping.Alg k S R)
  let PT := ModuleCat.of (Enveloping.Alg k S R) (Fin T.cover.rank → Enveloping.Alg k S R)
  obtain ⟨h,g',hu,hl⟩ := exists_exact_square_down (P := PU) (Q := PM)
    (U.embed tau) (U.cosyzygyProjection tau) (U.embed_injective tau)
    (U.cosyzygyProjection_exact tau) (U.cosyzygyProjection_surjective tau)
    (M.embed tau) (M.cosyzygyProjection tau) (M.cosyzygyProjection_exact tau) g
  obtain ⟨h',psi,hu',hl'⟩ := exists_exact_square_down (P := PM) (Q := PT)
    (M.embed tau) (M.cosyzygyProjection tau) (M.embed_injective tau)
    (M.cosyzygyProjection_exact tau) (M.cosyzygyProjection_surjective tau)
    T.syzygyInclusion T.cover.map T.syzygyInclusion_exact phi
  have hnon : psi.comp g' ∉ projectiveFactors (k := k) := by
    apply mt (exact_square_factors_iff (P := PU) (Q := PT)
      (U.embed tau) (U.cosyzygyProjection tau) (U.embed_injective tau)
      (U.cosyzygyProjection_exact tau) (U.cosyzygyProjection_surjective tau)
      T.syzygyInclusion T.cover.map T.syzygyInclusion_injective
      T.syzygyInclusion_exact T.cover.surjective
      (phi.comp g) (h'.comp h) (psi.comp g') ?_ ?_).mpr hn
    · rw [LinearMap.comp_assoc,hu,← LinearMap.comp_assoc,hu',LinearMap.comp_assoc]
    · rw [← LinearMap.comp_assoc,hl',LinearMap.comp_assoc,hl,← LinearMap.comp_assoc]
  intro hgeval
  have hshift : (Enveloping.evalMap X (ModuleCat.ofHom
      (X := (U.cosyzygy tau).obj) (Y := (M.cosyzygy tau).obj) g')).hom
        ∈ projectiveFactors (k := k) := by
    apply (Enveloping.eval_square_factors_iff t u X
      (ModuleCat.ofHom (X := U.obj) (Y := PU) (U.embed tau))
      (ModuleCat.ofHom (X := PU) (Y := (U.cosyzygy tau).obj) (U.cosyzygyProjection tau))
      (U.embed_injective tau) (U.cosyzygyProjection_exact tau) (U.cosyzygyProjection_surjective tau)
      (ModuleCat.ofHom (X := M.obj) (Y := PM) (M.embed tau))
      (ModuleCat.ofHom (X := PM) (Y := (M.cosyzygy tau).obj) (M.cosyzygyProjection tau))
      (M.embed_injective tau) (M.cosyzygyProjection_exact tau) (M.cosyzygyProjection_surjective tau)
      (ModuleCat.ofHom g) (ModuleCat.ofHom h) (ModuleCat.ofHom g')
      (ModuleCat.hom_ext hu) (ModuleCat.hom_ext hl)).mp hgeval
  let gt : (U.cosyzygy tau).obj ⟶ (M.cosyzygy tau).obj := ModuleCat.ofHom g'
  let psit : (M.cosyzygy tau).obj ⟶ HomBimodule.obj (k := k) X Z :=
    ModuleCat.ofHom (X := (M.cosyzygy tau).obj)
      (Y := HomBimodule.obj (k := k) X Z) (e.toLinearMap.comp psi)
  have hc : (BimoduleTensorHom.uncurry (gt ≫ psit)).hom ∈ projectiveFactors (k := k) := by
    rw [BimoduleTensorHom.uncurry_precompose]
    exact projectiveFactors_postcomp hshift (BimoduleTensorHom.uncurry psit).hom
  let : Module.Projective Rᵐᵒᵖ (Enveloping.Obj (U.cosyzygy tau).obj) :=
    Enveloping.cosyzygy_right_projective u t U
  have hh := BimoduleTensorHom.factors_of_uncurry t u hc
  have hh' := projectiveFactors_postcomp hh e.symm.toLinearMap
  apply hnon
  convert hh' using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  change psi (g' x) = e.symm (e (psi (g' x)))
  exact (e.symm_apply_apply _).symm
end Tachikawa



namespace Tachikawa.Construction
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q H : k) (hH : H ≠ 0)

theorem exists_evaluated_Y_lift (hq : q ≠ 0) :
    ∃ g : (finiteU q H hH).obj ⟶ (Y q).obj,
      (Enveloping.evalMap (xObj q) g).hom ∉ projectiveFactors (k := k) := by
  obtain ⟨g,psi,hn⟩ := exists_Y_lift_with_nonzero_composition q H hH hq
  let : Module.Projective (E q)ᵐᵒᵖ (Enveloping.Obj (Y q).obj) := (Y_side_projective q hq).2
  let : Module.Projective (E q)ᵐᵒᵖ (Enveloping.Obj (finiteU q H hH).obj) := by
    change Module.Projective (E q)ᵐᵒᵖ (Enveloping.Obj (U q H hH))
    infer_instance
  refine ⟨g,?_⟩
  exact evaluation_nonzero_of_syzygy_composition (formE q) (formE q)
    (xObj q) (xObj q) (finiteU q H hH) (Y q) (finiteS q)
    (LinearEquiv.refl _ _) g.hom psi.hom hn




theorem exists_nonzero_X_YX (hq : q ≠ 0) :
    ∃ g : (finiteU q H hH).obj ⟶ (Y q).obj,
      ((uXIso q H hH).inv ≫ Enveloping.evalMap (xObj q) g).hom ∉
        projectiveFactors (k := k) := by
  obtain ⟨g,hg⟩ := exists_evaluated_Y_lift q H hH hq
  refine ⟨g,?_⟩
  intro hh
  have hp := projectiveFactors_precomp hh (uXIso q H hH).hom.hom
  apply hg
  convert hp using 1
  all_goals try with_reducible_and_instances rfl
  apply ModuleCat.hom_ext_iff.mp
  change Enveloping.evalMap (xObj q) g =
    (uXIso q H hH).hom ≫ ((uXIso q H hH).inv ≫ Enveloping.evalMap (xObj q) g)
  simp

end Tachikawa.Construction

end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_HomProfile
attribute [-instance] _root_.OAI.Tachikawa.DownHom.instAddCommGroupCochain _root_.OAI.Tachikawa.DownHom.instModuleCochain _root_.OAI.Tachikawa.Triangular.instFiniteDimensionalAlgOfCarrierAlg _root_.OAI.Tachikawa.Triangular.instFiniteDimensionalCarrierAlgD₀ObjOfAlg _root_.OAI.Tachikawa.Triangular.instFiniteDimensionalCarrierAlgD₁Obj
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace Tachikawa.Construction
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q : k)
  (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0)

def finiteX : FiniteModule k (E q) where
  obj := xObj q
  finite := Module.Finite.of_restrictScalars_finite k _ _

abbrev xComplete := (finiteX q).complete (formE q)

def completeYStableEquiv (a : ℤ) :
    StableMap (k := k) (ModuleCat.of (E q) (CokerAt (xComplete q) a))
      (MissingYProfile.finiteYX q).obj ≃ₗ[k] MissingYProfile.W q a := by
  let : Module.Injective (E q) (E q) := (formE q).injective
  let e₁ := (yxFiberStableEquiv q hq hp).post
    (ModuleCat.of (E q) (CokerAt (xComplete q) a))
  have e₂ := cokerStableHomTranslate (xComplete q) ((finiteX q).complete_exact (formE q))
    (jjFiber q hq hp) (jjFiber_totallyAcyclic q hq hp).1
    ((finiteX q).complete_finite (formE q)) ((finiteX q).complete_projective (formE q))
    (jjFiber_finite q hq hp) (jjFiber_projective q hq hp) 0 (1-a) a (k := k)
  rw [zero_add,show 1-a+a=1 by omega] at e₂
  let e₃ := (StableEquiv.ofLinearEquiv (k := k)
    (M := ModuleCat.of (E q) (CokerAt (xComplete q) 0)) (N := xObj q)
    ((finiteX q).cokerEquiv (formE q))).pre
      (ModuleCat.of (E q) (CokerAt (jjFiber q hq hp) (1-a)))
  let e₄ := (yxShiftFiberStableEquiv q hq hp a).post (xObj q)
  exact e₁.trans (e₂.symm.trans (e₃.trans e₄.symm))

def completeYHomologyEquiv (a : ℤ) :
    VectorSplit.H (completeHom (k := k) (xComplete q) (MissingYProfile.finiteYX q).obj) a ≃ₗ[k]
      MissingYProfile.W q a :=
  (CompleteHom.equiv (xComplete q) (MissingYProfile.finiteYX q).obj
    ((finiteX q).complete_totallyAcyclic (formE q))
    ((finiteX q).complete_finite (formE q)) ((finiteX q).complete_projective (formE q)) a).trans
      (completeYStableEquiv q hq hp a)

end Tachikawa.Construction



namespace Tachikawa.Construction
open CategoryTheory CategoryTheory.Abelian
open scoped ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q : k)
  (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0)

abbrev selfHom := completeHom (k := k) (xComplete q) (xObj q)

def positiveSelfHomExt (n : ℕ) : VectorSplit.H (selfHom q) ((n+1:ℕ):ℤ) ≃ₗ[k]
    Ext (xObj q) (xObj q) (n+1) :=
  (CompleteHom.equiv (xComplete q) (xObj q)
    ((finiteX q).complete_totallyAcyclic (formE q))
    ((finiteX q).complete_finite (formE q)) ((finiteX q).complete_projective (formE q)) _).trans
  ((CompleteStableExt.equiv _ ((finiteX q).complete_totallyAcyclic (formE q))
    ((finiteX q).complete_finite (formE q)) ((finiteX q).complete_projective (formE q))
    (xObj q) n).trans (extIso (k := k) ((finiteX q).cokerEquiv (formE q)).toModuleIso
    (Iso.refl _) (n+1)))

def selfHomDual (a : ℤ) : VectorSplit.H (selfHom q) a ≃ₗ[k]
    Module.Dual k (VectorSplit.H (selfHom q) (-a-1)) := by
  let P := xComplete q
  let ce := (finiteX q).cokerEquiv (formE q)
  let ta := (finiteX q).complete_totallyAcyclic (formE q)
  let fin := (finiteX q).complete_finite (formE q)
  let proj := (finiteX q).complete_projective (formE q)
  let e₁ := CompleteHom.equiv (k := k) P (xObj q) ta fin proj a
  let e₂ := (StableEquiv.ofLinearEquiv (k := k)
    (M := ModuleCat.of (E q) (CokerAt P 0)) (N := xObj q) ce).symm.post
      (ModuleCat.of (E q) (CokerAt P a))
  have e₃ := cokerStableHomTranslate P ta.1 P ta.1 fin proj fin proj a 0 (-a) (k := k)
  rw [add_neg_cancel,zero_add] at e₃
  let e₄ := (StableEquiv.ofLinearEquiv (k := k)
    (M := ModuleCat.of (E q) (CokerAt P 0)) (N := xObj q) ce).pre
      (ModuleCat.of (E q) (CokerAt P (-a)))
  have e₅ := completeCokerDuality (formE q) P ta.1 fin proj (-a-1) (xObj q)
  rw [show -a-1+1 = -a by omega] at e₅
  exact e₁.trans (e₂.trans (e₃.trans (e₄.trans
    (e₅.trans (CompleteHom.equiv (k := k) P (xObj q) ta fin proj (-a-1)).dualMap))))

omit [CharP k 2] in
lemma XEnd_scalar (f : xObj q →ₗ[E q] xObj q) :
    f = (show k from f (1 : k)) • LinearMap.id := by
  apply LinearMap.ext
  intro x
  have h := f.map_smul (algebraMap k (E q) (show k from x)) (1:k)
  change f ((characterE q (algebraMap k (E q) (show k from x))) * 1) =
    (characterE q (algebraMap k (E q) (show k from x))) * (show k from f (1:k)) at h
  erw [(characterE q).commutes,Algebra.algebraMap_self,mul_one] at h
  change f x = (characterE q (algebraMap k (E q) (show k from f (1:k)))) * (show k from x)
  rw [(characterE q).commutes,Algebra.algebraMap_self]
  exact h.trans (mul_comm (show k from x) (show k from f (1:k)))

include hq hp in
def stableXEndEquiv : StableMap (k := k) (xObj q) (xObj q) ≃ₗ[k] k := by
  let : Module.Finite (E q) (xObj q) := (finiteX q).finite
  let v := stableClass (k := k) (LinearMap.id (R := E q) (M := xObj q))
  have hv : v ≠ 0 := (stable_id_ne_zero_iff (k := k)).mpr (X_nonprojective q hq hp)
  let f := LinearMap.toSpanSingleton k _ v
  apply (LinearEquiv.ofBijective f ?_).symm
  constructor
  · apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro c hc
    exact (smul_eq_zero.mp hc).resolve_right hv
  · intro x
    obtain ⟨g,rfl⟩ := stableClass_surjective x
    use (show k from g (1:k))
    conv_rhs => rw [XEnd_scalar q g,map_smul]
    rfl

def selfHomZeroEquiv : VectorSplit.H (selfHom q) 0 ≃ₗ[k] k :=
  (CompleteHom.zeroEquiv (xComplete q) ((finiteX q).complete_totallyAcyclic (formE q))
    ((finiteX q).complete_finite (formE q)) ((finiteX q).complete_projective (formE q))
    (X := xObj q) ((finiteX q).cokerEquiv (formE q)) (xObj q)).trans (stableXEndEquiv q hq hp)
end Tachikawa.Construction



namespace Tachikawa.Construction
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q H : k) (hH : H ≠ 0)
  (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0)

abbrev xTwistHom : selfHom q ⟶ selfHom q :=
  (finiteX q).completeTwistHom (formE q) (sigma q H hH) (XTwistIso q H hH)

end Tachikawa.Construction

end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Delta
attribute [-instance] _root_.OAI.Tachikawa.DownHom.instAddCommGroupCochain _root_.OAI.Tachikawa.DownHom.instModuleCochain _root_.OAI.Tachikawa.Triangular.instAddCommGroupOff _root_.OAI.Tachikawa.Triangular.instAddCommGroupTriple _root_.OAI.Tachikawa.Triangular.instAdditiveModuleCatAlgD₀ _root_.OAI.Tachikawa.Triangular.instAdditiveModuleCatAlgD₁ _root_.OAI.Tachikawa.Triangular.instFiniteDimensionalAlgOfCarrierAlg _root_.OAI.Tachikawa.Triangular.instFiniteDimensionalCarrierAlgD₀ObjOfAlg _root_.OAI.Tachikawa.Triangular.instFiniteDimensionalCarrierAlgD₁Obj _root_.OAI.Tachikawa.Triangular.instFiniteDimensionalTripleOfCarrier _root_.OAI.Tachikawa.Triangular.instIsScalarTowerAlgTriple _root_.OAI.Tachikawa.Triangular.instIsScalarTowerMulOppositeProdOff _root_.OAI.Tachikawa.Triangular.instIsScalarTowerProdOff _root_.OAI.Tachikawa.Triangular.instModuleAlgTriple _root_.OAI.Tachikawa.Triangular.instModuleMulOppositeProdOff _root_.OAI.Tachikawa.Triangular.instModuleOff _root_.OAI.Tachikawa.Triangular.instModuleProdOff _root_.OAI.Tachikawa.Triangular.instModuleTriple _root_.OAI.Tachikawa.Triangular.instSMulCommClassProdMulOppositeOff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace Tachikawa.Construction
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q : k)
variable (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0)

variable (H : k) (hH : H ≠ 0)

lemma exists_normalized_map : ∃ g : (finiteU q H hH).obj ⟶ (Y q).obj,
    evaluatedStableMap q H hH g = wZero q hq hp := by
  obtain ⟨g,hg⟩ := exists_nonzero_X_YX q H hH hq
  have hn : evaluatedStableMap q H hH g ≠ 0 := by
    exact fun h => hg ((stableClass_eq_zero_iff _).mp h)
  have hc : WZeroEquiv q hq hp (evaluatedStableMap q H hH g) ≠ 0 := by
    intro h
    exact hn ((WZeroEquiv q hq hp).injective (h.trans (map_zero _).symm))
  refine ⟨(WZeroEquiv q hq hp (evaluatedStableMap q H hH g))⁻¹ • g,?_⟩
  apply (WZeroEquiv q hq hp).injective
  rw [map_smul,map_smul]
  simp [wZero,smul_eq_mul,inv_mul_cancel₀ hc]

def normalizedMap : (finiteU q H hH).obj ⟶ (Y q).obj :=
  Classical.choose (exists_normalized_map q hq hp H hH)

lemma normalizedMap_class : evaluatedStableMap q H hH (normalizedMap q hq hp H hH) =
    wZero q hq hp := Classical.choose_spec (exists_normalized_map q hq hp H hH)

end Tachikawa.Construction



namespace Tachikawa.Construction
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q : k)
  (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0)
  (H₁ H₂ : k) (h₁ : H₁ ≠ 0) (h₂ : H₂ ≠ 0)

def concreteF : FiniteModule k (Enveloping.Alg k (E q) (E q)) :=
  Enveloping.fiber (finiteU q H₁ h₁) (finiteU q H₂ h₂) (Y q)
    (normalizedMap q hq hp H₁ h₁) (normalizedMap q hq hp H₂ h₂)

lemma concreteF_side_projective :
    Module.Projective (E q) (Enveloping.Obj (concreteF q hq hp H₁ H₂ h₁ h₂).obj) ∧
    Module.Projective (E q)ᵐᵒᵖ (Enveloping.Obj (concreteF q hq hp H₁ H₂ h₁ h₂).obj) := by
  let : Module.Projective (E q) (Enveloping.Obj (finiteU q H₁ h₁).obj) := by
    exact inferInstanceAs (Module.Projective (E q)
      (Enveloping.Obj (Enveloping.twistedRegular (sigma q H₁ h₁))))
  let : Module.Projective (E q) (Enveloping.Obj (finiteU q H₂ h₂).obj) := by
    exact inferInstanceAs (Module.Projective (E q)
      (Enveloping.Obj (Enveloping.twistedRegular (sigma q H₂ h₂))))
  let : Module.Projective (E q)ᵐᵒᵖ (Enveloping.Obj (finiteU q H₁ h₁).obj) := by
    exact inferInstanceAs (Module.Projective (E q)ᵐᵒᵖ
      (Enveloping.Obj (Enveloping.twistedRegular (sigma q H₁ h₁))))
  let : Module.Projective (E q)ᵐᵒᵖ (Enveloping.Obj (finiteU q H₂ h₂).obj) := by
    exact inferInstanceAs (Module.Projective (E q)ᵐᵒᵖ
      (Enveloping.Obj (Enveloping.twistedRegular (sigma q H₂ h₂))))
  let := (Y_side_projective q hq).1
  let := (Y_side_projective q hq).2
  constructor
  · exact Enveloping.fiber_left_projective _ _ _ _ _
  · exact Enveloping.fiber_right_projective _ _ _ _ _

abbrev concreteMiddle := Enveloping.fiberMiddle (finiteU q H₁ h₁) (finiteU q H₂ h₂) (Y q)
abbrev concreteProjection := Enveloping.fiberProjection (finiteU q H₁ h₁) (finiteU q H₂ h₂)
  (Y q) (normalizedMap q hq hp H₁ h₁) (normalizedMap q hq hp H₂ h₂)
abbrev concreteInclusion := Enveloping.fiberInclusion (finiteU q H₁ h₁) (finiteU q H₂ h₂)
  (Y q) (normalizedMap q hq hp H₁ h₁) (normalizedMap q hq hp H₂ h₂)

lemma concrete_evaluated_injective : Function.Injective
    (Enveloping.evalMap (xObj q) (concreteInclusion q hq hp H₁ H₂ h₁ h₂)) := by
  let : Module.Projective (E q)ᵐᵒᵖ (Enveloping.Obj
      (Enveloping.fiber (finiteU q H₁ h₁) (finiteU q H₂ h₂) (Y q)
        (normalizedMap q hq hp H₁ h₁) (normalizedMap q hq hp H₂ h₂)).obj) :=
    (concreteF_side_projective q hq hp H₁ H₂ h₁ h₂).2
  exact Enveloping.evalMap_injective (xObj q) (formE q) _
    (Enveloping.fiberInclusion_injective _ _ _ _ _)

lemma concrete_evaluated_exact : Function.Exact
    (Enveloping.evalMap (xObj q) (concreteInclusion q hq hp H₁ H₂ h₁ h₂))
    (Enveloping.evalMap (xObj q) (concreteProjection q hq hp H₁ H₂ h₁ h₂)) := by
  let : Module.Projective (E q)ᵐᵒᵖ (Enveloping.Obj
      (Enveloping.fiber (finiteU q H₁ h₁) (finiteU q H₂ h₂) (Y q)
        (normalizedMap q hq hp H₁ h₁) (normalizedMap q hq hp H₂ h₂)).obj) :=
    (concreteF_side_projective q hq hp H₁ H₂ h₁ h₂).2
  exact Enveloping.evalMap_exact (xObj q) (formE q) _ _
    (Enveloping.fiberInclusion_injective _ _ _ _ _)
    (Enveloping.fiber_exact _ _ _ _ _) (Enveloping.fiberProjection_surjective _ _ _ _ _)

end Tachikawa.Construction



namespace Tachikawa.Construction
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q : k)
  (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0)
  (H₁ H₂ : k) (h₁ : H₁ ≠ 0) (h₂ : H₂ ≠ 0)

abbrev concreteFst := concreteInclusion q hq hp H₁ H₂ h₁ h₂ ≫
  Enveloping.fiberFst (finiteU q H₁ h₁) (finiteU q H₂ h₂) (Y q)
abbrev concreteSnd := concreteInclusion q hq hp H₁ H₂ h₁ h₂ ≫
  Enveloping.fiberSnd (finiteU q H₁ h₁) (finiteU q H₂ h₂) (Y q)

lemma exists_concrete_vZero : ∃ v : xObj q ⟶ Enveloping.evalObj (xObj q)
    (concreteF q hq hp H₁ H₂ h₁ h₂).obj,
    v ≫ Enveloping.evalMap (xObj q) (concreteFst q hq hp H₁ H₂ h₁ h₂) = (uXIso q H₁ h₁).inv ∧
    v ≫ Enveloping.evalMap (xObj q) (concreteSnd q hq hp H₁ H₂ h₁ h₂) = (uXIso q H₂ h₂).inv := by
  let L := Enveloping.evaluation (k := k) (S := E q) (xObj q)
  let U := finiteU q H₁ h₁
  let V := finiteU q H₂ h₂
  let g := normalizedMap q hq hp H₁ h₁
  let h := normalizedMap q hq hp H₂ h₂
  let i := L.map (concreteInclusion q hq hp H₁ H₂ h₁ h₂)
  let p := L.map (concreteProjection q hq hp H₁ H₂ h₁ h₂)
  let j := L.map (Enveloping.fiberInr U V (Y q))
  let a := (uXIso q H₁ h₁).inv ≫ L.map (Enveloping.fiberInl U V (Y q)) +
    (uXIso q H₂ h₂).inv ≫ L.map (Enveloping.fiberInm U V (Y q))
  have hap : a ≫ p = (uXIso q H₁ h₁).inv ≫ L.map g +
      (uXIso q H₂ h₂).inv ≫ L.map h := by
    change (_ + _) ≫ L.map (Enveloping.fiberProjection U V (Y q) g h) = _
    refine (Preadditive.add_comp _ _ _ _ _ _).trans (congrArg₂ (· + ·) ?_ ?_)
    · exact (Category.assoc _ _ _).trans (congrArg (fun morphism =>
        (uXIso q H₁ h₁).inv ≫ morphism) ((L.map_comp _ _).symm.trans
          (congrArg L.map (Enveloping.fiberInl_projection U V (Y q) g h))))
    · exact (Category.assoc _ _ _).trans (congrArg (fun morphism =>
        (uXIso q H₂ h₂).inv ≫ morphism) ((L.map_comp _ _).symm.trans
          (congrArg L.map (Enveloping.fiberInm_projection U V (Y q) g h))))
  have haz : stableClass (k := k) (a ≫ p).hom = 0 := by
    rw [hap]
    change evaluatedStableMap q H₁ h₁ g + evaluatedStableMap q H₂ h₂ h = 0
    rw [normalizedMap_class,normalizedMap_class,← two_smul k]
    have hz : (2:k) = 0 := CharP.cast_eq_zero k 2
    rw [hz,zero_smul]
  have hjp : j ≫ p = L.map (ModuleCat.ofHom (Y q).cover.map) := by
    rw [← L.map_comp]
    exact congrArg L.map (Enveloping.fiberInr_projection U V (Y q) g h)
  have hj : Function.Surjective (j ≫ p) := by
    rw [hjp]
    exact Enveloping.evalMap_surjective (xObj q) _ (Y q).cover.surjective
  obtain ⟨v,b,hv⟩ := exists_stable_kernel_lift i p j
    (concrete_evaluated_injective q hq hp H₁ H₂ h₁ h₂)
    (concrete_evaluated_exact q hq hp H₁ H₂ h₁ h₂) hj a haz
  refine ⟨v,?_,?_⟩
  · change v ≫ L.map (_ ≫ Enveloping.fiberFst U V (Y q)) = _
    rw [L.map_comp,← Category.assoc]
    change (v ≫ i) ≫ L.map (Enveloping.fiberFst U V (Y q)) = _
    rw [hv]
    have hl : L.map (Enveloping.fiberInl U V (Y q)) ≫
        L.map (Enveloping.fiberFst U V (Y q)) = 𝟙 _ :=
      ((L.map_comp _ _).symm.trans (congrArg L.map
        (Enveloping.fiberInl_fst U V (Y q)))).trans (L.map_id _)
    have hm : L.map (Enveloping.fiberInm U V (Y q)) ≫
        L.map (Enveloping.fiberFst U V (Y q)) = 0 :=
      ((L.map_comp _ _).symm.trans (congrArg L.map
        (Enveloping.fiberInm_fst U V (Y q)))).trans (L.map_zero _ _)
    have hr : j ≫ L.map (Enveloping.fiberFst U V (Y q)) = 0 :=
      ((L.map_comp _ _).symm.trans (congrArg L.map
        (Enveloping.fiberInr_fst U V (Y q)))).trans (L.map_zero _ _)
    have ha : a ≫ L.map (Enveloping.fiberFst U V (Y q)) = (uXIso q H₁ h₁).inv :=
      (Preadditive.add_comp _ _ _ _ _ _).trans ((congrArg₂ (· + ·)
        ((Category.assoc _ _ _).trans ((congrArg (fun morphism =>
          (uXIso q H₁ h₁).inv ≫ morphism) hl).trans (Category.comp_id _)))
        ((Category.assoc _ _ _).trans ((congrArg (fun morphism =>
          (uXIso q H₂ h₂).inv ≫ morphism) hm).trans comp_zero))).trans (add_zero _))
    have hb : (b ≫ j) ≫ L.map (Enveloping.fiberFst U V (Y q)) = 0 :=
      (Category.assoc _ _ _).trans ((congrArg (fun morphism => b ≫ morphism) hr).trans
        comp_zero)
    exact (Preadditive.sub_comp _ _ _).trans
      ((congrArg₂ (· - ·) ha hb).trans (sub_zero _))
  · change v ≫ L.map (_ ≫ Enveloping.fiberSnd U V (Y q)) = _
    rw [L.map_comp,← Category.assoc]
    change (v ≫ i) ≫ L.map (Enveloping.fiberSnd U V (Y q)) = _
    rw [hv]
    have hl : L.map (Enveloping.fiberInl U V (Y q)) ≫
        L.map (Enveloping.fiberSnd U V (Y q)) = 0 :=
      ((L.map_comp _ _).symm.trans (congrArg L.map
        (Enveloping.fiberInl_snd U V (Y q)))).trans (L.map_zero _ _)
    have hm : L.map (Enveloping.fiberInm U V (Y q)) ≫
        L.map (Enveloping.fiberSnd U V (Y q)) = 𝟙 _ :=
      ((L.map_comp _ _).symm.trans (congrArg L.map
        (Enveloping.fiberInm_snd U V (Y q)))).trans (L.map_id _)
    have hr : j ≫ L.map (Enveloping.fiberSnd U V (Y q)) = 0 :=
      ((L.map_comp _ _).symm.trans (congrArg L.map
        (Enveloping.fiberInr_snd U V (Y q)))).trans (L.map_zero _ _)
    have ha : a ≫ L.map (Enveloping.fiberSnd U V (Y q)) = (uXIso q H₂ h₂).inv :=
      (Preadditive.add_comp _ _ _ _ _ _).trans ((congrArg₂ (· + ·)
        ((Category.assoc _ _ _).trans ((congrArg (fun morphism =>
          (uXIso q H₁ h₁).inv ≫ morphism) hl).trans comp_zero))
        ((Category.assoc _ _ _).trans ((congrArg (fun morphism =>
          (uXIso q H₂ h₂).inv ≫ morphism) hm).trans (Category.comp_id _)))).trans
            (zero_add _))
    have hb : (b ≫ j) ≫ L.map (Enveloping.fiberSnd U V (Y q)) = 0 :=
      (Category.assoc _ _ _).trans ((congrArg (fun morphism => b ≫ morphism) hr).trans
        comp_zero)
    exact (Preadditive.sub_comp _ _ _).trans
      ((congrArg₂ (· - ·) ha hb).trans (sub_zero _))

def concreteVZero := (exists_concrete_vZero q hq hp H₁ H₂ h₁ h₂).choose

end Tachikawa.Construction



namespace Tachikawa.Construction
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q : k)
  (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0)
  (H₁ H₂ : k) (h₁ : H₁ ≠ 0) (h₂ : H₂ ≠ 0)

abbrev FHom := completeHom (k := k) (xComplete q)
  (Enveloping.evalObj (xObj q) (concreteF q hq hp H₁ H₂ h₁ h₂).obj)
abbrev middleHom := completeHom (k := k) (xComplete q)
  (Enveloping.evalObj (xObj q) (concreteMiddle q H₁ H₂ h₁ h₂))
abbrev FHomInclusion := completeHomMap (k := k) (xComplete q)
  (Enveloping.evalMap (xObj q) (concreteInclusion q hq hp H₁ H₂ h₁ h₂))
abbrev FHomProjection := completeHomMap (k := k) (xComplete q)
  (Enveloping.evalMap (xObj q) (concreteProjection q hq hp H₁ H₂ h₁ h₂))

def middleHpair (a : ℤ) :=
  (completeHmap (k := k) (xComplete q) (Enveloping.evalMap (xObj q)
      (Enveloping.fiberFst (finiteU q H₁ h₁) (finiteU q H₂ h₂) (Y q))) a).prod
  (completeHmap (k := k) (xComplete q) (Enveloping.evalMap (xObj q)
      (Enveloping.fiberSnd (finiteU q H₁ h₁) (finiteU q H₂ h₂) (Y q))) a)

end Tachikawa.Construction



namespace Tachikawa.Construction
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q : k)
  (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0)
  (H₁ H₂ : k) (h₁ : H₁ ≠ 0) (h₂ : H₂ ≠ 0)

abbrev zeroHomEquiv (N : ModuleCat (E q)) :=
  CompleteHom.zeroEquiv (k := k) (xComplete q) ((finiteX q).complete_totallyAcyclic (formE q))
    ((finiteX q).complete_finite (formE q)) ((finiteX q).complete_projective (formE q))
    ((finiteX q).cokerEquiv (formE q)) N

def middleHpairX (a : ℤ) :=
  ((completeHomIso (k := k) (xComplete q) (uXIso q H₁ h₁) a).prodCongr
    (completeHomIso (k := k) (xComplete q) (uXIso q H₂ h₂) a)).toLinearMap.comp
      (middleHpair q H₁ H₂ h₁ h₂ a)

def FHomPair (a : ℤ) := (middleHpairX q H₁ H₂ h₁ h₂ a).comp
    (VectorSplit.Hmap (FHomInclusion q hq hp H₁ H₂ h₁ h₂) a)

end Tachikawa.Construction



namespace Tachikawa.Construction
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q : k)
  (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0)
  (H₁ H₂ : k) (h₁ : H₁ ≠ 0) (h₂ : H₂ ≠ 0)

local instance concreteF_left_projective : Module.Projective (E q)
    (Enveloping.Obj (concreteF q hq hp H₁ H₂ h₁ h₂).obj) :=
  (concreteF_side_projective q hq hp H₁ H₂ h₁ h₂).1
local instance concreteF_right_projective : Module.Projective (E q)ᵐᵒᵖ
    (Enveloping.Obj (concreteF q hq hp H₁ H₂ h₁ h₂).obj) :=
  (concreteF_side_projective q hq hp H₁ H₂ h₁ h₂).2
local instance concreteF_finite : FiniteDimensional k
    (Enveloping.Obj (concreteF q hq hp H₁ H₂ h₁ h₂).obj) :=
by
  change Module.Finite k (concreteF q hq hp H₁ H₂ h₁ h₂)
  infer_instance

abbrev concreteLift := Enveloping.tensorCompleteLift (concreteF q hq hp H₁ H₂ h₁ h₂).obj
  (finiteX q) (formE q) (concreteVZero q hq hp H₁ H₂ h₁ h₂)
abbrev FAction : selfHom q ⟶ FHom q hq hp H₁ H₂ h₁ h₂ :=
  completeFunctorHom (k := k) (Enveloping.tensorFunctor (concreteF q hq hp H₁ H₂ h₁ h₂).obj)
    (xComplete q) (xComplete q) (xObj q) (concreteLift q hq hp H₁ H₂ h₁ h₂)
abbrev VAction : selfHom q ⟶ FHom q hq hp H₁ H₂ h₁ h₂ :=
  completeHomMap (k := k) (xComplete q) (concreteVZero q hq hp H₁ H₂ h₁ h₂)
abbrev FFirst : FHom q hq hp H₁ H₂ h₁ h₂ ⟶ selfHom q :=
  completeHomMap (k := k) (xComplete q)
    (Enveloping.evalMap (xObj q) (concreteFst q hq hp H₁ H₂ h₁ h₂) ≫ (uXIso q H₁ h₁).hom)
abbrev FSecond : FHom q hq hp H₁ H₂ h₁ h₂ ⟶ selfHom q :=
  completeHomMap (k := k) (xComplete q)
    (Enveloping.evalMap (xObj q) (concreteSnd q hq hp H₁ H₂ h₁ h₂) ≫ (uXIso q H₂ h₂).hom)

end Tachikawa.Construction



namespace Tachikawa
namespace Construction
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q : k)
  (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0)
  (H₁ H₂ : k) (h₁ : H₁ ≠ 0) (h₂ : H₂ ≠ 0)

def delta (a : ℤ) : (VectorSplit.H (selfHom q) a × VectorSplit.H (selfHom q) a) →ₗ[k]
    VectorSplit.H (FHom q hq hp H₁ H₂ h₁ h₂) a :=
  (VectorSplit.Hmap (FAction q hq hp H₁ H₂ h₁ h₂) a).coprod
    (VectorSplit.Hmap (VAction q hq hp H₁ H₂ h₁ h₂) a)

end Construction

namespace SourceField
open Construction
abbrev sourceDelta (a : ℤ) := delta q (parameter_ne_zero 0) one_add_q_pow_ne_zero
  H₁ H₂ (parameter_ne_zero 1) (parameter_ne_zero 2) a

end SourceField
end Tachikawa



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Counterexample
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace Tachikawa.SourceField
open CategoryTheory Construction
open scoped ModuleCat.Algebra
abbrev sourceF := concreteF q (parameter_ne_zero 0) one_add_q_pow_ne_zero
  H₁ H₂ (parameter_ne_zero 1) (parameter_ne_zero 2)
abbrev sourceX := finiteX q
abbrev sourceP := xComplete q
local instance sourceF_left_rc56db7_1 : Module.Projective (E q) (Enveloping.Obj sourceF.obj) :=
  (concreteF_side_projective q (parameter_ne_zero 0) one_add_q_pow_ne_zero
    H₁ H₂ (parameter_ne_zero 1) (parameter_ne_zero 2)).1
local instance sourceF_right_rc56db7_1 : Module.Projective (E q)ᵐᵒᵖ (Enveloping.Obj sourceF.obj) :=
  (concreteF_side_projective q (parameter_ne_zero 0) one_add_q_pow_ne_zero
    H₁ H₂ (parameter_ne_zero 1) (parameter_ne_zero 2)).2
local instance sourceF_finite_rc56db7_1 : FiniteDimensional K (Enveloping.Obj sourceF.obj) :=
  inferInstanceAs (FiniteDimensional K sourceF)
abbrev sourceU := concreteLift q (parameter_ne_zero 0) one_add_q_pow_ne_zero
  H₁ H₂ (parameter_ne_zero 1) (parameter_ne_zero 2)
abbrev sourceUZero := concreteVZero q (parameter_ne_zero 0) one_add_q_pow_ne_zero
  H₁ H₂ (parameter_ne_zero 1) (parameter_ne_zero 2)
abbrev sourceTriangle := Triangular.Alg sourceF.obj
abbrev sourceCone := Triangular.cone sourceF.obj sourceU

abbrev sourceAug : sourceP.X 0 ⟶ sourceX.obj := ModuleCat.ofHom sourceX.cover.map
end Tachikawa.SourceField



namespace Tachikawa.SourceField
open CategoryTheory Construction
open scoped ModuleCat.Algebra
abbrev sourceConeModule := CokerAt sourceCone 0

abbrev sourceAlgebra := TrivialExtension K sourceTriangle
abbrev sourceModule := TrivialInduction.Obj K sourceTriangle sourceConeModule
end Tachikawa.SourceField



namespace Tachikawa.SourceField
instance sourceAlgebra_finite : Module.Finite K sourceAlgebra := inferInstanceAs
  (Module.Finite K (TrivialExtension K sourceTriangle))
end Tachikawa.SourceField



end

end OAI
end


