-- Prove2me | Definitions.Def_OAIQ116Ta014
-- name    : OAIQ116Ta014
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T02:19:28.583998+00:00
-- url     : https://prove2.me/theorems/913803a3-7d54-4d2d-985f-17b204264c50
-- title:
--   Definitions bundle OAIQ116Ta014 of the split of OpenAI, A counterexample to Tachikawa's second conjecture
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Tachikawa.main_theorem`, carved from OpenAI's openai/math development (OpenAI, *A counterexample to Tachikawa's second conjecture*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 158 declarations of OpenAI's Lean: 63 definitions, 5 instances and 90 theorems. The definitions and types are `OAI.Tachikawa.C.twistInitialHom`, `OAI.Tachikawa.C.twistMiddleHom`, `OAI.Tachikawa.C.twistUpperHom`, `OAI.Tachikawa.CompleteStableExt.cycles`, `OAI.Tachikawa.CompleteStableExt.equiv`, `OAI.Tachikawa.CompleteStableExt.toExt`, `OAI.Tachikawa.Construction.WFiberDualEquiv`, `OAI.Tachikawa.Construction.WZeroEquiv`, `OAI.Tachikawa.Construction.bDualRightResolution`, `OAI.Tachikawa.Construction.bimoduleRestriction`, `OAI.Tachikawa.Construction.eLeftResolution`, `OAI.Tachikawa.Construction.eRightResolution`, `OAI.Tachikawa.Construction.evalFiveFiberStableEquiv`, `OAI.Tachikawa.Construction.evalK`, `OAI.Tachikawa.Construction.evalNegativeFiveFiberStableEquiv`, `OAI.Tachikawa.Construction.evaluatedKJComparison`, `OAI.Tachikawa.Construction.evaluatedStableMap`, `OAI.Tachikawa.Construction.finiteS`, `OAI.Tachikawa.Construction.finiteU`, `OAI.Tachikawa.Construction.forwardJJHomEquiv`, `OAI.Tachikawa.Construction.inducedBToJComparison`, `OAI.Tachikawa.Construction.inducedRepresentationMap`, `OAI.Tachikawa.Construction.inducedSocleMap`, `OAI.Tachikawa.Construction.jjFiberHighCokerEquiv`, `OAI.Tachikawa.Construction.jjFiberHomEquiv`, `OAI.Tachikawa.Construction.jjFiberHomThreeEquiv`, `OAI.Tachikawa.Construction.jjFiberHomZeroEquiv`, `OAI.Tachikawa.Construction.jjFiberStableThreeEquiv`, `OAI.Tachikawa.Construction.jjFiberStableZeroEquiv`, `OAI.Tachikawa.Construction.jjNatIntCokerEquiv`, `OAI.Tachikawa.Construction.natJJFiveFiberEquiv`, `OAI.Tachikawa.Construction.restrictedBimoduleResolution`, `OAI.Tachikawa.Construction.restrictedLeftResolution`, `OAI.Tachikawa.Construction.restrictedRightResolution`, `OAI.Tachikawa.Construction.restrictedUUnderlying`, `OAI.Tachikawa.Construction.reverseJJHomEquiv`, `OAI.Tachikawa.Construction.rhoBimodule`, `OAI.Tachikawa.Construction.rhoBimoduleLinear`, `OAI.Tachikawa.Construction.tLeftResolution`, `OAI.Tachikawa.Construction.tRightResolution` and 23 more.
--
--   **Sources.** They come from these modules of lean/OAI/RingTheory, in whole or in part: `Tachikawa_Bimodule`, `Tachikawa_Coinduction`, `Tachikawa_Coresolution`, `Tachikawa_Delta`, `Tachikawa_DerivedDescent`, `Tachikawa_DerivedInduction`, `Tachikawa_FiniteCoinduction`, `Tachikawa_HomProfile`, `Tachikawa_Induction`, `Tachikawa_Perfect`, `Tachikawa_Period`, `Tachikawa_ReverseResolution`, `Tachikawa_StableLift`.
--
--   **Imports.** It imports the bundles `OAIQ116Ta010`, `OAIQ116Ta011` and `OAIQ116Ta012` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ116Ta016`.
-- source:
--   OpenAI, A counterexample to Tachikawa's second conjecture, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-counterexample-to-Tachikawas-second-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/RingTheory at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ116Ta010
import Definitions.Def_OAIQ116Ta011
import Definitions.Def_OAIQ116Ta012

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Coresolution
attribute [-instance] _root_.OAI.Tachikawa.DownHom.instAddCommGroupCochain _root_.OAI.Tachikawa.Enveloping.instAddCommGroupCarrierMulOppositeRightObj _root_.OAI.Tachikawa.Enveloping.instModuleCarrierMulOppositeRightObj_1 _root_.OAI.Tachikawa.LeftCoinduced.coextend_additive _root_.OAI.Tachikawa.LeftCoinduced.coextend_preservesInjective _root_.OAI.Tachikawa.OuterTensor.restrictionPreservesHomology _root_.OAI.Tachikawa.TotalDualPairing.instTensorSignsNatUp_solutions _root_.OAI.Tachikawa.TotalMap.sourceHasCoproduct _root_.OAI.Tachikawa.downIntTensorSigns
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

lemma resolutionHom_memZ (n : ℕ) (f : P.X n ⟶ N) :
    f ∈ VectorSplit.Z (resolutionHom k R P N) n ↔ P.d (n+1) n ≫ f = 0 := by
  change (resolutionHom k R P N).d n ((ComplexShape.up ℕ).next n) f = 0 ↔ _
  rw [show (ComplexShape.up ℕ).next n = n+1 from
    (ComplexShape.up ℕ).next_eq' rfl]
  rfl

variable {k R} {M : ModuleCat R} (Q : ProjectiveResolution M)

def resolutionCyclesToExt (n : ℕ) :
    VectorSplit.Z (resolutionHom k R Q.complex N) n →ₗ[k] Ext M N n where
  toFun z := Q.extMk z.val (n+1) rfl ((resolutionHom_memZ k R Q.complex N n z.val).mp z.property)
  map_add' x y := (Q.add_extMk x.val y.val (n+1) rfl _ _).symm
  map_smul' r z := extMk_smul N Q z.val ((resolutionHom_memZ k R Q.complex N n z.val).mp z.property) r _

end Tachikawa



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Period
attribute [-instance] _root_.OAI.Tachikawa.Construction.instFiniteCSubtypeMemSubmoduleCe _root_.OAI.Tachikawa.Construction.instFiniteCSubtypeMemSubmoduleCf _root_.OAI.Tachikawa.Construction.instFiniteMulOppositeC _root_.OAI.Tachikawa.Construction.instFiniteMulOppositeCSubtypeMemSubmoduleEC _root_.OAI.Tachikawa.Construction.instFiniteMulOppositeCSubtypeMemSubmoduleFC _root_.OAI.Tachikawa.Construction.instInjectiveE _root_.OAI.Tachikawa.Construction.instIsScalarTowerEX _root_.OAI.Tachikawa.Construction.instModuleEX _root_.OAI.Tachikawa.Construction.instProjectiveMulOppositeC _root_.OAI.Tachikawa.Construction.simpleTwist_preserves_projective _root_.OAI.Tachikawa.DownHom.instAddCommGroupCochain _root_.OAI.Tachikawa.DownHom.instModuleCochain _root_.OAI.Tachikawa.Enveloping.instAddCommGroupCarrierMulOppositeRightObj _root_.OAI.Tachikawa.Enveloping.instModuleCarrierMulOppositeRightObj_1 _root_.OAI.Tachikawa.LeftCoinduced.coextend_additive _root_.OAI.Tachikawa.LeftCoinduced.coextend_preservesInjective _root_.OAI.Tachikawa.downIntTensorSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace Tachikawa.C
open CategoryTheory CategoryTheory.Abelian
open scoped ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q H : k) (hH : H ≠ 0)

omit [CharP k 2] in
def twistInitialHom (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) :
    (initialShortComplex q hp).map (tTwist q H hH) ⟶ initialShortComplex q hp where
  τ₁ := rangeTwistComparison q H hH 0
  τ₂ := inducedTwistComparison q H hH 0
  τ₃ := simpleTwistComparison q H hH
  comm₁₂ := by rfl
  comm₂₃ := by rfl

def twistMiddleHom (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) :
    (middleShortComplex q hq hp).map (tTwist q H hH) ⟶ middleShortComplex q hq hp where
  τ₁ := rangeTwistComparison q H hH 1
  τ₂ := inducedTwistComparison q H hH 1
  τ₃ := rangeTwistComparison q H hH 0
  comm₁₂ := by rfl
  comm₂₃ := by
    apply ModuleCat.hom_ext
    ext x
    apply Subtype.ext
    exact congrArg (fun f => f x) (inducedTwist_d q H hH 0)

omit [CharP k 2] in
def twistUpperHom :
    (upperShortComplex q).map (tTwist q H hH) ⟶ upperShortComplex q where
  τ₁ := cyclesTwistComparison q H hH
  τ₂ := inducedTwistComparison q H hH 2
  τ₃ := rangeTwistComparison q H hH 1
  comm₁₂ := by rfl
  comm₂₃ := by
    apply ModuleCat.hom_ext
    ext x
    apply Subtype.ext
    exact congrArg (fun f => f x) (inducedTwist_d q H hH 1)

end Tachikawa.C



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_ReverseResolution
attribute [-instance] _root_.OAI.Tachikawa.Construction.instFiniteCSubtypeMemSubmoduleCe _root_.OAI.Tachikawa.Construction.instFiniteCSubtypeMemSubmoduleCf _root_.OAI.Tachikawa.Construction.instFiniteMulOppositeC _root_.OAI.Tachikawa.Construction.instFiniteMulOppositeCSubtypeMemSubmoduleEC _root_.OAI.Tachikawa.Construction.instFiniteMulOppositeCSubtypeMemSubmoduleFC _root_.OAI.Tachikawa.Construction.instProjectiveMulOppositeC _root_.OAI.Tachikawa.DownHom.instAddCommGroupCochain _root_.OAI.Tachikawa.DownHom.instModuleCochain _root_.OAI.Tachikawa.LeftCoinduced.coextend_additive _root_.OAI.Tachikawa.LeftCoinduced.coextend_preservesInjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



noncomputable section



namespace Tachikawa.Construction
open CategoryTheory HomologicalComplex
open scoped TensorProduct
variable {k : Type} [Field k] [CharP k 2] (q : k)

lemma jjReverseComparison_quasiIso (hq : q ≠ 0)
    (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) : QuasiIso (jjReverseComparison q hq hp) := by
  let := C.inducedReverseComparison_quasiIso q hq hp
  exact OuterTensor.quasiIso_int k (C.T q) (C.T q) _ _

end Tachikawa.Construction



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Bimodule
attribute [-instance] _root_.OAI.Tachikawa.Construction.instFiniteCSubtypeMemSubmoduleCe _root_.OAI.Tachikawa.Construction.instFiniteCSubtypeMemSubmoduleCf _root_.OAI.Tachikawa.Construction.instFiniteMulOppositeC _root_.OAI.Tachikawa.Construction.instFiniteMulOppositeCSubtypeMemSubmoduleEC _root_.OAI.Tachikawa.Construction.instFiniteMulOppositeCSubtypeMemSubmoduleFC _root_.OAI.Tachikawa.Construction.instProjectiveMulOppositeC _root_.OAI.Tachikawa.DownHom.instAddCommGroupCochain _root_.OAI.Tachikawa.DownHom.instModuleCochain _root_.OAI.Tachikawa.Enveloping.instAddCommGroupCarrierMulOppositeRightObj _root_.OAI.Tachikawa.Enveloping.instIsScalarTowerCarrierMulOppositeRightObj _root_.OAI.Tachikawa.Enveloping.instModuleCarrierMulOppositeRightObj_1 _root_.OAI.Tachikawa.LeftCoinduced.coextend_additive _root_.OAI.Tachikawa.LeftCoinduced.coextend_preservesInjective _root_.OAI.Tachikawa.Triangular.instFiniteDimensionalAlgOfCarrierAlg
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace Tachikawa.Construction
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q : k)

lemma forwardJ_finite (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) (j : ℤ) :
    Module.Finite k ((forwardJ q hp).X j) := by
  cases j with
  | ofNat n => exact C.inducedObj_finite q n
  | negSucc n =>
    change Module.Finite k ((TrivialInduction.functor (k := k)).obj (ModuleCat.of (C k q) PUnit))
    have : Subsingleton ((TrivialInduction.functor (k := k)).obj (ModuleCat.of (C k q) PUnit)) :=
      ModuleCat.subsingleton_of_isZero <| (TrivialInduction.functor (k := k)).map_isZero
        (ModuleCat.isZero_of_subsingleton _)
    infer_instance

lemma forwardJ_projective (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) (j : ℤ) :
    Module.Projective (C.T q) ((forwardJ q hp).X j) := by
  cases j with
  | ofNat n => exact C.inducedObj_projective q n
  | negSucc n =>
    change Module.Projective (C.T q) (TrivialInduction.Obj k (C k q) (ModuleCat.of (C k q) PUnit))
    infer_instance

lemma forwardJJ_finite (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) (j : ℤ) :
    Module.Finite (E q) ((forwardJJ q hp).X j) :=
  OuterTensor.total_finite_below_int _ _ 0 0 (forwardJ_finite q hp) (forwardJ_finite q hp)
    (forwardJ_below q hp) (forwardJ_below q hp) j

lemma forwardJJ_projective (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) (j : ℤ) :
    Module.Projective (E q) ((forwardJJ q hp).X j) := by
  have h (i : ℤ) : Module.Finite (C.T q) ((forwardJ q hp).X i) := by
    let := forwardJ_finite q hp i
    exact Module.Finite.of_restrictScalars_finite k _ _
  let := OuterTensor.total_projective_int (k := k) _ _ h h (forwardJ_projective q hp) (forwardJ_projective q hp) j
  infer_instance

lemma jjFiber_totallyAcyclic (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) :
    TotallyAcyclic (jjFiber q hq hp) := by
  let := jjReverseComparison_quasiIso q hq hp
  let := (formE q).injective
  exact ModuleFiber.totallyAcyclic _

lemma jjFiber_finite (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) (j : ℤ) :
    Module.Finite (E q) ((jjFiber q hq hp).X j) := by
  let := forwardJJ_finite q hp j
  let := reverseJJ_finite q hq (j+1)
  exact inferInstanceAs (Module.Finite (E q) ((reverseJJ q hq).X (j+1) × (forwardJJ q hp).X j))

lemma jjFiber_projective (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) (j : ℤ) :
    Module.Projective (E q) ((jjFiber q hq hp).X j) := by
  let := forwardJJ_projective q hp j
  let := reverseJJ_projective q hq (j+1)
  exact inferInstanceAs (Module.Projective (E q) ((reverseJJ q hq).X (j+1) × (forwardJJ q hp).X j))

end Tachikawa.Construction



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Coinduction
attribute [-instance] _root_.OAI.Tachikawa.DownHom.instAddCommGroupCochain _root_.OAI.Tachikawa.DownHom.instModuleCochain _root_.OAI.Tachikawa.Enveloping.eval_finite _root_.OAI.Tachikawa.Enveloping.instLinearModuleCatAlgEvaluation _root_.OAI.Tachikawa.Enveloping.rightFree_preservesFiniteColimits _root_.OAI.Tachikawa.Enveloping.rightFree_preservesFiniteLimits _root_.OAI.Tachikawa.HomBimodule.instFiniteDimensionalCarrierAlgObj _root_.OAI.Tachikawa.Triangular.instAddCommGroupOff _root_.OAI.Tachikawa.Triangular.instAddCommGroupTriple _root_.OAI.Tachikawa.Triangular.instAdditiveModuleCatAlgD₀ _root_.OAI.Tachikawa.Triangular.instAdditiveModuleCatAlgD₁ _root_.OAI.Tachikawa.Triangular.instFiniteDimensionalAlgOfCarrierAlg _root_.OAI.Tachikawa.Triangular.instIsScalarTowerMulOppositeProdOff _root_.OAI.Tachikawa.Triangular.instIsScalarTowerProdOff _root_.OAI.Tachikawa.Triangular.instModuleAlgTriple _root_.OAI.Tachikawa.Triangular.instModuleMulOppositeProdOff _root_.OAI.Tachikawa.Triangular.instModuleOff _root_.OAI.Tachikawa.Triangular.instModuleProdOff _root_.OAI.Tachikawa.Triangular.instProjectiveCarrierOneFree _root_.OAI.Tachikawa.Triangular.instSMulCommClassProdMulOppositeOff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace Tachikawa.Construction
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q : k)

def tLeftResolution (hq : q ≠ 0) : ProjectiveResolution (TLeftObj q) :=
  Tachikawa.ProjectiveResolution.prod
    (Tachikawa.ProjectiveResolution.simpleSelf (ModuleCat.of (C k q) (C k q)))
    (C.leftDualProjectiveResolution q hq)

def tRightResolution (hq : q ≠ 0) : ProjectiveResolution (TRightObj q) :=
  Tachikawa.ProjectiveResolution.prod
    (Tachikawa.ProjectiveResolution.simpleSelf (ModuleCat.of (C k q)ᵐᵒᵖ (C k q)))
    (C.rightDualProjectiveResolution q hq)

lemma tLeftResolution_finiteC (hq : q ≠ 0) (n : ℕ) :
    Module.Finite (C k q) ((tLeftResolution q hq).complex.X n) := by
  change Module.Finite (C k q) (((Tachikawa.ProjectiveResolution.simpleSelf
      (ModuleCat.of (C k q) (C k q))).complex.X n) × C.leftDualResObj q n)
  have h : Module.Finite (C k q) (C.leftDualResObj q n) := by
    rcases n with _ | _ | _ | n
    · exact inferInstanceAs (Module.Finite (C k q) (C.Ce q × C.Ce q))
    · exact inferInstanceAs (Module.Finite (C k q) (C.Ce q))
    · exact inferInstanceAs (Module.Finite (C k q) (C.Cf q))
    · exact inferInstanceAs (Module.Finite (C k q) PUnit)
  let := h
  let : Module.Finite (C k q) ((Tachikawa.ProjectiveResolution.simpleSelf
      (ModuleCat.of (C k q) (C k q))).complex.X n) := by
    cases n with
    | zero => exact inferInstanceAs (Module.Finite (C k q) (C k q))
    | succ n => exact inferInstanceAs (Module.Finite (C k q) PUnit)
  exact Module.Finite.prod

lemma tRightResolution_finiteC (hq : q ≠ 0) (n : ℕ) :
    Module.Finite (C k q)ᵐᵒᵖ ((tRightResolution q hq).complex.X n) := by
  change Module.Finite (C k q)ᵐᵒᵖ (((Tachikawa.ProjectiveResolution.simpleSelf
      (ModuleCat.of (C k q)ᵐᵒᵖ (C k q))).complex.X n) × C.rightDualResObj q n)
  have h : Module.Finite (C k q)ᵐᵒᵖ (C.rightDualResObj q n) := by
    rcases n with _ | _ | _ | n
    · exact inferInstanceAs (Module.Finite (C k q)ᵐᵒᵖ (C.eC q × C.eC q))
    · exact inferInstanceAs (Module.Finite (C k q)ᵐᵒᵖ (C.eC q))
    · exact inferInstanceAs (Module.Finite (C k q)ᵐᵒᵖ (C.fC q))
    · exact inferInstanceAs (Module.Finite (C k q)ᵐᵒᵖ PUnit)
  let := h
  let : Module.Finite (C k q)ᵐᵒᵖ ((Tachikawa.ProjectiveResolution.simpleSelf
      (ModuleCat.of (C k q)ᵐᵒᵖ (C k q))).complex.X n) := by
    cases n with
    | zero => exact inferInstanceAs (Module.Finite (C k q)ᵐᵒᵖ (C k q))
    | succ n => exact inferInstanceAs (Module.Finite (C k q)ᵐᵒᵖ PUnit)
  exact Module.Finite.prod

lemma tLeftResolution_finite (hq : q ≠ 0) (n : ℕ) :
    FiniteDimensional k ((tLeftResolution q hq).complex.X n) := by
  let := tLeftResolution_finiteC q hq n
  exact Module.Finite.trans (C k q) _

lemma tRightResolution_finite (hq : q ≠ 0) (n : ℕ) :
    FiniteDimensional k ((tRightResolution q hq).complex.X n) := by
  let := tRightResolution_finiteC q hq n
  exact Module.Finite.trans (C k q)ᵐᵒᵖ _

lemma tLeftResolution_above (hq : q ≠ 0) (n : ℕ) (hn : 2 < n) :
    IsZero ((tLeftResolution q hq).complex.X n) := by
  apply Tachikawa.ProjectiveResolution.prod_above _ _ 2 n _ _ hn
  · intro i hi
    exact Tachikawa.ProjectiveResolution.simpleSelf_above _ i (by omega)
  · intro i hi
    obtain ⟨i,rfl⟩ := Nat.exists_eq_add_of_le (show 3 ≤ i by omega)
    rw [Nat.add_comm 3 i]
    change IsZero (ModuleCat.of (C k q) PUnit)
    exact ModuleCat.isZero_of_subsingleton _

lemma tRightResolution_above (hq : q ≠ 0) (n : ℕ) (hn : 2 < n) :
    IsZero ((tRightResolution q hq).complex.X n) := by
  apply Tachikawa.ProjectiveResolution.prod_above _ _ 2 n _ _ hn
  · intro i hi
    exact Tachikawa.ProjectiveResolution.simpleSelf_above _ i (by omega)
  · intro i hi
    obtain ⟨i,rfl⟩ := Nat.exists_eq_add_of_le (show 3 ≤ i by omega)
    rw [Nat.add_comm 3 i]
    change IsZero (ModuleCat.of (C k q)ᵐᵒᵖ PUnit)
    exact ModuleCat.isZero_of_subsingleton _

def eLeftResolution (hq : q ≠ 0) : ProjectiveResolution (ELeftObj q) :=
  OuterTensor.resolution k _ _ (tLeftResolution q hq) (tLeftResolution q hq)
    (tLeftResolution_finiteC q hq) (tLeftResolution_finiteC q hq)

def eRightResolution (hq : q ≠ 0) : ProjectiveResolution (ERightObj q) :=
  OuterTensor.resolution k _ _ (tRightResolution q hq) (tRightResolution q hq)
    (tRightResolution_finiteC q hq) (tRightResolution_finiteC q hq)

lemma eLeftResolution_above (hq : q ≠ 0) (n : ℕ) (hn : 4 < n) :
    IsZero ((eLeftResolution q hq).complex.X n) :=
  OuterTensor.total_isZero_above _ _ 2 2 (tLeftResolution_above q hq) (tLeftResolution_above q hq) n hn

lemma eRightResolution_above (hq : q ≠ 0) (n : ℕ) (hn : 4 < n) :
    IsZero ((eRightResolution q hq).complex.X n) :=
  OuterTensor.total_isZero_above _ _ 2 2 (tRightResolution_above q hq) (tRightResolution_above q hq) n hn

end Tachikawa.Construction



namespace Tachikawa.Construction
open CategoryTheory
open scoped ModuleCat.Algebra

variable {k : Type} [Field k] (q H : k) (hH : H ≠ 0)

lemma representation_socle (a : E q) :
    Enveloping.twistedUnderlying (sigma q H hH)
      ((HomBimodule.representation (k := k) (ModuleCat.of (E q) (X q)) ≫
        socleBimoduleMap q H hH) (Enveloping.regularUnderlyingEquiv.symm a)) =
      characterE q a • zeta q := by
  change (characterE q a * 1) • zeta q = _
  rw [mul_one]

end Tachikawa.Construction



namespace Tachikawa.Enveloping
open CategoryTheory CategoryTheory.Abelian
open scoped TensorProduct ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R] [FiniteDimensional k R]

lemma regular_outer_ext_zero (n : ℕ) :
    Subsingleton (Ext (regular (k := k) (R := R)) (ordinaryOuterObj (k := k) (R := R)) (n+1)) := by
  let e : ordinaryOuterObj (k := k) (R := R) ≅
      coindObj (k := k) (R := R) (rightRegularObj (S := R)) :=
    (dualOuterEquiv (rightRegularObj (S := R))).toModuleIso
  let := regular_coind_ext_zero (k := k) (R := R) (rightRegularObj (S := R)) n
  exact Function.Injective.subsingleton (extIso (k := k) (Iso.refl _) e (n+1)).injective

end Tachikawa.Enveloping

end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Induction
attribute [-instance] _root_.OAI.Tachikawa.DownHom.instAddCommGroupCochain _root_.OAI.Tachikawa.DownHom.instModuleCochain _root_.OAI.Tachikawa.Enveloping.eval_finite _root_.OAI.Tachikawa.Enveloping.instLinearModuleCatAlgEvaluation _root_.OAI.Tachikawa.Enveloping.rightFree_preservesFiniteColimits _root_.OAI.Tachikawa.Enveloping.rightFree_preservesFiniteLimits _root_.OAI.Tachikawa.HomBimodule.instFiniteDimensionalCarrierAlgObj _root_.OAI.Tachikawa.Triangular.instAddCommGroupOff _root_.OAI.Tachikawa.Triangular.instAddCommGroupTriple _root_.OAI.Tachikawa.Triangular.instAdditiveModuleCatAlgD₀ _root_.OAI.Tachikawa.Triangular.instAdditiveModuleCatAlgD₁ _root_.OAI.Tachikawa.Triangular.instFiniteDimensionalAlgOfCarrierAlg _root_.OAI.Tachikawa.Triangular.instIsScalarTowerMulOppositeProdOff _root_.OAI.Tachikawa.Triangular.instIsScalarTowerProdOff _root_.OAI.Tachikawa.Triangular.instModuleAlgTriple _root_.OAI.Tachikawa.Triangular.instModuleMulOppositeProdOff _root_.OAI.Tachikawa.Triangular.instModuleOff _root_.OAI.Tachikawa.Triangular.instModuleProdOff _root_.OAI.Tachikawa.Triangular.instSMulCommClassProdMulOppositeOff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace Tachikawa.Construction
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k : Type} [Field k] (q : k)

lemma rho_representation_socle (H : k) (hH : H ≠ 0) (a : B q) :
    rho q (Enveloping.twistedUnderlying (sigma q H hH)
      ((HomBimodule.representation (k := k) (ModuleCat.of (E q) (X q)) ≫
        socleBimoduleMap q H hH) (Enveloping.regularUnderlyingEquiv.symm (inclusionB q a)))) =
      characterMapB q a := by
  rw [representation_socle,map_smul,rho_zeta,character_inclusion]
  rfl

end Tachikawa.Construction



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_DerivedInduction
attribute [-instance] _root_.OAI.Tachikawa.DownHom.instAddCommGroupCochain _root_.OAI.Tachikawa.DownHom.instModuleCochain _root_.OAI.Tachikawa.Enveloping.eval_finite _root_.OAI.Tachikawa.Enveloping.instLinearModuleCatAlgEvaluation _root_.OAI.Tachikawa.Enveloping.rightFree_preservesFiniteColimits _root_.OAI.Tachikawa.Enveloping.rightFree_preservesFiniteLimits _root_.OAI.Tachikawa.HomBimodule.instFiniteDimensionalCarrierAlgObj _root_.OAI.Tachikawa.Triangular.instAddCommGroupOff _root_.OAI.Tachikawa.Triangular.instAddCommGroupTriple _root_.OAI.Tachikawa.Triangular.instAdditiveModuleCatAlgD₀ _root_.OAI.Tachikawa.Triangular.instAdditiveModuleCatAlgD₁ _root_.OAI.Tachikawa.Triangular.instFiniteDimensionalAlgOfCarrierAlg _root_.OAI.Tachikawa.Triangular.instIsScalarTowerMulOppositeProdOff _root_.OAI.Tachikawa.Triangular.instIsScalarTowerProdOff _root_.OAI.Tachikawa.Triangular.instModuleAlgTriple _root_.OAI.Tachikawa.Triangular.instModuleMulOppositeProdOff _root_.OAI.Tachikawa.Triangular.instModuleOff _root_.OAI.Tachikawa.Triangular.instModuleProdOff _root_.OAI.Tachikawa.Triangular.instSMulCommClassProdMulOppositeOff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
set_option backward.isDefEq.respectTransparency false


noncomputable section
namespace Tachikawa.Construction
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q : k) (hq : q ≠ 0)

def restrictedLeftResolution :
    ProjectiveResolution ((AlgebraInduction.res (inclusionB q)).obj (ModuleCat.of (E q) (E q))) :=
  Tachikawa.transportResolution (eLeftResolution q hq) (eLeftRestrictionIso q)

lemma restrictedLeftResolution_above (n : ℕ) (hn : 4 < n) :
    IsZero ((restrictedLeftResolution q hq).complex.X n) := eLeftResolution_above q hq n hn

def restrictedRightResolution :
    ProjectiveResolution ((AlgebraInduction.res (inclusionB q).op).obj
      (ModuleCat.of (E q)ᵐᵒᵖ (E q)ᵐᵒᵖ)) :=
  Tachikawa.transportResolution
    ((opTensorRestriction q).mapProjectiveResolution (eRightResolution q hq))
    (eRightRestrictionIso q)

lemma restrictedRightResolution_above (n : ℕ) (hn : 4 < n) :
    IsZero ((restrictedRightResolution q hq).complex.X n) :=
  (opTensorRestriction q).map_isZero (eRightResolution_above q hq n hn)

include hq in
lemma c5_left_projective : Module.Projective (E q)
    (Enveloping.Obj (Enveloping.inducedCokerFive (inclusionB q)).obj) :=
  Enveloping.inducedCoker_left_projective (inclusionB q) (restrictedLeftResolution q hq) 4
    (restrictedLeftResolution_above q hq 5 (by omega))

include hq in
lemma c5_right_projective : Module.Projective (E q)ᵐᵒᵖ
    (Enveloping.Obj (Enveloping.inducedCokerFive (inclusionB q)).obj) :=
  Enveloping.inducedCoker_right_projective (inclusionB q) (restrictedRightResolution q hq) 4
    (restrictedRightResolution_above q hq 5 (by omega))

include hq in
lemma Y_side_projective : Module.Projective (E q) (Enveloping.Obj (Y q).obj) ∧
    Module.Projective (E q)ᵐᵒᵖ (Enveloping.Obj (Y q).obj) := by
  let := c5_left_projective q hq
  let := c5_right_projective q hq
  exact Enveloping.negative_side_projective (formE q) (formE q)
    (Enveloping.inducedCokerFive (inclusionB q)) 4

end Tachikawa.Construction



namespace Tachikawa.Construction
open CategoryTheory HomologicalComplex
open scoped ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q : k)

def inducedBToJComparison (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) :
    (((AlgebraInduction.functor (inclusionB q)).mapHomologicalComplex _).obj
      (bSimpleTensorResolution q hp).complex) ≅
    mapBifunctor (C.inducedComplex q hp) (C.inducedComplex q hp)
      (OuterTensor.bifunctor k (T q) (T q)) (.down ℕ) :=
  OuterTensor.inductionTotalIso (inclusionC q) (inclusionC q)
    (C.projectiveResolution q hp).complex (C.projectiveResolution q hp).complex ≪≫
    C.inducedJTensorComparison q hp

def evaluatedKJComparison (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) :
    HomotopyEquiv
      (((Enveloping.evaluation (k := k) (ModuleCat.of (E q) (X q))).mapHomologicalComplex _).obj
        (Enveloping.inducedRegularComplex (inclusionB q)))
      (mapBifunctor (C.inducedComplex q hp) (C.inducedComplex q hp)
        (OuterTensor.bifunctor k (T q) (T q)) (.down ℕ)) :=
  (evaluatedKComparison q hp).trans (HomotopyEquiv.ofIso (inducedBToJComparison q hp))

end Tachikawa.Construction



namespace Tachikawa.Enveloping
open CategoryTheory HomologicalComplex
open scoped TensorProduct ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  [FiniteDimensional k R] (φ : R →ₐ[k] S)

lemma induced_regular_square {U : ModuleCat.{0} (Alg k S S)} {N : ModuleCat.{0} (Alg k R R)}
    (v : regular (k := k) (R := S) ⟶ U)
    (b : (AlgebraInduction.res (envelopingMap φ)).obj U ⟶ N) :
    AlgebraInduction.complexUnit (envelopingMap φ) (.up ℤ)
      (regularResolution (k := k) (R := R)).cochainComplex ≫
    (AlgebraInduction.complexRestriction (envelopingMap φ) (.up ℤ)).map
      (inducedRegularAugmentation φ ≫ (CochainComplex.singleFunctor _ 0).map v) ≫
    (singleMapHomologicalComplex (AlgebraInduction.res (envelopingMap φ)) (.up ℤ) 0).hom.app U ≫
    (CochainComplex.singleFunctor _ 0).map b =
    (regularResolution (k := k) (R := R)).π' ≫
      (CochainComplex.singleFunctor _ 0).map
        (restrictedRegularMap φ ≫ (AlgebraInduction.res (envelopingMap φ)).map v ≫ b) := by
  rw [Functor.map_comp]
  rw [← Category.assoc,← Category.assoc,← Category.assoc]
  dsimp only [inducedRegularAugmentation]
  rw [AlgebraInduction.complexUnit_extend]
  dsimp only [regularPreAugmentation]
  simp only [Category.assoc]
  have hn : (AlgebraInduction.complexRestriction (envelopingMap φ) (.up ℤ)).map
      ((CochainComplex.singleFunctor _ 0).map v) ≫
      (singleMapHomologicalComplex (AlgebraInduction.res (envelopingMap φ)) (.up ℤ) 0).hom.app U =
      (singleMapHomologicalComplex (AlgebraInduction.res (envelopingMap φ)) (.up ℤ) 0).hom.app _ ≫
      (CochainComplex.singleFunctor _ 0).map ((AlgebraInduction.res (envelopingMap φ)).map v) :=
    (singleMapHomologicalComplex (AlgebraInduction.res (envelopingMap φ)) (.up ℤ) 0).hom.naturality v
  rw [← Category.assoc ((AlgebraInduction.complexRestriction (envelopingMap φ) (.up ℤ)).map
    ((CochainComplex.singleFunctor _ 0).map v)), hn]
  simp only [Iso.inv_hom_id_app_assoc,Functor.map_comp,Category.assoc]

end Tachikawa.Enveloping



namespace Tachikawa
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra
variable {R : Type} [Ring R] {M : ModuleCat.{0} R}

namespace Enveloping
open scoped TensorProduct
variable {k S : Type} [Field k] [Ring S] [Algebra k R] [Algebra k S]
  [FiniteDimensional k R] [FiniteDimensional k S] (φ : R →ₐ[k] S)

instance inducedRegularCochain_projective (i : ℤ) :
    Projective ((inducedRegularCochain φ).X i) := by
  let P := regularResolution (k := k) (R := R)
  let : Module.Finite (Alg k R R) (P.cochainComplex.X i) :=
    finite_resolution_cochain P (fun _ => inferInstance) i
  change Projective ((AlgebraInduction.functor (envelopingMap φ)).obj (P.cochainComplex.X i))
  infer_instance

instance inducedRegularCochain_bounded : (inducedRegularCochain φ).IsStrictlyLE 0 := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  exact (AlgebraInduction.functor (envelopingMap φ)).map_isZero
    ((regularResolution (k := k) (R := R)).cochainComplex.isZero_of_isStrictlyLE 0 i hi)

instance inducedRegularCochain_isKProjective : (inducedRegularCochain φ).IsKProjective :=
  CochainComplex.isKProjective_of_projective _ 0

end Enveloping
end Tachikawa



namespace Tachikawa
open CategoryTheory HomologicalComplex CategoryTheory.Limits

namespace Construction
open scoped TensorProduct ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q : k) (hq : q ≠ 0)

include hq in

lemma inducedRegularComplex_exact (n : ℕ) (hn : 4 < n) :
    Function.Exact ((Enveloping.inducedRegularComplex (inclusionB q)).d (n+1) n)
      ((Enveloping.inducedRegularComplex (inclusionB q)).d n (n-1)) := by
  let Q := restrictedLeftResolution q hq
  let F := AlgebraInduction.functor (inclusionB q)
  let e := Enveloping.inducedLeftHomotopy (inclusionB q) Q
  have hz : IsZero (((F.mapHomologicalComplex (.down ℕ)).obj Q.complex).X n) :=
    F.map_isZero (restrictedLeftResolution_above q hq n hn)
  have he : (Enveloping.leftComplex (Enveloping.inducedRegularComplex (inclusionB q))).ExactAt n :=
    (exactAt_iff_of_quasiIsoAt e.hom n).mpr (ExactAt.of_isZero hz)
  have hf := (chainNat_exactAt_iff
    (Enveloping.leftComplex (Enveloping.inducedRegularComplex (inclusionB q))) n (by omega)).mp he
  exact hf

end Construction
end Tachikawa



namespace Tachikawa
open CategoryTheory HomologicalComplex
variable {R S : Type} [Ring R] [Ring S]

namespace Construction
variable {k : Type} [Field k] [CharP k 2] (q : k) (hq : q ≠ 0)
include hq in
lemma inducedRegularCochain_reflect_exact (n : ℕ) (hn : 4 < n) :
    Function.Exact ((reflectCochain (Enveloping.inducedRegularCochain (inclusionB q))).d
      ((n:ℤ)+1) n)
      ((reflectCochain (Enveloping.inducedRegularCochain (inclusionB q))).d n ((n:ℤ)-1)) :=
  Enveloping.inducedReflect_exact (inclusionB q) n (by omega)
       (inducedRegularComplex_exact q hq n hn)
end Construction
end Tachikawa

end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Perfect
attribute [-instance] _root_.OAI.Tachikawa.DownHom.instAddCommGroupCochain _root_.OAI.Tachikawa.DownHom.instModuleCochain _root_.OAI.Tachikawa.Enveloping.eval_finite _root_.OAI.Tachikawa.Enveloping.instLinearModuleCatAlgEvaluation _root_.OAI.Tachikawa.Enveloping.rightFree_preservesFiniteColimits _root_.OAI.Tachikawa.Enveloping.rightFree_preservesFiniteLimits _root_.OAI.Tachikawa.HomBimodule.instFiniteDimensionalCarrierAlgObj _root_.OAI.Tachikawa.Triangular.instAddCommGroupOff _root_.OAI.Tachikawa.Triangular.instAddCommGroupTriple _root_.OAI.Tachikawa.Triangular.instAdditiveModuleCatAlgD₀ _root_.OAI.Tachikawa.Triangular.instAdditiveModuleCatAlgD₁ _root_.OAI.Tachikawa.Triangular.instFiniteCarrierOneFree _root_.OAI.Tachikawa.Triangular.instFiniteDimensionalAlgOfCarrierAlg _root_.OAI.Tachikawa.Triangular.instIsScalarTowerMulOppositeProdOff _root_.OAI.Tachikawa.Triangular.instIsScalarTowerProdOff _root_.OAI.Tachikawa.Triangular.instModuleAlgTriple _root_.OAI.Tachikawa.Triangular.instModuleMulOppositeProdOff _root_.OAI.Tachikawa.Triangular.instModuleOff _root_.OAI.Tachikawa.Triangular.instModuleProdOff _root_.OAI.Tachikawa.Triangular.instSMulCommClassProdMulOppositeOff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace Tachikawa.Construction
open CategoryTheory CategoryTheory.Limits HomologicalComplex HomologicalComplex₂
variable {k : Type} [Field k] [CharP k 2] (q : k)
variable (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0)

lemma jjNatInt_d₁ (i j n : ℕ) (h : i+j=n+1) :
    (natJJDouble q hp).d₁ (.down ℕ) i j n ≫ jjNatIntX q hp n =
      (intJJDouble q hp).d₁ (.down ℤ) (i:ℤ) (j:ℤ) (n:ℤ) := by
  cases i with
  | zero =>
    erw [HomologicalComplex₂.d₁_eq_zero _ _ _ _ _ (by change ¬ _+1=0; omega), zero_comp,
      HomologicalComplex₂.d₁_eq' _ _ (show (ComplexShape.down ℤ).Rel 0 (-1) from rfl)]
    change 0 = (1:ℤˣ) • (((OuterTensor.bifunctor k (T q) (T q)).map
      ((forwardJ q hp).d 0 (-1) )).app ((forwardJ q hp).X (j:ℤ))) ≫ _
    erw [forwardJ_d_bottom, Functor.map_zero, NatTrans.app_zero, zero_comp, smul_zero]
  | succ i =>
    rw [HomologicalComplex₂.d₁_eq _ _ (show (ComplexShape.down ℕ).Rel (i+1) i from rfl)
        j n (by change i+j=n; omega),
      HomologicalComplex₂.d₁_eq _ _ (show (ComplexShape.down ℤ).Rel ((i+1:ℕ):ℤ) (i:ℤ) from rfl)
        (j:ℤ) (n:ℤ) (by change (i:ℤ)+(j:ℤ)=(n:ℤ); omega)]
    change ((1:ℤˣ) • (((OuterTensor.bifunctor k (T q) (T q)).map
      ((C.inducedComplex q hp).d (i+1) i)).app ((C.inducedComplex q hp).X j)) ≫ _) ≫ _ =
      (1:ℤˣ) • (((OuterTensor.bifunctor k (T q) (T q)).map
      ((forwardJ q hp).d ((i:ℤ)+1) (i:ℤ) )).app ((forwardJ q hp).X (j:ℤ))) ≫ _
    erw [one_smul, one_smul, Category.assoc, ι_jjNatIntX,
      C.inducedComplex_d, forwardJ_d_nat]
    rfl

lemma jjNatInt_d₂ (i j n : ℕ) (h : i+j=n+1) :
    (natJJDouble q hp).d₂ (.down ℕ) i j n ≫ jjNatIntX q hp n =
      (intJJDouble q hp).d₂ (.down ℤ) (i:ℤ) (j:ℤ) (n:ℤ) := by
  cases j with
  | zero =>
    erw [HomologicalComplex₂.d₂_eq_zero _ _ _ _ _ (by change ¬ _+1=0; omega), zero_comp,
      HomologicalComplex₂.d₂_eq' _ _ (i:ℤ) (show (ComplexShape.down ℤ).Rel 0 (-1) from rfl)]
    change 0 = (i:ℤ).negOnePow • (((OuterTensor.bifunctor k (T q) (T q)).obj
      ((forwardJ q hp).X (i:ℤ) )).map ((forwardJ q hp).d 0 (-1))) ≫ _
    erw [forwardJ_d_bottom, Functor.map_zero, zero_comp, smul_zero]
  | succ j =>
    rw [HomologicalComplex₂.d₂_eq _ _ i (show (ComplexShape.down ℕ).Rel (j+1) j from rfl)
        n (by change i+j=n; omega),
      HomologicalComplex₂.d₂_eq _ _ (i:ℤ) (show (ComplexShape.down ℤ).Rel ((j+1:ℕ):ℤ) (j:ℤ) from rfl)
        (n:ℤ) (by change (i:ℤ)+(j:ℤ)=(n:ℤ); omega)]
    change (((-1:ℤˣ)^i) • (((OuterTensor.bifunctor k (T q) (T q)).obj
      ((C.inducedComplex q hp).X i)).map ((C.inducedComplex q hp).d (j+1) j)) ≫ _) ≫ _ =
      (i:ℤ).negOnePow • (((OuterTensor.bifunctor k (T q) (T q)).obj
      ((forwardJ q hp).X (i:ℤ) )).map ((forwardJ q hp).d ((j:ℤ)+1) (j:ℤ))) ≫ _
    erw [Linear.units_smul_comp, Category.assoc, ι_jjNatIntX,
      C.inducedComplex_d, forwardJ_d_nat, natIntSign]
    rfl

lemma jjNatInt_d (n : ℕ) :
    jjNatIntX q hp (n+1) ≫ (forwardJJ q hp).d ((n+1:ℕ):ℤ) (n:ℤ) =
      (natJJ q hp).d (n+1) n ≫ jjNatIntX q hp n := by
  apply total.hom_ext
  intro i j h
  rw [ι_jjNatIntX_assoc]
  simp only [total_d, Preadditive.comp_add, Preadditive.add_comp,
    ι_D₁_assoc, ι_D₂_assoc]
  rw [jjNatInt_d₁ q hp i j n h, jjNatInt_d₂ q hp i j n h]
  erw [Preadditive.comp_add, ι_D₁, ι_D₂]

def jjNatIntCokerEquiv (n : ℕ) :
    ((natJJ q hp).X (n+1) ⧸ LinearMap.range ((natJJ q hp).d (n+2) (n+1)).hom) ≃ₗ[E q]
      CokerAt (forwardJJ q hp) ((n+1:ℕ):ℤ) :=
  cokerLinearEquiv _ _ (jjNatIntIso q hp (n+2)).toLinearEquiv
    (jjNatIntIso q hp (n+1)).toLinearEquiv
    (ModuleCat.hom_ext_iff.mp (jjNatInt_d q hp (n+1)).symm)

end Tachikawa.Construction



namespace Tachikawa.Construction
open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable {k : Type} [Field k] [CharP k 2] (q : k)
variable (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0)

def jjFiberHighCokerEquiv (j : ℤ) (hj : 4 ≤ j) :
    CokerAt (jjFiber q hq hp) j ≃ₗ[E q] CokerAt (forwardJJ q hp) j := by
  apply cokerLinearEquiv _ _
    ((jjFiberHighEquiv q hq hp (j+1) (by omega)).trans (LinearEquiv.neg (E q)))
    (jjFiberHighEquiv q hq hp j hj)
  apply LinearMap.ext
  intro x
  change ((jjFiber q hq hp).d (j+1) j x).2 = (forwardJJ q hp).d (j+1) j (-x.2)
  rw [show (jjFiber q hq hp).d (j+1) j = ModuleFiber.differential (jjReverseComparison q hq hp) j from
    ModuleFiber.complex_d _ j]
  change -(forwardJJ q hp).d (j+1) j x.2 = (forwardJJ q hp).d (j+1) j (-x.2)
  rw [map_neg]

def natJJFiveFiberEquiv : NatCoker.C (natJJ q hp) 4 ≃ₗ[E q] CokerAt (jjFiber q hq hp) 5 :=
  (jjNatIntCokerEquiv q hp 4).trans (jjFiberHighCokerEquiv q hq hp 5 (by omega)).symm

end Tachikawa.Construction



namespace Tachikawa
open CategoryTheory HomologicalComplex
variable {R : Type} [Ring R]

namespace Cutoff
variable (Q : ChainComplex (ModuleCat.{0} R) ℤ) (n : ℤ)

@[simp] lemma differential_val (i j : ℤ) (x : term Q n i) :
    (differential Q n i j x).val = Q.d i j x.val := rfl

def complex : ChainComplex (ModuleCat.{0} R) ℤ where
  X j := ModuleCat.of R (term Q n j)
  d i j := ModuleCat.ofHom (differential Q n i j)
  shape i j h := by
    apply ModuleCat.hom_ext
    ext x
    change Q.d i j x.val = 0
    rw [Q.shape i j h]
    rfl
  d_comp_d' i j l _ _ := by
    apply ModuleCat.hom_ext
    ext x
    change Q.d j l (Q.d i j x.val) = 0
    exact LinearMap.congr_fun (ModuleCat.hom_ext_iff.mp (Q.d_comp_d i j l)) x.val

def inclusion : complex Q n ⟶ Q where
  f j := ModuleCat.ofHom (term Q n j).subtype
  comm' _ _ _ := rfl

variable {Q} {P : ChainComplex (ModuleCat.{0} R) ℤ}

def lift (f : P ⟶ Q) (h : ∀ j, n < j → f.f j = 0) : P ⟶ complex Q n where
  f j := ModuleCat.ofHom <| (f.f j).hom.codRestrict (term Q n j) (by
    intro x
    by_cases hj : j ≤ n
    · simp only [term, ite_eq_left hj, Submodule.mem_top]
    · change f.f j x ∈ term Q n j
      rw [h j (by omega)]
      exact (term Q n j).zero_mem)
  comm' i j _ := by
    apply ModuleCat.hom_ext
    ext x
    apply Subtype.ext
    change Q.d i j (f.f i x) = f.f j (P.d i j x)
    exact LinearMap.congr_fun (ModuleCat.hom_ext_iff.mp (f.comm i j)) x

lemma lift_inclusion (f : P ⟶ Q) (h : ∀ j, n < j → f.f j = 0) :
    lift n f h ≫ inclusion Q n = f := by
  ext j x
  rfl

lemma term_subsingleton (j : ℤ) (h : n < j) : Subsingleton (term Q n j) := by
  simpa only [term, ite_eq_right (show ¬ j ≤ n by omega)] using
    (inferInstance : Subsingleton (⊥ : Submodule R (Q.X j)))

lemma term_projective (j : ℤ) [Module.Projective R (Q.X j)] :
    Module.Projective R (term Q n j) := by
  classical
  by_cases h : j ≤ n
  · have he : term Q n j = ⊤ := ite_eq_left h
    exact Module.Projective.of_equiv ((LinearEquiv.ofEq _ _ he).trans
      (Submodule.topEquiv : (⊤ : Submodule R (Q.X j)) ≃ₗ[R] Q.X j)).symm
  · have := term_subsingleton (Q := Q) n j (by omega)
    infer_instance

lemma term_finite (j : ℤ) [Module.Finite R (Q.X j)] : Module.Finite R (term Q n j) := by
  classical
  by_cases h : j ≤ n
  · have he : term Q n j = ⊤ := ite_eq_left h
    exact Module.Finite.equiv ((LinearEquiv.ofEq _ _ he).trans
      (Submodule.topEquiv : (⊤ : Submodule R (Q.X j)) ≃ₗ[R] Q.X j)).symm
  · have := term_subsingleton (Q := Q) n j (by omega)
    infer_instance

lemma term_subsingleton_below (l : ℤ) (hQ : ∀ j, j < l → Subsingleton (Q.X j))
    (j : ℤ) (hj : j < l) : Subsingleton (term Q n j) := by
  let := hQ j hj
  infer_instance

end Cutoff
end Tachikawa



namespace Tachikawa
open CategoryTheory HomologicalComplex
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable [Module.Injective R R]
variable {P Q : ChainComplex (ModuleCat.{0} R) ℤ}

theorem perfect_factorization (f : P ⟶ Q) (n l : ℤ)
    (hp : Function.Exact (P.d (n+1) n) (P.d n (n-1)))
    (hq : ∀ j, n ≤ j → Function.Exact (Q.d (j+1) j) (Q.d j (j-1)))
    (pproj : ∀ j, Module.Projective R (P.X j))
    (qproj : ∀ j, Module.Projective R (Q.X j))
    (qfin : ∀ j, Module.Finite R (Q.X j))
    (qbound : ∀ j, j < l → Subsingleton (Q.X j))
    (hf : CokerAt.map f n ∈ projectiveFactors (k := k)) :
    ∃ (K : ChainComplex (ModuleCat.{0} R) ℤ) (a : P ⟶ K) (b : K ⟶ Q),
      Nonempty (Homotopy f (a ≫ b)) ∧
      (∀ j, Module.Projective R (K.X j)) ∧
      (∀ j, Module.Finite R (K.X j)) ∧
      (∀ j, j < l ∨ n ≤ j → Subsingleton (K.X j)) := by
  obtain ⟨a₀, ha₀⟩ := tail_initial_component f n hp hf
  let astart : TailNull.State f n (n-1) := by
    unfold TailNull.State
    have hi : n-1+1=n := by omega
    rw [hi]
    exact ⟨a₀, fun _ => ha₀⟩
  let h := TailNull.hom f n hq pproj astart
  let z := Homotopy.nullHomotopicMap h
  let f' := f-z
  have hf' (j : ℤ) (hj : n-1 < j) : f'.f j = 0 := by
    change f.f j - z.f j = 0
    rw [TailNull.nullHomotopicMap_f f n hq pproj astart j (by omega)]
    exact sub_self _
  let a := Cutoff.lift (n-1) f' hf'
  refine ⟨Cutoff.complex Q (n-1), a, Cutoff.inclusion Q (n-1), ?_, ?_, ?_, ?_⟩
  · have he : a ≫ Cutoff.inclusion Q (n-1) = f' := Cutoff.lift_inclusion (n-1) f' hf'
    rw [he]
    apply Nonempty.intro
    refine Homotopy.equivSubZero.symm ?_
    have hz : f-f'=z := by dsimp only [f']; abel
    rw [hz]
    exact Homotopy.nullHomotopy h (TailNull.hom_zero f n hq pproj astart)
  · intro j
    let := qproj j
    exact Cutoff.term_projective (Q := Q) (n-1) j
  · intro j
    let := qfin j
    exact Cutoff.term_finite (Q := Q) (n-1) j
  · intro j hj
    rcases hj with hj | hj
    · exact Cutoff.term_subsingleton_below (n-1) l qbound j hj
    · exact Cutoff.term_subsingleton (n-1) j (by omega)

end Tachikawa



namespace Tachikawa
open CategoryTheory HomologicalComplex CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {k R : Type} [Field k] [Ring R] [Algebra k R] [Module.Injective R R]
variable {P Q : CochainComplex (ModuleCat.{0} R) ℤ}

theorem cochain_perfect_factorization (f : P ⟶ Q) (n l : ℤ)
    (hp : Function.Exact ((reflectCochain P).d (n+1) n) ((reflectCochain P).d n (n-1)))
    (hq : ∀ j, n ≤ j → Function.Exact ((reflectCochain Q).d (j+1) j)
      ((reflectCochain Q).d j (j-1)))
    (pproj : ∀ j, Module.Projective R (P.X j))
    (qproj : ∀ j, Module.Projective R (Q.X j))
    (qfin : ∀ j, Module.Finite R (Q.X j))
    (qbound : ∀ j, -l < j → Subsingleton (Q.X j))
    (hf : CokerAt.map (reflectCochainMap f) n ∈ projectiveFactors (k := k)) :
    ∃ (L : CochainComplex (ModuleCat.{0} R) ℤ)
      (a : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj L)
      (b : DerivedCategory.Q.obj L ⟶ DerivedCategory.Q.obj Q),
      a ≫ b = DerivedCategory.Q.map f ∧
      (∀ j, Module.Projective R (L.X j)) ∧
      (∀ j, Module.Finite R (L.X j)) ∧
      (∀ j, j < -n+1 ∨ -l < j → IsZero (L.X j)) := by
  obtain ⟨L,a,b,⟨H⟩,hproj,hfin,hbound⟩ := perfect_factorization
    (reflectCochainMap f) n l hp hq (fun j => pproj (-j))
      (fun j => qproj (-j)) (fun j => qfin (-j))
      (fun j hj => qbound (-j) (by omega)) hf
  let a' := (reflectCochainIso P).inv ≫ reflectChainMap a
  let b' := reflectChainMap b ≫ (reflectCochainIso Q).hom
  refine ⟨reflectChain L, DerivedCategory.Q.map a', DerivedCategory.Q.map b', ?_,
    (fun j => hproj (-j)), (fun j => hfin (-j)), ?_⟩
  · have he : (reflectCochainIso P).inv ≫ reflectChainMap (reflectCochainMap f) ≫
      (reflectCochainIso Q).hom = f := by
      rw [reflectCochainIso_natural, Iso.inv_hom_id_assoc]
    have H' := ((reflectChainHomotopy H).compLeft (reflectCochainIso P).inv).compRight
      (reflectCochainIso Q).hom
    have hH := DerivedCategory.Q_map_eq_of_homotopy (ModuleCat.{0} R) H'
    rw [Category.assoc,he] at hH
    rw [← Functor.map_comp]
    exact hH.symm.trans (congrArg DerivedCategory.Q.map (by rfl))
  · intro j hj
    exact ModuleCat.isZero_iff_subsingleton.mpr (hbound (-j) (by omega))

end Tachikawa



namespace Tachikawa
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped ModuleCat.Algebra
attribute [local instance] HasDerivedCategory.standard
variable {k R : Type} [Field k] [Ring R] [Algebra k R] [FiniteDimensional k R]

theorem stably_nonzero_high_lift [Module.Injective R R]
    (P : CochainComplex (ModuleCat.{0} R) ℤ)
    (pproj : ∀ j, Module.Projective R (P.X j)) (M : FiniteModule k R)
    (v : P ⟶ (CochainComplex.singleFunctor _ 0).obj M.obj)
    (n₀ : ℕ) (hn₀ : 0 < n₀)
    (hex : ∀ n : ℕ, n₀ ≤ n → Function.Exact ((reflectCochain P).d ((n:ℤ)+1) n)
      ((reflectCochain P).d n ((n:ℤ)-1)))
    (hnot : ∀ (L : CochainComplex (ModuleCat.{0} R) ℤ)
      ( _hfin : ∀ j, Module.Finite R (L.X j)) ( _hproj : ∀ j, Module.Projective R (L.X j))
      (l u : ℤ) ( _hb : ∀ j, j < l ∨ u < j → IsZero (L.X j))
      (a : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj L)
      (b : DerivedCategory.Q.obj L ⟶ DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj M.obj)),
      a ≫ b ≠ DerivedCategory.Q.map v)
    (f : P ⟶ M.projectiveResolution.cochainComplex)
    (hfv : DerivedCategory.Q.map f ≫ DerivedCategory.Q.map M.projectiveResolution.π' =
      DerivedCategory.Q.map v) :
    ∀ n : ℕ, n₀ ≤ n → CokerAt.map (reflectCochainMap f) n ∉ projectiveFactors (k := k) := by
  let Q := M.projectiveResolution
  intro n hn hz
  have hq (j : ℤ) (hj : (n:ℤ) ≤ j) :
      Function.Exact ((reflectCochain Q.cochainComplex).d (j+1) j)
        ((reflectCochain Q.cochainComplex).d j (j-1)) := by
    lift j to ℕ using (show 0 ≤ j by omega) with m hm
    subst hm
    exact projectiveResolution_reflect_exact Q m (by omega)
  have qproj (j : ℤ) : Module.Projective R (Q.cochainComplex.X j) := by infer_instance
  have qfin (j : ℤ) : Module.Finite R (Q.cochainComplex.X j) :=
    finite_resolution_cochain Q (fun _ => inferInstance) j
  have qb (j : ℤ) (hj : -(0:ℤ) < j) : Subsingleton (Q.cochainComplex.X j) :=
    ModuleCat.isZero_iff_subsingleton.mp (Q.cochainComplex.isZero_of_isStrictlyLE 0 j (by omega))
  obtain ⟨L,a,b,he,hlp,hlf,hlb⟩ := cochain_perfect_factorization f n 0 (hex n hn)
    hq pproj qproj qfin qb hz
  apply hnot L hlf hlp (-(n:ℤ)+1) 0 (by simpa only [neg_zero] using hlb) a
    (b ≫ DerivedCategory.Q.map Q.π')
  rw [← Category.assoc,he,hfv]

end Tachikawa



namespace Tachikawa.Enveloping
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]

def restrictedOuterRegularEquiv (φ : R →ₐ[k] S) :
    restrictedOuterRegular φ ≃ₗ[Alg k R R]
      (AlgebraInduction.res (envelopingMap φ)).obj (ModuleCat.of (Alg k S S) (Alg k S S)) where
  __ := (restrictedOuterRegularUnderlying φ).toAddEquiv
  map_smul' a z := restrictedOuterRegular_action φ a z

def restrictedOuterRegularIso (φ : R →ₐ[k] S) :
    restrictedOuterRegular φ ≅
      (AlgebraInduction.res (envelopingMap φ)).obj (ModuleCat.of (Alg k S S) (Alg k S S)) :=
  (restrictedOuterRegularEquiv φ).toModuleIso

end Tachikawa.Enveloping



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_DerivedDescent
attribute [-instance] _root_.OAI.Tachikawa.DownHom.instAddCommGroupCochain _root_.OAI.Tachikawa.DownHom.instModuleCochain _root_.OAI.Tachikawa.Enveloping.eval_finite _root_.OAI.Tachikawa.Enveloping.instLinearModuleCatAlgEvaluation _root_.OAI.Tachikawa.Enveloping.rightFree_preservesFiniteColimits _root_.OAI.Tachikawa.Enveloping.rightFree_preservesFiniteLimits _root_.OAI.Tachikawa.HomBimodule.instFiniteDimensionalCarrierAlgObj _root_.OAI.Tachikawa.Triangular.instAddCommGroupOff _root_.OAI.Tachikawa.Triangular.instAddCommGroupTriple _root_.OAI.Tachikawa.Triangular.instAdditiveModuleCatAlgD₀ _root_.OAI.Tachikawa.Triangular.instAdditiveModuleCatAlgD₁ _root_.OAI.Tachikawa.Triangular.instFiniteDimensionalAlgOfCarrierAlg _root_.OAI.Tachikawa.Triangular.instIsScalarTowerMulOppositeProdOff _root_.OAI.Tachikawa.Triangular.instIsScalarTowerProdOff _root_.OAI.Tachikawa.Triangular.instModuleAlgTriple _root_.OAI.Tachikawa.Triangular.instModuleMulOppositeProdOff _root_.OAI.Tachikawa.Triangular.instModuleOff _root_.OAI.Tachikawa.Triangular.instModuleProdOff _root_.OAI.Tachikawa.Triangular.instProjectiveCarrierOneFree _root_.OAI.Tachikawa.Triangular.instSMulCommClassProdMulOppositeOff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace Tachikawa.Construction
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q : k) (hq : q ≠ 0)

lemma restrictedLeftResolution_finite (n : ℕ) :
    Module.Finite (B q) ((restrictedLeftResolution q hq).complex.X n) :=
  OuterTensor.total_finite (tLeftResolution q hq).complex (tLeftResolution q hq).complex
    (tLeftResolution_finite q hq) (tLeftResolution_finite q hq) n

lemma restrictedRightResolution_finite (n : ℕ) :
    Module.Finite (B q)ᵐᵒᵖ ((restrictedRightResolution q hq).complex.X n) := by
  let : Module.Finite ((C k q)ᵐᵒᵖ ⊗[k] (C k q)ᵐᵒᵖ)
      ((eRightResolution q hq).complex.X n) :=
    OuterTensor.total_finite (tRightResolution q hq).complex (tRightResolution q hq).complex
      (tRightResolution_finite q hq) (tRightResolution_finite q hq) n
  let : FiniteDimensional k ((eRightResolution q hq).complex.X n) :=
    Module.Finite.trans ((C k q)ᵐᵒᵖ ⊗[k] (C k q)ᵐᵒᵖ) _
  change Module.Finite (B q)ᵐᵒᵖ ((opTensorRestriction q).obj ((eRightResolution q hq).complex.X n))
  let e : (opTensorRestriction q).obj ((eRightResolution q hq).complex.X n) ≃ₗ[k]
      (eRightResolution q hq).complex.X n :=
    { toFun := id
      invFun := id
      left_inv _ := rfl
      right_inv _ := rfl
      map_add' _ _ := rfl
      map_smul' c x := by
        change ((opTensorB q).symm (algebraMap k (B q)ᵐᵒᵖ c)) •
          (show (eRightResolution q hq).complex.X n from x) = c • _
        rw [AlgEquiv.commutes]
        rfl }
  let : FiniteDimensional k ((opTensorRestriction q).obj ((eRightResolution q hq).complex.X n)) :=
    Module.Finite.equiv e.symm
  exact Module.Finite.of_restrictScalars_finite k _ _

def restrictedBimoduleResolution : ProjectiveResolution
    ((AlgebraInduction.res (k := k) (R := Enveloping.Alg k (B q) (B q))
      (S := Enveloping.Alg k (E q) (E q)) (Enveloping.envelopingMap (inclusionB q))).obj
      (ModuleCat.of (Enveloping.Alg k (E q) (E q)) (Enveloping.Alg k (E q) (E q)))) :=
  transportResolution
    (OuterTensor.resolution k (B q) (B q)ᵐᵒᵖ
      (restrictedLeftResolution q hq) (restrictedRightResolution q hq)
      (restrictedLeftResolution_finite q hq) (restrictedRightResolution_finite q hq))
    (Enveloping.restrictedOuterRegularIso (inclusionB q))

lemma restrictedBimoduleResolution_above (n : ℕ) (hn : 8 < n) :
    IsZero ((restrictedBimoduleResolution q hq).complex.X n) :=
  OuterTensor.total_isZero_above _ _ 4 4
    (restrictedLeftResolution_above q hq) (restrictedRightResolution_above q hq) n hn

include hq in
lemma restrictedBimodule_pd : HasProjectiveDimensionLE
    ((AlgebraInduction.res (k := k) (R := Enveloping.Alg k (B q) (B q))
      (S := Enveloping.Alg k (E q) (E q)) (Enveloping.envelopingMap (inclusionB q))).obj
      (ModuleCat.of (Enveloping.Alg k (E q) (E q)) (Enveloping.Alg k (E q) (E q)))) 8 :=
  projective_dimension_of_bounded_resolution (restrictedBimoduleResolution q hq) 8
    (restrictedBimoduleResolution_above q hq)

include hq in

lemma restrictedProjective_pd (P : ModuleCat (Enveloping.Alg k (E q) (E q)))
    [Module.Finite (Enveloping.Alg k (E q) (E q)) P]
    [Module.Projective (Enveloping.Alg k (E q) (E q)) P] :
    HasProjectiveDimensionLE
      ((AlgebraInduction.res (k := k) (R := Enveloping.Alg k (B q) (B q))
      (S := Enveloping.Alg k (E q) (E q)) (Enveloping.envelopingMap (inclusionB q))).obj P) 8 := by
  let := restrictedBimodule_pd q hq
  exact ((finiteProjective_inAdd P).map
    (AlgebraInduction.res (k := k) (R := Enveloping.Alg k (B q) (B q))
      (S := Enveloping.Alg k (E q) (E q)) (Enveloping.envelopingMap (inclusionB q)))).projectiveDimension 9

end Tachikawa.Construction



namespace Tachikawa
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open scoped ModuleCat.Algebra
attribute [instance] IndReplacement.quasiIso

end Tachikawa



namespace Tachikawa.Construction
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q : k) (hq : q ≠ 0)

abbrev bimoduleRestriction : ModuleCat.{0} (Enveloping.Alg k (E q) (E q)) ⥤
    ModuleCat.{0} (Enveloping.Alg k (B q) (B q)) :=
  AlgebraInduction.res (k := k) (R := Enveloping.Alg k (B q) (B q))
    (S := Enveloping.Alg k (E q) (E q)) (Enveloping.envelopingMap (inclusionB q))

include hq in

theorem restricted_perfect_replacement
    (P : CochainComplex (ModuleCat.{0} (Enveloping.Alg k (E q) (E q))) ℤ)
    (hfin : ∀ i, Module.Finite (Enveloping.Alg k (E q) (E q)) (P.X i))
    (hproj : ∀ i, Module.Projective (Enveloping.Alg k (E q) (E q)) (P.X i))
    (l u : ℤ) (hb : ∀ i, i < l ∨ u < i → IsZero (P.X i)) :
    ∃ (Q : CochainComplex (ModuleCat.{0} (Enveloping.Alg k (B q) (B q))) ℤ)
      (f : Q ⟶ ((bimoduleRestriction q).mapHomologicalComplex (.up ℤ)).obj P),
      QuasiIso f ∧
      (∀ i, Module.Projective (Enveloping.Alg k (B q) (B q)) (Q.X i)) ∧
      (∀ i, Module.Finite (Enveloping.Alg k (B q) (B q)) (Q.X i)) ∧
      (∀ i, i < l-8 ∨ u < i → IsZero (Q.X i)) := by
  have hfin' (i : ℤ) : FiniteDimensional k ((bimoduleRestriction q).obj (P.X i)) := by
    let := hfin i
    let : IsScalarTower k (Enveloping.Alg k (E q) (E q)) (P.X i) :=
      ModuleCat.Algebra.instIsScalarTowerCarrier (S₀ := k)
        (S := Enveloping.Alg k (E q) (E q)) (M := P.X i)
    let : FiniteDimensional k (P.X i) := Module.Finite.trans (Enveloping.Alg k (E q) (E q)) _
    exact AlgebraInduction.resFinite _ _
  have hpd (i : ℤ) : HasProjectiveDimensionLE ((bimoduleRestriction q).obj (P.X i)) 8 := by
    let := hfin i
    let := hproj i
    exact restrictedProjective_pd q hq (P.X i)
  obtain ⟨Q,f,hf,hp,hf',hb'⟩ := bounded_projective_replacement
    (((bimoduleRestriction q).mapHomologicalComplex (.up ℤ)).obj P) 8 hfin' hpd l u
    (fun i hi => (bimoduleRestriction q).map_isZero (hb i hi))
  refine ⟨Q,f,hf,?_,?_,hb'⟩
  · intro i
    let := hp i
    infer_instance
  · intro i
    let := hf' i
    let : IsScalarTower k (Enveloping.Alg k (B q) (B q)) (Q.X i) :=
      ModuleCat.Algebra.instIsScalarTowerCarrier (S₀ := k)
        (S := Enveloping.Alg k (B q) (B q)) (M := Q.X i)
    exact Module.Finite.of_restrictScalars_finite k _ _

end Tachikawa.Construction



namespace Tachikawa.Construction
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra

variable {k : Type} [Field k] (q H : k) (hH : H ≠ 0)

def restrictedUUnderlying : (bimoduleRestriction q).obj (U q H hH) ≃ₗ[k] E q :=
  restrictedTwistedUnderlying (inclusionB q) (sigma q H hH)

def rhoBimoduleLinear : (bimoduleRestriction q).obj (U q H hH) →ₗ[k]
    Enveloping.dualRegularObj (k := k) (R := B q) :=
  (Enveloping.dualRegularUnderlying (k := k) (R := B q)).symm.toLinearMap.comp
    ((rho q).comp (restrictedUUnderlying q H hH).toLinearMap)

lemma rhoBimoduleLinear_tensor (r : B q) (s : (B q)ᵐᵒᵖ)
    (x : (bimoduleRestriction q).obj (U q H hH)) :
    rhoBimoduleLinear q H hH ((r ⊗ₜ[k] s) • x) =
      (r ⊗ₜ[k] s) • rhoBimoduleLinear q H hH x := by
  apply Enveloping.dualRegularUnderlying.injective
  change rho q (inclusionB q r * ((show E q from x) * sigma q H hH (inclusionB q s.unop))) =
    r • MulOpposite.op s.unop • rho q (show E q from x)
  rw [sigma_inclusionB,rho_left,rho_right]

def rhoBimodule : (bimoduleRestriction q).obj (U q H hH) ⟶
    Enveloping.dualRegularObj (k := k) (R := B q) :=
  Enveloping.homOfLinear (rhoBimoduleLinear q H hH) (rhoBimoduleLinear_tensor q H hH)

lemma restricted_socle_character :
    Enveloping.restrictedRegularMap (inclusionB q) ≫
      (bimoduleRestriction q).map
        (HomBimodule.representation (k := k) (ModuleCat.of (E q) (X q)) ≫
          socleBimoduleMap q H hH) ≫ rhoBimodule q H hH = characterBimoduleMap q := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Enveloping.dualRegularUnderlying.injective
  exact rho_representation_socle q H hH (Enveloping.regularUnderlyingEquiv x)

end Tachikawa.Construction



namespace Tachikawa.Enveloping
open CategoryTheory HomologicalComplex
open scoped TensorProduct ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  [FiniteDimensional k R] (φ : R →ₐ[k] S)

lemma regularUnit_square {U : ModuleCat.{0} (Alg k S S)} {N : ModuleCat.{0} (Alg k R R)}
    (v : regular (k := k) (R := S) ⟶ U)
    (b : (AlgebraInduction.res (envelopingMap φ)).obj U ⟶ N) :
    regularUnit φ ≫ ((AlgebraInduction.res (envelopingMap φ)).mapHomologicalComplex (.up ℤ)).map
      (inducedRegularAugmentation φ ≫ (CochainComplex.singleFunctor _ 0).map v) ≫
      restrictedSingleMap φ b = (regularResolution (k := k) (R := R)).π' ≫
        (CochainComplex.singleFunctor _ 0).map
          (restrictedRegularMap φ ≫ (AlgebraInduction.res (envelopingMap φ)).map v ≫ b) :=
  induced_regular_square φ v b

end Tachikawa.Enveloping



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_FiniteCoinduction
attribute [-instance] _root_.OAI.Tachikawa.DownHom.instAddCommGroupCochain _root_.OAI.Tachikawa.DownHom.instModuleCochain _root_.OAI.Tachikawa.Enveloping.eval_finite _root_.OAI.Tachikawa.Enveloping.instLinearModuleCatAlgEvaluation _root_.OAI.Tachikawa.HomBimodule.instFiniteDimensionalCarrierAlgObj _root_.OAI.Tachikawa.Triangular.instAddCommGroupOff _root_.OAI.Tachikawa.Triangular.instAddCommGroupTriple _root_.OAI.Tachikawa.Triangular.instAdditiveModuleCatAlgD₀ _root_.OAI.Tachikawa.Triangular.instAdditiveModuleCatAlgD₁ _root_.OAI.Tachikawa.Triangular.instFiniteDimensionalAlgOfCarrierAlg _root_.OAI.Tachikawa.Triangular.instIsScalarTowerMulOppositeProdOff _root_.OAI.Tachikawa.Triangular.instIsScalarTowerProdOff _root_.OAI.Tachikawa.Triangular.instModuleAlgTriple _root_.OAI.Tachikawa.Triangular.instModuleMulOppositeProdOff _root_.OAI.Tachikawa.Triangular.instModuleOff _root_.OAI.Tachikawa.Triangular.instModuleProdOff _root_.OAI.Tachikawa.Triangular.instSMulCommClassProdMulOppositeOff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace Tachikawa
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  [FiniteDimensional k R] [FiniteDimensional k S]

def dualRightObj : ModuleCat Rᵐᵒᵖ := ModuleCat.of Rᵐᵒᵖ (DualBimodule k R)

def dualRightUnderlying : dualRightObj (k := k) (R := R) ≃ₗ[k] DualBimodule k R :=
  moduleCatUnderlyingEquiv (k := k) (R := Rᵐᵒᵖ) (DualBimodule k R)

def dualRightTensorUnderlying :
    OuterTensor.Obj k Rᵐᵒᵖ Sᵐᵒᵖ (dualRightObj (k := k) (R := R)) (dualRightObj (k := k) (R := S)) ≃ₗ[k]
      DualBimodule k (R ⊗[k] S) :=
  (TensorProduct.congr (dualRightUnderlying (k := k) (R := R))
    (dualRightUnderlying (k := k) (R := S))).trans
    (TensorProduct.dualDistribEquiv k R S)

lemma dualRightTensorUnderlying_tmul (φ : dualRightObj (k := k) (R := R))
    (ψ : dualRightObj (k := k) (R := S)) (r : R) (s : S) :
    dualRightTensorUnderlying (φ ⊗ₜ[k] ψ) (r ⊗ₜ[k] s) =
      (show DualBimodule k R from φ) r * (show DualBimodule k S from ψ) s := by
  rfl

lemma dualRightTensor_action (a : Rᵐᵒᵖ ⊗[k] Sᵐᵒᵖ)
    (z : OuterTensor.Obj k Rᵐᵒᵖ Sᵐᵒᵖ (dualRightObj (k := k) (R := R)) (dualRightObj (k := k) (R := S))) :
    dualRightTensorUnderlying ((OuterTensor.action k Rᵐᵒᵖ Sᵐᵒᵖ _ _ a) z) =
      (Algebra.TensorProduct.opAlgEquiv k k R S a) • dualRightTensorUnderlying z := by
  induction a using OAI.tensorInductionOn with
  | add a b ha hb => erw [map_add,LinearMap.add_apply,map_add,ha,hb,map_add,add_smul]
  | tmul r s =>
    induction z using OAI.tensorInductionOn with
    | add x y hx hy => erw [map_add,map_add,hx,hy,map_add,smul_add]
    | tmul φ ψ =>
      apply TensorProduct.ext'
      intro x y
      change (show DualBimodule k R from φ) (r.unop*x) * (show DualBimodule k S from ψ) (s.unop*y) =
        dualRightTensorUnderlying (φ ⊗ₜ[k] ψ) ((r.unop ⊗ₜ[k] s.unop) * (x ⊗ₜ[k] y))
      rw [Algebra.TensorProduct.tmul_mul_tmul,dualRightTensorUnderlying_tmul]

def dualRightTensorIso :
    (dualRightTensorRestriction (k := k) (R := R) (S := S)).obj
      (((OuterTensor.bifunctor k Rᵐᵒᵖ Sᵐᵒᵖ).obj (dualRightObj (k := k) (R := R))).obj
        (dualRightObj (k := k) (R := S))) ≅ dualRightObj (k := k) (R := R ⊗[k] S) := by
  let X := (dualRightTensorRestriction (k := k) (R := R) (S := S)).obj
      (((OuterTensor.bifunctor k Rᵐᵒᵖ Sᵐᵒᵖ).obj (dualRightObj (k := k) (R := R))).obj
        (dualRightObj (k := k) (R := S)))
  let Y := dualRightObj (k := k) (R := R ⊗[k] S)
  exact LinearEquiv.toModuleIso (X₁ := X) (X₂ := Y) (m₁ := X.isModule) (m₂ := Y.isModule)
    { __ := (dualRightTensorUnderlying (k := k) (R := R) (S := S)).toAddEquiv
      map_smul' r x := by
        change dualRightTensorUnderlying ((OuterTensor.action k Rᵐᵒᵖ Sᵐᵒᵖ _ _
          ((Algebra.TensorProduct.opAlgEquiv k k R S).symm r)) x) = r • dualRightTensorUnderlying x
        erw [dualRightTensor_action,AlgEquiv.apply_symm_apply] }


end Tachikawa



namespace Tachikawa.Construction
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q : k)

lemma cDualRight_finite (hq : q ≠ 0) (n : ℕ) :
    Module.Finite (C k q)ᵐᵒᵖ ((C.rightDualProjectiveResolution q hq).complex.X n) := by
  change Module.Finite (C k q)ᵐᵒᵖ (C.rightDualResObj q n)
  rcases n with _ | _ | _ | n
  · exact inferInstanceAs (Module.Finite (C k q)ᵐᵒᵖ (C.eC q × C.eC q))
  · exact inferInstanceAs (Module.Finite (C k q)ᵐᵒᵖ (C.eC q))
  · exact inferInstanceAs (Module.Finite (C k q)ᵐᵒᵖ (C.fC q))
  · exact inferInstanceAs (Module.Finite (C k q)ᵐᵒᵖ PUnit)

lemma cDualRight_above (hq : q ≠ 0) (n : ℕ) (hn : 2 < n) :
    IsZero ((C.rightDualProjectiveResolution q hq).complex.X n) := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_add_of_le (show 3 ≤ n by omega)
  rw [Nat.add_comm 3 n]
  exact ModuleCat.isZero_of_subsingleton (ModuleCat.of (C k q)ᵐᵒᵖ PUnit)

def bDualRightResolution (hq : q ≠ 0) :
    ProjectiveResolution (dualRightObj (k := k) (R := B q)) :=
  Tachikawa.transportResolution
    ((dualRightTensorRestriction (k := k) (R := C k q) (S := C k q)).mapProjectiveResolution
      (OuterTensor.resolution k _ _ (C.rightDualProjectiveResolution q hq)
        (C.rightDualProjectiveResolution q hq) (cDualRight_finite q hq) (cDualRight_finite q hq)))
    (dualRightTensorIso (k := k) (R := C k q) (S := C k q))

lemma bDualRight_above (hq : q ≠ 0) (n : ℕ) (hn : 4 < n) :
    IsZero ((bDualRightResolution q hq).complex.X n) :=
  (dualRightTensorRestriction (k := k) (R := C k q) (S := C k q)).map_isZero
    (OuterTensor.total_isZero_above _ _ 2 2 (cDualRight_above q hq) (cDualRight_above q hq) n hn)

end Tachikawa.Construction



namespace Tachikawa
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R] [FiniteDimensional k R]

def doubleDualRegularEquiv : R ≃ₗ[R] LeftDual (k := k) (dualRightObj (k := k) (R := R)) where
  __ := ((Module.evalEquiv k R).trans (dualRightUnderlying (k := k) (R := R)).dualMap).toAddEquiv
  map_smul' r x := by
    apply LeftDual.ext
    intro φ
    change (show DualBimodule k R from φ) (r*x) = (show DualBimodule k R from (MulOpposite.op r) • φ) x
    rfl

def doubleDualRegularIso : ModuleCat.of R R ≅ leftDualObj (k := k) (dualRightObj (k := k) (R := R)) :=
  doubleDualRegularEquiv.toModuleIso

namespace Construction
variable [CharP k 2] (q : k)

lemma b_regular_ext_zero (hq : q ≠ 0) (V : ModuleCat (B q)) (n : ℕ) (hn : 4 < n) :
    Subsingleton (Abelian.Ext V (ModuleCat.of (B q) (B q)) n) := by
  let : Subsingleton (Abelian.Ext V (leftDualObj (k := k) (dualRightObj (k := k) (R := B q))) n) :=
    dualResolution_ext_zero (bDualRightResolution q hq) 4 (bDualRight_above q hq) V n hn
  exact (extIso (k := k) (Iso.refl V) (doubleDualRegularIso (k := k) (R := B q)) n).injective.subsingleton

end Construction
end Tachikawa



namespace Tachikawa
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra
variable {k R M : Type} [Field k] [Ring R] [Algebra k R] [FiniteDimensional k R]
  [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]
  [FiniteDimensional k M] [Module.Injective R M]

omit [FiniteDimensional k R] in

lemma finite_injective_retract_dual :
    ∃ (n : ℕ) (i : M →ₗ[R] (Fin n → DualBimodule k R))
      (p : (Fin n → DualBimodule k R) →ₗ[R] M), p.comp i = LinearMap.id := by
  let i := finiteCoinducedEmbedding (k := k) (R := R) (M := M)
  obtain ⟨s,hs⟩ := Module.Injective.extension_property R M M _ i
    finiteCoinducedEmbedding_injective LinearMap.id
  exact ⟨_,i,s,hs⟩

end Tachikawa



namespace Tachikawa
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra
attribute [local instance] Abelian.hasFiniteBiproducts
variable {k R : Type} [Field k] [Ring R] [Algebra k R]

lemma finiteInjective_inAdd (M : ModuleCat R) [FiniteDimensional k M] [Injective M] :
    InAdd (Enveloping.dualLeftObj (k := k) (R := R)) M := by
  let : Module.Injective R M := Module.injective_module_of_injective_object R M
  obtain ⟨n,i,p,hp⟩ := finite_injective_retract_dual (k := k) (R := R) (M := M)
  let e := ModuleCat.biproductIsoPi (fun _ : Fin n => Enveloping.dualLeftObj (k := k) (R := R))
  refine ⟨n,⟨{i := ModuleCat.ofHom i ≫ e.inv, r := e.hom ≫ ModuleCat.ofHom p, retract := ?_}⟩⟩
  erw [Category.assoc,← Category.assoc e.inv,e.inv_hom_id,Category.id_comp]
  exact ModuleCat.hom_ext hp

end Tachikawa



namespace Tachikawa.Construction
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q : k)

instance instFiniteDimensionalCarrierBBRegularLeftObj : FiniteDimensional k (bRegularLeftObj q) :=
  moduleCatFinite (k := k) (R := B q) (B q)

lemma b_injectiveDimension (hq : q ≠ 0) : HasInjectiveDimensionLE (bRegularLeftObj q) 4 := by
  apply HasInjectiveDimensionLT.mk
  intro n hn V e
  let : Subsingleton (Abelian.Ext V (bRegularLeftObj q) n) := b_regular_ext_zero q hq V n (by omega)
  exact Subsingleton.elim _ _

lemma b_iterate_injective (hq : q ≠ 0) :
    Injective ((LeftCoinduced.iterate (k := k) 4).obj (bRegularLeftObj q)) := by
  let := b_injectiveDimension q hq
  exact LeftCoinduced.iterate_injective _ 4

lemma b_iterate_inAdd (hq : q ≠ 0) :
    InAdd (Enveloping.dualLeftObj (k := k) (R := B q))
      ((LeftCoinduced.iterate (k := k) 4).obj (bRegularLeftObj q)) := by
  let := b_iterate_injective q hq
  exact finiteInjective_inAdd _

omit [CharP k 2] in
lemma b_coindTerm_inAdd (n : ℕ) :
    InAdd (Enveloping.dualLeftObj (k := k) (R := B q))
      ((LeftCoinduced.J (k := k)).obj
        ((LeftCoinduced.iterate (k := k) n).obj (bRegularLeftObj q))) :=
  by
    exact finiteInjective_inAdd _

end Tachikawa.Construction



namespace Tachikawa.Construction
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q : k)

omit [CharP k 2] in
lemma b_outerCoindTerm_inAdd (n : ℕ) :
    InAdd (Enveloping.ordinaryOuterObj (k := k) (R := B q))
      (Enveloping.coindTerm
        (Enveloping.rightFreeObj (k := k) (S := B q) (bRegularLeftObj q)) n) :=
  ((b_coindTerm_inAdd q n).map (Enveloping.rightFreeFunctor (k := k) (S := B q))).iso
    (Enveloping.coindTermTensorIso (bRegularLeftObj q) n).symm

lemma b_outerIterate_inAdd (hq : q ≠ 0) :
    InAdd (Enveloping.ordinaryOuterObj (k := k) (R := B q))
      ((Enveloping.coindIterate (k := k) 4).obj
        (Enveloping.rightFreeObj (k := k) (S := B q) (bRegularLeftObj q))) :=
  ((b_iterate_inAdd q hq).map (Enveloping.rightFreeFunctor (k := k) (S := B q))).iso
    (Enveloping.coindIterateTensorIso (bRegularLeftObj q) 4).symm

theorem b_projective_coinduced_terms (hq : q ≠ 0)
    (L : ModuleCat (Enveloping.Alg k (B q) (B q)))
    [Module.Finite (Enveloping.Alg k (B q) (B q)) L]
    [Module.Projective (Enveloping.Alg k (B q) (B q)) L] :
    (∀ n : ℕ, InAdd (Enveloping.ordinaryOuterObj (k := k) (R := B q))
      (Enveloping.coindTerm L n)) ∧
    InAdd (Enveloping.ordinaryOuterObj (k := k) (R := B q))
      ((Enveloping.coindIterate (k := k) 4).obj L) := by
  have hL : InAdd (Enveloping.rightFreeObj (k := k) (S := B q) (bRegularLeftObj q)) L :=
    Enveloping.finiteProjective_inAdd_outer L
  constructor
  · intro n
    exact (b_outerCoindTerm_inAdd q n).trans
      (hL.map (Enveloping.coindIterate (k := k) n ⋙ Enveloping.coindEndo))
  · exact (b_outerIterate_inAdd q hq).trans (hL.map (Enveloping.coindIterate (k := k) 4))

end Tachikawa.Construction



namespace Tachikawa.Enveloping
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex

attribute [instance] CoindReplacement.quasiIso

end Tachikawa.Enveloping



namespace Tachikawa.Construction
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
variable {k : Type} [Field k] [CharP k 2] (q : k)

lemma b_coindGoodTerms (hq : q ≠ 0)
    (P : CochainComplex (ModuleCat (Enveloping.Alg k (B q) (B q))) ℤ)
    (hfin : ∀ i, Module.Finite (Enveloping.Alg k (B q) (B q)) (P.X i))
    (hproj : ∀ i, Module.Projective (Enveloping.Alg k (B q) (B q)) (P.X i)) :
    Enveloping.CoindGoodTerms (Enveloping.ordinaryOuterObj (k := k) (R := B q)) 4 P := by
  have h (i : ℤ) := by
    let := hfin i
    let := hproj i
    exact b_projective_coinduced_terms q hq (P.X i)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i; exact (h i).1 0
  · intro i; exact (h i).1 1
  · intro i; exact (h i).1 2
  · intro i; exact (h i).1 3
  · intro i; exact (h i).2

theorem b_bounded_ordinary_replacement (hq : q ≠ 0)
    (P : CochainComplex (ModuleCat (Enveloping.Alg k (B q) (B q))) ℤ)
    (hfin : ∀ i, Module.Finite (Enveloping.Alg k (B q) (B q)) (P.X i))
    (hproj : ∀ i, Module.Projective (Enveloping.Alg k (B q) (B q)) (P.X i))
    (l u : ℤ) (hbound : ∀ i, i < l ∨ u < i → IsZero (P.X i)) :
    ∃ (P' : CochainComplex (ModuleCat (Enveloping.Alg k (B q) (B q))) ℤ) (f : P ⟶ P'),
      QuasiIso f ∧
      (∀ i, InAdd (Enveloping.ordinaryOuterObj (k := k) (R := B q)) (P'.X i)) ∧
      (∀ i, i < l ∨ u + 4 < i → IsZero (P'.X i)) := by
  refine ⟨(Enveloping.coindReplacement 4 P).complex,
    (Enveloping.coindReplacement 4 P).map, inferInstance, ?_, ?_⟩
  · exact Enveloping.coindReplacement_terms _ 4 P (b_coindGoodTerms q hq P hfin hproj)
  · exact Enveloping.coindReplacement_bounded 4 P l u hbound

end Tachikawa.Construction



namespace Tachikawa.Construction
open CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [local instance] HasDerivedCategory.standard
variable {k : Type} [Field k] [CharP k 2] (q : k)

theorem b_ordinary_factorization (hq : q ≠ 0)
    (P : CochainComplex (ModuleCat (Enveloping.Alg k (B q) (B q))) ℤ)
    (hfin : ∀ i, Module.Finite (Enveloping.Alg k (B q) (B q)) (P.X i))
    (hproj : ∀ i, Module.Projective (Enveloping.Alg k (B q) (B q)) (P.X i))
    (l u : ℤ) (hbound : ∀ i, i < l ∨ u < i → IsZero (P.X i))
    (v : Enveloping.regular (k := k) (R := B q) ⟶ Enveloping.dualRegularObj (k := k) (R := B q))
    (α : DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj (Enveloping.regular (k := k) (R := B q))) ⟶ DerivedCategory.Q.obj P)
    (β : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj (Enveloping.dualRegularObj (k := k) (R := B q))))
    (hv : α ≫ β = DerivedCategory.Q.map ((CochainComplex.singleFunctor _ 0).map v)) :
    ∃ (V : ModuleCat (Enveloping.Alg k (B q) (B q)))
      (a : Enveloping.regular (k := k) (R := B q) ⟶ V)
      (b : V ⟶ Enveloping.dualRegularObj (k := k) (R := B q)),
      InAdd (Enveloping.ordinaryOuterObj (k := k) (R := B q)) V ∧ a ≫ b = v := by
  obtain ⟨P',f,hf,ht,hb⟩ := b_bounded_ordinary_replacement q hq P hfin hproj l u hbound
  let := hf
  have he : (α ≫ DerivedCategory.Q.map f) ≫ (inv (DerivedCategory.Q.map f) ≫ β) =
      DerivedCategory.Q.map ((CochainComplex.singleFunctor _ 0).map v) := by
    simpa only [Category.assoc, IsIso.hom_inv_id_assoc] using hv
  obtain ⟨a,b,hab⟩ := bounded_ordinary_factorization
    (Enveloping.regularResolution (k := k) (R := B q))
    (injectiveResolution (Enveloping.dualRegularObj (k := k) (R := B q)))
    P' l (u+4) hb ht
    (Enveloping.regular_outer_ext_zero (k := k) (R := B q))
    (Enveloping.outer_dual_ext_zero (k := k) (R := B q)) v
    (α ≫ DerivedCategory.Q.map f) (inv (DerivedCategory.Q.map f) ≫ β) he
  exact ⟨P'.X 0,a,b,ht 0,hab⟩

end Tachikawa.Construction

end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_StableLift
attribute [-instance] _root_.OAI.Tachikawa.DownHom.instAddCommGroupCochain _root_.OAI.Tachikawa.DownHom.instModuleCochain _root_.OAI.Tachikawa.Enveloping.instLinearModuleCatAlgEvaluation _root_.OAI.Tachikawa.Triangular.instAddCommGroupOff _root_.OAI.Tachikawa.Triangular.instAddCommGroupTriple _root_.OAI.Tachikawa.Triangular.instAdditiveModuleCatAlgD₀ _root_.OAI.Tachikawa.Triangular.instAdditiveModuleCatAlgD₁ _root_.OAI.Tachikawa.Triangular.instFiniteCarrierOneFree _root_.OAI.Tachikawa.Triangular.instFiniteDimensionalAlgOfCarrierAlg _root_.OAI.Tachikawa.Triangular.instIsScalarTowerMulOppositeProdOff _root_.OAI.Tachikawa.Triangular.instIsScalarTowerProdOff _root_.OAI.Tachikawa.Triangular.instModuleAlgTriple _root_.OAI.Tachikawa.Triangular.instModuleMulOppositeProdOff _root_.OAI.Tachikawa.Triangular.instModuleOff _root_.OAI.Tachikawa.Triangular.instModuleProdOff _root_.OAI.Tachikawa.Triangular.instProjectiveCarrierOneFree _root_.OAI.Tachikawa.Triangular.instSMulCommClassProdMulOppositeOff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace Tachikawa
open CategoryTheory CategoryTheory.Limits
attribute [local instance] Abelian.hasFiniteBiproducts HasDerivedCategory.standard
open scoped TensorProduct ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q : k)

lemma ordinary_inAdd_factorization_pf_zero
    {V : ModuleCat (Enveloping.Alg k (B q) (B q))}
    (hV : InAdd (Enveloping.ordinaryOuterObj (k := k) (R := B q)) V)
    (a : Enveloping.regular (k := k) (R := B q) ⟶ V)
    (b : V ⟶ Enveloping.dualRegularObj (k := k) (R := B q)) :
    Enveloping.dualRegularUnderlying ((a ≫ b) (Enveloping.regularUnderlyingEquiv.symm 1)) (pf q) = 0 := by
  classical
  obtain ⟨n,⟨r⟩⟩ := hV
  let W := Enveloping.ordinaryOuterObj (k := k) (R := B q)
  have he : ∑ i : Fin n, (a ≫ r.i ≫ biproduct.π (fun _ : Fin n => W) i) ≫
      (biproduct.ι (fun _ : Fin n => W) i ≫ r.r ≫ b) = a ≫ b := by
    simp only [Category.assoc]
    rw [← Preadditive.comp_sum,← Preadditive.comp_sum]
    conv_lhs => arg 2; arg 2; simp only [← Category.assoc]
    rw [← Preadditive.sum_comp,← Preadditive.sum_comp,biproduct.total]
    dsimp only [W]
    simp only [Category.id_comp,← Category.assoc]
    rw [Category.assoc a,r.retract,Category.comp_id]
  rw [← he]
  change Enveloping.dualRegularUnderlying ((∑ i : Fin n,
    (a ≫ r.i ≫ biproduct.π (fun _ : Fin n => W) i) ≫
      (biproduct.ι (fun _ : Fin n => W) i ≫ r.r ≫ b)).hom
        (Enveloping.regularUnderlyingEquiv.symm 1)) (pf q) = 0
  simp only [ModuleCat.hom_sum,LinearMap.sum_apply,map_sum]
  exact Finset.sum_eq_zero (fun i _ => ordinary_morphism_factorization_pf_zero q _ _)

lemma characterBimoduleMap_not_inAdd_factor
    {V : ModuleCat (Enveloping.Alg k (B q) (B q))}
    (hV : InAdd (Enveloping.ordinaryOuterObj (k := k) (R := B q)) V)
    (a : Enveloping.regular (k := k) (R := B q) ⟶ V)
    (b : V ⟶ Enveloping.dualRegularObj (k := k) (R := B q)) :
    a ≫ b ≠ characterBimoduleMap q := by
  intro h
  have hz := ordinary_inAdd_factorization_pf_zero q hV a b
  rw [h,characterBimoduleMap_apply,characterMapB_one_pf] at hz
  exact one_ne_zero hz

theorem characterBimoduleMap_not_derived_perfect_factor (hq : q ≠ 0)
    (P : CochainComplex (ModuleCat (Enveloping.Alg k (B q) (B q))) ℤ)
    (hfin : ∀ i, Module.Finite (Enveloping.Alg k (B q) (B q)) (P.X i))
    (hproj : ∀ i, Module.Projective (Enveloping.Alg k (B q) (B q)) (P.X i))
    (l u : ℤ) (hbound : ∀ i, i < l ∨ u < i → IsZero (P.X i))
    (α : DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj (Enveloping.regular (k := k) (R := B q))) ⟶ DerivedCategory.Q.obj P)
    (β : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj (Enveloping.dualRegularObj (k := k) (R := B q)))) :
    α ≫ β ≠ DerivedCategory.Q.map ((CochainComplex.singleFunctor _ 0).map (characterBimoduleMap q)) := by
  intro h
  obtain ⟨V,a,b,hV,hab⟩ := Construction.b_ordinary_factorization q hq P hfin hproj l u hbound
    (characterBimoduleMap q) α β h
  exact characterBimoduleMap_not_inAdd_factor q hV a b hab

end Tachikawa



namespace Tachikawa.Construction
open CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [local instance] HasDerivedCategory.standard
open scoped TensorProduct ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q H : k) (hH : H ≠ 0)

def inducedSocleMap : Enveloping.inducedRegularCochain (inclusionB q) ⟶
    (CochainComplex.singleFunctor _ 0).obj (U q H hH) :=
  Enveloping.inducedRegularAugmentation (inclusionB q) ≫
    (CochainComplex.singleFunctor _ 0).map
      (HomBimodule.representation (k := k) (ModuleCat.of (E q) (X q)) ≫
        socleBimoduleMap q H hH)

omit [CharP k 2] in

lemma inducedSocleMap_square :
    Enveloping.regularUnit (inclusionB q) ≫
    ((bimoduleRestriction q).mapHomologicalComplex (.up ℤ)).map (inducedSocleMap q H hH) ≫
      Enveloping.restrictedSingleMap (inclusionB q) (rhoBimodule q H hH) =
    (Enveloping.regularResolution (k := k) (R := B q)).π' ≫
      (CochainComplex.singleFunctor _ 0).map (characterBimoduleMap q) := by
  have h := Enveloping.regularUnit_square (inclusionB q)
    (HomBimodule.representation (k := k) (ModuleCat.of (E q) (X q)) ≫
      socleBimoduleMap q H hH) (rhoBimodule q H hH)
  rw [restricted_socle_character] at h
  exact h

theorem inducedSocleMap_not_derived_perfect_factor (hq : q ≠ 0)
    (P : CochainComplex (ModuleCat.{0} (Enveloping.Alg k (E q) (E q))) ℤ)
    (hfin : ∀ i, Module.Finite (Enveloping.Alg k (E q) (E q)) (P.X i))
    (hproj : ∀ i, Module.Projective (Enveloping.Alg k (E q) (E q)) (P.X i))
    (l u : ℤ) (hb : ∀ i, i < l ∨ u < i → IsZero (P.X i))
    (α : DerivedCategory.Q.obj (Enveloping.inducedRegularCochain (inclusionB q)) ⟶
      DerivedCategory.Q.obj P)
    (β : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj
      ((CochainComplex.singleFunctor _ 0).obj (U q H hH))) :
    α ≫ β ≠ DerivedCategory.Q.map (inducedSocleMap q H hH) := by
  intro h
  obtain ⟨P',f,hf,hp',hfin',hb'⟩ := restricted_perfect_replacement q hq P hfin hproj l u hb
  let := hf
  let F := bimoduleRestriction q
  let Qb := DerivedCategory.Q (C := ModuleCat.{0} (Enveloping.Alg k (B q) (B q)))
  let π := (Enveloping.regularResolution (k := k) (R := B q)).π'
  let η := Enveloping.regularUnit (inclusionB q)
  let ρ := Enveloping.restrictedSingleMap (inclusionB q) (rhoBimodule q H hH)
  let a := inv (Qb.map π) ≫ Qb.map η ≫ exactDerivedHom F α ≫ inv (Qb.map f)
  let b := Qb.map f ≫ exactDerivedHom F β ≫ Qb.map ρ
  apply characterBimoduleMap_not_derived_perfect_factor q hq P' hfin' hp' (l-8) u hb' a b
  calc
    a ≫ b = inv (Qb.map π) ≫ Qb.map η ≫ exactDerivedHom F (α ≫ β) ≫ Qb.map ρ := by
      simp only [a,b,Category.assoc,IsIso.inv_hom_id_assoc,exactDerivedHom_comp]
    _ = inv (Qb.map π) ≫ Qb.map η ≫
        Qb.map ((F.mapHomologicalComplex (.up ℤ)).map (inducedSocleMap q H hH)) ≫ Qb.map ρ := by
      rw [h,exactDerivedHom_map]
    _ = inv (Qb.map π) ≫ Qb.map (π ≫
        (CochainComplex.singleFunctor _ 0).map (characterBimoduleMap q)) := by
      rw [← Functor.map_comp,← Functor.map_comp]
      congr 2
      exact inducedSocleMap_square q H hH
    _ = Qb.map ((CochainComplex.singleFunctor _ 0).map (characterBimoduleMap q)) := by
      simp only [Functor.map_comp,IsIso.inv_hom_id_assoc]

end Tachikawa.Construction



namespace Tachikawa.Construction
open CategoryTheory HomologicalComplex
open scoped TensorProduct ModuleCat.Algebra
attribute [local instance] HasDerivedCategory.standard
variable {k : Type} [Field k] [CharP k 2] (q H : k) (hH : H ≠ 0)

def finiteU : FiniteModule k (Enveloping.Alg k (E q) (E q)) where
  obj := U q H hH
  finite := by
    let : IsScalarTower k (Enveloping.Alg k (E q) (E q)) (U q H hH) :=
      IsScalarTower.restrictScalars k (Enveloping.Alg k (E q) (E q)) (U q H hH)
    exact Module.Finite.of_restrictScalars_finite k _ _

lemma inducedSocleMap_high_lift_nonzero (hq : q ≠ 0)
    (f : Enveloping.inducedRegularCochain (inclusionB q) ⟶
        (finiteU q H hH).projectiveResolution.cochainComplex)
    (hf : DerivedCategory.Q.map f ≫ DerivedCategory.Q.map (finiteU q H hH).projectiveResolution.π' =
        DerivedCategory.Q.map (inducedSocleMap q H hH)) :
    ∀ n : ℕ, 5 ≤ n → CokerAt.map (reflectCochainMap f) n ∉ projectiveFactors (k := k) := by
  let : Module.Injective (Enveloping.Alg k (E q) (E q)) (Enveloping.Alg k (E q) (E q)) :=
    (Enveloping.envelopingForm (formE q) (formE q)).injective
  exact stably_nonzero_high_lift (Enveloping.inducedRegularCochain (inclusionB q))
    (fun _ => by infer_instance) (finiteU q H hH) (inducedSocleMap q H hH) 5 (by omega)
    (fun n hn => inducedRegularCochain_reflect_exact q hq n (by omega))
    (inducedSocleMap_not_derived_perfect_factor q H hH hq) f hf

end Tachikawa.Construction



namespace Tachikawa
open CategoryTheory HomologicalComplex
open scoped ModuleCat.Algebra
attribute [local instance] HasDerivedCategory.standard

namespace Construction
variable {k : Type} [Field k] [CharP k 2] (q H : k) (hH : H ≠ 0)

def xObj : ModuleCat (E q) := ModuleCat.of (E q) (X q)

def xUnderlyingLinear : xObj q ≃ₗ[k] k where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c x := by
    change characterE q (algebraMap k (E q) c) * (show k from x) = c * (show k from x)
    rw [AlgHom.commutes]; rfl

instance instFiniteDimensionalCarrierEXObj : FiniteDimensional k (xObj q) :=
  Module.Finite.equiv (xUnderlyingLinear q).symm

def finiteS : FiniteModule k (Enveloping.Alg k (E q) (E q)) where
  obj := S q
  finite := by
    let : Module.Finite k (S q) := Module.Finite.equiv
      (HomBimodule.underlyingLinearEquiv (k := k) (xObj q) (xObj q)).symm
    let : IsScalarTower k (Enveloping.Alg k (E q) (E q)) (S q) :=
      IsScalarTower.restrictScalars k (Enveloping.Alg k (E q) (E q)) (S q)
    exact Module.Finite.of_restrictScalars_finite k _ _

def inducedRepresentationMap : Enveloping.inducedRegularCochain (inclusionB q) ⟶
    (CochainComplex.singleFunctor _ 0).obj (S q) :=
  Enveloping.inducedRegularAugmentation (inclusionB q) ≫
    (CochainComplex.singleFunctor _ 0).map
      (HomBimodule.representation (k := k) (ModuleCat.of (E q) (X q)))

omit [CharP k 2] in
lemma inducedRepresentation_socle : inducedRepresentationMap q ≫
    (CochainComplex.singleFunctor _ 0).map (socleBimoduleMap q H hH) = inducedSocleMap q H hH := by
  simp only [inducedRepresentationMap,inducedSocleMap,Functor.map_comp,Category.assoc]

theorem separated_stably_nonzero_lifts (hq : q ≠ 0) :
    ∃ (a : Enveloping.inducedRegularCochain (inclusionB q) ⟶
        (finiteS q).projectiveResolution.cochainComplex)
      (b : (finiteS q).projectiveResolution.cochainComplex ⟶
        (finiteU q H hH).projectiveResolution.cochainComplex),
      DerivedCategory.Q.map a ≫ DerivedCategory.Q.map (finiteS q).projectiveResolution.π' =
        DerivedCategory.Q.map (inducedRepresentationMap q) ∧
      DerivedCategory.Q.map b ≫ DerivedCategory.Q.map (finiteU q H hH).projectiveResolution.π' =
        DerivedCategory.Q.map (finiteS q).projectiveResolution.π' ≫
          DerivedCategory.Q.map ((CochainComplex.singleFunctor _ 0).map (socleBimoduleMap q H hH)) ∧
      ∀ n : ℕ, 5 ≤ n →
        (CokerAt.map (reflectCochainMap b) n).comp (CokerAt.map (reflectCochainMap a) n)
          ∉ projectiveFactors (k := k) := by
  let : Module.Injective (Enveloping.Alg k (E q) (E q)) (Enveloping.Alg k (E q) (E q)) :=
    (Enveloping.envelopingForm (formE q) (formE q)).injective
  obtain ⟨a,ha⟩ := finiteResolutionLift (Enveloping.inducedRegularCochain (inclusionB q))
    (finiteS q) (DerivedCategory.Q.map (inducedRepresentationMap q))
  obtain ⟨b,hb⟩ := finiteResolutionLift (finiteS q).projectiveResolution.cochainComplex
    (finiteU q H hH) (DerivedCategory.Q.map (finiteS q).projectiveResolution.π' ≫
      DerivedCategory.Q.map ((CochainComplex.singleFunctor _ 0).map (socleBimoduleMap q H hH)))
  refine ⟨a,b,ha,hb,?_⟩
  have hc : DerivedCategory.Q.map (a ≫ b) ≫
      DerivedCategory.Q.map (finiteU q H hH).projectiveResolution.π' =
      DerivedCategory.Q.map (inducedSocleMap q H hH) := by
    exact (lift_composite_eq DerivedCategory.Q a b _ _ _ _ ha hb).trans
      (congrArg DerivedCategory.Q.map (inducedRepresentation_socle q H hH))
  have hn := inducedSocleMap_high_lift_nonzero q H hH hq (a ≫ b) hc
  intro n h
  have he : reflectCochainMap (a ≫ b) = reflectCochainMap a ≫ reflectCochainMap b := rfl
  simpa only [he,CokerAt.map_comp] using hn n h
end Construction
end Tachikawa



namespace Tachikawa
open CategoryTheory
open scoped ModuleCat.Algebra TensorProduct
namespace Enveloping
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  [FiniteDimensional k R] [FiniteDimensional k S]
def inducedFiveCokerEquiv (f : R →ₐ[k] S) :
    CokerAt (reflectCochain (inducedRegularCochain f)) 5 ≃ₗ[Alg k S S] (inducedCokerFive f).obj :=
  resolutionReflectCokerEquiv (regularResolution (k := k) (R := R))
    (AlgebraInduction.functor (envelopingMap f)) 5
end Enveloping

namespace Construction
variable {k : Type} [Field k] [CharP k 2] (q H : k) (hH : H ≠ 0)

theorem exists_Y_lift_with_nonzero_composition (hq : q ≠ 0) :
    ∃ (g : (finiteU q H hH).obj ⟶ (Y q).obj)
      (psi : (Y q).obj ⟶ ((finiteS q).positive 1).obj),
      (g ≫ psi).hom ∉ projectiveFactors (k := k) := by
  let N := Enveloping.inducedCokerFive (inclusionB q)
  let Us := finiteU q H hH
  let Ss := finiteS q
  let t := Enveloping.envelopingForm (formE q) (formE q)
  obtain ⟨a,b,_ha,_hb,hn⟩ := separated_stably_nonzero_lifts q H hH hq
  let aa := CokerAt.map (reflectCochainMap a) 5
  let bb := CokerAt.map (reflectCochainMap b) 5
  let eN := Enveloping.inducedFiveCokerEquiv (inclusionB q)
  let eS := Ss.reflectCokerPositiveEquiv 5
  let eU := Us.reflectCokerPositiveEquiv 5
  let phi :=
    (eS.toLinearMap.comp aa).comp eN.symm.toLinearMap
  let b' :=
    (eU.toLinearMap.comp bb).comp eS.symm.toLinearMap
  have hbphi : b'.comp phi ∉ projectiveFactors (k := k) := by
    have he : b'.comp phi = (eU.toLinearMap.comp (bb.comp aa)).comp eN.symm.toLinearMap := by
      ext x
      change eU (bb (eS.symm (eS (aa (eN.symm x))))) = eU (bb (aa (eN.symm x)))
      rw [eS.symm_apply_apply]
    rw [he, projectiveFactors_conjugate_iff]
    exact hn 5 (by omega)
  obtain ⟨beta,hbeta⟩ := t.exists_syzygy_postcomposition Us N (Ss.positive 5) 4 b' phi hbphi
  obtain ⟨g,psi,hg⟩ := FiniteModule.descend_nonzero_composition_iterated t Us Ss 4 N beta phi hbeta
  exact ⟨ModuleCat.ofHom (X := (finiteU q H hH).obj) (Y := (Y q).obj) g,
    ModuleCat.ofHom (X := (Y q).obj) (Y := ((finiteS q).positive 1).obj) psi,hg⟩
end Construction
end Tachikawa



namespace Tachikawa.Enveloping
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  [FiniteDimensional k R] [FiniteDimensional k S]
  (t : SymmetrizingForm (k := k) (R := R)) (u : SymmetrizingForm (k := k) (R := S))
  (X : ModuleCat.{0} R) [FiniteDimensional k X]
  {M N P Q M' N' : ModuleCat.{0} (Alg k S R)}
  [FiniteDimensional k M] [FiniteDimensional k N]
  [Module.Projective Rᵐᵒᵖ (Obj M)] [Module.Projective Rᵐᵒᵖ (Obj N)]
  [Module.Finite (Alg k S R) P] [Module.Projective (Alg k S R) P]
  [Module.Finite (Alg k S R) Q] [Module.Projective (Alg k S R) Q]

include t u in

lemma eval_square_factors_iff
    (i : M ⟶ P) (pi : P ⟶ M') (hi : Function.Injective i)
    (hex : Function.Exact i pi) (hpi : Function.Surjective pi)
    (j : N ⟶ Q) (delta : Q ⟶ N') (hj : Function.Injective j)
    (hex' : Function.Exact j delta) (hdelta : Function.Surjective delta)
    (f : M ⟶ N) (h : P ⟶ Q) (g : M' ⟶ N')
    (hu : i ≫ h = f ≫ j) (hl : h ≫ delta = pi ≫ g) :
    (evalMap X f).hom ∈ projectiveFactors (k := k) ↔
      (evalMap X g).hom ∈ projectiveFactors (k := k) := by
  let : Module.Injective S S := u.injective
  let : FiniteDimensional k P := Module.Finite.trans (Alg k S R) P
  let : FiniteDimensional k Q := Module.Finite.trans (Alg k S R) Q
  apply exact_square_factors_iff (P := evalObj X P) (Q := evalObj X Q)
    (evalMap X i).hom (evalMap X pi).hom
    (evalMap_injective X t i hi) (evalMap_exact X t i pi hi hex hpi)
    (evalMap_surjective X pi hpi)
    (evalMap X j).hom (evalMap X delta).hom
    (evalMap_injective X t j hj) (evalMap_exact X t j delta hj hex' hdelta)
    (evalMap_surjective X delta hdelta)
    (evalMap X f).hom (evalMap X h).hom (evalMap X g).hom
  · have hmap := congrArg (evaluation X).map hu
    rw [Functor.map_comp,Functor.map_comp] at hmap
    ext x
    exact congrArg (fun a : (evaluation X).obj M ⟶ (evaluation X).obj Q => a x) hmap
  · have hmap := congrArg (evaluation X).map hl
    rw [Functor.map_comp,Functor.map_comp] at hmap
    ext x
    exact congrArg (fun a : (evaluation X).obj P ⟶ (evaluation X).obj N' => a x) hmap
end Tachikawa.Enveloping



namespace Tachikawa.Construction
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q H : k) (hH : H ≠ 0)




omit [CharP k 2] in
lemma sigma_fixed_x (r : E q) (x : xObj q) :
    sigma q H hH r • x = r • x := by
  change characterE q (sigma q H hH r) * (show k from x) =
    characterE q r * (show k from x)
  rw [characterE_sigma]

def uXIso : Enveloping.evalObj (xObj q) (finiteU q H hH).obj ≅ xObj q :=
  Enveloping.twistedEvalIso (sigma q H hH) (xObj q) (sigma_fixed_x q H hH)

end Tachikawa.Construction

end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_HomProfile
attribute [-instance] _root_.OAI.Tachikawa.DownHom.instAddCommGroupCochain _root_.OAI.Tachikawa.DownHom.instModuleCochain _root_.OAI.Tachikawa.Enveloping.instLinearModuleCatAlgEvaluation _root_.OAI.Tachikawa.Triangular.instAddCommGroupOff _root_.OAI.Tachikawa.Triangular.instAddCommGroupTriple _root_.OAI.Tachikawa.Triangular.instAdditiveModuleCatAlgD₀ _root_.OAI.Tachikawa.Triangular.instAdditiveModuleCatAlgD₁ _root_.OAI.Tachikawa.Triangular.instFiniteCarrierOneFree _root_.OAI.Tachikawa.Triangular.instFiniteDimensionalAlgOfCarrierAlg _root_.OAI.Tachikawa.Triangular.instIsScalarTowerMulOppositeProdOff _root_.OAI.Tachikawa.Triangular.instIsScalarTowerProdOff _root_.OAI.Tachikawa.Triangular.instModuleAlgTriple _root_.OAI.Tachikawa.Triangular.instModuleMulOppositeProdOff _root_.OAI.Tachikawa.Triangular.instModuleOff _root_.OAI.Tachikawa.Triangular.instModuleProdOff _root_.OAI.Tachikawa.Triangular.instSMulCommClassProdMulOppositeOff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace Tachikawa.MissingYProfile
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2]

def finiteYX (q : k) : FiniteModule k (Construction.E q) where
  obj := Enveloping.evalObj (Construction.xObj q) (Construction.Y q).obj
  finite := inferInstance

def shift (q : k) (M : FiniteModule k (Construction.E q)) : ℤ → FiniteModule k (Construction.E q)
  | .ofNat n => M.negative (Construction.formE q) n
  | .negSucc n => M.positive (n+1)

abbrev W (q : k) (a : ℤ) := StableHom (k := k) (R := Construction.E q)
  (M := Construction.xObj q) (N := (shift q (finiteYX q) a).obj)

def profile (q : k) : Prop := ∀ a : ℤ,
  ((a = -3 ∨ a = 0) → Nonempty (W q a ≃ₗ[k] k)) ∧
  (a ≠ -3 → a ≠ 0 → Subsingleton (W q a))

end Tachikawa.MissingYProfile



namespace Tachikawa.Construction
open CategoryTheory HomologicalComplex
open scoped ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q : k)
variable (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0)

abbrev evalK := ((Enveloping.evaluation (k := k) (xObj q)).mapHomologicalComplex _).obj
  (Enveloping.inducedRegularComplex (inclusionB q))

omit [CharP k 2] in
lemma evalK_finite (n : ℕ) : Module.Finite (E q) ((evalK q).X n) := by
  change Module.Finite (E q) (Enveloping.evalObj (xObj q)
    ((Enveloping.inducedRegularComplex (inclusionB q)).X n))
  infer_instance

omit [CharP k 2] in
lemma evalK_projective (n : ℕ) : Module.Projective (E q) ((evalK q).X n) := by
  change Module.Projective (E q) (Enveloping.evalObj (xObj q)
    ((Enveloping.inducedRegularComplex (inclusionB q)).X n))
  infer_instance

lemma natJJ_finite (n : ℕ) : Module.Finite (E q) ((natJJ q hp).X n) := by
  let := forwardJJ_finite q hp (n:ℤ)
  exact Module.Finite.equiv (jjNatIntIso q hp n).toLinearEquiv.symm

lemma natJJ_projective (n : ℕ) : Module.Projective (E q) ((natJJ q hp).X n) := by
  let := forwardJJ_projective q hp (n:ℤ)
  exact Module.Projective.of_equiv (jjNatIntIso q hp n).toLinearEquiv.symm

def evalFiveFiberStableEquiv : StableEquiv (k := k)
    (Enveloping.evalObj (xObj q) (Enveloping.inducedCokerFive (inclusionB q)).obj)
    (ModuleCat.of (E q) (CokerAt (jjFiber q hq hp) 5)) := by
  let := evalK_finite q 4
  let := evalK_projective q 4
  let := natJJ_finite q hp 4
  let := natJJ_projective q hp 4
  let e : HomotopyEquiv (evalK q) (natJJ q hp) := evaluatedKJComparison q hp
  let e₁ := Enveloping.evalCokerIso (xObj q)
    ((Enveloping.inducedRegularComplex (inclusionB q)).d 6 5)
  exact (StableEquiv.ofLinearEquiv e₁.toLinearEquiv).trans
    ((NatCoker.stableEquiv e 4).trans
      (StableEquiv.ofLinearEquiv (natJJFiveFiberEquiv q hq hp)))

end Tachikawa.Construction



namespace Tachikawa.Construction
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q : k)
variable (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0)

def evalNegativeFiveFiberStableEquiv (n : ℕ) : StableEquiv (k := k)
    (Enveloping.evalObj (xObj q)
      ((Enveloping.inducedCokerFive (inclusionB q)).negative
        (Enveloping.envelopingForm (formE q) (formE q)) n).obj)
    (ModuleCat.of (E q) (CokerAt (jjFiber q hq hp) (5-(n:ℤ)))) := by
  let N := Enveloping.inducedCokerFive (inclusionB q)
  let τ := Enveloping.envelopingForm (formE q) (formE q)
  let := c5_left_projective q hq
  let := c5_right_projective q hq
  induction n with
  | zero => exact evalFiveFiberStableEquiv q hq hp
  | succ n ih =>
    let : Module.Projective (E q)ᵐᵒᵖ (Enveloping.Obj (N.negative τ n).obj) :=
      (Enveloping.negative_side_projective (formE q) (formE q) N n).2
    have e := Enveloping.evalCosyCokerStableEquiv (formE q) (formE q) (xObj q)
      (N.negative τ n) (jjFiber q hq hp) (jjFiber_totallyAcyclic q hq hp).1
      (jjFiber_finite q hq hp) (jjFiber_projective q hq hp) (5-(n:ℤ)) ih
    change StableEquiv (k := k) (Enveloping.evalObj (xObj q) ((N.negative τ n).cosyzygy τ).obj)
      (ModuleCat.of (E q) (CokerAt (jjFiber q hq hp) (5-((n+1:ℕ):ℤ))))
    rw [show 5-((n+1:ℕ):ℤ) = (5-(n:ℤ))-1 by omega]
    exact e

def yxFiberStableEquiv : StableEquiv (k := k) (MissingYProfile.finiteYX q).obj
    (ModuleCat.of (E q) (CokerAt (jjFiber q hq hp) 1)) :=
  evalNegativeFiveFiberStableEquiv q hq hp 4

end Tachikawa.Construction



namespace Tachikawa.Construction
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q : k)

local instance simpleGround_r1f91a4_1 : Module k (C.simpleObj q) := ModuleCat.Algebra.instModuleCarrier
lemma forwardJJ_hom_zero (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0)
    (j : ℤ) (hj : j ≠ 0) (f : (forwardJJ q hp).X j ⟶ XTensorObj q) : f = 0 := by
  apply OuterTensor.total_hom_zero (forwardJ q hp) (forwardJ q hp)
    (C.simpleObj q) (C.simpleObj q) 0 0 j (by simpa using hj)
    (fun i => by
      let := forwardJ_finite q hp i
      exact Module.Finite.of_restrictScalars_finite k _ _)
    (fun i => by
      let := forwardJ_finite q hp i
      exact Module.Finite.of_restrictScalars_finite k _ _)
    (forwardJ_projective q hp) (forwardJ_projective q hp)
    (C.forwardJ_hom_zero q hp) (C.forwardJ_hom_zero q hp) f

lemma reverseJJ_hom_zero (hq : q ≠ 0)
    (j : ℤ) (hj : j ≠ 4) (f : (reverseJJ q hq).X j ⟶ XTensorObj q) : f = 0 := by
  apply OuterTensor.total_hom_zero (reverseJ q hq) (reverseJ q hq)
    (C.simpleObj q) (C.simpleObj q) 2 2 j (by simpa using hj)
    (fun i => by
      let := reverseJ_finite q hq i
      exact Module.Finite.of_restrictScalars_finite k _ _)
    (fun i => by
      let := reverseJ_finite q hq i
      exact Module.Finite.of_restrictScalars_finite k _ _)
    (reverseJ_projective q hq) (reverseJ_projective q hq)
    (C.reverseJ_hom_zero q hq) (C.reverseJ_hom_zero q hq) f

def forwardJJHomEquiv (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) :
    ((forwardJJ q hp).X 0 ⟶ XTensorObj q) ≃ₗ[k] k := by
  let f (i : ℤ) : Module.Finite (C.T q) ((forwardJ q hp).X i) := by
    let := forwardJ_finite q hp i
    exact Module.Finite.of_restrictScalars_finite k _ _
  let e := OuterTensor.totalHomSupported (k := k) (forwardJ q hp) (forwardJ q hp)
    (C.simpleObj q) (C.simpleObj q) 0 0 f f
    (forwardJ_projective q hp) (forwardJ_projective q hp)
    (C.forwardJ_hom_zero q hp) (C.forwardJ_hom_zero q hp)
  let := C.inducedObj_finite q 0
  let : Module.Finite (C.T q) (C.inducedObj q 0) := Module.Finite.of_restrictScalars_finite k _ _
  let := C.inducedObj_projective q 0
  exact e.trans ((OuterTensor.homEquiv (C.inducedObj q 0) (C.simpleObj q)
    (C.inducedObj q 0) (C.simpleObj q)).symm.trans
    ((TensorProduct.congr (C.inducedFHomEquiv q) (C.inducedFHomEquiv q)).trans
      (TensorProduct.lid k k)))

def reverseJJHomEquiv (hq : q ≠ 0) :
    ((reverseJJ q hq).X 4 ⟶ XTensorObj q) ≃ₗ[k] k := by
  let f (i : ℤ) : Module.Finite (C.T q) ((reverseJ q hq).X i) := by
    let := reverseJ_finite q hq i
    exact Module.Finite.of_restrictScalars_finite k _ _
  let e := OuterTensor.totalHomSupported (k := k) (reverseJ q hq) (reverseJ q hq)
    (C.simpleObj q) (C.simpleObj q) 2 2 f f
    (reverseJ_projective q hq) (reverseJ_projective q hq)
    (C.reverseJ_hom_zero q hq) (C.reverseJ_hom_zero q hq)
  let := C.inducedObj_finite q 0
  let : Module.Finite (C.T q) (C.inducedObj q 0) := Module.Finite.of_restrictScalars_finite k _ _
  let := C.inducedObj_projective q 0
  exact e.trans ((OuterTensor.homEquiv (C.inducedObj q 0) (C.simpleObj q)
    (C.inducedObj q 0) (C.simpleObj q)).symm.trans
    ((TensorProduct.congr (C.inducedFHomEquiv q) (C.inducedFHomEquiv q)).trans
      (TensorProduct.lid k k)))

def jjFiberHomEquiv (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) (j : ℤ) :
    ((jjFiber q hq hp).X j ⟶ XTensorObj q) ≃ₗ[k]
    (((reverseJJ q hq).X (j+1) ⟶ XTensorObj q) ×
      ((forwardJJ q hp).X j ⟶ XTensorObj q)) :=
  ModuleCat.homLinearEquiv.trans ((LinearMap.coprodEquiv k).symm.trans
    (LinearEquiv.prodCongr ModuleCat.homLinearEquiv.symm ModuleCat.homLinearEquiv.symm))

lemma jjFiber_hom_zero (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0)
    (j : ℤ) (h0 : j ≠ 0) (h3 : j ≠ 3)
    (f : (jjFiber q hq hp).X j ⟶ XTensorObj q) : f = 0 := by
  apply (jjFiberHomEquiv q hq hp j).injective
  rw [map_zero]
  apply Prod.ext
  · exact reverseJJ_hom_zero q hq (j+1) (by omega) _
  · exact forwardJJ_hom_zero q hp j h0 _

def jjFiberHomZeroEquiv (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) :
    ((jjFiber q hq hp).X 0 ⟶ XTensorObj q) ≃ₗ[k] k := by
  let : Subsingleton ((reverseJJ q hq).X (0+1) ⟶ XTensorObj q) :=
    ⟨fun f g => (reverseJJ_hom_zero q hq _ (by norm_num) f).trans
      (reverseJJ_hom_zero q hq _ (by norm_num) g).symm⟩
  let : Unique ((reverseJJ q hq).X (0+1) ⟶ XTensorObj q) := ⟨⟨0⟩, fun _ => Subsingleton.elim _ _⟩
  exact (jjFiberHomEquiv q hq hp 0).trans ((LinearEquiv.prodComm k _ _).trans
    (LinearEquiv.prodUnique.trans (forwardJJHomEquiv q hp)))

def jjFiberHomThreeEquiv (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) :
    ((jjFiber q hq hp).X 3 ⟶ XTensorObj q) ≃ₗ[k] k := by
  let : Subsingleton ((forwardJJ q hp).X 3 ⟶ XTensorObj q) :=
    ⟨fun f g => (forwardJJ_hom_zero q hp _ (by norm_num) f).trans
      (forwardJJ_hom_zero q hp _ (by norm_num) g).symm⟩
  let : Unique ((forwardJJ q hp).X 3 ⟶ XTensorObj q) := ⟨⟨0⟩, fun _ => Subsingleton.elim _ _⟩
  exact (jjFiberHomEquiv q hq hp 3).trans
    (LinearEquiv.prodUnique.trans (reverseJJHomEquiv q hq))

end Tachikawa.Construction



namespace Tachikawa.Construction
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q : k)

theorem jjFiber_stable_zero (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0)
    (j : ℤ) (h0 : j ≠ 0) (h3 : j ≠ 3) :
    Subsingleton (StableHom (k := k) (R := E q)
      (M := CokerAt (jjFiber q hq hp) j) (N := XTensorObj q)) :=
  stableCoker_subsingleton _ _ j (jjFiber_hom_zero q hq hp j h0 h3)

def jjFiberStableZeroEquiv (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) :
    StableHom (k := k) (R := E q)
      (M := CokerAt (jjFiber q hq hp) 0) (N := XTensorObj q) ≃ₗ[k] k :=
  (stableCokerIsolatedEquiv _ _ (jjFiber_totallyAcyclic q hq hp)
    (jjFiber_finite q hq hp) (jjFiber_projective q hq hp) 0
    (jjFiber_hom_zero q hq hp _ (by norm_num) (by norm_num))
    (jjFiber_hom_zero q hq hp _ (by norm_num) (by norm_num))).symm.trans
    (jjFiberHomZeroEquiv q hq hp)

def jjFiberStableThreeEquiv (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) :
    StableHom (k := k) (R := E q)
      (M := CokerAt (jjFiber q hq hp) 3) (N := XTensorObj q) ≃ₗ[k] k :=
  (stableCokerIsolatedEquiv _ _ (jjFiber_totallyAcyclic q hq hp)
    (jjFiber_finite q hq hp) (jjFiber_projective q hq hp) 3
    (jjFiber_hom_zero q hq hp _ (by norm_num) (by norm_num))
    (jjFiber_hom_zero q hq hp _ (by norm_num) (by norm_num))).symm.trans
    (jjFiberHomThreeEquiv q hq hp)

theorem jjFiber_stable_profile (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0)
    (j : ℤ) :
    ((j = 0 ∨ j = 3) → Nonempty (StableHom (k := k) (R := E q)
      (M := CokerAt (jjFiber q hq hp) j) (N := XTensorObj q) ≃ₗ[k] k)) ∧
    (j ≠ 0 → j ≠ 3 → Subsingleton (StableHom (k := k) (R := E q)
      (M := CokerAt (jjFiber q hq hp) j) (N := XTensorObj q))) := by
  constructor
  · rintro (rfl | rfl)
    · exact ⟨jjFiberStableZeroEquiv q hq hp⟩
    · exact ⟨jjFiberStableThreeEquiv q hq hp⟩
  · exact jjFiber_stable_zero q hq hp j

end Tachikawa.Construction



namespace Tachikawa.Construction
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q : k)
variable (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0)

def yxShiftFiberStableEquiv (a : ℤ) : StableEquiv (k := k)
    (MissingYProfile.shift q (MissingYProfile.finiteYX q) a).obj
    (ModuleCat.of (E q) (CokerAt (jjFiber q hq hp) (1-a))) := by
  cases a with
  | ofNat n =>
    exact negativeCokerStableEquiv (formE q) _
      (jjFiber_totallyAcyclic q hq hp).1 (jjFiber_finite q hq hp) (jjFiber_projective q hq hp)
      _ 1 (yxFiberStableEquiv q hq hp) n
  | negSucc n =>
    change StableEquiv (k := k) ((MissingYProfile.finiteYX q).positive (n+1)).obj _
    rw [show 1-Int.negSucc n = 1+((n+1:ℕ):ℤ) by omega]
    exact positiveCokerStableEquiv (formE q) _
      (jjFiber_totallyAcyclic q hq hp).1 (jjFiber_finite q hq hp) (jjFiber_projective q hq hp)
      _ 1 (yxFiberStableEquiv q hq hp) (n+1)

def WFiberDualEquiv (a : ℤ) : MissingYProfile.W q a ≃ₗ[k]
    Module.Dual k (StableHom (k := k) (R := E q)
      (M := CokerAt (jjFiber q hq hp) (-a)) (N := XTensorObj q)) := by
  let e₁ := (yxShiftFiberStableEquiv q hq hp a).post (xObj q)
  have e₂ := completeCokerDuality (formE q) (jjFiber q hq hp)
    (jjFiber_totallyAcyclic q hq hp).1 (jjFiber_finite q hq hp) (jjFiber_projective q hq hp)
    (-a) (xObj q)
  rw [show -a+1 = 1-a by omega] at e₂
  let e₃ := (StableEquiv.ofLinearEquiv (k := k) (M := XTensorObj q) (N := xObj q)
    (XTensorEquiv q)).post (ModuleCat.of (E q) (CokerAt (jjFiber q hq hp) (-a)))
  exact e₁.trans (e₂.trans e₃.dualMap)

include hq hp in
theorem y_profile : MissingYProfile.profile q := by
  intro a
  constructor
  · intro ha
    obtain ⟨e⟩ := (jjFiber_stable_profile q hq hp (-a)).1 (by omega)
    exact ⟨(WFiberDualEquiv q hq hp a).trans
      (e.symm.dualMap.trans (LinearMap.ringLmapEquivSelf k k k))⟩
  · intro h3 h0
    let := jjFiber_stable_zero q hq hp (-a) (by omega) (by omega)
    let : Subsingleton (Module.Dual k (StableHom (k := k) (R := E q)
        (M := CokerAt (jjFiber q hq hp) (-a)) (N := XTensorObj q))) := by
      constructor
      intro f g
      ext x
      have hx : x = 0 := Subsingleton.elim _ _
      rw [hx,map_zero,map_zero]
    exact (WFiberDualEquiv q hq hp a).injective.subsingleton

end Tachikawa.Construction



namespace Tachikawa
open CategoryTheory CategoryTheory.Abelian
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable (C : ChainComplex (ModuleCat R) ℤ) (hC : TotallyAcyclic C)
  (fin : ∀ j, Module.Finite R (C.X j)) (proj : ∀ j, Module.Projective R (C.X j))
  (N : ModuleCat R)

namespace CompleteStableExt

def cycles (n : ℕ) :
    (CokerAt C (n : ℤ) →ₗ[R] N) →ₗ[k]
      VectorSplit.Z (resolutionHom k R (Q C hC proj).complex N) n where
  toFun f := ⟨ModuleCat.ofHom (f.comp (CokerAt.π C (n : ℤ))), by
    erw [resolutionHom_memZ,completeResolutionTail_d]
    apply ModuleCat.hom_ext
    change (f.comp (CokerAt.π C (n : ℤ))).comp
      (C.d ((n+1 : ℕ) : ℤ) (n : ℤ)).hom = 0
    rw [LinearMap.comp_assoc, Nat.cast_add, Nat.cast_one, CokerAt.π_d,
      LinearMap.comp_zero]⟩
  map_add' f g := by rfl
  map_smul' c f := by rfl

def toExt (n : ℕ) : (CokerAt C (n : ℤ) →ₗ[R] N) →ₗ[k]
    Ext (ModuleCat.of R (CokerAt C 0)) N n :=
  (resolutionCyclesToExt N (Q C hC proj) n).comp (cycles C hC proj N n)

lemma toExt_surjective (n : ℕ) : Function.Surjective (toExt C hC proj N n (k := k)) := by
  intro x
  obtain ⟨f,hf,rfl⟩ := (Q C hC proj).extMk_surjective x (n+1) rfl
  rw [completeResolutionTail_d] at hf
  have hf' : f.hom.comp (C.d ((n : ℤ)+1) (n : ℤ)).hom = 0 := by
    have h := congrArg ModuleCat.Hom.hom hf
    change f.hom.comp (C.d ((n+1 : ℕ) : ℤ) (n : ℤ)).hom = 0 at h
    rw [show ((n+1 : ℕ) : ℤ) = (n : ℤ)+1 by omega] at h
    exact h
  use CokerAt.descend C (n : ℤ) f.hom hf'
  rfl

include fin in
lemma toExt_kernel (n : ℕ) :
    LinearMap.ker (toExt C hC proj N (n+1) (k := k)) =
      projectiveFactors (k := k) (M := CokerAt C ((n+1 : ℕ) : ℤ)) (N := N) := by
  ext f
  have hz : (f.comp (CokerAt.π C ((n+1 : ℕ) : ℤ))).comp
      (C.d (((n+1 : ℕ) : ℤ)+1) ((n+1 : ℕ) : ℤ)).hom = 0 := by
    rw [LinearMap.comp_assoc,CokerAt.π_d,LinearMap.comp_zero]
  have hdesc : CokerAt.descend C ((n+1 : ℕ) : ℤ)
      (f.comp (CokerAt.π C ((n+1 : ℕ) : ℤ))) hz = f := by
    apply LinearMap.ext
    intro x
    obtain ⟨y,rfl⟩ := CokerAt.π_surjective C ((n+1 : ℕ) : ℤ) x
    rfl
  have hf : (Q C hC proj).complex.d (n+2) (n+1) ≫
      ModuleCat.ofHom (f.comp (CokerAt.π C ((n+1 : ℕ) : ℤ))) = 0 := by
    rw [completeResolutionTail_d]
    apply ModuleCat.hom_ext
    change (f.comp (CokerAt.π C ((n+1 : ℕ) : ℤ))).comp
      (C.d (((n+1)+1 : ℕ) : ℤ) ((n+1 : ℕ) : ℤ)).hom = 0
    rw [show (((n+1)+1 : ℕ) : ℤ) = ((n+1 : ℕ) : ℤ)+1 by omega]
    exact hz
  change (Q C hC proj).extMk (ModuleCat.ofHom (f.comp (CokerAt.π C ((n+1 : ℕ) : ℤ))))
    (n+2) rfl hf = 0 ↔ _
  have hab := hC.factors_iff_boundary (k := k) fin proj ((n+1 : ℕ) : ℤ)
    (f.comp (CokerAt.π C ((n+1 : ℕ) : ℤ))) hz
  rw [hdesc, show ((n+1 : ℕ) : ℤ)-1 = (n : ℤ) by omega] at hab
  erw [(Q C hC proj).extMk_eq_zero_iff _ _ _ _ n rfl, hab]
  constructor
  · rintro ⟨g,hg⟩
    rw [completeResolutionTail_d] at hg
    exact ⟨g.hom,ModuleCat.hom_ext_iff.mp hg⟩
  · rintro ⟨g,hg⟩
    refine ⟨ModuleCat.ofHom g,?_⟩
    rw [completeResolutionTail_d]
    exact ModuleCat.hom_ext hg

def equiv (n : ℕ) :
    StableHom (k := k) (R := R) (M := CokerAt C ((n+1 : ℕ) : ℤ)) (N := N) ≃ₗ[k]
      Ext (ModuleCat.of R (CokerAt C 0)) N (n+1) := by
  change ((CokerAt C ((n+1 : ℕ) : ℤ) →ₗ[R] N) ⧸ projectiveFactors (k := k)) ≃ₗ[k] _
  rw [← toExt_kernel C hC fin proj N n]
  exact (toExt C hC proj N (n+1)).quotKerEquivOfSurjective
    (toExt_surjective C hC proj N (n+1))

end CompleteStableExt
end Tachikawa



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Delta
attribute [-instance] _root_.OAI.Tachikawa.DownHom.instAddCommGroupCochain _root_.OAI.Tachikawa.DownHom.instModuleCochain _root_.OAI.Tachikawa.Triangular.instAddCommGroupOff _root_.OAI.Tachikawa.Triangular.instAddCommGroupTriple _root_.OAI.Tachikawa.Triangular.instAdditiveModuleCatAlgD₀ _root_.OAI.Tachikawa.Triangular.instAdditiveModuleCatAlgD₁ _root_.OAI.Tachikawa.Triangular.instFiniteDimensionalAlgOfCarrierAlg _root_.OAI.Tachikawa.Triangular.instIsScalarTowerMulOppositeProdOff _root_.OAI.Tachikawa.Triangular.instIsScalarTowerProdOff _root_.OAI.Tachikawa.Triangular.instModuleAlgTriple _root_.OAI.Tachikawa.Triangular.instModuleMulOppositeProdOff _root_.OAI.Tachikawa.Triangular.instModuleOff _root_.OAI.Tachikawa.Triangular.instModuleProdOff _root_.OAI.Tachikawa.Triangular.instSMulCommClassProdMulOppositeOff
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

def WZeroEquiv : MissingYProfile.W q 0 ≃ₗ[k] k :=
  Classical.choice ((y_profile q hq hp 0).1 (Or.inr rfl))

def wZero : MissingYProfile.W q 0 := (WZeroEquiv q hq hp).symm 1

variable (H : k) (hH : H ≠ 0)

def evaluatedStableMap : ((finiteU q H hH).obj ⟶ (Y q).obj) →ₗ[k]
    MissingYProfile.W q 0 where
  toFun g := stableClass (k := k) (((uXIso q H hH).inv ≫
    Enveloping.evalMap (xObj q) g).hom)
  map_add' g h := by
    change stableClass (k := k) _ = _
    rw [show Enveloping.evalMap (xObj q) (g+h) =
      Enveloping.evalMap (xObj q) g + Enveloping.evalMap (xObj q) h from
      (Enveloping.evaluation (xObj q)).map_add,Preadditive.comp_add]
    exact map_add _ _ _
  map_smul' c g := by
    rw [Enveloping.evalMap_smul,Linear.comp_smul]
    exact map_smul _ _ _

end Tachikawa.Construction



end

end OAI
end


