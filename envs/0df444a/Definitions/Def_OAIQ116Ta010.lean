-- Prove2me | Definitions.Def_OAIQ116Ta010
-- name    : OAIQ116Ta010
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T01:56:14.816169+00:00
-- url     : https://prove2.me/theorems/3bc4c4d0-f442-4069-b97b-7271d00f9ef5
-- title:
--   Definitions bundle OAIQ116Ta010 of the split of OpenAI, A counterexample to Tachikawa's second conjecture
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Tachikawa.main_theorem`, carved from OpenAI's openai/math development (OpenAI, *A counterexample to Tachikawa's second conjecture*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 105 declarations of OpenAI's Lean: 44 definitions and 61 theorems. The definitions and types are `OAI.Tachikawa.C.homCfSimpleEquiv`, `OAI.Tachikawa.C.homologyClass`, `OAI.Tachikawa.C.homologyShortComplex`, `OAI.Tachikawa.C.inducedAug`, `OAI.Tachikawa.C.inducedBoundaryResolution`, `OAI.Tachikawa.C.inducedFHomEquiv`, `OAI.Tachikawa.C.inducedJComparison`, `OAI.Tachikawa.C.inducedJTensorComparison`, `OAI.Tachikawa.C.inducedRangeObj`, `OAI.Tachikawa.C.inducedTwoAug`, `OAI.Tachikawa.C.initialClass`, `OAI.Tachikawa.C.initialShiftEquiv`, `OAI.Tachikawa.C.initialShortComplex`, `OAI.Tachikawa.C.leftDualProjectiveResolution`, `OAI.Tachikawa.C.leftDualResD`, `OAI.Tachikawa.C.middleClass`, `OAI.Tachikawa.C.middleShiftEquiv`, `OAI.Tachikawa.C.middleShortComplex`, `OAI.Tachikawa.C.rangeTwistComparison`, `OAI.Tachikawa.C.rightDualProjectiveResolution`, `OAI.Tachikawa.C.rightDualResD`, `OAI.Tachikawa.C.simpleEndEquiv`, `OAI.Tachikawa.C.simpleExtMultiple`, `OAI.Tachikawa.C.simpleExtPeriod`, `OAI.Tachikawa.C.simpleExtZeroEquiv`, `OAI.Tachikawa.C.simpleTwistComparison`, `OAI.Tachikawa.C.simpleTwistExt`, `OAI.Tachikawa.C.simpleTwistIso`, `OAI.Tachikawa.C.tau`, `OAI.Tachikawa.C.tauPower`, `OAI.Tachikawa.C.threeShiftEquiv`, `OAI.Tachikawa.C.upperClass`, `OAI.Tachikawa.C.upperInclusion`, `OAI.Tachikawa.C.upperRangeMap`, `OAI.Tachikawa.C.upperShiftEquiv`, `OAI.Tachikawa.C.upperShortComplex`, `OAI.Tachikawa.Construction.bRegularLeftObj`, `OAI.Tachikawa.Construction.jjFiberHighEquiv`, `OAI.Tachikawa.Nakayama.evaluationEquiv`, `OAI.Tachikawa.TrivialInduction.tensorComparisonEquiv` and 4 more.
--
--   **Sources.** They come from these modules of lean/OAI/RingTheory, in whole or in part: [`Tachikawa_Coinduction`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RingTheory/Tachikawa/Coinduction.lean), [`Tachikawa_Coresolution`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RingTheory/Tachikawa/Coresolution.lean), [`Tachikawa_DerivedInduction`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RingTheory/Tachikawa/DerivedInduction.lean), [`Tachikawa_FiniteCoinduction`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RingTheory/Tachikawa/FiniteCoinduction.lean), [`Tachikawa_HomProfile`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RingTheory/Tachikawa/HomProfile.lean), [`Tachikawa_Nakayama`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RingTheory/Tachikawa/Nakayama.lean), [`Tachikawa_Perfect`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RingTheory/Tachikawa/Perfect.lean), [`Tachikawa_Period`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RingTheory/Tachikawa/Period.lean), [`Tachikawa_ReverseResolution`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RingTheory/Tachikawa/ReverseResolution.lean).
--
--   **Imports.** It imports the published bundle `Def_Tachikawa`; the bundles `OAIQ116Ta017` and `OAIQ116Ta007` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ116Ta014` and `OAIQ116Ta015`; the statement `OAI.Tachikawa.Construction.XInverseTwist_weight`.
-- source:
--   OpenAI, A counterexample to Tachikawa's second conjecture, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-counterexample-to-Tachikawas-second-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/RingTheory at commit adc7f12

import Mathlib
import Definitions.Def_Tachikawa
import Definitions.Def_OAIQ116Ta017
import Definitions.Def_OAIQ116Ta007

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Coresolution
attribute [-instance] _root_.OAI.Tachikawa.Enveloping.instAddCommGroupCarrierMulOppositeRightObj _root_.OAI.Tachikawa.Enveloping.instModuleCarrierMulOppositeRightObj_1 _root_.OAI.Tachikawa.LeftCoinduced.coextend_additive _root_.OAI.Tachikawa.LeftCoinduced.coextend_preservesInjective _root_.OAI.Tachikawa.OuterTensor.restrictionPreservesHomology _root_.OAI.Tachikawa.TotalDualPairing.instTensorSignsNatUp_solutions _root_.OAI.Tachikawa.TotalMap.sourceHasCoproduct _root_.OAI.Tachikawa.downIntTensorSigns
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

@[simp] lemma resolutionHom_d (i j : ℕ) (f : P.X i ⟶ N) :
    (resolutionHom k R P N).d i j f = P.d j i ≫ f := rfl

end Tachikawa



namespace Tachikawa
open CategoryTheory CategoryTheory.Abelian CochainComplex.HomComplex
open scoped ModuleCat.Algebra
variable (k R : Type) [Field k] [Ring R] [Algebra k R]
  (P : CochainComplex (ModuleCat R) ℕ) (N : ModuleCat R)

@[simp] lemma coresolutionHom_X (n : ℕ) :
    (coresolutionHom k R P N).X n = ModuleCat.of k (N ⟶ P.X n) := rfl
@[simp] lemma coresolutionHom_d (i j : ℕ) (f : N ⟶ P.X i) :
    (coresolutionHom k R P N).d i j f = f ≫ P.d i j := rfl
end Tachikawa



namespace Tachikawa
open CategoryTheory CategoryTheory.Abelian
universe u v w
variable {k : Type*} [Field k] {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  [Linear k C]
variable {X X' Y Y' : C}

def extIso (e : X ≅ X') (f : Y ≅ Y') (n : ℕ) : Ext X Y n ≃ₗ[k] Ext X' Y' n where
  toFun x := (Ext.mk₀ e.inv).comp (x.comp (Ext.mk₀ f.hom) (add_zero n)) (zero_add n)
  invFun x := (Ext.mk₀ e.hom).comp (x.comp (Ext.mk₀ f.inv) (add_zero n)) (zero_add n)
  left_inv x := by simp
  right_inv x := by simp
  map_add' x y := by simp only [Ext.add_comp,Ext.comp_add]
  map_smul' c x := by simp only [Ext.smul_comp,Ext.comp_smul,RingHom.id_apply]

end Tachikawa



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Nakayama
attribute [-instance] _root_.OAI.Tachikawa.Construction.instModuleEX _root_.OAI.Tachikawa.LeftCoinduced.coextend_additive _root_.OAI.Tachikawa.LeftCoinduced.coextend_preservesInjective _root_.OAI.Tachikawa.TrivialInduction.instAdditiveModuleCatTrivialExtensionFunctor _root_.OAI.Tachikawa.downIntTensorSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace Tachikawa
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable {M N : Type} [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

namespace Nakayama

variable [Module k M] [IsScalarTower k R M]

variable [Module k N] [IsScalarTower k R N]

variable [FiniteDimensional k R]
local notation "V" => BalancedTensor.T (k := k) (R := R) (S := R) (M := DualBimodule k R) (N := M)

variable [FiniteDimensional k M]

def evaluationEquiv : V ≃ₗ[R] Nakayama k R M :=
  LinearEquiv.ofBijective evaluation ⟨evaluation_injective, evaluation_surjective⟩

end Nakayama
end Tachikawa



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Period
attribute [-instance] _root_.OAI.Tachikawa.AlgebraInduction.resFinite _root_.OAI.Tachikawa.Construction.instFiniteCSubtypeMemSubmoduleCe _root_.OAI.Tachikawa.Construction.instFiniteCSubtypeMemSubmoduleCf _root_.OAI.Tachikawa.Construction.instModuleEX _root_.OAI.Tachikawa.Enveloping.instAddCommGroupCarrierMulOppositeRightObj _root_.OAI.Tachikawa.Enveloping.instIsScalarTowerCarrierMulOppositeRightObj _root_.OAI.Tachikawa.Enveloping.instModuleCarrierMulOppositeRightObj_1 _root_.OAI.Tachikawa.LeftCoinduced.coextend_additive _root_.OAI.Tachikawa.LeftCoinduced.coextend_preservesInjective _root_.OAI.Tachikawa.downIntTensorSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace Tachikawa
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]

namespace C
variable [CharP k 2] (q : k)

lemma inducedComplex_d (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) (n : ℕ) :
    (inducedComplex q hp).d (n+1) n = inducedD q n := ChainComplex.of_d _ _ _

omit [CharP k 2] in
lemma inducedObj_projective (n : ℕ) : Module.Projective (T q) (inducedObj q n) := by
  cases n <;> dsimp [inducedObj, resObj]
  · let : Module.Finite k (Cf q) := Module.Finite.of_injective
      ((Cf q).subtype.restrictScalars k) Subtype.val_injective
    let : Module.Finite (C k q) (Cf q) := Module.Finite.of_restrictScalars_finite k _ _
    exact TrivialInduction.inducedProjective (k := k) (R := C k q) (M := Cf q)
  · let : Module.Finite k (Ce q) := Module.Finite.of_injective
      ((Ce q).subtype.restrictScalars k) Subtype.val_injective
    let : Module.Finite (C k q) (Ce q) := Module.Finite.of_restrictScalars_finite k _ _
    exact TrivialInduction.inducedProjective (k := k) (R := C k q) (M := Ce q)

omit [CharP k 2] in
lemma inducedObj_finite (n : ℕ) : Module.Finite k (inducedObj q n) := by
  have hf : Module.Finite (T q) (inducedObj q n) := by
    cases n with
    | zero =>
      let : Module.Finite k (Cf q) := Module.Finite.of_injective
        ((Cf q).subtype.restrictScalars k) Subtype.val_injective
      let : Module.Finite k (TrivialInduction.Obj k (C k q) (Cf q)) :=
        TrivialInduction.inducedFinite (k := k) (R := C k q) (M := Cf q)
      exact Module.Finite.of_restrictScalars_finite k (T q)
        (TrivialInduction.Obj k (C k q) (Cf q))
    | succ n =>
      let : Module.Finite k (Ce q) := Module.Finite.of_injective
        ((Ce q).subtype.restrictScalars k) Subtype.val_injective
      let : Module.Finite k (TrivialInduction.Obj k (C k q) (Ce q)) :=
        TrivialInduction.inducedFinite (k := k) (R := C k q) (M := Ce q)
      exact Module.Finite.of_restrictScalars_finite k (T q)
        (TrivialInduction.Obj k (C k q) (Ce q))
  exact Module.Finite.trans (T q) (inducedObj q n)

lemma inducedD_exact (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0)
    (n : ℕ) (hn : n ≠ 1) : Function.Exact (inducedD q (n+1)) (inducedD q n) :=
  TrivialInduction.map_exact _ _ (resD_exact q hp n) (nu_resD_exact q hq hp n hn)

def inducedAug : inducedObj q 0 ⟶ ModuleCat.of (T q) (TSimple q) :=
  ModuleCat.ofHom (TrivialInflation.lift (augmentation q))

omit [CharP k 2] in
lemma inducedAug_surjective : Function.Surjective (inducedAug q) := by
  intro x
  obtain ⟨y,hy⟩ := augmentation_surjective q x
  exact ⟨(y,0),hy⟩

omit [CharP k 2] in
lemma inducedAug_exact (hq1 : 1+q ≠ 0) : Function.Exact (inducedD q 0) (inducedAug q) := by
  intro x
  constructor
  · intro hx
    obtain ⟨a,ha⟩ := (exact_augmentation q hq1 x.1).mp hx
    obtain ⟨ψ,hψ⟩ := nu_rhoU_surjective q x.2
    exact ⟨(a,ψ),Prod.ext ha hψ⟩
  · rintro ⟨y,rfl⟩
    exact (exact_augmentation q hq1).apply_apply_eq_zero y.1

end C
end Tachikawa



namespace Tachikawa.TrivialInduction
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
  (H : k) (hH : H ≠ 0) (M : ModuleCat R)

lemma twistComparison_natural {N : ModuleCat R} (f : M ⟶ N) :
    (inverseTwist (R := R) H hH).map ((functor (k := k)).map f) ≫ twistComparison H hH N =
      twistComparison H hH M ≫ (functor (k := k)).map f := by
  apply ModuleCat.hom_ext
  ext x
  apply Prod.ext
  · rfl
  · change H • Nakayama.map f.hom x.2 = Nakayama.map f.hom (H • x.2)
    exact (Nakayama.map f.hom).map_smul_of_tower H x.2 |>.symm

end Tachikawa.TrivialInduction



namespace Tachikawa.C
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q : k)

def inducedBoundaryResolution (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) :
    ProjectiveResolution (inducedBoundaryObj q) :=
  resolutionOfExact _ (fun n => inducedObj q (n+3)) (fun n => inducedD q (n+3))
    (ModuleCat.ofHom (inducedD q 2).hom.rangeRestrict)
    (fun n => inducedD_exact q hq hp (n+3) (by omega))
    (fun x => by
      constructor
      · intro hx
        exact (inducedD_exact q hq hp 2 (by omega) x).mp (congrArg Subtype.val hx)
      · rintro ⟨y,rfl⟩
        exact Subtype.ext ((inducedD_exact q hq hp 2 (by omega)).apply_apply_eq_zero y))
    (by rintro ⟨x,y,hy⟩; exact ⟨y,Subtype.ext hy⟩)
    (fun n => by
      let := inducedObj_projective q (n+3)
      infer_instance)

lemma inducedBoundary_ext_zero (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) (n : ℕ) :
    Subsingleton (Abelian.Ext (inducedBoundaryObj q) (ModuleCat.of (T q) (TSimple q)) n) := by
  cases n with
  | zero =>
    have : Subsingleton (inducedBoundaryObj q ⟶ ModuleCat.of (T q) (TSimple q)) := by
      apply subsingleton_of_forall_eq 0
      intro f
      have hh : ModuleCat.ofHom (inducedD q 2).hom.rangeRestrict ≫ f = 0 :=
        induced_positive_hom_zero q 2 _
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      rintro ⟨x,y,hy⟩
      subst x
      exact congrArg (fun g : inducedObj q 3 ⟶ ModuleCat.of (T q) (TSimple q) => g y) hh
    exact Abelian.Ext.addEquiv₀.injective.subsingleton
  | succ n =>
    let P := inducedBoundaryResolution q hq hp
    apply ext_subsingleton_of_boundaries P n
    intro f _hf
    refine ⟨0, ?_⟩
    rw [Limits.comp_zero]
    exact (induced_positive_hom_zero q (n+3) f).symm

end Tachikawa.C



namespace Tachikawa.C
variable {k : Type} [Field k] [CharP k 2] (q : k)

lemma hom_comp_rhoEll_one_six (f : Ce q →ₗ[C k q] C k q) :
    ((f.comp (rhoEll q 1)) (LeftCorner.generator (e_idempotent q))) 6 = 0 := by
  have he := RightCorner.homEquiv_precomp (e_idempotent q) (e_idempotent q) (ell q 1)
    (e_mul_ell q 1) (ell_mul_e q 1) f
  exact (congrArg (fun a : eC q => a.val 6) he).trans (lambdaEll_one_six q _)

lemma nuTwoCycle_closed : Nakayama.map (k := k) (rhoEll q 1) (nuTwoCycle q) = 0 :=
  LinearMap.ext (fun f => hom_comp_rhoEll_one_six q f)

omit [CharP k 2] in
lemma nuTwoAug_boundary (z : k) (ψ : Nakayama k (C k q) (Ce q)) :
    nuTwoAug q (Nakayama.map (rhoEll q z) ψ) = 0 :=
  dual_vHom_rhoEll q z ψ

lemma nuTwo_boundary_iff (hq : q ≠ 0) (hq1 : 1+q ≠ 0)
    (ψ : Nakayama k (C k q) (Ce q))
    (hψ : Nakayama.map (rhoEll q 1) ψ = 0) :
    nuTwoAug q ψ = 0 ↔ ∃ ξ, Nakayama.map (rhoEll q q) ξ = ψ :=
  dual_vHom_boundary_iff q hq hq1 ψ (fun g => LinearMap.congr_fun hψ g)

lemma nuTwoAug_smul (hq : q ≠ 0) (hq1 : 1+q ≠ 0)
    (ψ : Nakayama k (C k q) (Ce q)) (hψ : Nakayama.map (rhoEll q 1) ψ = 0)
    (a : C k q) : nuTwoAug q (a • ψ) = a • nuTwoAug q ψ := by
  change (a • ψ) (vHom q) = (a 1) * ψ (vHom q)
  rw [Nakayama.action_apply]
  exact dual_vHom_action q hq hq1 ψ (fun g => LinearMap.congr_fun hψ g) a

end Tachikawa.C



namespace Tachikawa.C
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q : k)

lemma vHom_twoCycles (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) (x : InducedTwoCycles q) :
    vHom q x.val.1 = 0 := by
  obtain ⟨y,hy⟩ := (exact_rhoEll_one q hp _).mp (twoCycles_first q x)
  rw [← hy]
  exact LinearMap.congr_fun (vHom_rhoEll q q) y

def inducedTwoAug (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) :
    InducedTwoCycles q →ₗ[T q] TSimple q where
  toFun x := nuTwoAug q x.val.2
  map_add' _ _ := rfl
  map_smul' a x := by
    change nuTwoAug q (Nakayama.evaluationBilinear a.snd x.val.1 + a.fst • x.val.2) =
      a.fst • nuTwoAug q x.val.2
    rw [map_add, nuTwoAug_smul q hq (by simpa only [pow_one] using hp 1 (by omega))
      x.val.2 (twoCycles_second q x)]
    have hz : nuTwoAug q (Nakayama.evaluationBilinear a.snd x.val.1) = 0 := by
      change a.snd (vHom q x.val.1) = 0
      rw [vHom_twoCycles q hp, map_zero]
    rw [hz, zero_add]

lemma inducedTwoAug_surjective (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) :
    Function.Surjective (inducedTwoAug q hq hp) := by
  intro x
  let r : k := x
  have hz : (0, r • nuTwoCycle q) ∈ InducedTwoCycles q := by
    change (rhoEll q 1 0, Nakayama.map (rhoEll q 1) (r • nuTwoCycle q)) = (0,0)
    rw [map_zero, (Nakayama.map (rhoEll q 1)).map_smul_of_tower, nuTwoCycle_closed, smul_zero]
  refine ⟨⟨(0,r • nuTwoCycle q),hz⟩, ?_⟩
  change nuTwoAug q (r • nuTwoCycle q) = x
  rw [map_smul, nuTwoCycle_aug]
  exact mul_one r

omit [CharP k 2] in
lemma inducedD_two_apply (x : TrivialInduction.Obj k (C k q) (Ce q)) :
    inducedD q 2 x = (rhoEll q q x.1, Nakayama.map (rhoEll q q) x.2) := by
  change (rhoEll q (q^1) x.1, Nakayama.map (rhoEll q (q^1)) x.2) = _
  rw [pow_one]

lemma inducedTwoAug_exact (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) :
    Function.Exact (inducedTwoBoundary q hp) (inducedTwoAug q hq hp) := by
  intro x
  constructor
  · intro hx
    obtain ⟨a,ha⟩ := (exact_rhoEll_one q hp _).mp (twoCycles_first q x)
    obtain ⟨ξ,hξ⟩ := (nuTwo_boundary_iff q hq
      (by simpa only [pow_one] using hp 1 (by omega)) x.val.2 (twoCycles_second q x)).mp hx
    refine ⟨(show TrivialInduction.Obj k (C k q) (Ce q) from (a,ξ)),Subtype.ext ?_⟩
    change inducedD q 2 (show TrivialInduction.Obj k (C k q) (Ce q) from (a,ξ)) = x.val
    rw [inducedD_two_apply]
    exact Prod.ext ha hξ
  · rintro ⟨y,rfl⟩
    exact (congrArg (fun z : TrivialInduction.Obj k (C k q) (Ce q) => nuTwoAug q z.2)
      (inducedD_two_apply q y)).trans (nuTwoAug_boundary q q y.2)

end Tachikawa.C



namespace Tachikawa.C
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q : k)

abbrev inducedRangeObj (n : ℕ) := ModuleCat.of (T q) (InducedRange q n)

abbrev initialShortComplex (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) : ShortComplex (ModuleCat (T q)) :=
  linearShortComplex (InducedRange q 0).subtype (inducedAug q).hom (fun x => by
    constructor
    · intro hx
      obtain ⟨y,hy⟩ := (inducedAug_exact q (by simpa only [pow_one] using hp 1 (by omega)) x).mp hx
      exact ⟨⟨x,y,hy⟩, rfl⟩
    · rintro ⟨⟨x,y,hy⟩,rfl⟩
      change inducedAug q x = 0
      exact (congrArg (inducedAug q) hy).symm.trans
        ((inducedAug_exact q (by simpa only [pow_one] using hp 1 (by omega))).apply_apply_eq_zero y))

omit [CharP k 2] in
lemma initial_shortExact (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) :
    (initialShortComplex q hp).ShortExact :=
  linearShortExact _ _ _ Subtype.val_injective (inducedAug_surjective q)

abbrev middleShortComplex (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) :
    ShortComplex (ModuleCat (T q)) :=
  linearShortComplex (InducedRange q 1).subtype (inducedD q 0).hom.rangeRestrict (fun x => by
    constructor
    · intro hx
      obtain ⟨y,hy⟩ := (inducedD_exact q hq hp 0 (by omega) x).mp (congrArg Subtype.val hx)
      exact ⟨⟨x,y,hy⟩,rfl⟩
    · rintro ⟨⟨x,y,hy⟩,rfl⟩
      apply Subtype.ext
      change inducedD q 0 x = 0
      exact (congrArg (inducedD q 0) hy).symm.trans
        ((inducedD_exact q hq hp 0 (by omega)).apply_apply_eq_zero y))

lemma middle_shortExact (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) :
    (middleShortComplex q hq hp).ShortExact :=
  linearShortExact _ _ _ Subtype.val_injective (by
    rintro ⟨x,y,hy⟩
    exact ⟨y,Subtype.ext hy⟩)

def upperInclusion : InducedTwoCycles q →ₗ[T q] inducedObj q 2 where
  toFun := Subtype.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def upperRangeMap : inducedObj q 2 →ₗ[T q] InducedRange q 1 :=
  (inducedD q 1).hom.rangeRestrict

omit [CharP k 2] in
lemma upper_exact : Function.Exact (upperInclusion q) (upperRangeMap q) := by
  intro x
  constructor
  · intro hx
    refine ⟨⟨x, ?_⟩, rfl⟩
    have h := congrArg Subtype.val hx
    change TrivialInduction.map (k := k) (rhoEll q 1) x = 0
    change TrivialInduction.map (k := k) (rhoEll q (q^0)) x = 0 at h
    simpa only [pow_zero] using h
  · rintro ⟨y,rfl⟩
    apply Subtype.ext
    change TrivialInduction.map (k := k) (rhoEll q (q^0)) y.val = 0
    have hy : TrivialInduction.map (k := k) (rhoEll q 1) y.val = 0 := y.property
    simpa only [pow_zero] using hy

abbrev upperShortComplex : ShortComplex (ModuleCat (T q)) :=
  linearShortComplex (upperInclusion q) (upperRangeMap q) (upper_exact q)

omit [CharP k 2] in
lemma upper_shortExact : (upperShortComplex q).ShortExact :=
  linearShortExact _ _ _ Subtype.val_injective (by
    rintro ⟨x,y,hy⟩
    exact ⟨y,Subtype.ext hy⟩)

abbrev homologyShortComplex (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) :
    ShortComplex (ModuleCat (T q)) :=
  linearShortComplex (boundaryInclusion q hp) (inducedTwoAug q hq hp) (fun x => by
    constructor
    · intro hx
      obtain ⟨y,hy⟩ := (inducedTwoAug_exact q hq hp x).mp hx
      refine ⟨⟨x.val, y, congrArg Subtype.val hy⟩, ?_⟩
      exact Subtype.ext rfl
    · rintro ⟨⟨x,y,hy⟩,rfl⟩
      have he : boundaryInclusion q hp ⟨x,y,hy⟩ = inducedTwoBoundary q hp y :=
        Subtype.ext hy.symm
      rw [he]
      exact (inducedTwoAug_exact q hq hp).apply_apply_eq_zero y)

lemma homology_shortExact (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) :
    (homologyShortComplex q hq hp).ShortExact :=
  linearShortExact _ _ _ (by
    intro x y h
    apply Subtype.ext
    exact congrArg (fun z : InducedTwoCycles q => z.val) h)
    (inducedTwoAug_surjective q hq hp)

omit [CharP k 2] in

lemma induced_positive_ext_zero (i n : ℕ) :
    Subsingleton (Abelian.Ext (inducedObj q (i+1)) (ModuleCat.of (T q) (TSimple q)) n) := by
  cases n with
  | zero =>
    have : Subsingleton (inducedObj q (i+1) ⟶ ModuleCat.of (T q) (TSimple q)) :=
      subsingleton_of_forall_eq 0 (induced_positive_hom_zero q i)
    exact Abelian.Ext.addEquiv₀.injective.subsingleton
  | succ n =>
    let := inducedObj_projective q (i+1)
    exact Abelian.Ext.subsingleton_of_projective _ _ n

end Tachikawa.C



namespace Tachikawa.C
open CategoryTheory CategoryTheory.Abelian
open scoped ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q : k)

def upperShiftEquiv (n : ℕ) :
    Ext (ModuleCat.of (T q) (InducedTwoCycles q)) (simpleObj q) n ≃ₗ[k]
      Ext (inducedRangeObj q 1) (simpleObj q) (n+1) := by
  let : Subsingleton (Ext (upperShortComplex q).X₂ (simpleObj q) n) :=
    induced_positive_ext_zero q 1 n
  let : Subsingleton (Ext (upperShortComplex q).X₂ (simpleObj q) (n+1)) :=
    induced_positive_ext_zero q 1 (n+1)
  exact extShiftEquiv k (upper_shortExact q) (simpleObj q) n

def middleShiftEquiv (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) (n : ℕ) :
    Ext (inducedRangeObj q 1) (simpleObj q) n ≃ₗ[k]
      Ext (inducedRangeObj q 0) (simpleObj q) (n+1) := by
  let : Subsingleton (Ext (middleShortComplex q hq hp).X₂ (simpleObj q) n) :=
    induced_positive_ext_zero q 0 n
  let : Subsingleton (Ext (middleShortComplex q hq hp).X₂ (simpleObj q) (n+1)) :=
    induced_positive_ext_zero q 0 (n+1)
  exact extShiftEquiv k (middle_shortExact q hq hp) (simpleObj q) n

def initialShiftEquiv (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) (n : ℕ) :
    Ext (inducedRangeObj q 0) (simpleObj q) (n+1) ≃ₗ[k]
      Ext (simpleObj q) (simpleObj q) (n+2) := by
  let : Module.Projective (T q) (inducedObj q 0) := inducedObj_projective q 0
  let : Subsingleton (Ext (initialShortComplex q hp).X₂ (simpleObj q) (n+1)) :=
    show Subsingleton (Ext (inducedObj q 0) (simpleObj q) (n+1)) from
      Ext.subsingleton_of_projective _ _ n
  let : Subsingleton (Ext (initialShortComplex q hp).X₂ (simpleObj q) (n+2)) :=
    show Subsingleton (Ext (inducedObj q 0) (simpleObj q) (n+2)) from
      Ext.subsingleton_of_projective _ _ (n+1)
  exact extShiftEquiv k (initial_shortExact q hp) (simpleObj q) (n+1)

def threeShiftEquiv (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) (hq : q ≠ 0) (n : ℕ) :
    Ext (ModuleCat.of (T q) (InducedTwoCycles q)) (simpleObj q) n ≃ₗ[k]
      Ext (simpleObj q) (simpleObj q) (n+3) :=
  ((upperShiftEquiv q n).trans (middleShiftEquiv q hq hp (n+1))).trans
    (initialShiftEquiv q hp (n+1))

def simpleExtPeriod (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) (n : ℕ) :
    Ext (simpleObj q) (simpleObj q) n ≃ₗ[k] Ext (simpleObj q) (simpleObj q) (n+3) :=
  (extQuotientEquiv k (homology_shortExact q hq hp) (simpleObj q)
    (inducedBoundary_ext_zero q hq hp) n).trans (threeShiftEquiv q hp hq n)

end Tachikawa.C



namespace Tachikawa.C
open CategoryTheory CategoryTheory.Abelian
open scoped ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q : k)

def initialClass (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) :
    Ext (simpleObj q) (inducedRangeObj q 0) 1 := (initial_shortExact q hp).extClass

def middleClass (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) :
    Ext (inducedRangeObj q 0) (inducedRangeObj q 1) 1 := (middle_shortExact q hq hp).extClass

def upperClass : Ext (inducedRangeObj q 1) (ModuleCat.of (T q) (InducedTwoCycles q)) 1 :=
  (upper_shortExact q).extClass

def homologyClass (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) :
    Ext (ModuleCat.of (T q) (InducedTwoCycles q)) (simpleObj q) 0 :=
  Ext.mk₀ (homologyShortComplex q hq hp).g

def tau (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) :
    Ext (simpleObj q) (simpleObj q) 3 :=
  simpleExtPeriod q hq hp 0 (Ext.mk₀ (𝟙 (simpleObj q)))

omit [CharP k 2] in

def simpleEndEquiv : (simpleObj q ⟶ simpleObj q) ≃ₗ[k] k where
  toFun f := f (show TSimple q from (1 : k))
  invFun r := r • 𝟙 (simpleObj q)
  left_inv f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    have hf := f.hom.map_smul_of_tower (show k from x) (show TSimple q from (1 : k))
    change f (show TSimple q from (show k from x)*1) =
      (show k from x) * (show k from f (show TSimple q from (1 : k))) at hf
    change (show k from f (show TSimple q from (1 : k))) * (show k from x) = (show k from f x)
    have hx : (show TSimple q from (show k from x)*1) = x := mul_one (show k from x)
    rw [hx] at hf
    exact (mul_comm _ _).trans hf.symm
  right_inv r := mul_one r
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [CharP k 2] in
def simpleExtZeroEquiv : Ext (simpleObj q) (simpleObj q) 0 ≃ₗ[k] k :=
  { toAddEquiv := Ext.addEquiv₀.trans (simpleEndEquiv q).toAddEquiv
    map_smul' := by
      intro r x
      obtain ⟨f, rfl⟩ := Ext.homEquiv₀.symm.surjective x
      change simpleEndEquiv q (Ext.homEquiv₀ (r • Ext.mk₀ f)) =
        r • simpleEndEquiv q (Ext.homEquiv₀ (Ext.mk₀ f))
      rw [← Ext.mk₀_smul]
      have h0 (g : simpleObj q ⟶ simpleObj q) : Ext.homEquiv₀ (Ext.mk₀ g) = g :=
        Ext.homEquiv₀.apply_symm_apply g
      rw [h0, h0]
      change (algebraMap k (T q) r) • (f (show TSimple q from (1:k))) =
        r • (f (show TSimple q from (1:k)))
      exact IsScalarTower.algebraMap_smul (T q) r _ }

def simpleExtMultiple (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) :
    (m : ℕ) → Ext (simpleObj q) (simpleObj q) (3*m) ≃ₗ[k] k
  | 0 => simpleExtZeroEquiv q
  | m+1 => by
      have h : 3*(m+1) = 3*m+3 := by omega
      rw [h]
      exact (simpleExtPeriod q hq hp (3*m)).symm.trans (simpleExtMultiple hq hp m)

end Tachikawa.C



namespace Tachikawa.C
open CategoryTheory CategoryTheory.Abelian
open scoped ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q H : k) (hH : H ≠ 0)

omit [CharP k 2] in
def simpleTwistComparison : (tTwist q H hH).obj (simpleObj q) ⟶ simpleObj q :=
  ModuleCat.ofHom (X := (tTwist q H hH).obj (simpleObj q)) (Y := simpleObj q)
    { toFun := id
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }

omit [CharP k 2] in
lemma inducedTwist_d (n : ℕ) :
    (tTwist q H hH).map (inducedD q n) ≫ inducedTwistComparison q H hH n =
      inducedTwistComparison q H hH (n+1) ≫ inducedD q n :=
  TrivialInduction.twistComparison_natural H hH (resObj q (n+1)) (resD q n)

omit [CharP k 2] in
def rangeTwistComparison (n : ℕ) :
    (tTwist q H hH).obj (inducedRangeObj q n) ⟶ inducedRangeObj q n :=
  ModuleCat.ofHom (X := (tTwist q H hH).obj (inducedRangeObj q n))
    (Y := inducedRangeObj q n)
    { toFun := fun x => ⟨inducedTwistComparison q H hH n x.val, by
        obtain ⟨y,hy⟩ := x.property
        refine ⟨inducedTwistComparison q H hH (n+1) y,?_⟩
        rw [← hy]
        exact (congrArg (fun f => f y) (inducedTwist_d q H hH n)).symm⟩
      map_add' := fun x y => Subtype.ext ((inducedTwistComparison q H hH n).hom.map_add x.val y.val)
      map_smul' := fun r x => Subtype.ext ((inducedTwistComparison q H hH n).hom.map_smul r x.val) }

end Tachikawa.C



namespace Tachikawa.C
open CategoryTheory CategoryTheory.Abelian
open scoped ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q : k)
  (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0)

def tauPower (m : ℕ) : Ext (simpleObj q) (simpleObj q) (3*m) :=
  (simpleExtMultiple q hq hp m).symm 1

end Tachikawa.C



namespace Tachikawa
open CategoryTheory CategoryTheory.Abelian
open scoped ModuleCat.Algebra

namespace C
variable {k : Type} [Field k] [CharP k 2] (q H : k) (hH : H ≠ 0)
  (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0)

omit [CharP k 2] in
def simpleTwistIso : (tTwist q H hH).obj (simpleObj q) ≅ simpleObj q where
  hom := simpleTwistComparison q H hH
  inv := ModuleCat.ofHom (X := simpleObj q)
    (Y := (tTwist q H hH).obj (simpleObj q))
    { toFun := id
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  hom_inv_id := rfl
  inv_hom_id := rfl

omit [CharP k 2] in
def simpleTwistExt (n : ℕ) : Ext (simpleObj q) (simpleObj q) n →ₗ[k]
    Ext (simpleObj q) (simpleObj q) n :=
  (extIso (simpleTwistIso q H hH) (simpleTwistIso q H hH) n).toLinearMap.comp
    ((tTwist q H hH).mapExtLinearMap k (simpleObj q) (simpleObj q) n)

end C
end Tachikawa

end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_ReverseResolution
attribute [-instance] _root_.OAI.Tachikawa.Construction.instFiniteCSubtypeMemSubmoduleCe _root_.OAI.Tachikawa.Construction.instFiniteCSubtypeMemSubmoduleCf _root_.OAI.Tachikawa.Enveloping.instAddCommGroupCarrierMulOppositeRightObj _root_.OAI.Tachikawa.Enveloping.instModuleCarrierMulOppositeRightObj_1 _root_.OAI.Tachikawa.LeftCoinduced.coextend_additive _root_.OAI.Tachikawa.LeftCoinduced.coextend_preservesInjective _root_.OAI.Tachikawa.Triangular.instProjectiveCarrierOneFree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace Tachikawa.C
open CategoryTheory
variable {k : Type} [Field k] (q : k)

lemma leftDualAug_surjective (hq : q ≠ 0) : Function.Surjective (leftDualAug q) := by
  intro φ
  refine ⟨(ce q (φ (basis q 4)) (φ (basis q 3)) (φ (basis q 2)/q)
    (φ (basis q 0)) (φ (basis q 6)/q) (φ (basis q 5)),
    ce q (φ (basis q 8)) (φ (basis q 7)) 0 0 (φ (basis q 9)/q) (φ (basis q 1))), ?_⟩
  change (_ : Module.Dual k (C k q)) = φ
  apply (basis q).ext
  intro i
  change leftDualZ q _ (basis q i) + leftDualJ q _ (basis q i) = φ (basis q i)
  simp only [LinearMap.fst_apply, LinearMap.snd_apply, leftDualZ_ce, leftDualJ_ce]
  fin_cases i <;> simp [basis_apply] <;> field_simp

lemma rhoT_injective (hq : q ≠ 0) : Function.Injective (rhoT q) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  rw [← cf_eta q x, rhoT_cf, ce_eq_zero] at hx
  obtain ⟨_, _, hu, hv, ha, hn⟩ := hx
  rw [← cf_eta q x, cf_eq_zero]
  exact ⟨ha, hu, (mul_eq_zero.mp hv).resolve_left hq, (mul_eq_zero.mp hn).resolve_left hq⟩

end Tachikawa.C

namespace Tachikawa.C
open CategoryTheory
variable {k : Type} [Field k] [CharP k 2] (q : k)

def leftDualResD : ∀ n, leftDualResObj q (n+1) ⟶ leftDualResObj q n
  | 0 => ModuleCat.ofHom (leftDualD₁ q)
  | 1 => ModuleCat.ofHom (rhoT q)
  | _+2 => 0

lemma leftDualResD_exact (hq : q ≠ 0) (n : ℕ) :
    Function.Exact (leftDualResD q (n+1)) (leftDualResD q n) := by
  rcases n with _ | _ | _ | n
  · change Function.Exact (rhoT q) (leftDualD₁ q)
    intro x
    change (0, rhoEll q ((q^2)⁻¹) x) = (0,0) ↔ _
    rw [Prod.mk.injEq]
    simpa only [true_and] using exact_rhoT q hq x
  · change Function.Exact (fun _ : PUnit => (0 : Cf q)) (rhoT q)
    intro x
    constructor
    · intro hx
      refine ⟨PUnit.unit, ?_⟩
      exact ((rhoT_injective q hq) (hx.trans (map_zero (rhoT q)).symm)).symm
    · rintro ⟨_, rfl⟩
      exact map_zero _
  · change Function.Exact (fun _ : PUnit => (0 : PUnit)) (fun _ : PUnit => (0 : Cf q))
    intro x
    exact ⟨fun _ => ⟨PUnit.unit, Subsingleton.elim _ _⟩, fun _ => rfl⟩
  · change Function.Exact (fun _ : PUnit => (0 : PUnit)) (fun _ : PUnit => (0 : PUnit))
    intro x
    exact ⟨fun _ => ⟨PUnit.unit, Subsingleton.elim _ _⟩, fun _ => rfl⟩

def leftDualProjectiveResolution (hq : q ≠ 0) :
    ProjectiveResolution (ModuleCat.of (C k q) (DualBimodule k (C k q))) :=
  resolutionOfExact _ (leftDualResObj q) (leftDualResD q)
    (ModuleCat.ofHom (leftDualAug q)) (leftDualResD_exact q hq)
    (exact_leftDualAug q hq) (leftDualAug_surjective q hq) (fun n => by
      rcases n with _ | _ | _ | n <;> dsimp [leftDualResObj] <;> infer_instance)

end Tachikawa.C



namespace Tachikawa.C
open CategoryTheory
variable {k : Type} [Field k] (q : k)

variable [CharP k 2]

lemma reverseD_exact (hq : q ≠ 0)
    (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) (n : ℕ) :
    Function.Exact (rhoEll q (reverseCoeff q (n+1)))
      (rhoEll q (reverseCoeff q (n+2))) := by
  rw [← reverseCoeff_step q hq (n+1)]
  apply exact_rhoEll
  · exact reverseCoeff_nonexceptional q hq hp (n+1)
  · rw [reverseCoeff_step q hq (n+1)]
    exact reverseCoeff_nonexceptional q hq hp n

end Tachikawa.C



namespace Tachikawa.C
open CategoryTheory CategoryTheory.Limits
variable {k : Type} [Field k] [CharP k 2] (q : k)

lemma reverseComplex_exactAt (hq : q ≠ 0)
    (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0)
    (j : ℤ) (hj : j ≠ 0) : (reverseComplex q hq).ExactAt j := by
  obtain ⟨i,rfl⟩ : ∃ i : ℤ, j = i+1 := ⟨j-1, by omega⟩
  rw [HomologicalComplex.exactAt_iff' _ (i+1+1) (i+1) i (by simp) (by simp)]
  apply (ShortComplex.moduleCat_exact_iff _).mpr
  change ∀ x, ChainComplex.of.d _ (reverseD q) (i+1) i x = 0 →
    ∃ y, ChainComplex.of.d _ (reverseD q) (i+1+1) (i+1) y = x
  simp only [ChainComplex.of_d]
  cases i with
  | ofNat n =>
    rcases n with _ | _ | n
    · exact fun x hx => (exact_rhoT q hq x).mp hx
    · intro x hx
      refine ⟨0, ?_⟩
      exact (rhoT_injective q hq (hx.trans (map_zero (rhoT q)).symm)).symm
    · intro x _
      exact ⟨0, @Subsingleton.elim PUnit inferInstance _ _⟩
  | negSucc n =>
    rcases n with _ | _ | n
    · exact (hj rfl).elim
    · exact fun x hx => (reverseD_exact q hq hp 0 x).mp hx
    · exact fun x hx => (reverseD_exact q hq hp (n+1) x).mp hx

lemma reverseComparison_quasiIso (hq : q ≠ 0)
    (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) : QuasiIso (reverseComparison q hq hp) := by
  constructor
  intro j
  by_cases hj : j = 0
  · subst j
    rw [quasiIsoAt_iff' _ 1 0 (-1) (by simp) (by simp)]
    apply shortComplex_quasiIso_of_cycles
    · intro x _ hx
      exact comparison_injective_cycles q hq hp x hx
    · intro y hy
      obtain ⟨x,z,hz⟩ := comparison_surjective_cycles q hq hp y hy
      exact ⟨x, rfl, z, hz⟩
  · have hS := forwardComplex_exactAt q hp j hj
    have hT := reverseComplex_exactAt q hq hp j hj
    exact (quasiIsoAt_iff_exactAt (reverseComparison q hq hp) j hS).mpr hT

end Tachikawa.C



namespace Tachikawa.C
open CategoryTheory
variable {k : Type} [Field k] (q : k)

variable [CharP k 2]

lemma hom_exact_rhoEll_general (hq : q ≠ 0) (z : k)
    (hz : 1+z ≠ 0) (hz' : 1+q*z ≠ 0) : Function.Exact
    (homPrecomp (k := k) (Z := C k q) (rhoEll q z))
    (homPrecomp (k := k) (Z := C k q) (rhoEll q (q*z))) := by
  intro f
  constructor
  · intro hf
    have hh := congrArg (RightCorner.homEquiv (e_idempotent q)) hf
    have hz0 : lambdaEll q (q*z) (RightCorner.homEquiv (e_idempotent q) f) = 0 := by
      simpa only [homPrecomp_apply, rhoEll, lambdaEll,
        RightCorner.homEquiv_precomp (e_idempotent q) (e_idempotent q)
          (ell q (q*z)) (e_mul_ell q _) (ell_mul_e q _), map_zero] using hh
    obtain ⟨a,ha⟩ := (exact_lambdaEll q hq z hz hz' _).mp hz0
    refine ⟨(RightCorner.homEquiv (e_idempotent q)).symm a, ?_⟩
    apply (RightCorner.homEquiv (e_idempotent q)).injective
    change RightCorner.homEquiv (e_idempotent q)
      (((RightCorner.homEquiv (e_idempotent q)).symm a).comp (rhoEll q z)) = _
    rw [rhoEll, RightCorner.homEquiv_precomp (e_idempotent q) (e_idempotent q)
      (ell q z) (e_mul_ell q _) (ell_mul_e q _)]
    simpa only [LinearEquiv.apply_symm_apply, lambdaEll] using ha
  · rintro ⟨g,rfl⟩
    apply LinearMap.ext
    intro x
    change g (rhoEll q z (rhoEll q (q*z) x)) = 0
    rw [rhoEll_comp_zero, map_zero]

lemma hom_exact_rhoT (hq : q ≠ 0)
    (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) : Function.Exact
    (homPrecomp (k := k) (Z := C k q) (rhoEll q (reverseCoeff q 0)))
    (homPrecomp (k := k) (Z := C k q) (rhoT q)) := by
  intro f
  constructor
  · intro hf
    have hh := congrArg (RightCorner.homEquiv (f_idempotent q)) hf
    have hz : lambdaT q (RightCorner.homEquiv (e_idempotent q) f) = 0 := by
      simpa only [homPrecomp_apply, rhoT, lambdaT,
        RightCorner.homEquiv_precomp (f_idempotent q) (e_idempotent q)
          (t q) (f_mul_t q) (t_mul_e q), map_zero] using hh
    obtain ⟨a,ha⟩ := (exact_lambdaT q hq hp _).mp hz
    refine ⟨(RightCorner.homEquiv (e_idempotent q)).symm a, ?_⟩
    apply (RightCorner.homEquiv (e_idempotent q)).injective
    change RightCorner.homEquiv (e_idempotent q)
      (((RightCorner.homEquiv (e_idempotent q)).symm a).comp (rhoEll q (reverseCoeff q 0))) = _
    rw [rhoEll, RightCorner.homEquiv_precomp (e_idempotent q) (e_idempotent q)
      (ell q _) (e_mul_ell q _) (ell_mul_e q _)]
    simpa only [LinearEquiv.apply_symm_apply, lambdaEll] using ha
  · rintro ⟨g,rfl⟩
    apply LinearMap.ext
    intro x
    change g (rhoEll q ((q^2)⁻¹) (rhoT q x)) = 0
    rw [(exact_rhoT q hq).apply_apply_eq_zero, map_zero]

lemma nu_reverseEll_exact (hq : q ≠ 0)
    (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) (n : ℕ) : Function.Exact
    (Nakayama.map (k := k) (rhoEll q (reverseCoeff q n)))
    (Nakayama.map (rhoEll q (reverseCoeff q (n+1)))) := by
  rw [← reverseCoeff_step q hq n]
  exact exact_dual _ _ (hom_exact_rhoEll_general q hq _
    (one_add_inv_power_ne_zero q hp (n+1+2) (by omega))
    (by change 1+q*reverseCoeff q (n+1) ≠ 0; rw [reverseCoeff_step q hq n]; exact one_add_inv_power_ne_zero q hp (n+2) (by omega)))

lemma nu_reverseTop_exact (hq : q ≠ 0)
    (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) : Function.Exact
    (Nakayama.map (k := k) (rhoT q))
    (Nakayama.map (rhoEll q (reverseCoeff q 0))) :=
  exact_dual _ _ (hom_exact_rhoT q hq hp)

end Tachikawa.C



namespace Tachikawa.C
variable {k : Type} [Field k] [CharP k 2] (q : k)

omit [CharP k 2] in
lemma nuV_nuTwoCycle : Nakayama.map (k := k) (rhoV q) (nuTwoCycle q) = nuTopCycle q := by
  apply LinearMap.ext
  intro g
  have h := RightCorner.homEquiv_precomp (e_idempotent q) (f_idempotent q)
    (v q) (e_mul_v q) (v_mul_f q) g
  change ((g.comp (rhoV q)) (LeftCorner.generator (e_idempotent q))) 6 = _
  change (RightCorner.homEquiv (e_idempotent q) (g.comp (rhoV q))).val 6 = _
  rw [rhoV, h]
  change mul q (v q) (g (LeftCorner.generator (f_idempotent q))) 6 = _
  simp [mul, v, nuTopCycle]
  rfl

omit [CharP k 2] in
lemma homTop_decompose (hq1 : 1+q ≠ 0) (g : Cf q →ₗ[C k q] C k q) :
    ∃ h : Ce q →ₗ[C k q] C k q,
      g = h.comp (rhoT q) +
        ((RightCorner.homEquiv (f_idempotent q) g).val 1) • fHom q := by
  let a := RightCorner.homEquiv (f_idempotent q) g
  let b := ec q (a.val 7) (a.val 8) 0 0 (a.val 9/(1+q)) 0
  refine ⟨(RightCorner.homEquiv (e_idempotent q)).symm b, ?_⟩
  apply (RightCorner.homEquiv (f_idempotent q)).injective
  rw [map_add]
  change (a : fC q) = _ + _
  have hcomp : RightCorner.homEquiv (f_idempotent q)
      (((RightCorner.homEquiv (e_idempotent q)).symm b).comp (rhoT q)) = lambdaT q b := by
    rw [rhoT, RightCorner.homEquiv_precomp (f_idempotent q) (e_idempotent q)
      (t q) (f_mul_t q) (t_mul_e q), LinearEquiv.apply_symm_apply]
    rfl
  rw [hcomp]
  have hsmul : RightCorner.homEquiv (f_idempotent q) (a.val 1 • fHom q) =
      a.val 1 • fc q 1 0 0 0 := by
    exact (RightCorner.homEquivScalar (k := k) (f_idempotent q)).map_smul _ _ |>.trans
      (congrArg (fun x : fC q => a.val 1 • x) (homEquiv_fHom q))
  rw [hsmul]
  dsimp only [b]
  rw [lambdaT_ec, mul_zero, add_zero, mul_div_cancel₀ _ hq1]
  rw [← fc_eta q a]
  apply Subtype.ext
  ext i
  change (fc q (a.val 1) (a.val 7) (a.val 8) (a.val 9)).val i =
    (fc q 0 (a.val 7) (a.val 8) (a.val 9)).val i + a.val 1 * (fc q 1 0 0 0).val i
  fin_cases i <;> simp [fc]

omit [CharP k 2] in
lemma nuTopCycle_description (hq1 : 1+q ≠ 0) (ψ : Nakayama k (C k q) (Cf q))
    (hψ : Nakayama.map (rhoT q) ψ = 0) : ψ = ψ (fHom q) • nuTopCycle q := by
  apply LinearMap.ext
  intro g
  obtain ⟨h,hg⟩ := homTop_decompose q hq1 g
  have hh : ψ (h.comp (rhoT q)) = 0 := LinearMap.congr_fun hψ h
  conv_lhs => erw [hg, map_add, hh, zero_add, map_smul]
  change (g (LeftCorner.generator (f_idempotent q))) 1 * ψ (fHom q) = ψ (fHom q) * (g (LeftCorner.generator (f_idempotent q))) 1
  exact mul_comm _ _

lemma nuV_cycles_injective (hq : q ≠ 0) (hq1 : 1+q ≠ 0)
    (ψ : Nakayama k (C k q) (Ce q))
    (hψ : Nakayama.map (rhoEll q 1) ψ = 0)
    (hV : Nakayama.map (rhoV q) ψ = 0) :
    ∃ ξ, Nakayama.map (rhoEll q q) ξ = ψ := by
  apply (nuTwo_boundary_iff q hq hq1 ψ hψ).mp
  have h := LinearMap.congr_fun hV (fHom q)
  change ψ ((fHom q).comp (rhoV q)) = 0 at h
  rw [fHom_rhoV] at h
  exact h

lemma nuV_cycles_surjective (hq1 : 1+q ≠ 0)
    (ψ : Nakayama k (C k q) (Cf q))
    (hψ : Nakayama.map (rhoT q) ψ = 0) :
    ∃ ξ : Nakayama k (C k q) (Ce q),
      Nakayama.map (rhoEll q 1) ξ = 0 ∧ Nakayama.map (rhoV q) ξ = ψ := by
  refine ⟨ψ (fHom q) • nuTwoCycle q, ?_, ?_⟩
  · rw [LinearMap.map_smul_of_tower, nuTwoCycle_closed, smul_zero]
  · rw [LinearMap.map_smul_of_tower, nuV_nuTwoCycle]
    exact (nuTopCycle_description q hq1 ψ hψ).symm

end Tachikawa.C



namespace Tachikawa.C
open CategoryTheory CategoryTheory.Limits
variable {k : Type} [Field k] [CharP k 2] (q : k)

lemma nuForward_exactAt (hq : q ≠ 0)
    (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0)
    (j : ℤ) (hj : j ≠ 2) :
    (Nakayama.complex (k := k) (forwardComplex q hp)).ExactAt j := by
  obtain ⟨i,rfl⟩ : ∃ i : ℤ, j = i+1 := ⟨j-1, by omega⟩
  rw [HomologicalComplex.exactAt_iff' _ (i+1+1) (i+1) i (by simp) (by simp)]
  apply (ShortComplex.moduleCat_exact_iff _).mpr
  change ∀ x, Nakayama.map (ChainComplex.of.d _ (forwardD q) (i+1) i).hom x = 0 →
    ∃ y, Nakayama.map (ChainComplex.of.d _ (forwardD q) (i+1+1) (i+1)).hom y = x
  simp only [ChainComplex.of_d]
  cases i with
  | ofNat n => exact fun x hx => (nu_resD_exact q hq hp n (by intro hn; subst n; exact hj rfl) x).mp hx
  | negSucc n =>
    cases n with
    | zero => exact fun x _ => nu_rhoU_surjective q x
    | succ n =>
      intro x _
      refine ⟨0, ?_⟩
      exact @Subsingleton.elim ((PUnit →ₗ[C k q] C k q) →ₗ[k] k) inferInstance _ _

lemma nuReverse_exactAt (hq : q ≠ 0)
    (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0)
    (j : ℤ) (hj : j ≠ 2) :
    (Nakayama.complex (k := k) (reverseComplex q hq)).ExactAt j := by
  obtain ⟨i,rfl⟩ : ∃ i : ℤ, j = i+1 := ⟨j-1, by omega⟩
  rw [HomologicalComplex.exactAt_iff' _ (i+1+1) (i+1) i (by simp) (by simp)]
  apply (ShortComplex.moduleCat_exact_iff _).mpr
  change ∀ x, Nakayama.map (ChainComplex.of.d _ (reverseD q) (i+1) i).hom x = 0 →
    ∃ y, Nakayama.map (ChainComplex.of.d _ (reverseD q) (i+1+1) (i+1)).hom y = x
  simp only [ChainComplex.of_d]
  cases i with
  | ofNat n =>
    rcases n with _ | _ | n
    · exact fun x hx => (nu_reverseTop_exact q hq hp x).mp hx
    · exact (hj rfl).elim
    · intro x _
      exact ⟨0, @Subsingleton.elim ((PUnit →ₗ[C k q] C k q) →ₗ[k] k) inferInstance _ _⟩
  | negSucc n =>
    rcases n with _ | _ | n
    · exact fun x hx => (nu_reverseEll_exact q hq hp 0 x).mp hx
    · exact fun x hx => (nu_reverseEll_exact q hq hp 1 x).mp hx
    · exact fun x hx => (nu_reverseEll_exact q hq hp (n+2) x).mp hx

lemma nuReverseComparison_quasiIso (hq : q ≠ 0)
    (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) :
    QuasiIso (((Nakayama.functor (k := k)).mapHomologicalComplex (ComplexShape.down ℤ)).map
      (reverseComparison q hq hp)) := by
  constructor
  intro j
  by_cases hj : j = 2
  · subst j
    rw [quasiIsoAt_iff' _ 3 2 1 (by simp) (by simp)]
    apply shortComplex_quasiIso_of_cycles
    · intro x hx hb
      obtain ⟨z,hz⟩ := hb
      change Nakayama.map (rhoEll q (q^0)) x = 0 at hx
      rw [pow_zero] at hx
      have hV : Nakayama.map (rhoV q) x = 0 := by
        change Nakayama.map (0 : PUnit →ₗ[C k q] Cf q) z = Nakayama.map (rhoV q) x at hz
        erw [Nakayama.map_zero, LinearMap.zero_apply] at hz
        exact hz.symm
      obtain ⟨ξ,hξ⟩ := nuV_cycles_injective q hq (by simpa only [pow_one] using hp 1 (by omega)) x hx hV
      refine ⟨ξ, ?_⟩
      change Nakayama.map (rhoEll q (q^1)) ξ = x
      simpa only [pow_one] using hξ
    · intro y hy
      obtain ⟨x,hx,hV⟩ := nuV_cycles_surjective q (by simpa only [pow_one] using hp 1 (by omega)) y hy
      refine ⟨x, ?_, 0, ?_⟩
      · change Nakayama.map (rhoEll q (q^0)) x = 0
        simpa only [pow_zero] using hx
      · change Nakayama.map (0 : PUnit →ₗ[C k q] Cf q) 0 = Nakayama.map (rhoV q) x - (show Nakayama k (C k q) (Cf q) from y)
        erw [map_zero, hV, sub_self]
  · exact (quasiIsoAt_iff_exactAt _ j (nuForward_exactAt q hq hp j hj)).mpr
      (nuReverse_exactAt q hq hp j hj)

end Tachikawa.C



namespace Tachikawa
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]

namespace TrivialInduction

lemma quasiIso_map {P Q : ChainComplex (ModuleCat R) ℤ} (f : P ⟶ Q)
    (hf : QuasiIso f)
    (hν : QuasiIso (((Nakayama.functor (k := k)).mapHomologicalComplex _).map f)) :
    QuasiIso (((functor (k := k)).mapHomologicalComplex _).map f) := by
  let := hf
  let := hν
  constructor
  intro j
  rw [quasiIsoAt_iff' _ (j+1) j (j-1) (by simp) (by simp)]
  have hf' := shortComplex_cycles_of_quasiIso _
    ((quasiIsoAt_iff' f (j+1) j (j-1) (by simp) (by simp)).mp inferInstance)
  have hν' := shortComplex_cycles_of_quasiIso _
    ((quasiIsoAt_iff' (((Nakayama.functor (k := k)).mapHomologicalComplex _).map f)
      (j+1) j (j-1) (by simp) (by simp)).mp inferInstance)
  apply shortComplex_quasiIso_of_cycles
  · intro x hx hbd
    obtain ⟨z,hz⟩ := hbd
    obtain ⟨a,ha⟩ := hf'.1 x.1 (congrArg Prod.fst hx) ⟨z.1, congrArg Prod.fst hz⟩
    obtain ⟨b,hb⟩ := hν'.1 x.2 (congrArg Prod.snd hx) ⟨z.2, congrArg Prod.snd hz⟩
    exact ⟨(a,b), Prod.ext ha hb⟩
  · intro y hy
    obtain ⟨a,ha,z,hz⟩ := hf'.2 y.1 (congrArg Prod.fst hy)
    obtain ⟨b,hb,w,hw⟩ := hν'.2 y.2 (congrArg Prod.snd hy)
    exact ⟨(a,b), Prod.ext ha hb, (z,w), Prod.ext hz hw⟩
end TrivialInduction
end Tachikawa



namespace Tachikawa.C
open CategoryTheory
variable {k : Type} [Field k] [CharP k 2] (q : k)

lemma inducedReverseComparison_quasiIso (hq : q ≠ 0)
    (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) :
    QuasiIso (inducedReverseComparison q hq hp) :=
  TrivialInduction.quasiIso_map _ (reverseComparison_quasiIso q hq hp)
    (nuReverseComparison_quasiIso q hq hp)

end Tachikawa.C

end



noncomputable section



namespace Tachikawa.OuterTensor
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct ModuleCat.Algebra
variable {k A B : Type} [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
variable (P : ChainComplex (ModuleCat.{0} A) ℤ) (Q : ChainComplex (ModuleCat.{0} B) ℤ)

lemma total_isZero_above_int (a b : ℤ)
    (hP : ∀ i, a < i → IsZero (P.X i)) (hQ : ∀ j, b < j → IsZero (Q.X j))
    (n : ℤ) (hn : a+b < n) :
    IsZero ((mapBifunctor P Q (bifunctor k A B) (.down ℤ)).X n) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  apply HomologicalComplex₂.total.hom_ext
  intro i j hij
  have h : IsZero (((bifunctor k A B).obj (P.X i)).obj (Q.X j)) := by
    by_cases hi : a < i
    · exact isZero_obj_left _ _ (hP i hi)
    · exact isZero_obj_right _ _ (hQ j (by dsimp at hij; omega))
  exact h.eq_of_src _ _

end Tachikawa.OuterTensor

end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Coinduction
attribute [-instance] _root_.OAI.Tachikawa.Triangular.instProjectiveCarrierOneFree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace Tachikawa.C
open CategoryTheory
variable {k : Type} [Field k] (q : k)

lemma rightDualZ_ec (a b c d u v : k) (x : C k q) :
    rightDualZ q (ec q a b c d u v) x =
      a*x 4 + d*x 0 + q*b*x 3 + c*x 2 + u*x 8 + q*v*x 7 := rfl

lemma rightDualV_ec (a b c d u v : k) (x : C k q) :
    rightDualV q (ec q a b c d u v) x =
      a*x 6 + v*x 1 + b*x 5 + c*x 5 + u*x 9 := rfl

lemma rightDualAug_surjective (hq : q ≠ 0) : Function.Surjective (rightDualAug q) := by
  intro φ
  refine ⟨(ec q (φ (basis q 4)) (φ (basis q 3)/q) (φ (basis q 2))
    (φ (basis q 0)) (φ (basis q 8)) (φ (basis q 7)/q),
    ec q (φ (basis q 6)) (φ (basis q 5)) 0 0 (φ (basis q 9)) (φ (basis q 1))), ?_⟩
  change (_ : Module.Dual k (C k q)) = φ
  apply (basis q).ext
  intro i
  change rightDualZ q _ (basis q i) + rightDualV q _ (basis q i) = φ (basis q i)
  simp only [LinearMap.fst_apply, LinearMap.snd_apply, rightDualZ_ec, rightDualV_ec]
  fin_cases i <;> simp [basis_apply] <;> field_simp

end Tachikawa.C

namespace Tachikawa.C
open CategoryTheory
variable {k : Type} [Field k] [CharP k 2] (q : k)

def rightDualResD : ∀ n, rightDualResObj q (n+1) ⟶ rightDualResObj q n
  | 0 => ModuleCat.ofHom (rightDualD₁ q)
  | 1 => ModuleCat.ofHom (lambdaU q)
  | _+2 => 0

lemma rightDualResD_exact (_hq : q ≠ 0) (n : ℕ) :
    Function.Exact (rightDualResD q (n+1)) (rightDualResD q n) := by
  rcases n with _ | _ | _ | n
  · change Function.Exact (lambdaU q) (rightDualD₁ q)
    intro x
    change (0, lambdaEll q 1 x) = (0,0) ↔ _
    rw [Prod.mk.injEq]
    simpa only [true_and] using exact_lambdaU q x
  · change Function.Exact (fun _ : PUnit => (0 : fC q)) (lambdaU q)
    intro x
    constructor
    · intro hx
      refine ⟨PUnit.unit, ?_⟩
      exact ((lambdaU_injective q) (hx.trans (map_zero (lambdaU q)).symm)).symm
    · rintro ⟨_, rfl⟩
      exact map_zero _
  · change Function.Exact (fun _ : PUnit => (0 : PUnit)) (fun _ : PUnit => (0 : fC q))
    intro x
    exact ⟨fun _ => ⟨PUnit.unit, Subsingleton.elim _ _⟩, fun _ => rfl⟩
  · change Function.Exact (fun _ : PUnit => (0 : PUnit)) (fun _ : PUnit => (0 : PUnit))
    intro x
    exact ⟨fun _ => ⟨PUnit.unit, Subsingleton.elim _ _⟩, fun _ => rfl⟩

def rightDualProjectiveResolution (hq : q ≠ 0) :
    ProjectiveResolution (ModuleCat.of (C k q)ᵐᵒᵖ (DualBimodule k (C k q))) :=
  resolutionOfExact _ (rightDualResObj q) (rightDualResD q)
    (ModuleCat.ofHom (rightDualAug q)) (rightDualResD_exact q hq)
    (exact_rightDualAug q hq) (rightDualAug_surjective q hq) (fun n => by
      rcases n with _ | _ | _ | n <;> dsimp [rightDualResObj] <;> infer_instance)

end Tachikawa.C



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_DerivedInduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
set_option backward.isDefEq.respectTransparency false


noncomputable section



namespace Tachikawa.TrivialInduction
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]

variable [FiniteDimensional k R] (M : ModuleCat.{0} R) [FiniteDimensional k M]

def tensorInverse (x : Obj k R M) :
    (AlgebraInduction.functor (inclusion (k := k) (R := R))).obj M :=
  AlgebraInduction.unit (inclusion (k := k) (R := R)) M x.1 +
    lowerTensor (k := k) M ((Nakayama.evaluationEquiv (k := k) (R := R) (M := M)).symm x.2)

lemma tensorComparison_inverse (x : Obj k R M) :
    tensorComparison (k := k) M (tensorInverse (k := k) M x) = x := by
  change tensorComparison (k := k) M (AlgebraInduction.unit (inclusion (k := k) (R := R)) M x.1 +
    lowerTensor (k := k) M ((Nakayama.evaluationEquiv (k := k) (R := R) (M := M)).symm x.2)) = x
  erw [map_add, tensorComparison_lower]
  have he := (Nakayama.evaluationEquiv (k := k) (R := R) (M := M)).apply_symm_apply x.2
  change Nakayama.evaluation ((Nakayama.evaluationEquiv (k := k) (R := R) (M := M)).symm x.2) = x.2 at he
  rw [he]
  change (1 : TrivialExtension k R) • unit x.1 + (0,x.2) = x
  erw [one_smul]
  apply Prod.ext
  · exact add_zero _
  · exact zero_add _

lemma tensorInverse_zero : tensorInverse (k := k) M 0 = 0 := by
  change AlgebraInduction.unit (inclusion (k := k) (R := R)) M 0 + lowerTensor (k := k) M
    ((Nakayama.evaluationEquiv (k := k) (R := R) (M := M)).symm 0) = 0
  simp

lemma tensorInverse_add (x y : Obj k R M) :
    tensorInverse (k := k) M (x+y) = tensorInverse (k := k) M x + tensorInverse (k := k) M y := by
  change AlgebraInduction.unit (inclusion (k := k) (R := R)) M (x.1+y.1) + lowerTensor (k := k) M
    ((Nakayama.evaluationEquiv (k := k) (R := R) (M := M)).symm (x.2+y.2)) = _
  simp only [map_add]
  change _ = (AlgebraInduction.unit (inclusion (k := k) (R := R)) M x.1 + lowerTensor (k := k) M
    ((Nakayama.evaluationEquiv (k := k) (R := R) (M := M)).symm x.2)) +
    (AlgebraInduction.unit (inclusion (k := k) (R := R)) M y.1 + lowerTensor (k := k) M
    ((Nakayama.evaluationEquiv (k := k) (R := R) (M := M)).symm y.2))
  abel

lemma tensorInverse_comparison (z : (AlgebraInduction.functor
    (inclusion (k := k) (R := R))).obj M) :
    tensorInverse (k := k) M (tensorComparison (k := k) M z) = z := by
  induction z using BalancedTensor.induction_on with
  | h0 =>
    exact (congrArg (tensorInverse (k := k) M)
      (tensorComparison (k := k) M).hom.map_zero).trans (tensorInverse_zero M)
  | ha x y hx hy =>
    erw [map_add, tensorInverse_add, hx, hy]
    try rfl
  | ht a m =>
    have he : (tensorComparison (k := k) M (BalancedTensor.mk a m) : Obj k R M) =
        ((show TrivialExtension k R from a).fst • m,
          Nakayama.evaluationBilinear (show TrivialExtension k R from a).snd m) := by
      apply Prod.ext
      · rfl
      · change Nakayama.evaluationBilinear _ m + _ • (0 : Nakayama k R M) = _
        rw [smul_zero, add_zero]
    rw [he]
    change AlgebraInduction.unit (inclusion (k := k) (R := R)) M ((show TrivialExtension k R from a).fst • m) +
      lowerTensor (k := k) M ((Nakayama.evaluationEquiv (k := k) (R := R) (M := M)).symm
        (Nakayama.evaluationBilinear (show TrivialExtension k R from a).snd m)) = _
    have hinv : (Nakayama.evaluationEquiv (k := k) (R := R) (M := M)).symm
        (Nakayama.evaluationBilinear (show TrivialExtension k R from a).snd m) =
        BalancedTensor.mk (k := k) (R := R) (S := R) (M := DualBimodule k R) (N := M) (show TrivialExtension k R from a).snd m := by
      have h := (Nakayama.evaluationEquiv (k := k) (R := R) (M := M)).symm_apply_apply
        (BalancedTensor.mk (k := k) (R := R) (S := R) (M := DualBimodule k R) (N := M) (show TrivialExtension k R from a).snd m)
      exact h
    rw [hinv]
    change BalancedTensor.mk (k := k) (R := R) (S := TrivialExtension k R)
      (show AlgebraInduction.Bimod (inclusion (k := k) (R := R)) from (1 : TrivialExtension k R)) ((show TrivialExtension k R from a).fst • m) +
      BalancedTensor.mk (show AlgebraInduction.Bimod (inclusion (k := k) (R := R)) from
        TrivSqZeroExt.inr (show TrivialExtension k R from a).snd) m = _
    rw [← BalancedTensor.balance]
    change BalancedTensor.mk (k := k) (R := R) (S := TrivialExtension k R)
      (show AlgebraInduction.Bimod (inclusion (k := k) (R := R)) from (1 : TrivialExtension k R) * TrivSqZeroExt.inl
        (show TrivialExtension k R from a).fst) m +
      BalancedTensor.mk (show AlgebraInduction.Bimod (inclusion (k := k) (R := R)) from
        TrivSqZeroExt.inr (show TrivialExtension k R from a).snd) m = _
    erw [one_mul]
    erw [← LinearMap.add_apply, ← map_add]
    exact congrArg (fun t : AlgebraInduction.Bimod (inclusion (k := k) (R := R)) =>
      BalancedTensor.mk (k := k) (R := R) (S := TrivialExtension k R) t m)
      (TrivSqZeroExt.inl_fst_add_inr_snd_eq (show TrivialExtension k R from a))

def tensorComparisonEquiv :
    (AlgebraInduction.functor (inclusion (k := k) (R := R))).obj M ≃ₗ[TrivialExtension k R]
      (functor (k := k) (R := R)).obj M :=
  LinearEquiv.ofBijective (tensorComparison (k := k) M).hom
    ⟨Function.LeftInverse.injective (tensorInverse_comparison M),
      Function.RightInverse.surjective (tensorComparison_inverse M)⟩

def tensorComparisonIso :
    (AlgebraInduction.functor (inclusion (k := k) (R := R))).obj M ≅
      (functor (k := k) (R := R)).obj M :=
  LinearEquiv.toModuleIso (tensorComparisonEquiv M)

end Tachikawa.TrivialInduction



namespace Tachikawa.TrivialInduction
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]

variable [FiniteDimensional k R]

def tensorComplexIso {ι : Type} {c : ComplexShape ι}
    (P : HomologicalComplex (ModuleCat.{0} R) c)
    [∀ i, FiniteDimensional k (P.X i)] :
    (((AlgebraInduction.functor (inclusion (k := k) (R := R))).mapHomologicalComplex c).obj P) ≅
      (((functor (k := k) (R := R)).mapHomologicalComplex c).obj P) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => tensorComparisonIso (P.X i)) (fun i j _ => (tensorComparison_natural (P.d i j)).symm)

end Tachikawa.TrivialInduction



namespace Tachikawa.C
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q : k)

lemma projectiveResolution_d (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) (n : ℕ) :
    (projectiveResolution q hp).complex.d (n+1) n = resD q n := by
  dsimp only [projectiveResolution, resolutionOfExact]
  exact ChainComplex.of_d _ _ _

def inducedJComparison (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) :
    (((AlgebraInduction.functor (TrivialInduction.inclusion (k := k) (R := C k q))).mapHomologicalComplex _).obj
      (projectiveResolution q hp).complex) ≅ inducedComplex q hp := by
  letI : ∀ n, Module.Finite k ((projectiveResolution q hp).complex.X n) :=
    fun n => resObj_finite_k q n
  refine (TrivialInduction.tensorComplexIso (projectiveResolution q hp).complex) ≪≫ ?_
  refine HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) ?_
  intro i j hij
  have h : j+1 = i := by simpa using hij
  subst i
  symm
  change ModuleCat.ofHom (TrivialInduction.map (k := k) (R := C k q)
    ((projectiveResolution q hp).complex.d (j+1) j).hom) = _
  rw [projectiveResolution_d, inducedComplex_d]
  rfl

end Tachikawa.C



namespace Tachikawa.C
open CategoryTheory HomologicalComplex
open scoped TensorProduct ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q : k)

def inducedJTensorComparison (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) :
    mapBifunctor (balancedInducedResolution q hp) (balancedInducedResolution q hp)
      (OuterTensor.bifunctor k (T q) (T q)) (.down ℕ) ≅
    mapBifunctor (inducedComplex q hp) (inducedComplex q hp)
      (OuterTensor.bifunctor k (T q) (T q)) (.down ℕ) := by
  let F := (OuterTensor.bifunctor k (T q) (T q)).map₂HomologicalComplex
    (.down ℕ) (.down ℕ) (.down ℕ)
  exact ((F.mapIso (inducedJComparison q hp)).app (balancedInducedResolution q hp)) ≪≫
    ((F.obj (inducedComplex q hp)).mapIso (inducedJComparison q hp))

end Tachikawa.C



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Perfect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace Tachikawa.Construction
open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable {k : Type} [Field k] [CharP k 2] (q : k)
variable (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0)

lemma reverseJJ_above (j : ℤ) (hj : 4 < j) : IsZero ((reverseJJ q hq).X j) :=
  OuterTensor.total_isZero_above_int _ _ 2 2 (reverseJ_above q hq) (reverseJ_above q hq) j hj

def jjFiberHighEquiv (j : ℤ) (hj : 4 ≤ j) :
    (jjFiber q hq hp).X j ≃ₗ[E q] (forwardJJ q hp).X j := by
  let : Subsingleton ((reverseJJ q hq).X (j+1)) :=
    ModuleCat.subsingleton_of_isZero (reverseJJ_above q hq (j+1) (by omega))
  exact LinearEquiv.ofBijective (LinearMap.snd (E q) ((reverseJJ q hq).X (j+1)) _) ⟨
    fun x y h => Prod.ext (Subsingleton.elim _ _) h, fun y => ⟨(0,y),rfl⟩⟩

@[simp] lemma jjFiberHighEquiv_apply (j : ℤ) (hj : 4 ≤ j) (x : (jjFiber q hq hp).X j) :
    jjFiberHighEquiv q hq hp j hj x = x.2 := rfl

end Tachikawa.Construction



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_FiniteCoinduction
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

def bRegularLeftObj : ModuleCat (B q) := ModuleCat.of (B q) (B q)

end Tachikawa.Construction



namespace Tachikawa.Enveloping
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex

attribute [instance] CoindReplacement.quasiIso

end Tachikawa.Enveloping



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_HomProfile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace Tachikawa.C
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra
variable {k : Type} [Field k] (q : k)

def homCfSimpleEquiv : (Cf q →ₗ[C k q] Simple q) ≃ₗ[k] k where
  toFun f := f (LeftCorner.generator (f_idempotent q))
  invFun a := LeftCorner.lift (show Simple q from a) (f_smul_simple q a)
  left_inv _ := LeftCorner.hom_ext (f_idempotent q) (f_smul_simple q _)
  right_inv a := f_smul_simple q a
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

local instance simpleGround_r09b566_1 : Module k (simpleObj q) := ModuleCat.Algebra.instModuleCarrier
def inducedFHomEquiv : (inducedObj q 0 ⟶ simpleObj q) ≃ₗ[k] k := by
  let : Module.Finite k (Cf q) := Module.Finite.of_injective
    ((Cf q).subtype.restrictScalars k) Subtype.val_injective
  let e := (TrivialInflation.homEquiv (k := k) (R := C k q) (M := Cf q)
    (N := Simple q)).trans (homCfSimpleEquiv q)
  exact {
    toFun := fun f => e f.hom
    invFun := fun a => ModuleCat.ofHom (e.symm a)
    left_inv := fun f => ModuleCat.hom_ext (e.symm_apply_apply f.hom)
    right_inv := e.apply_symm_apply
    map_add' := fun f g => e.map_add f.hom g.hom
    map_smul' := by
      intro r f
      change Construction.characterT q (algebraMap k (T q) r) *
        (show k from f (TrivialInduction.unit (LeftCorner.generator (f_idempotent q)))) =
        r * (show k from f (TrivialInduction.unit (LeftCorner.generator (f_idempotent q))))
      rw [AlgHom.commutes]
      rfl }

variable [CharP k 2]

lemma forwardJ_hom_zero (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0)
    (j : ℤ) (hj : j ≠ 0) (f : (Construction.forwardJ q hp).X j ⟶ simpleObj q) : f = 0 := by
  cases j with
  | ofNat n =>
    cases n with
    | zero => exact (hj rfl).elim
    | succ n => exact induced_positive_hom_zero q n f
  | negSucc n => exact (Construction.forwardJ_below q hp _ (by omega)).eq_of_src _ _

lemma reverseJ_hom_zero (hq : q ≠ 0) (j : ℤ) (hj : j ≠ 2)
    (f : (Construction.reverseJ q hq).X j ⟶ simpleObj q) : f = 0 := by
  cases j with
  | ofNat n =>
    rcases n with _ | _ | _ | n
    · exact induced_positive_hom_zero q 0 f
    · exact induced_positive_hom_zero q 0 f
    · exact (hj rfl).elim
    · exact (Construction.reverseJ_above q hq _ (by change 2 < ((n+3 : ℕ) : ℤ); omega)).eq_of_src _ _
  | negSucc n => exact induced_positive_hom_zero q 0 f

end Tachikawa.C



end

end OAI
end


