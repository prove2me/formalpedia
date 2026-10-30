-- Prove2me | Definitions.Def_OAIQ116Ta017
-- name    : OAIQ116Ta017
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T01:50:51.397702+00:00
-- url     : https://prove2.me/theorems/b43f1139-f118-4ad3-a1ec-2757080027f6
-- title:
--   Definitions bundle OAIQ116Ta017 of the split of OpenAI, A counterexample to Tachikawa's second conjecture
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Tachikawa.main_theorem`, carved from OpenAI's openai/math development (OpenAI, *A counterexample to Tachikawa's second conjecture*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 85 declarations of OpenAI's Lean: 34 definitions, 5 instances and 46 theorems. The definitions and types are `OAI.Tachikawa.C.fHom`, `OAI.Tachikawa.C.forwardComplex`, `OAI.Tachikawa.C.inducedBoundaryObj`, `OAI.Tachikawa.C.inducedComplex`, `OAI.Tachikawa.C.inducedReverseComparison`, `OAI.Tachikawa.C.lambdaT`, `OAI.Tachikawa.C.leftDualAug`, `OAI.Tachikawa.C.leftDualD₁`, `OAI.Tachikawa.C.leftDualJ`, `OAI.Tachikawa.C.leftDualZ`, `OAI.Tachikawa.C.reverseComparison`, `OAI.Tachikawa.C.reverseComplex`, `OAI.Tachikawa.C.rightDualAug`, `OAI.Tachikawa.C.rightDualD₁`, `OAI.Tachikawa.C.rightDualV`, `OAI.Tachikawa.C.rightDualZ`, `OAI.Tachikawa.C.simpleObj`, `OAI.Tachikawa.Construction.forwardJ`, `OAI.Tachikawa.Construction.forwardJJ`, `OAI.Tachikawa.Construction.intJJDouble`, `OAI.Tachikawa.Construction.jjFiber`, `OAI.Tachikawa.Construction.jjIntNatComponent`, `OAI.Tachikawa.Construction.jjIntNatX`, `OAI.Tachikawa.Construction.jjNatIntX`, `OAI.Tachikawa.Construction.jjReverseComparison`, `OAI.Tachikawa.Construction.natJJ`, `OAI.Tachikawa.Construction.natJJDouble`, `OAI.Tachikawa.Construction.reverseJ`, `OAI.Tachikawa.Construction.reverseJJ`, `OAI.Tachikawa.OuterTensor.inductionIso`, `OAI.Tachikawa.OuterTensor.tensorTwistLiftHom`, `OAI.Tachikawa.TrivialInflation.homEquiv`, `OAI.Tachikawa.TrivialInflation.lift`, `OAI.Tachikawa.TrivialInflation.restrict`.
--
--   **Sources.** They come from these modules of lean/OAI/RingTheory, in whole or in part: [`Tachikawa_Bimodule`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RingTheory/Tachikawa/Bimodule.lean), [`Tachikawa_Coinduction`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RingTheory/Tachikawa/Coinduction.lean), [`Tachikawa_Coresolution`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RingTheory/Tachikawa/Coresolution.lean), [`Tachikawa_Nakayama`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RingTheory/Tachikawa/Nakayama.lean), [`Tachikawa_OuterExt`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RingTheory/Tachikawa/OuterExt.lean), [`Tachikawa_OuterTensor`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RingTheory/Tachikawa/OuterTensor.lean), [`Tachikawa_Perfect`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RingTheory/Tachikawa/Perfect.lean), [`Tachikawa_Period`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RingTheory/Tachikawa/Period.lean), [`Tachikawa_ReverseResolution`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RingTheory/Tachikawa/ReverseResolution.lean).
--
--   **Imports.** It imports the bundle `OAIQ116Ta006` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ116Ta010`, `OAIQ116Ta011`, `OAIQ116Ta012` and `OAIQ116Ta013`.
-- source:
--   OpenAI, A counterexample to Tachikawa's second conjecture, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-counterexample-to-Tachikawas-second-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/RingTheory at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ116Ta006

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Coresolution
attribute [-instance] _root_.OAI.Tachikawa.LeftCoinduced.coextend_additive _root_.OAI.Tachikawa.LeftCoinduced.coextend_preservesInjective _root_.OAI.Tachikawa.OuterTensor.restrictionPreservesHomology _root_.OAI.Tachikawa.TotalDualPairing.instTensorSignsNatUp_solutions _root_.OAI.Tachikawa.TotalMap.sourceHasCoproduct _root_.OAI.Tachikawa.downIntTensorSigns
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

@[simp] lemma inverseTwistHom_apply {X Y : ModuleCat R} (f : X ⟶ (twistFunctor σ).obj Y)
    (x : (twistFunctor σ.symm).obj X) : inverseTwistHom σ f x = f x := rfl

end Tachikawa.SymmetrizingForm



namespace Tachikawa.SymmetrizingForm
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R] (σ : R ≃ₐ[k] R)

instance twist_isEquivalence : (twistFunctor σ).IsEquivalence :=
  ModuleCat.restrictScalars_isEquivalence_of_ringEquiv σ.symm.toRingEquiv

instance twist_preserves_projective : (twistFunctor σ).PreservesProjectiveObjects := inferInstance

end Tachikawa.SymmetrizingForm



namespace Tachikawa
open CategoryTheory CategoryTheory.Abelian
open scoped ModuleCat.Algebra
variable (k R : Type) [Field k] [Ring R] [Algebra k R]
  (P : ChainComplex (ModuleCat R) ℕ) (N : ModuleCat R)

@[simp] lemma resolutionHom_X (n : ℕ) :
    (resolutionHom k R P N).X n = ModuleCat.of k (P.X n ⟶ N) := rfl

end Tachikawa



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_OuterTensor
attribute [-instance] _root_.OAI.Tachikawa.LeftCoinduced.coextend_additive _root_.OAI.Tachikawa.LeftCoinduced.coextend_preservesInjective _root_.OAI.Tachikawa.OuterTensor.restrictionPreservesHomology _root_.OAI.Tachikawa.TotalDualPairing.instTensorSignsNatUp_solutions _root_.OAI.Tachikawa.downIntTensorSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
set_option backward.isDefEq.respectTransparency false


noncomputable section
set_option backward.isDefEq.respectTransparency true



namespace Tachikawa.OuterTensor
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k A B S T : Type} [Field k] [Ring A] [Ring B] [Ring S] [Ring T]
  [Algebra k A] [Algebra k B] [Algebra k S] [Algebra k T]
  (φ : A →ₐ[k] S) (ψ : B →ₐ[k] T) (M : ModuleCat A) (N : ModuleCat B)

lemma inductionInverse_comparison_pure (s : S) (t : T) (x : M) (y : N) :
    inductionInverseLinear φ ψ M N
      (inductionComparison φ ψ M N (inductionSourceMk φ ψ M N (s ⊗ₜ[k] t) (x ⊗ₜ[k] y))) =
      inductionSourceMk φ ψ M N (s ⊗ₜ[k] t) (x ⊗ₜ[k] y) := by
  change inductionInverseLinear φ ψ M N
    ((s • AlgebraInduction.unitLinear φ M x) ⊗ₜ[k]
      (t • AlgebraInduction.unitLinear ψ N y)) = _
  have hs : (s • AlgebraInduction.unitLinear φ M x : (AlgebraInduction.functor φ).obj M) =
      BalancedTensor.mk (k := k) (R := A) (S := S) (show AlgebraInduction.Bimod φ from s) x :=
    (AlgebraInduction.mk_one_smul φ M s x).symm
  have ht : (t • AlgebraInduction.unitLinear ψ N y : (AlgebraInduction.functor ψ).obj N) =
      BalancedTensor.mk (k := k) (R := B) (S := T) (show AlgebraInduction.Bimod ψ from t) y :=
    (AlgebraInduction.mk_one_smul ψ N t y).symm
  exact (congrArg (inductionInverseLinear φ ψ M N)
    (congrArg₂ (fun (u : (AlgebraInduction.functor φ).obj M)
      (v : (AlgebraInduction.functor ψ).obj N) =>
        (show inductionTarget φ ψ M N from u ⊗ₜ[k] v)) hs ht)).trans
      (inductionInverseLinear_pure φ ψ M N s x t y)

lemma inductionInverse_comparison :
    (inductionInverseLinear φ ψ M N).comp
      ((inductionComparison φ ψ M N).hom.restrictScalars k) = LinearMap.id := by
  let e := AlgebraInduction.underlyingEquiv (Algebra.TensorProduct.map φ ψ)
    (((bifunctor k A B).obj M).obj N)
  let f := ((inductionInverseLinear φ ψ M N).comp
      ((inductionComparison φ ψ M N).hom.restrictScalars k)).comp e.symm.toLinearMap
  have hfg : f = e.symm.toLinearMap := by
    apply BalancedTensor.hom_ext_ground
    intro s z
    change (f.comp ((BalancedTensor.mk (k := k) (R := A ⊗[k] B) (S := S ⊗[k] T)
      (M := AlgebraInduction.Bimod (Algebra.TensorProduct.map φ ψ))
      (N := ((bifunctor k A B).obj M).obj N)) s)) z = _
    let F : (S ⊗[k] T) →ₗ[k] (M ⊗[k] N) →ₗ[k] inductionSource φ ψ M N :=
      (inductionSourceMk φ ψ M N).compr₂
        ((inductionInverseLinear φ ψ M N).comp
          ((inductionComparison φ ψ M N).hom.restrictScalars k))
    have hF : F = inductionSourceMk φ ψ M N := by
      apply LinearMap.ext
      intro st
      induction st using OAI.tensorInductionOn with
      | add st uv hst huv => simp only [map_add, hst, huv]
      | tmul s t =>
        apply TensorProduct.ext'
        intro x y
        exact inductionInverse_comparison_pure φ ψ M N s t x y
    exact LinearMap.congr_fun (LinearMap.congr_fun hF (show S ⊗[k] T from s))
      (show M ⊗[k] N from z)
  apply LinearMap.ext
  intro z
  exact LinearMap.congr_fun hfg (e z)

lemma inductionComparison_injective : Function.Injective (inductionComparison φ ψ M N) := by
  apply Function.LeftInverse.injective (f := inductionComparison φ ψ M N)
    (g := inductionInverseLinear φ ψ M N)
  intro z
  exact LinearMap.congr_fun (inductionInverse_comparison φ ψ M N) z

def inductionIso : inductionSource φ ψ M N ≅ inductionTarget φ ψ M N :=
  (LinearEquiv.ofBijective (inductionComparison φ ψ M N).hom
    ⟨inductionComparison_injective φ ψ M N, inductionComparison_surjective φ ψ M N⟩).toModuleIso

@[simp] lemma inductionIso_hom : (inductionIso φ ψ M N).hom = inductionComparison φ ψ M N := rfl

end Tachikawa.OuterTensor



namespace Tachikawa.OuterTensor
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k A B : Type} [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]

@[simp] lemma morphism_id (M : ModuleCat A) (N : ModuleCat B) :
    morphism (k := k) (𝟙 M) (𝟙 N) = 𝟙 (((bifunctor k A B).obj M).obj N) :=
  ModuleCat.hom_ext (map_id M N)

end Tachikawa.OuterTensor

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

@[reassoc]
lemma bifunctor_maps {M M' : ModuleCat A} {N N' : ModuleCat B}
    (u : M ⟶ M') (v : N ⟶ N') :
    ((bifunctor k A B).map u).app N ≫ ((bifunctor k A B).obj M').map v = morphism u v := by
  change morphism u (𝟙 N) ≫ morphism (𝟙 M') v = _
  rw [morphism_comp,Category.comp_id,Category.id_comp]

instance algebraTwist_preserves_projective {R : Type} [Ring R] [Algebra k R]
    (ρ : R ≃ₐ[k] R) : (algebraTwist ρ).PreservesProjectiveObjects := by
  have : (algebraTwist ρ).IsEquivalence :=
    ModuleCat.restrictScalars_isEquivalence_of_ringEquiv ρ.symm.toRingEquiv
  infer_instance

variable {M : ModuleCat A} {N : ModuleCat B}
  (P : ProjectiveResolution M) (Q : ProjectiveResolution N)
  (e : (algebraTwist σ).obj M ≅ M) (f : (algebraTwist τ).obj N ≅ N)
  (lP : ProjectiveResolution.Hom P (mappedResolution (algebraTwist σ) P) e.inv)
  (lQ : ProjectiveResolution.Hom Q (mappedResolution (algebraTwist τ) Q) f.inv)

abbrev tensorTwistLiftHom :=
  mapBifunctorMap lP.hom lQ.hom (bifunctor k A B) (.down ℕ) ≫
    (twistTotalIso σ τ P.complex Q.complex (.down ℕ)).hom

@[reassoc]
lemma ι_tensorTwistLiftHom (i j n : ℕ) (h : i+j=n) :
    ιMapBifunctor P.complex Q.complex (bifunctor k A B) (.down ℕ) i j n h ≫
      (tensorTwistLiftHom σ τ P Q e f lP lQ).f n =
    morphism (lP.hom.f i) (lQ.hom.f j) ≫
      (twistObjIso σ τ (P.complex.X i) (Q.complex.X j)).hom ≫
      (algebraTwist (Algebra.TensorProduct.congr σ τ)).map
        (ιMapBifunctor P.complex Q.complex (bifunctor k A B) (.down ℕ) i j n h) := by
  dsimp only [mappedResolution] at lP lQ ⊢
  change _ ≫ (_ ≫ _) = _
  rw [← Category.assoc,ι_mapBifunctorMap]
  simp only [Category.assoc]
  rw [bifunctor_maps_assoc]
  change morphism (lP.hom.f i) (lQ.hom.f j) ≫
    ιMapBifunctor (twistComplex σ P.complex) (twistComplex τ Q.complex)
      (bifunctor k A B) (.down ℕ) i j n h ≫
      (twistTotalIso σ τ P.complex Q.complex (.down ℕ)).hom.f n = _
  exact congrArg (fun morph => morphism (lP.hom.f i) (lQ.hom.f j) ≫ morph)
    (ι_twistTotalIso σ τ P.complex Q.complex (.down ℕ) i j n h)

end Tachikawa.OuterTensor



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Nakayama
attribute [-instance] _root_.OAI.Tachikawa.Construction.instModuleEX _root_.OAI.Tachikawa.LeftCoinduced.coextend_additive _root_.OAI.Tachikawa.LeftCoinduced.coextend_preservesInjective _root_.OAI.Tachikawa.downIntTensorSigns
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

variable [FiniteDimensional k M]

lemma evaluation_surjective : Function.Surjective (evaluation (k := k) (R := R) (M := M)) := by
  let : Module.Finite k (M →ₗ[R] R) :=
    Module.Finite.of_injective (LinearMap.restrictScalarsₗ k R M R k)
      (LinearMap.restrictScalars_injective k)
  apply (LinearMap.dualMap_injective_iff (f := (evaluation (k := k) (R := R) (M := M)).restrictScalars k)).mp
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro l hl
  let f := (Module.evalEquiv k (M →ₗ[R] R)).symm l
  have he : ∀ ψ : Nakayama k R M, l ψ = ψ f := by
    intro ψ
    exact (Module.apply_evalEquiv_symm_apply k (M →ₗ[R] R) ψ l).symm
  have hf : f = 0 := by
    ext m
    apply (Module.forall_dual_apply_eq_zero_iff k (f m)).mp
    intro φ
    have hz := LinearMap.congr_fun hl (BalancedTensor.mk (M := DualBimodule k R) φ m)
    change l (evaluation (BalancedTensor.mk (M := DualBimodule k R) φ m)) = 0 at hz
    rw [he] at hz
    exact hz
  apply LinearMap.ext
  intro ψ
  rw [he, hf]
  exact LinearMap.map_zero ψ

end Nakayama
end Tachikawa



namespace Tachikawa
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]

namespace TrivialInflation
variable {M N : Type} [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]
  [AddCommGroup N] [Module R N] [Module k N] [IsScalarTower k R N]
instance instIsScalarTowerTrivialExtension : IsScalarTower k (TrivialExtension k R) (TrivialInflation k R M) :=
  IsScalarTower.of_algebraMap_smul fun c x => by
    change (algebraMap k R c) • (show M from x) = c • x
    exact IsScalarTower.algebraMap_smul R c x

def restrict (f : TrivialInduction.Obj k R M →ₗ[TrivialExtension k R] TrivialInflation k R N) : M →ₗ[R] N where
  toFun m := f (TrivialInduction.unit m)
  map_add' m n := by rw [map_add, map_add]; rfl
  map_smul' r m := by
    rw [map_smul, ← TrivialInduction.inl_smul, map_smul]
    rfl

def lift (f : M →ₗ[R] N) : TrivialInduction.Obj k R M →ₗ[TrivialExtension k R] TrivialInflation k R N where
  toFun x := f x.1
  map_add' x y := f.map_add x.1 y.1
  map_smul' a x := f.map_smul a.fst x.1

omit [Module k N] [IsScalarTower k R N] in
@[simp] lemma restrict_lift (f : M →ₗ[R] N) : restrict (lift (k := k) f) = f := rfl

omit [Module k N] [IsScalarTower k R N] in
lemma lift_restrict [FiniteDimensional k R] [FiniteDimensional k M]
    (f : TrivialInduction.Obj k R M →ₗ[TrivialExtension k R] TrivialInflation k R N) :
    lift (restrict f) = f := by
  let lower : Nakayama k R M →ₗ[R] TrivialInduction.Obj k R M := LinearMap.inr R M _
  have hz : ∀ ψ : Nakayama k R M, f (lower ψ) = 0 := by
    intro ψ
    obtain ⟨z, rfl⟩ := Nakayama.evaluation_surjective (k := k) (R := R) (M := M) ψ
    induction z using BalancedTensor.induction_on with
    | h0 => rw [map_zero, map_zero, map_zero]
    | ht φ m =>
      have he : lower (Nakayama.evaluation (BalancedTensor.mk φ m)) =
          (TrivSqZeroExt.inr φ : TrivialExtension k R) • TrivialInduction.unit m := by
        apply Prod.ext
        · exact (zero_smul R m).symm
        · change Nakayama.evaluationBilinear φ m = Nakayama.evaluationBilinear φ m + (0:R) • (0 : Nakayama k R M)
          rw [zero_smul, add_zero]
      rw [he, map_smul, inr_smul]
    | ha z w hz hw => rw [map_add, map_add, map_add, hz, hw, add_zero]
  apply LinearMap.ext
  intro x
  have hx : x = TrivialInduction.unit (k := k) (R := R) x.1 + lower x.2 := by
    apply Prod.ext
    · exact (add_zero _).symm
    · exact (zero_add _).symm
  change f (TrivialInduction.unit x.1) = f x
  conv_rhs => rw [hx, map_add, hz, add_zero]

def homEquiv [FiniteDimensional k R] [FiniteDimensional k M] :
    (TrivialInduction.Obj k R M →ₗ[TrivialExtension k R] TrivialInflation k R N) ≃ₗ[k] (M →ₗ[R] N) where
  toFun := restrict
  invFun := lift
  left_inv := lift_restrict
  right_inv := restrict_lift
  map_add' f g := by apply LinearMap.ext; intro m; rfl
  map_smul' c f := by apply LinearMap.ext; intro m; rfl

end TrivialInflation
end Tachikawa

end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Period
attribute [-instance] _root_.OAI.Tachikawa.Construction.instModuleEX _root_.OAI.Tachikawa.LeftCoinduced.coextend_additive _root_.OAI.Tachikawa.LeftCoinduced.coextend_preservesInjective _root_.OAI.Tachikawa.downIntTensorSigns
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
namespace TrivialInduction

instance instAdditiveModuleCatTrivialExtensionFunctor : (functor (k := k) (R := R)).Additive where
  map_add {X Y f g} := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Prod.ext
    · rfl
    · apply LinearMap.ext
      intro a
      change x.2 (a.comp (f.hom+g.hom)) = x.2 (a.comp f.hom) + x.2 (a.comp g.hom)
      rw [LinearMap.comp_add, map_add]

end TrivialInduction

namespace C
variable [CharP k 2] (q : k)

def inducedComplex (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) : ChainComplex (ModuleCat (T q)) ℕ :=
  ChainComplex.of (inducedObj q) (inducedD q) (inducedD_comp q hp)

omit [CharP k 2] in

lemma induced_positive_hom_zero (n : ℕ)
    (f : inducedObj q (n+1) ⟶ ModuleCat.of (T q) (TSimple q)) : f = 0 := by
  apply ModuleCat.hom_ext
  let f₀ : TrivialInduction.Obj k (C k q) (Ce q) →ₗ[T q] TSimple q := f.hom
  change f₀ = 0
  apply (TrivialInflation.homEquiv (k := k) (R := C k q) (M := Ce q) (N := Simple q)).injective
  exact (homCeSimple_zero q (TrivialInflation.restrict f₀)).trans (map_zero _).symm

end C
end Tachikawa



namespace Tachikawa.C
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q : k)

abbrev inducedBoundaryObj := ModuleCat.of (T q) (InducedBoundaries q)

end Tachikawa.C



namespace Tachikawa.C
variable {k : Type} [Field k] [CharP k 2] (q : k)

omit [CharP k 2] in
lemma vHom_rhoEll (z : k) : (vHom q).comp (rhoEll q z) = 0 := by
  apply (RightCorner.homEquiv (e_idempotent q)).injective
  rw [rhoEll, RightCorner.homEquiv_precomp (e_idempotent q) (e_idempotent q) (ell q z)
    (e_mul_ell q z) (ell_mul_e q z), map_zero, homEquiv_vHom]
  change lambdaEll q z (ec q 0 0 0 0 0 1) = 0
  rw [lambdaEll_ec, ec_eq_zero]
  simp

omit [CharP k 2] in
lemma dual_vHom_rhoEll (z : k) (ψ : Module.Dual k (Ce q →ₗ[C k q] C k q)) :
    ψ ((vHom q).comp (rhoEll q z)) = 0 :=
  (congrArg ψ (vHom_rhoEll q z)).trans ψ.map_zero

lemma hom_cycle_decompose (hq : q ≠ 0) (hq1 : 1+q ≠ 0)
    (f : Ce q →ₗ[C k q] C k q) (hf : f.comp (rhoEll q q) = 0) :
    ∃ g : Ce q →ₗ[C k q] C k q,
      f = g.comp (rhoEll q 1) + ((RightCorner.homEquiv (e_idempotent q) f).val 6) • vHom q := by
  let ε := RightCorner.homEquivScalar (k := k) (e_idempotent q)
  have hz : lambdaEll q q (ε f) = 0 := by
    change lambdaEll q q (RightCorner.homEquiv (e_idempotent q) f) = 0
    have h := congrArg (RightCorner.homEquiv (e_idempotent q)) hf
    simpa only [rhoEll, lambdaEll,
      RightCorner.homEquiv_precomp (e_idempotent q) (e_idempotent q) (ell q q)
        (e_mul_ell q q) (ell_mul_e q q), map_zero] using h
  let a : LinearMap.ker (lambdaEll q q) := ⟨ε f, hz⟩
  refine ⟨ε.symm (ec q (a.val.val 2) (a.val.val 4) 0 0 0 0), ?_⟩
  apply ε.injective
  rw [map_add, map_smul]
  have hc : ε ((ε.symm (ec q (a.val.val 2) (a.val.val 4) 0 0 0 0)).comp (rhoEll q 1)) =
      lambdaEll q 1 (ec q (a.val.val 2) (a.val.val 4) 0 0 0 0) := by
    change RightCorner.homEquivScalar (k := k) (e_idempotent q)
      ((ε.symm (ec q (a.val.val 2) (a.val.val 4) 0 0 0 0)).comp (rhoEll q 1)) = _
    rw [rhoEll, RightCorner.homEquivScalar_precomp (e_idempotent q) (e_idempotent q) (ell q 1)
      (e_mul_ell q 1) (ell_mul_e q 1)]
    exact congrArg (lambdaEll q 1) (ε.apply_symm_apply _)
  rw [hc]
  have hv : ((RightCorner.homEquiv (e_idempotent q) f).val 6) • ε (vHom q) =
      ec q 0 0 0 0 0 ((RightCorner.homEquiv (e_idempotent q) f).val 6) := by
    change _ • RightCorner.homEquiv (e_idempotent q) (vHom q) = _
    rw [homEquiv_vHom]
    apply Subtype.ext
    change ((RightCorner.homEquiv (e_idempotent q) f).val 6) •
      (ec q 0 0 0 0 0 1).val = _
    ext i
    rw [smul_apply]
    fin_cases i <;> simp [ec]
  rw [hv]
  exact dualTwoCycle_decompose q hq hq1 a

lemma dual_vHom_boundary_iff (hq : q ≠ 0) (hq1 : 1+q ≠ 0)
    (ψ : Module.Dual k (Ce q →ₗ[C k q] C k q))
    (hψ : ∀ g : Ce q →ₗ[C k q] C k q, ψ (g.comp (rhoEll q 1)) = 0) :
    ψ (vHom q) = 0 ↔ ψ ∈ LinearMap.range (homPrecomp (k := k) (Z := C k q) (rhoEll q q)).dualMap := by
  rw [LinearMap.range_dualMap_eq_dualAnnihilator_ker, Submodule.mem_dualAnnihilator]
  constructor
  · intro ha f hf
    obtain ⟨g,hg⟩ := hom_cycle_decompose q hq hq1 f hf
    rw [hg, map_add, map_smul, hψ, ha, smul_zero, add_zero]
  · intro h
    exact h (vHom q) (vHom_rhoEll q q)

lemma dual_vHom_action (hq : q ≠ 0) (hq1 : 1+q ≠ 0)
    (ψ : Module.Dual k (Ce q →ₗ[C k q] C k q))
    (hψ : ∀ g : Ce q →ₗ[C k q] C k q, ψ (g.comp (rhoEll q 1)) = 0) (a : C k q) :
    ψ (Nakayama.homRight (k := k) a (vHom q)) = (a 1) * ψ (vHom q) := by
  let h := Nakayama.homRight (k := k) a (vHom q)
  have hh : h.comp (rhoEll q q) = 0 := by
    change ((rightMultiply a).comp (vHom q)).comp (rhoEll q q) = 0
    rw [LinearMap.comp_assoc, vHom_rhoEll, LinearMap.comp_zero]
  obtain ⟨g,hg⟩ := hom_cycle_decompose q hq hq1 h hh
  rw [homRight_vHom_six q a] at hg
  change ψ h = _
  rw [hg, map_add, map_smul, hψ, zero_add]
  rfl

end Tachikawa.C



namespace Tachikawa.C
open CategoryTheory CategoryTheory.Abelian
open scoped ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q : k)

abbrev simpleObj := ModuleCat.of (T q) (TSimple q)

end Tachikawa.C



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_ReverseResolution
attribute [-instance] _root_.OAI.Tachikawa.LeftCoinduced.coextend_additive _root_.OAI.Tachikawa.LeftCoinduced.coextend_preservesInjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace Tachikawa.C
open CategoryTheory
variable {k : Type} [Field k] (q : k)

lemma e_fixed_z : e q • dualCoeff q 4 = dualCoeff q 4 := by
  ext a
  change (a * e q) 4 = a 4
  rw [mul_e]
  rfl

lemma e_fixed_j : e q • dualCoeff q 8 = dualCoeff q 8 := by
  ext a
  change (a * e q) 8 = a 8
  rw [mul_e]
  rfl

def leftDualZ : Ce q →ₗ[C k q] DualBimodule k (C k q) :=
  LeftCorner.lift (dualCoeff q 4) (e_fixed_z q)

def leftDualJ : Ce q →ₗ[C k q] DualBimodule k (C k q) :=
  LeftCorner.lift (dualCoeff q 8) (e_fixed_j q)

lemma leftDualZ_ce (a b c d t j : k) (x : C k q) :
    leftDualZ q (ce q a b c d t j) x =
      x 0*d + x 4*a + q*x 2*c + x 3*b + x 5*j + q*x 6*t := rfl

lemma leftDualJ_ce (a b c d t j : k) (x : C k q) :
    leftDualJ q (ce q a b c d t j) x =
      x 1*j + x 8*a + x 7*b + q^2*x 7*c + q*x 9*t := rfl

def leftDualAug : (Ce q × Ce q) →ₗ[C k q] DualBimodule k (C k q) :=
  (leftDualZ q).coprod (leftDualJ q)

def leftDualD₁ : Ce q →ₗ[C k q] (Ce q × Ce q) :=
  (0 : Ce q →ₗ[C k q] Ce q).prod (rhoEll q ((q^2)⁻¹))

lemma leftDualAug_apply (x y : Ce q) (a : C k q) :
    leftDualAug q (x,y) a =
      a 0*x.val 4 + a 4*x.val 0 + q*a 2*x.val 3 + a 3*x.val 2 +
      a 5*x.val 8 + q*a 6*x.val 7 +
      (a 1*y.val 8 + a 8*y.val 0 + a 7*y.val 2 + q^2*a 7*y.val 3 + q*a 9*y.val 7) := by
  rw [← ce_eta q x, ← ce_eta q y]
  change leftDualZ q _ a + leftDualJ q _ a = _
  simp only [LinearMap.fst_apply, LinearMap.snd_apply, leftDualZ_ce, leftDualJ_ce]
  rfl

lemma leftDualAug_eq_zero_iff (hq : q ≠ 0) (x y : Ce q) :
    leftDualAug q (x,y) = 0 ↔ x = 0 ∧ y.val 0 = 0 ∧
      y.val 2 + q^2*y.val 3 = 0 ∧ y.val 7 = 0 ∧ y.val 8 = 0 := by
  constructor
  · intro hh
    have h (i : Fin 10) := congrArg (fun ψ : DualBimodule k (C k q) => ψ (basis q i)) hh
    simp only [leftDualAug_apply, DualBimodule.zero_apply] at h
    have hx0 : x.val 0 = 0 := by simpa [basis_apply] using h 4
    have hx2 : x.val 2 = 0 := by simpa [basis_apply] using h 3
    have hx3 : x.val 3 = 0 := by simpa [basis_apply, hq] using h 2
    have hx4 : x.val 4 = 0 := by simpa [basis_apply] using h 0
    have hx7 : x.val 7 = 0 := by simpa [basis_apply, hq] using h 6
    have hx8 : x.val 8 = 0 := by simpa [basis_apply] using h 5
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [← ce_eta q x, ce_eq_zero]
      exact ⟨hx0,hx2,hx3,hx4,hx7,hx8⟩
    · simpa [basis_apply] using h 8
    · simpa [basis_apply] using h 7
    · simpa [basis_apply, hq] using h 9
    · simpa [basis_apply] using h 1
  · rintro ⟨rfl, hy0, hy2, hy7, hy8⟩
    ext a
    rw [leftDualAug_apply]
    change _ = 0
    simp only [Submodule.coe_zero, zero_apply, mul_zero, add_zero, zero_add, hy0, hy7, hy8]
    calc a 7 * y.val 2 + q^2*a 7*y.val 3 = a 7 * (y.val 2 + q^2*y.val 3) := by ring
         _ = 0 := by rw [hy2, mul_zero]

variable [CharP k 2]

lemma exact_leftDualAug (hq : q ≠ 0) :
    Function.Exact (leftDualD₁ q) (leftDualAug q) := by
  rintro ⟨x,y⟩
  constructor
  · intro hh
    obtain ⟨hx, ha, hbc, ht, hj⟩ := (leftDualAug_eq_zero_iff q hq x y).mp hh
    subst x
    have hb : y.val 2 = q^2*y.val 3 := by
      have he := eq_neg_of_add_eq_zero_left hbc
      simpa only [CharTwo.neg_eq] using he
    refine ⟨ce q (q^2*y.val 3) 0 (y.val 4) 0 0 0, ?_⟩
    apply Prod.ext
    · rfl
    · change rhoEll q ((q^2)⁻¹) _ = y
      rw [rhoEll_ce]
      have hy := ce_eta q y
      rw [ha, ht, hj, hb] at hy
      simpa only [mul_zero, add_zero, zero_add, inv_mul_cancel_left₀ (pow_ne_zero 2 hq)] using hy
  · rintro ⟨z, hz⟩
    rw [← hz]
    change leftDualAug q (0, rhoEll q ((q^2)⁻¹) z) = 0
    rw [leftDualAug_eq_zero_iff q hq]
    rw [← ce_eta q z, rhoEll_ce]
    change (0 : Ce q) = 0 ∧ (0:k) = 0 ∧ z.val 0 + q^2*((q^2)⁻¹*z.val 0) = 0 ∧
      (0:k) = 0 ∧ (1+q^2*(q^2)⁻¹)*z.val 7 = 0
    simp [mul_inv_cancel₀ (pow_ne_zero 2 hq), mul_inv_cancel_left₀ (pow_ne_zero 2 hq), CharTwo.add_self_eq_zero]

lemma exact_rhoT (hq : q ≠ 0) : Function.Exact (rhoT q) (rhoEll q ((q^2)⁻¹)) := by
  intro x
  constructor
  · intro hh
    rw [← ce_eta q x, rhoEll_ce, ce_eq_zero] at hh
    obtain ⟨_, ha, _, hbc, _, _⟩ := hh
    have hc : x.val 3 = q*(q^2)⁻¹*x.val 2 := by
      have he := eq_neg_of_add_eq_zero_right hbc
      simpa only [CharTwo.neg_eq] using he
    have hb : q*x.val 3 = x.val 2 := by
      rw [hc]
      field_simp
    refine ⟨cf q (x.val 7) (x.val 3) (x.val 4/q) (x.val 8/q), ?_⟩
    rw [rhoT_cf, hb]
    have hx := ce_eta q x
    rw [ha] at hx
    simpa only [mul_div_cancel₀ _ hq] using hx
  · rintro ⟨z, rfl⟩
    rw [← cf_eta q z, rhoT_cf, rhoEll_ce, ce_eq_zero]
    have hz : q*(q^2)⁻¹*q = 1 := by field_simp
    simp only [mul_zero, mul_inv_cancel₀ (pow_ne_zero 2 hq),
      CharTwo.add_self_eq_zero, zero_mul, true_and, and_true]
    rw [← _root_.mul_assoc, hz, one_mul, CharTwo.add_self_eq_zero]

end Tachikawa.C



namespace Tachikawa.C
open CategoryTheory
variable {k : Type} [Field k] (q : k)

variable [CharP k 2]

lemma reverseD_comp (hq : q ≠ 0) (n : ℕ) (a : Ce q) :
    rhoEll q (reverseCoeff q (n+1)) (rhoEll q (reverseCoeff q n) a) = 0 := by
  rw [← reverseCoeff_step q hq n]
  exact rhoEll_comp_zero q _ a

end Tachikawa.C



namespace Tachikawa.C
open CategoryTheory CategoryTheory.Limits
variable {k : Type} [Field k] [CharP k 2] (q : k)

lemma forwardD_comp (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) (j : ℤ) :
    forwardD q (j+1) ≫ forwardD q j = 0 := by
  cases j with
  | ofNat n => exact ModuleCat.hom_ext <| LinearMap.ext <|
      (resD_exact q hp n).apply_apply_eq_zero
  | negSucc n =>
    cases n with
    | zero => exact comp_zero
    | succ n => exact comp_zero

def forwardComplex (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) :
    ChainComplex (ModuleCat (C k q)) ℤ :=
  ChainComplex.of (forwardObj q) (forwardD q) (forwardD_comp q hp)

lemma reverseD_comp_zero (hq : q ≠ 0) (j : ℤ) :
    reverseD q (j+1) ≫ reverseD q j = 0 := by
  cases j with
  | ofNat n =>
    rcases n with _ | _ | n
    · exact ModuleCat.hom_ext <| LinearMap.ext <| (exact_rhoT q hq).apply_apply_eq_zero
    · exact zero_comp
    · exact zero_comp
  | negSucc n =>
    rcases n with _ | _ | n
    · exact ModuleCat.hom_ext <| LinearMap.ext <| reverseD_comp q hq 0
    · exact ModuleCat.hom_ext <| LinearMap.ext <| reverseD_comp q hq 1
    · exact ModuleCat.hom_ext <| LinearMap.ext <| reverseD_comp q hq (n+2)

def reverseComplex (hq : q ≠ 0) : ChainComplex (ModuleCat (C k q)) ℤ :=
  ChainComplex.of (reverseObj q) (reverseD q) (reverseD_comp_zero q hq)

def reverseComparison (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) :
    forwardComplex q hp ⟶ reverseComplex q hq where
  f := comparisonComponent q
  comm' i j hij := by
    have h : i = j+1 := by simpa [eq_comm] using hij
    subst i
    change comparisonComponent q (j+1) ≫ ChainComplex.of.d _ (reverseD q) (j+1) j =
      ChainComplex.of.d _ (forwardD q) (j+1) j ≫ comparisonComponent q j
    simp only [ChainComplex.of_d]
    exact comparison_comm q hq j

end Tachikawa.C



namespace Tachikawa.C
open CategoryTheory CategoryTheory.Limits
variable {k : Type} [Field k] [CharP k 2] (q : k)

lemma forwardComplex_exactAt (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0)
    (j : ℤ) (hj : j ≠ 0) : (forwardComplex q hp).ExactAt j := by
  obtain ⟨i,rfl⟩ : ∃ i : ℤ, j = i+1 := ⟨j-1, by omega⟩
  rw [HomologicalComplex.exactAt_iff' _ (i+1+1) (i+1) i (by simp) (by simp)]
  apply (ShortComplex.moduleCat_exact_iff _).mpr
  change ∀ x, ChainComplex.of.d _ (forwardD q) (i+1) i x = 0 →
    ∃ y, ChainComplex.of.d _ (forwardD q) (i+1+1) (i+1) y = x
  simp only [ChainComplex.of_d]
  cases i with
  | ofNat n => exact fun x hx => (resD_exact q hp n x).mp hx
  | negSucc n =>
    cases n with
    | zero => exact (hj rfl).elim
    | succ n =>
      intro x _
      exact ⟨0, @Subsingleton.elim PUnit inferInstance _ _⟩

end Tachikawa.C



namespace Tachikawa.C
open CategoryTheory
variable {k : Type} [Field k] (q : k)

lemma f_mul_t : f q * t q = t q := by rw [f_mul]; rfl

def lambdaT : eC q →ₗ[(C k q)ᵐᵒᵖ] fC q := RightCorner.mulLeft (t q) (f_mul_t q)

lemma lambdaT_ec (a b c d u v : k) :
    lambdaT q (ec q a b c d u v) = fc q 0 a (b+q^2*c) ((1+q)*u) := by
  apply Subtype.ext
  ext i
  change mul q (t q) ![a,0,b,c,d,u,v,0,0,0] i = _
  fin_cases i <;> simp [mul, t, fc]

variable [CharP k 2]

lemma exact_lambdaT (hq : q ≠ 0)
    (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) :
    Function.Exact (lambdaEll q (reverseCoeff q 0)) (lambdaT q) := by
  intro x
  constructor
  · intro h
    rw [← ec_eta q x, lambdaT_ec, fc_eq_zero] at h
    obtain ⟨_,ha,hbc,hu⟩ := h
    have hu' : x.val 5 = 0 := (mul_eq_zero.mp hu).resolve_left (by simpa only [pow_one] using hp 1 (by omega))
    have hc : x.val 3 = reverseCoeff q 0 * x.val 2 := by
      have hb : x.val 2 = q^2*x.val 3 := by
        simpa only [CharTwo.neg_eq] using eq_neg_of_add_eq_zero_left hbc
      rw [hb, reverseCoeff, Nat.zero_add]
      field_simp
    have hz : 1+reverseCoeff q 0 ≠ 0 :=
      one_add_inv_power_ne_zero q hp 2 (by omega)
    refine ⟨ec q (x.val 2) 0 (x.val 4/q) 0 (x.val 6/(1+reverseCoeff q 0)) 0, ?_⟩
    rw [lambdaEll_ec]
    have he := ec_eta q x
    rw [ha,hu',hc] at he
    simpa only [mul_zero, zero_add, mul_div_cancel₀ _ hq, mul_div_cancel₀ _ hz] using he
  · rintro ⟨x,rfl⟩
    rw [← ec_eta q x, lambdaEll_ec, lambdaT_ec, fc_eq_zero]
    simp [reverseCoeff, hq, CharTwo.add_self_eq_zero]

end Tachikawa.C



namespace Tachikawa.C
variable {k : Type} [Field k] [CharP k 2] (q : k)

def fHom : Cf q →ₗ[C k q] C k q := LeftCorner.lift (f q) (f_idempotent q)

omit [CharP k 2] in
lemma homEquiv_fHom : RightCorner.homEquiv (f_idempotent q) (fHom q) = fc q 1 0 0 0 :=
  Subtype.ext (LeftCorner.lift_generator (f_idempotent q) _ _)

omit [CharP k 2] in
lemma fHom_rhoV : (fHom q).comp (rhoV q) = vHom q := by
  apply (RightCorner.homEquiv (e_idempotent q)).injective
  rw [rhoV, RightCorner.homEquiv_precomp (e_idempotent q) (f_idempotent q)
    (v q) (e_mul_v q) (v_mul_f q), homEquiv_fHom, homEquiv_vHom]
  apply Subtype.ext
  change v q * (fc q 1 0 0 0).val = (ec q 0 0 0 0 0 1).val
  ext i
  change mul q (v q) _ i = _
  fin_cases i <;> simp [mul, v, fc, ec]

end Tachikawa.C



namespace Tachikawa.C
open CategoryTheory
variable {k : Type} [Field k] [CharP k 2] (q : k)

def inducedReverseComparison (hq : q ≠ 0)
    (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) :=
  ((TrivialInduction.functor (k := k)).mapHomologicalComplex (ComplexShape.down ℤ)).map
    (reverseComparison q hq hp)

end Tachikawa.C

end



noncomputable section



namespace Tachikawa.Construction
open CategoryTheory HomologicalComplex
open scoped TensorProduct
variable {k : Type} [Field k] [CharP k 2] (q : k)

abbrev forwardJ (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) :=
  ((TrivialInduction.functor (k := k)).mapHomologicalComplex (ComplexShape.down ℤ)).obj
    (C.forwardComplex q hp)

abbrev reverseJ (hq : q ≠ 0) :=
  ((TrivialInduction.functor (k := k)).mapHomologicalComplex (ComplexShape.down ℤ)).obj
    (C.reverseComplex q hq)

abbrev forwardJJ (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) :=
  mapBifunctor (forwardJ q hp) (forwardJ q hp)
    (OuterTensor.bifunctor k (C.T q) (C.T q)) (.down ℤ)

abbrev reverseJJ (hq : q ≠ 0) :=
  mapBifunctor (reverseJ q hq) (reverseJ q hq)
    (OuterTensor.bifunctor k (C.T q) (C.T q)) (.down ℤ)

def jjReverseComparison (hq : q ≠ 0)
    (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) : forwardJJ q hp ⟶ reverseJJ q hq :=
  mapBifunctorMap (C.inducedReverseComparison q hq hp) (C.inducedReverseComparison q hq hp)
    (OuterTensor.bifunctor k (C.T q) (C.T q)) (.down ℤ)

end Tachikawa.Construction



namespace Tachikawa.OuterTensor
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct ModuleCat.Algebra
variable {k A B : Type} [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]

lemma isZero_obj_left (M : ModuleCat.{0} A) (N : ModuleCat.{0} B) (h : IsZero M) :
    IsZero (((bifunctor k A B).obj M).obj N) :=
  ((bifunctor k A B).flip.obj N).map_isZero h

lemma isZero_obj_right (M : ModuleCat.{0} A) (N : ModuleCat.{0} B) (h : IsZero N) :
    IsZero (((bifunctor k A B).obj M).obj N) := ((bifunctor k A B).obj M).map_isZero h

end Tachikawa.OuterTensor



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Bimodule
attribute [-instance] _root_.OAI.Tachikawa.LeftCoinduced.coextend_additive _root_.OAI.Tachikawa.LeftCoinduced.coextend_preservesInjective
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

lemma forwardJ_below (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) (j : ℤ) (hj : j < 0) :
    IsZero ((forwardJ q hp).X j) := by
  cases j with
  | ofNat n => change (n : ℤ) < 0 at hj; omega
  | negSucc n =>
    exact (TrivialInduction.functor (k := k)).map_isZero
      (ModuleCat.isZero_of_subsingleton (ModuleCat.of (C k q) PUnit))

lemma reverseJ_above (hq : q ≠ 0) (j : ℤ) (hj : 2 < j) :
    IsZero ((reverseJ q hq).X j) := by
  cases j with
  | ofNat n =>
    change 2 < (n : ℤ) at hj
    rcases n with _ | _ | _ | n
    · norm_num at hj
    · norm_num at hj
    · norm_num at hj
    · exact (TrivialInduction.functor (k := k)).map_isZero
        (ModuleCat.isZero_of_subsingleton (ModuleCat.of (C k q) PUnit))
  | negSucc n => change 2 < -((n : ℤ)+1) at hj; omega

def jjFiber (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) :
    ChainComplex (ModuleCat (E q)) ℤ := ModuleFiber.complex (jjReverseComparison q hq hp)

end Tachikawa.Construction



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Coinduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace Tachikawa.C
open CategoryTheory
variable {k : Type} [Field k] (q : k)

lemma z_fixed_e : MulOpposite.op (e q) • dualCoeff q 4 = dualCoeff q 4 := by
  ext a
  change (e q * a) 4 = a 4
  rw [e_mul]
  rfl

lemma v_fixed_e : MulOpposite.op (e q) • dualCoeff q 6 = dualCoeff q 6 := by
  ext a
  change (e q * a) 6 = a 6
  rw [e_mul]
  rfl

def rightDualZ : eC q →ₗ[(C k q)ᵐᵒᵖ] DualBimodule k (C k q) :=
  RightCorner.lift (dualCoeff q 4) (z_fixed_e q)

def rightDualV : eC q →ₗ[(C k q)ᵐᵒᵖ] DualBimodule k (C k q) :=
  RightCorner.lift (dualCoeff q 6) (v_fixed_e q)

def rightDualAug : (eC q × eC q) →ₗ[(C k q)ᵐᵒᵖ] DualBimodule k (C k q) :=
  (rightDualZ q).coprod (rightDualV q)

lemma rightDualAug_apply (x y : eC q) (a : C k q) :
    rightDualAug q (x,y) a =
      x.val 0*a 4 + x.val 4*a 0 + q*x.val 2*a 3 + x.val 3*a 2 +
      x.val 5*a 8 + q*x.val 6*a 7 +
      (y.val 0*a 6 + y.val 6*a 1 + y.val 2*a 5 + y.val 3*a 5 + y.val 5*a 9) := by
  rw [← ec_eta q x, ← ec_eta q y]
  rfl

lemma rightDualAug_eq_zero_iff (hq : q ≠ 0) (x y : eC q) :
    rightDualAug q (x,y) = 0 ↔ x = 0 ∧ y.val 0 = 0 ∧
      y.val 2 + y.val 3 = 0 ∧ y.val 5 = 0 ∧ y.val 6 = 0 := by
  constructor
  · intro hh
    have h (i : Fin 10) := congrArg (fun ψ : DualBimodule k (C k q) => ψ (basis q i)) hh
    simp only [rightDualAug_apply, DualBimodule.zero_apply] at h
    have hx0 : x.val 0 = 0 := by simpa [basis_apply] using h 4
    have hx2 : x.val 2 = 0 := by simpa [basis_apply, hq] using h 3
    have hx3 : x.val 3 = 0 := by simpa [basis_apply] using h 2
    have hx4 : x.val 4 = 0 := by simpa [basis_apply] using h 0
    have hx5 : x.val 5 = 0 := by simpa [basis_apply] using h 8
    have hx6 : x.val 6 = 0 := by simpa [basis_apply, hq] using h 7
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [← ec_eta q x, ec_eq_zero]
      exact ⟨hx0,hx2,hx3,hx4,hx5,hx6⟩
    · simpa [basis_apply] using h 6
    · simpa [basis_apply] using h 5
    · simpa [basis_apply] using h 9
    · simpa [basis_apply] using h 1
  · rintro ⟨rfl, hy0, hy2, hy5, hy6⟩
    ext a
    rw [rightDualAug_apply]
    change _ = 0
    simp only [Submodule.coe_zero, zero_apply, zero_mul, add_zero, zero_add, hy0, hy5, hy6]
    rw [← _root_.add_mul, hy2, zero_mul]
    simp

def rightDualD₁ : eC q →ₗ[(C k q)ᵐᵒᵖ] (eC q × eC q) :=
  (0 : eC q →ₗ[(C k q)ᵐᵒᵖ] eC q).prod (lambdaEll q 1)

variable [CharP k 2]

lemma exact_rightDualAug (hq : q ≠ 0) :
    Function.Exact (rightDualD₁ q) (rightDualAug q) := by
  rintro ⟨x,y⟩
  constructor
  · intro hh
    obtain ⟨hx, ha, hbc, hu, hv⟩ := (rightDualAug_eq_zero_iff q hq x y).mp hh
    subst x
    have hc : y.val 3 = y.val 2 := by
      simpa only [CharTwo.neg_eq] using eq_neg_of_add_eq_zero_right hbc
    refine ⟨ec q (y.val 2) (y.val 4) 0 0 0 0, ?_⟩
    apply Prod.ext
    · rfl
    · change lambdaEll q 1 _ = y
      rw [lambdaEll_ec]
      have hy := ec_eta q y
      rw [ha, hu, hv, hc] at hy
      simpa only [mul_zero, add_zero, one_mul] using hy
  · rintro ⟨z, hz⟩
    rw [← hz]
    change rightDualAug q (0, lambdaEll q 1 z) = 0
    rw [rightDualAug_eq_zero_iff q hq]
    rw [← ec_eta q z, lambdaEll_ec]
    change (0 : eC q) = 0 ∧ (0:k) = 0 ∧ z.val 0 + 1*z.val 0 = 0 ∧
      (0:k) = 0 ∧ (1+1)*z.val 5 = 0
    simp [CharTwo.add_self_eq_zero]

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
open CategoryTheory CategoryTheory.Limits HomologicalComplex HomologicalComplex₂
variable {k : Type} [Field k] [CharP k 2] (q : k)
variable (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0)

abbrev natJJ := mapBifunctor (C.inducedComplex q hp) (C.inducedComplex q hp)
  (OuterTensor.bifunctor k (T q) (T q)) (.down ℕ)
abbrev natJJDouble := ((OuterTensor.bifunctor k (T q) (T q)).mapBifunctorHomologicalComplex
  (.down ℕ) (.down ℕ)).obj (C.inducedComplex q hp) |>.obj (C.inducedComplex q hp)
abbrev intJJDouble := ((OuterTensor.bifunctor k (T q) (T q)).mapBifunctorHomologicalComplex
  (.down ℤ) (.down ℤ)).obj (forwardJ q hp) |>.obj (forwardJ q hp)

def jjNatIntX (n : ℕ) : (natJJ q hp).X n ⟶ (forwardJJ q hp).X (n:ℤ) :=
  (natJJDouble q hp).totalDesc (c₁₂ := .down ℕ) (fun i j h =>
    (intJJDouble q hp).ιTotal (.down ℤ) (i:ℤ) (j:ℤ) (n:ℤ) (by
      change (i:ℤ)+(j:ℤ)=(n:ℤ); change i+j=n at h; omega))

@[reassoc (attr := simp)] lemma ι_jjNatIntX (i j n : ℕ) (h : i+j=n) :
    (natJJDouble q hp).ιTotal (.down ℕ) i j n h ≫ jjNatIntX q hp n =
      (intJJDouble q hp).ιTotal (.down ℤ) (i:ℤ) (j:ℤ) (n:ℤ) (by
        change (i:ℤ)+(j:ℤ)=(n:ℤ); omega) := by
  apply ι_totalDesc

def jjIntNatComponent (n : ℕ) (i j : ℤ) (h : i+j=(n:ℤ)) :
    ((intJJDouble q hp).X i).X j ⟶ (natJJ q hp).X n := by
  cases i with
  | ofNat i =>
    cases j with
    | ofNat j => exact (natJJDouble q hp).ιTotal (.down ℕ) i j n (by change i+j=n; dsimp at h; omega)
    | negSucc j => exact 0
  | negSucc i => exact 0

def jjIntNatX (n : ℕ) : (forwardJJ q hp).X (n:ℤ) ⟶ (natJJ q hp).X n :=
  (intJJDouble q hp).totalDesc (c₁₂ := .down ℤ) (jjIntNatComponent q hp n)

@[reassoc (attr := simp)] lemma ι_jjIntNatX (i j : ℤ) (n : ℕ) (h : i+j=(n:ℤ)) :
    (intJJDouble q hp).ιTotal (.down ℤ) i j (n:ℤ) h ≫ jjIntNatX q hp n =
      jjIntNatComponent q hp n i j h := by
  apply ι_totalDesc

end Tachikawa.Construction



end

end OAI
end


