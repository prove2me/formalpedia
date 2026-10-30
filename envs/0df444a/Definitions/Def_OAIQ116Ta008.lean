-- Prove2me | Definitions.Def_OAIQ116Ta008
-- name    : OAIQ116Ta008
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T01:42:32.936046+00:00
-- url     : https://prove2.me/theorems/45618629-7518-402b-a51f-48fafd8e5304
-- title:
--   Definitions bundle OAIQ116Ta008 of the split of OpenAI, A counterexample to Tachikawa's second conjecture
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Tachikawa.main_theorem`, carved from OpenAI's openai/math development (OpenAI, *A counterexample to Tachikawa's second conjecture*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 202 declarations of OpenAI's Lean: 98 definitions, 30 instances and 74 theorems. The definitions and types are `OAI.Tachikawa.Construction.S`, `OAI.Tachikawa.Construction.XTwistComparison`, `OAI.Tachikawa.Construction.bSimpleTensorUnderlying`, `OAI.Tachikawa.Construction.cSimpleCanon`, `OAI.Tachikawa.Construction.cSimpleUnderlying`, `OAI.Tachikawa.Construction.opTensorB`, `OAI.Tachikawa.Construction.opTensorE`, `OAI.Tachikawa.Construction.opTensorRestriction`, `OAI.Tachikawa.Construction.rho`, `OAI.Tachikawa.Construction.socleBimoduleLinear`, `OAI.Tachikawa.Construction.twistE`, `OAI.Tachikawa.Construction.zT`, `OAI.Tachikawa.Construction.zeta`, `OAI.Tachikawa.DownHom.evalClass`, `OAI.Tachikawa.DownHom.evalCycle`, `OAI.Tachikawa.DownHom.homologyDelta`, `OAI.Tachikawa.Enveloping.coindCoker`, `OAI.Tachikawa.Enveloping.coindEndo`, `OAI.Tachikawa.Enveloping.coindEvaluate`, `OAI.Tachikawa.Enveloping.coindExtend`, `OAI.Tachikawa.Enveloping.coindExtendLeft`, `OAI.Tachikawa.Enveloping.coindFunctor`, `OAI.Tachikawa.Enveloping.coindHomEquiv`, `OAI.Tachikawa.Enveloping.coindIterate`, `OAI.Tachikawa.Enveloping.coindMap`, `OAI.Tachikawa.Enveloping.coindObj`, `OAI.Tachikawa.Enveloping.coindShort`, `OAI.Tachikawa.Enveloping.coindTerm`, `OAI.Tachikawa.Enveloping.coindUnderlying`, `OAI.Tachikawa.Enveloping.coindUnit`, `OAI.Tachikawa.Enveloping.coindUnitNat`, `OAI.Tachikawa.Enveloping.coindπ`, `OAI.Tachikawa.Enveloping.dualLeftFinite`, `OAI.Tachikawa.Enveloping.dualLeftObj`, `OAI.Tachikawa.Enveloping.dualLeftUnderlying`, `OAI.Tachikawa.Enveloping.dualOuterEquiv`, `OAI.Tachikawa.Enveloping.dualOuterUnderlying`, `OAI.Tachikawa.Enveloping.dualRegularLeftEquiv`, `OAI.Tachikawa.Enveloping.dualRegularObj`, `OAI.Tachikawa.Enveloping.dualRegularUnderlying` and 58 more.
--
--   **Sources.** They come from these modules of lean/OAI/RingTheory, in whole or in part: `Tachikawa_Bimodule`, `Tachikawa_Coinduction`, `Tachikawa_CompleteTensor`, `Tachikawa_Delta`, `Tachikawa_DerivedDescent`, `Tachikawa_DerivedInduction`, `Tachikawa_DownHom`, `Tachikawa_FiniteCoinduction`, `Tachikawa_HomProfile`, `Tachikawa_Induction`, `Tachikawa_Nakayama`, `Tachikawa_Perfect`, `Tachikawa_RightInduction`, `Tachikawa_Socle`, `Tachikawa_StableDuality`, `Tachikawa_StableLift`, `Tachikawa_StableShift`, `Tachikawa_Twisting`.
--
--   **Imports.** It imports the bundles `OAIQ116Ta003`, `OAIQ116Ta004` and `OAIQ116Ta005` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ116Ta011` and `OAIQ116Ta012`.
-- source:
--   OpenAI, A counterexample to Tachikawa's second conjecture, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-counterexample-to-Tachikawas-second-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/RingTheory at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ116Ta003
import Definitions.Def_OAIQ116Ta004
import Definitions.Def_OAIQ116Ta005

section
-- module Solutions.OAIQ116_Tach.Tachikawa_StableDuality
attribute [-instance] _root_.OAI.Tachikawa.AlgebraInduction.instProjectiveCarrierObjModuleCatFunctorOfFinite _root_.OAI.Tachikawa.DownHom.instAddCommGroupCochain _root_.OAI.Tachikawa.DownHom.instModuleCochain _root_.OAI.Tachikawa.FiniteModule.instAddCommGroupCarrierObj _root_.OAI.Tachikawa.FiniteModule.instModuleCarrierObj _root_.OAI.Tachikawa.LeftCoinduced.coextend_additive _root_.OAI.Tachikawa.LeftCoinduced.coextend_preservesInjective _root_.OAI.Tachikawa.OuterTensor.restrictionPreservesHomology _root_.OAI.Tachikawa.TotalDualPairing.instFiniteDiag _root_.OAI.Tachikawa.TotalDualPairing.instTensorSignsNatUp_solutions _root_.OAI.Tachikawa.TotalMap.sourceHasCoproduct _root_.OAI.Tachikawa.Triangular.instProjectiveCarrierOneFree _root_.OAI.Tachikawa.downIntTensorSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace Tachikawa
variable {k R : Type} [Field k] [Ring R] [Algebra k R] [FiniteDimensional k R]
variable {M N : Type} [AddCommGroup M] [AddCommGroup N]
  [Module R M] [Module R N] [Module k N]
  [IsScalarTower k R N]
namespace SymmetrizingForm
variable (t : SymmetrizingForm (k := k) (R := R))
variable {n : ℕ} (ε : (Fin n → R) →ₗ[R] M)

lemma syzygyPair_vanish_left {m : ℕ} (i : M →ₗ[R] (Fin m → R))
    (hi : Function.Injective i) (g : N →ₗ[R] LinearMap.ker ε)
    (f : M →ₗ[R] N) (hf : f ∈ projectiveFactors (k := k)) :
    t.syzygyPair ε g f = 0 := by
  let : Module.Injective R R := t.injective
  obtain ⟨a, rfl⟩ := (factors_iff_extends i hi f).mp hf
  rw [syzygyPair_apply, LinearMap.comp_assoc, t.freeHomDual_cyclic_rect]
  have hzero : (i.comp ε).comp ((LinearMap.ker ε).subtype.comp g) = 0 := by
    apply LinearMap.ext
    intro x
    change i (ε (g x).val) = 0
    rw [(g x).property, map_zero]
  rw [hzero, map_zero, LinearMap.zero_apply]

def syzygyPairOnStable {m : ℕ} (i : M →ₗ[R] (Fin m → R))
    (hi : Function.Injective i) :
    (N →ₗ[R] LinearMap.ker ε) →ₗ[k]
      Module.Dual k (StableHom (k := k) (R := R) (M := M) (N := N)) where
  toFun g := (projectiveFactors (k := k)).liftQ (t.syzygyPair ε g)
    (by intro f hf; exact t.syzygyPair_vanish_left ε i hi g f hf)
  map_add' g h := by
    ext x
    obtain ⟨f, rfl⟩ := stableClass_surjective x
    change t.syzygyPair ε (g+h) f = t.syzygyPair ε g f + t.syzygyPair ε h f
    rw [map_add, LinearMap.add_apply]
  map_smul' c g := by
    ext x
    obtain ⟨f, rfl⟩ := stableClass_surjective x
    change t.syzygyPair ε (c • g) f = c • t.syzygyPair ε g f
    rw [map_smul, LinearMap.smul_apply]

def stableDualMap {m p : ℕ} (i : M →ₗ[R] (Fin m → R))
    (hi : Function.Injective i) (d : (Fin p → R) →ₗ[R] LinearMap.ker ε)
    (hd : Function.Surjective d) :
    StableHom (k := k) (R := R) (M := N) (N := LinearMap.ker ε) →ₗ[k]
      Module.Dual k (StableHom (k := k) (R := R) (M := M) (N := N)) :=
  (projectiveFactors (k := k)).liftQ (t.syzygyPairOnStable ε i hi)
    (by
      intro g hg
      ext x
      obtain ⟨f, rfl⟩ := stableClass_surjective x
      change t.syzygyPair ε g f = 0
      rw [t.syzygyPair_vanish_right ε d hd g hg, LinearMap.zero_apply])

lemma stableDualMap_injective (hε : Function.Surjective ε) {m p : ℕ}
    (i : M →ₗ[R] (Fin m → R)) (hi : Function.Injective i)
    (d : (Fin p → R) →ₗ[R] LinearMap.ker ε) (hd : Function.Surjective d) :
    Function.Injective (t.stableDualMap (N := N) ε i hi d hd) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  obtain ⟨g, rfl⟩ := stableClass_surjective x
  apply (stableClass_eq_zero_iff g).mpr
  apply (t.syzygyPair_eq_zero_iff ε hε d hd g).mp
  ext f
  exact LinearMap.congr_fun hx (stableClass (k := k) f)

lemma stableDualMap_surjective (hε : Function.Surjective ε) {m p : ℕ}
    (i : M →ₗ[R] (Fin m → R)) (hi : Function.Injective i)
    (d : (Fin p → R) →ₗ[R] LinearMap.ker ε) (hd : Function.Surjective d) :
    Function.Surjective (t.stableDualMap (N := N) ε i hi d hd) := by
  intro l
  have hinj : Function.Injective (homPrecompose (k := k) (N := N) ε) := by
    intro f g h
    apply LinearMap.ext
    intro x
    obtain ⟨y, rfl⟩ := hε x
    exact LinearMap.congr_fun h y
  obtain ⟨L, hL⟩ := LinearMap.dualMap_surjective_of_injective hinj
    (l.comp (stableClass (k := k)))
  obtain ⟨g₀, rfl⟩ := (t.freeHomDual (Fin n) (N := N)).surjective L
  have hzero : (i.comp ε).comp g₀ = 0 := by
    apply (t.freeHomDual (Fin m)).injective
    apply LinearMap.ext
    intro a
    rw [map_zero, LinearMap.zero_apply]
    rw [← t.freeHomDual_cyclic_rect]
    have ha := LinearMap.congr_fun hL (a.comp i)
    change t.freeHomDual (Fin n) g₀ ((a.comp i).comp ε) =
      l (stableClass (k := k) (a.comp i)) at ha
    rw [LinearMap.comp_assoc] at ha
    have hac : stableClass (k := k) (a.comp i) = 0 := by
      apply (stableClass_eq_zero_iff _).mpr
      exact ⟨ModuleCat.of R (Fin m → R), inferInstance, inferInstance, i, a, rfl⟩
    rw [ha, hac, map_zero]
  have hk (x : N) : g₀ x ∈ LinearMap.ker ε := by
    apply hi
    have hx := LinearMap.congr_fun hzero x
    simpa only [LinearMap.comp_apply, LinearMap.zero_apply, map_zero] using hx
  let g : N →ₗ[R] LinearMap.ker ε := g₀.codRestrict (LinearMap.ker ε) hk
  refine ⟨stableClass (k := k) g, ?_⟩
  apply LinearMap.ext
  intro x
  obtain ⟨f, rfl⟩ := stableClass_surjective x
  exact LinearMap.congr_fun hL f

def stableDualEquiv (hε : Function.Surjective ε) {m p : ℕ}
    (i : M →ₗ[R] (Fin m → R)) (hi : Function.Injective i)
    (d : (Fin p → R) →ₗ[R] LinearMap.ker ε) (hd : Function.Surjective d) :
    StableHom (k := k) (R := R) (M := N) (N := LinearMap.ker ε) ≃ₗ[k]
      Module.Dual k (StableHom (k := k) (R := R) (M := M) (N := N)) :=
  LinearEquiv.ofBijective (t.stableDualMap ε i hi d hd)
    ⟨t.stableDualMap_injective ε hε i hi d hd,
      t.stableDualMap_surjective ε hε i hi d hd⟩

end SymmetrizingForm
end Tachikawa



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_CompleteTensor
attribute [-instance] _root_.OAI.Tachikawa.DownHom.instAddCommGroupCochain _root_.OAI.Tachikawa.DownHom.instModuleCochain _root_.OAI.Tachikawa.LeftCoinduced.coextend_additive _root_.OAI.Tachikawa.LeftCoinduced.coextend_preservesInjective _root_.OAI.Tachikawa.OuterTensor.restrictionPreservesHomology _root_.OAI.Tachikawa.TotalDualPairing.instTensorSignsNatUp_solutions _root_.OAI.Tachikawa.TotalMap.sourceHasCoproduct _root_.OAI.Tachikawa.Triangular.instFiniteCarrierOneFree _root_.OAI.Tachikawa.downIntTensorSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace Tachikawa
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R] [FiniteDimensional k R]

namespace FiniteModule

variable (M : FiniteModule k R)

variable (t : SymmetrizingForm (k := k) (R := R))

lemma complete_exact : ComplexExact (M.complete t) := by
  suffices ∀ (j i : ℤ), i=j-1 →
      Function.Exact ((M.complete t).d (j+1) j) ((M.complete t).d j i) by
    exact fun j => this j (j-1) rfl
  intro j i hi
  have hj : j=i+1 := by omega
  subst j
  change Function.Exact (ChainComplex.of.d (M.term t) (M.differential t) (i+1+1) (i+1))
    (ChainComplex.of.d (M.term t) (M.differential t) (i+1) i)
  simp only [ChainComplex.of_d]
  exact M.differential_exact t i

lemma complete_projective (j : ℤ) : Module.Projective R ((M.complete t).X j) := by
  cases j <;> exact inferInstanceAs (Module.Projective R (Fin _ → R))

lemma complete_finite (j : ℤ) : Module.Finite R ((M.complete t).X j) := by
  cases j <;> exact inferInstanceAs (Module.Finite R (Fin _ → R))

def augmentation : CokerAt (M.complete t) 0 →ₗ[R] M :=
  CokerAt.descend _ _ M.cover.map (by
    rw [complete_d]
    apply LinearMap.ext
    intro x
    exact ((M.positive 1).cover.map x).property)

lemma augmentation_surjective : Function.Surjective (M.augmentation t) := by
  intro x
  obtain ⟨y, rfl⟩ := M.cover.surjective x
  exact ⟨CokerAt.π (M.complete t) 0 y, rfl⟩

lemma augmentation_injective : Function.Injective (M.augmentation t) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  obtain ⟨y, rfl⟩ := CokerAt.π_surjective (M.complete t) 0 x
  change M.cover.map y = 0 at hx
  obtain ⟨z, hz⟩ := (M.positive 1).cover.surjective ⟨y, hx⟩
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  use z
  rw [complete_d]
  exact congrArg Subtype.val hz

def cokerEquiv : CokerAt (M.complete t) 0 ≃ₗ[R] M :=
  LinearEquiv.ofBijective (M.augmentation t)
    ⟨M.augmentation_injective t, M.augmentation_surjective t⟩

lemma complete_totallyAcyclic : TotallyAcyclic (M.complete t) := by
  refine ⟨M.complete_exact t, ?_⟩
  intro j f hf
  let : Module.Injective R R := t.injective
  obtain ⟨g, hg⟩ := Module.Injective.extension_property R R
    (CokerAt (M.complete t) j) ((M.complete t).X (j-1))
    (CokerAt.ι (M.complete t) j) (CokerAt.ι_injective _ _ (M.complete_exact t j))
    (CokerAt.descend _ _ f hf)
  refine ⟨g, ?_⟩
  have hh := congrArg (fun a => a.comp (CokerAt.π (M.complete t) j)) hg
  simpa only [LinearMap.comp_assoc, CokerAt.ι_comp_π, CokerAt.descend_comp_π] using hh

end FiniteModule
end Tachikawa



namespace Tachikawa.FiniteModule
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R] [FiniteDimensional k R]
  (M : FiniteModule k R)

instance instFiniteCarrierXNatModuleCatComplexProjectiveResolution (n : ℕ) : Module.Finite R (M.projectiveResolution.complex.X n) := by
  change Module.Finite R (M.posTerm n)
  infer_instance

instance instFiniteDimensionalCarrierXNatModuleCatComplexProjectiveResolution (n : ℕ) : FiniteDimensional k (M.projectiveResolution.complex.X n) :=
  Module.Finite.trans R _

end Tachikawa.FiniteModule



namespace Tachikawa.Enveloping
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  (M : ModuleCat.{0} (Alg k S R))

abbrev tensorComplex (P : ChainComplex (ModuleCat.{0} R) ℤ) :=
  ((tensorFunctor M).mapHomologicalComplex (.down ℤ)).obj P

lemma tensorComplex_finite [FiniteDimensional k R] [FiniteDimensional k (Obj M)]
    (P : ChainComplex (ModuleCat.{0} R) ℤ) (fin : ∀ j, Module.Finite R (P.X j)) (j : ℤ) :
    Module.Finite S ((tensorComplex M P).X j) := by
  let := fin j
  let : FiniteDimensional k (P.X j) := Module.Finite.trans R _
  let : FiniteDimensional k ((tensorComplex M P).X j) := inferInstanceAs
    (FiniteDimensional k (BalancedTensor.T (k := k) (R := R) (S := S) (M := Obj M) (N := P.X j)))
  exact Module.Finite.of_restrictScalars_finite k _ _

lemma tensorComplex_projective [Module.Projective S (Obj M)]
    (P : ChainComplex (ModuleCat.{0} R) ℤ)
    (fin : ∀ j, Module.Finite R (P.X j)) (proj : ∀ j, Module.Projective R (P.X j)) (j : ℤ) :
    Module.Projective S ((tensorComplex M P).X j) := by
  let := fin j
  let := proj j
  exact BalancedTensor.map_projective (k := k) (R := R) (S := S) (M := Obj M) (N := P.X j)

variable [FiniteDimensional k R] [FiniteDimensional k (Obj M)]
  [Module.Projective Rᵐᵒᵖ (Obj M)]
  (N : FiniteModule k R) (t : SymmetrizingForm (k := k) (R := R))

omit [FiniteDimensional k R] [FiniteDimensional k (Obj M)] [Module.Projective Rᵐᵒᵖ (Obj M)] in
lemma tensor_map_surjective {X Y : ModuleCat R} (f : X ⟶ Y)
    (hf : Function.Surjective f) : Function.Surjective ((tensorFunctor M).map f) :=
  BalancedTensor.mapRight_surjective f.hom hf

end Tachikawa.Enveloping



namespace Tachikawa.Enveloping
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]

def tensorNatTrans {M M' : ModuleCat (Alg k R R)} (f : M ⟶ M') :
    tensorFunctor M ⟶ tensorFunctor M' where
  app X := evalMap X f
  naturality {X Y} g := by
    apply ModuleCat.hom_ext
    apply BalancedTensor.hom_ext
    intro m x
    rfl

end Tachikawa.Enveloping



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_StableShift
attribute [-instance] _root_.OAI.Tachikawa.DownHom.instAddCommGroupCochain _root_.OAI.Tachikawa.DownHom.instModuleCochain _root_.OAI.Tachikawa.LeftCoinduced.coextend_additive _root_.OAI.Tachikawa.LeftCoinduced.coextend_preservesInjective _root_.OAI.Tachikawa.OuterTensor.restrictionPreservesHomology _root_.OAI.Tachikawa.TotalDualPairing.instTensorSignsNatUp_solutions _root_.OAI.Tachikawa.TotalMap.sourceHasCoproduct _root_.OAI.Tachikawa.downIntTensorSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace Tachikawa
variable {k R M N P Q : Type} [Field k] [Ring R] [Algebra k R]
 [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [AddCommGroup Q]
 [Module R M] [Module R N] [Module R P] [Module R Q]
 [Module k N] [Module k Q]
 [IsScalarTower k R N] [IsScalarTower k R Q]

namespace StableShift
variable (ε : P →ₗ[R] M) (δ : Q →ₗ[R] N) (hδ : Function.Surjective δ)
 [Module.Projective R P]

variable [Module.Finite R P]

variable [Module.Finite R Q] [Module.Projective R Q]

variable [Module.Injective R R] (hε : Function.Surjective ε)

include hε in
lemma kernelMap_reflects_factors (f : M →ₗ[R] N)
    (hf : kernelMap (k := k) ε δ hδ f ∈ projectiveFactors (k := k)) :
    f ∈ projectiveFactors (k := k) := by
  obtain ⟨v,hv⟩ := (factors_iff_extends (k := k) (LinearMap.ker ε).subtype Subtype.val_injective _).mp hf
  let d := liftLinear (k := k) ε δ hδ f - (LinearMap.ker δ).subtype.comp v
  have hd : LinearMap.ker ε ≤ LinearMap.ker d := by
    intro x hx
    have hh := congrArg Subtype.val (LinearMap.congr_fun hv ⟨x,hx⟩)
    change (v x : Q) = liftLinear (k := k) ε δ hδ f x at hh
    change liftLinear (k := k) ε δ hδ f x - (v x : Q) = 0
    rw [hh,sub_self]
  obtain ⟨s,hs⟩ := linear_descent ε hε d hd
  apply (factors_iff_lifts δ hδ f).mpr
  refine ⟨s, ?_⟩
  apply LinearMap.ext
  intro x
  obtain ⟨y,rfl⟩ := hε x
  have h₁ := LinearMap.congr_fun hs y
  have h₂ := LinearMap.congr_fun (liftLinear_lifts (k := k) ε δ hδ f) y
  change s (ε y) = liftLinear (k := k) ε δ hδ f y - (v y : Q) at h₁
  change δ (s (ε y)) = f (ε y)
  rw [h₁,map_sub,(v y).property,sub_zero]
  exact h₂

include hε in
lemma map_injective : Function.Injective (map (k := k) ε δ hδ) := by
  apply (LinearMap.ker_eq_bot).mp
  apply eq_bot_iff.mpr
  intro x hx
  obtain ⟨f,rfl⟩ := stableClass_surjective x
  change stableClass (k := k) (kernelMap (k := k) ε δ hδ f) = 0 at hx
  exact (stableClass_eq_zero_iff _).mpr (kernelMap_reflects_factors (k := k) ε δ hδ hε f
    ((stableClass_eq_zero_iff _).mp hx))

include hε in
lemma map_surjective : Function.Surjective (map (k := k) ε δ hδ) := by
  let : Module.Injective R Q := injective_of_finite_projective
  intro x
  obtain ⟨g,rfl⟩ := stableClass_surjective x
  obtain ⟨h,hh⟩ := Module.Injective.extension_property R Q (LinearMap.ker ε) P
    (LinearMap.ker ε).subtype Subtype.val_injective ((LinearMap.ker δ).subtype.comp g)
  have hd : LinearMap.ker ε ≤ LinearMap.ker (δ.comp h) := by
    intro x hx
    have h₁ := LinearMap.congr_fun hh ⟨x,hx⟩
    change h x = (g ⟨x,hx⟩ : Q) at h₁
    change δ (h x) = 0
    rw [h₁]
    exact (g ⟨x,hx⟩).property
  obtain ⟨f,hf⟩ := linear_descent ε hε (δ.comp h) hd
  refine ⟨stableClass (k := k) f, ?_⟩
  exact kernelMap_class (k := k) ε δ hδ f g h hf.symm hh

def equiv : StableHom (k := k) (R := R) (M := M) (N := N) ≃ₗ[k]
    StableHom (k := k) (R := R) (M := LinearMap.ker ε) (N := LinearMap.ker δ) :=
  LinearEquiv.ofBijective (map (k := k) ε δ hδ)
    ⟨map_injective (k := k) ε δ hδ hε, map_surjective (k := k) ε δ hδ hε⟩

end StableShift
end Tachikawa



namespace Tachikawa
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
  (P : ChainComplex (ModuleCat.{0} R) ℤ)

def completeHomIso {M N : ModuleCat.{0} R} (e : M ≅ N) (a : ℤ) :
    VectorSplit.H (completeHom (k := k) P M) a ≃ₗ[k]
    VectorSplit.H (completeHom (k := k) P N) a :=
  LinearEquiv.ofLinearMap (completeHmap P e.hom a) (completeHmap P e.inv a)
    (by rw [← completeHmap_comp,e.inv_hom_id,completeHmap_id])
    (by rw [← completeHmap_comp,e.hom_inv_id,completeHmap_id])
end Tachikawa



namespace Tachikawa
open CategoryTheory HomologicalComplex
open scoped ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  (F : ModuleCat.{0} R ⥤ ModuleCat.{0} S) [F.Additive] [F.Linear k]
  (P : ChainComplex (ModuleCat.{0} R) ℤ) (Q : ChainComplex (ModuleCat.{0} S) ℤ)
  (X : ModuleCat.{0} R)
  (l : Q ⟶ (F.mapHomologicalComplex (.down ℤ)).obj P)

def completeFunctorHom : completeHom (k := k) P X ⟶ completeHom Q (F.obj X) where
  f a := ModuleCat.ofHom (show (P.X a ⟶ X) →ₗ[k] (Q.X a ⟶ F.obj X) from
    { toFun := fun g => l.f a ≫ F.map g
      map_add' := fun g h => by
        rw [F.map_add]; exact Preadditive.comp_add _ _ _ _ _ _
      map_smul' := fun c g => by
        rw [F.map_smul]; exact Linear.comp_smul _ _ _ _ _ _ })
  comm' a b _ := by
    ext g
    change P.X a ⟶ X at g
    change Q.d b a ≫ l.f a ≫ F.map g = l.f b ≫ F.map (P.d b a ≫ g)
    erw [F.map_comp,← Category.assoc,← Category.assoc]
    exact congrArg (fun z => z ≫ F.map g) (l.comm b a).symm

end Tachikawa



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Twisting
attribute [-instance] _root_.OAI.Tachikawa.DownHom.instAddCommGroupCochain _root_.OAI.Tachikawa.LeftCoinduced.coextend_additive _root_.OAI.Tachikawa.LeftCoinduced.coextend_preservesInjective _root_.OAI.Tachikawa.OuterTensor.restrictionPreservesHomology _root_.OAI.Tachikawa.TotalDualPairing.instTensorSignsNatUp_solutions _root_.OAI.Tachikawa.TotalMap.sourceHasCoproduct _root_.OAI.Tachikawa.downIntTensorSigns
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

def regularLeftEquiv : Obj (regular (k := k) (R := R)) ≃ₗ[R] R where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r x := by
    change r * ((show R from x) * 1) = r * (show R from x)
    rw [mul_one]

end Tachikawa.Enveloping



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Nakayama
attribute [-instance] _root_.OAI.Tachikawa.DownHom.instAddCommGroupCochain _root_.OAI.Tachikawa.DownHom.instModuleCochain _root_.OAI.Tachikawa.LeftCoinduced.coextend_additive _root_.OAI.Tachikawa.LeftCoinduced.coextend_preservesInjective _root_.OAI.Tachikawa.downIntTensorSigns
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

lemma coevaluation_natural_right {Z' : Type} [AddCommGroup Z'] [Module R Z']
    [Module k Z'] [IsScalarTower k R Z'] (f : Z' →ₗ[R] Z) (ψ : Module.Dual k (P →ₗ[R] Z)) :
    (coevaluation ψ).comp f = coevaluation (ψ.comp (LinearMap.compRight k f)) := by
  ext z a
  change ψ (rankOne a (f z)) = ψ (f.comp (rankOne a z))
  congr 1
  ext p
  exact (f.map_smul _ _).symm

end Nakayama
end Tachikawa



namespace Tachikawa
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
namespace Nakayama

variable {P Q Z : Type} [AddCommGroup P] [Module R P]
  [AddCommGroup Q] [Module R Q] [AddCommGroup Z] [Module R Z]

lemma homPrecomp_exact (f : P →ₗ[R] Q) (g : Q →ₗ[R] Z)
    (h : Function.Exact f g) (hg : Function.Surjective g) :
    Function.Exact (homPrecomp (k := k) (Z := R) g) (homPrecomp (k := k) f) := by
  intro a
  change a.comp f = 0 ↔ ∃ b : Z →ₗ[R] R, b.comp g = a
  constructor
  · intro ha
    have hk : LinearMap.ker g ≤ LinearMap.ker a := by
      intro q hq
      obtain ⟨p, rfl⟩ := (h q).mp hq
      exact LinearMap.congr_fun ha p
    let b := (g.ker.liftQ a hk).comp (g.quotKerEquivOfSurjective hg).symm.toLinearMap
    refine ⟨b, ?_⟩
    ext q
    change g.ker.liftQ a hk ((g.quotKerEquivOfSurjective hg).symm (g q)) = a q
    rw [LinearMap.quotKerEquivOfSurjective_symm_apply]
    rfl
  · rintro ⟨b, rfl⟩
    rw [LinearMap.comp_assoc, h.linearMap_comp_eq_zero, LinearMap.comp_zero]

end Nakayama
end Tachikawa



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Socle
attribute [-instance] _root_.OAI.Tachikawa.AlgebraInduction.resFinite _root_.OAI.Tachikawa.DownHom.instAddCommGroupCochain _root_.OAI.Tachikawa.DownHom.instModuleCochain _root_.OAI.Tachikawa.LeftCoinduced.coextend_additive _root_.OAI.Tachikawa.LeftCoinduced.coextend_preservesInjective _root_.OAI.Tachikawa.downIntTensorSigns
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

instance instIsScalarTowerEX : IsScalarTower k (E q) (X q) :=
  IsScalarTower.of_algebraMap_smul (R := k) (A := E q) (M := X q) fun r x => by
    change (characterE q (algebraMap k (E q) r)) • x = r • x
    rw [AlgHom.commutes]
    rfl

end Construction
end Tachikawa



namespace Tachikawa.Construction
open scoped TensorProduct
variable {k : Type} [Field k] (q : k)

def zT : T q := TrivSqZeroExt.inr ((C.character q).toLinearMap : DualBimodule k (C k q))
def zeta : E q := zT q ⊗ₜ[k] zT q

lemma zT_left (a : T q) : a * zT q = characterT q a • zT q := by
  apply TrivSqZeroExt.ext
  · change a.fst * 0 = characterT q a • (0 : C k q)
    simp
  · apply LinearMap.ext; intro c
    change (C.character q) (c*a.fst) + a.snd ((0:C k q)*c) =
      characterT q a * C.character q c
    simp only [map_mul,zero_mul,map_zero,add_zero]
    exact mul_comm _ _

lemma zT_right (a : T q) : zT q * a = characterT q a • zT q := by
  apply TrivSqZeroExt.ext
  · change 0 * a.fst = characterT q a • (0 : C k q)
    simp
  · apply LinearMap.ext; intro c
    change a.snd (c*(0:C k q)) + (C.character q) (a.fst*c) =
      characterT q a * C.character q c
    simp only [mul_zero,map_zero,zero_add,map_mul]
    rfl

lemma zeta_left (a : E q) : a * zeta q = characterE q a • zeta q := by
  induction a using OAI.tensorInductionOn with
  | add a b ha hb => simp only [add_mul,map_add,add_smul,ha,hb]
  | tmul a b =>
    rw [zeta,Algebra.TensorProduct.tmul_mul_tmul]
    change (a*zT q) ⊗ₜ[k] (b*zT q) = (characterT q a * characterT q b) • (zT q ⊗ₜ[k] zT q)
    rw [zT_left,zT_left,TensorProduct.smul_tmul_smul]

lemma zeta_right (a : E q) : zeta q * a = characterE q a • zeta q := by
  induction a using OAI.tensorInductionOn with
  | add a b ha hb => simp only [mul_add,map_add,add_smul,ha,hb]
  | tmul a b =>
    rw [zeta,Algebra.TensorProduct.tmul_mul_tmul]
    change (zT q*a) ⊗ₜ[k] (zT q*b) = (characterT q a * characterT q b) • (zT q ⊗ₜ[k] zT q)
    rw [zT_right,zT_right,TensorProduct.smul_tmul_smul]

end Tachikawa.Construction



namespace Tachikawa.Construction
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k : Type} [Field k] (q H : k) (hH : H ≠ 0)

abbrev twistE : ModuleCat (E q) ⥤ ModuleCat (E q) :=
  AlgebraInduction.res (sigma q H hH).symm.toAlgHom

def XTwistComparison : (twistE q H hH).obj (ModuleCat.of (E q) (X q)) ⟶
    ModuleCat.of (E q) (X q) := ModuleCat.ofHom
  (X := (twistE q H hH).obj (ModuleCat.of (E q) (X q)))
  (Y := ModuleCat.of (E q) (X q)) {
  toFun := id
  map_add' _ _ := rfl
  map_smul' a x := by
    change characterE q ((sigma q H hH).symm a) * (show k from x) =
      characterE q a * (show k from x)
    have hc := characterE_sigma q H hH ((sigma q H hH).symm a)
    rw [AlgEquiv.apply_symm_apply] at hc
    rw [hc] }

end Tachikawa.Construction



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Bimodule
attribute [-instance] _root_.OAI.Tachikawa.DownHom.instAddCommGroupCochain _root_.OAI.Tachikawa.LeftCoinduced.coextend_additive _root_.OAI.Tachikawa.LeftCoinduced.coextend_preservesInjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace Tachikawa.HomBimodule
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  (X : ModuleCat R) {Z Z' : ModuleCat S}

lemma postMap_surjective (g : Z ⟶ Z') (hg : Function.Surjective g) :
    Function.Surjective (postMap (k := k) X g) := by
  intro f
  obtain ⟨p, hp⟩ := Module.projective_lifting_property (g.hom.restrictScalars k)
    (show X →ₗ[k] Z' from f) hg
  refine ⟨p, ?_⟩
  exact hp

instance instEpiModuleCatAlgPostMap (g : Z ⟶ Z') [Epi g] : Epi (postMap (k := k) X g) :=
  (ModuleCat.epi_iff_surjective _).mpr (postMap_surjective X g ((ModuleCat.epi_iff_surjective g).mp inferInstance))

end Tachikawa.HomBimodule



namespace Tachikawa
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  (X : ModuleCat.{0} R)

def homBimoduleFunctor : ModuleCat.{0} S ⥤ ModuleCat.{0} (Enveloping.Alg k S R) where
  obj Z := HomBimodule.obj (k := k) X Z
  map g := HomBimodule.postMap X g
  map_id Z := by ext f; rfl
  map_comp g h := by ext f; rfl

end Tachikawa



namespace Tachikawa.Enveloping
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]

lemma leftFunctor_eq : leftFunctor (k := k) (R := R) (S := S) =
    ModuleCat.restrictScalars (Algebra.TensorProduct.includeLeft : R →ₐ[k] Alg k R S).toRingHom := rfl

end Tachikawa.Enveloping

end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_RightInduction
attribute [-instance] _root_.OAI.Tachikawa.DownHom.instAddCommGroupCochain _root_.OAI.Tachikawa.DownHom.instModuleCochain _root_.OAI.Tachikawa.LeftCoinduced.coextend_additive _root_.OAI.Tachikawa.LeftCoinduced.coextend_preservesInjective
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
  (X : ModuleCat R)

instance instAdditiveModuleCatMulOppositeRightEvaluation : (rightEvaluation (k := k) X).Additive where
  map_add {M N f g} := by
    apply ModuleCat.hom_ext
    apply BalancedTensor.hom_ext
    intro m x
    change BalancedTensor.mk (k := k) (R := R) (S := k) ((f m) + (g m)) x = _
    exact congrArg (fun h : X →ₗ[k] _ => h x) ((BalancedTensor.mk (k := k) (R := R)
      (S := k) (M := N) (N := X)).map_add (f m) (g m))

def evalScalarEquiv (M : ModuleCat (Alg k S R)) :
    (ModuleCat.restrictScalars (algebraMap k S)).obj (evalObj X M) ≃ₗ[k] evalType X M where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c x := by
    change (algebraMap k S c) • (show evalType X M from x) = c • (show evalType X M from x)
    exact IsScalarTower.algebraMap_smul S c (show evalType X M from x)

def rightEvaluationComparisonIso (M : ModuleCat (Alg k S R)) :
    (ModuleCat.restrictScalars (algebraMap k S)).obj (evalObj X M) ≅
      (rightEvaluation (k := k) X).obj (rightFunctor.obj M) :=
  LinearEquiv.toModuleIso ((evalScalarEquiv X M).trans (rightEvaluationEquiv (k := k) X M))

def rightEvaluationComparison :
    evaluation (k := k) (S := S) X ⋙ ModuleCat.restrictScalars (algebraMap k S) ≅
      rightFunctor (k := k) (R := S) (S := R) ⋙ rightEvaluation (k := k) X :=
  NatIso.ofComponents (rightEvaluationComparisonIso X) (by
    intro M N f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change rightEvaluationEquiv X N
      (BalancedTensor.mapLeft (k := k) (R := R) (S := S) (N := X)
        (leftMap f) (fun r m => (rightMap f).map_smul r m) (show evalType X M from x)) =
      ((rightEvaluation (k := k) X).map (rightFunctor.map f)).hom
        (rightEvaluationEquiv X M x)
    induction (show evalType X M from x) using BalancedTensor.induction_on with
    | h0 => simp only [map_zero]
    | ht m y => rfl
    | ha x y hx hy => simp only [map_add, hx, hy])

end Tachikawa.Enveloping



namespace Tachikawa.Enveloping
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R] (X : ModuleCat R)

def regularEvalBilinear : Obj (regular (k := k) (R := R)) →ₗ[R] X →ₗ[k] X where
  toFun m :=
    { toFun := fun x => regularLeftEquiv m • x
      map_add' := fun x y => smul_add _ x y
      map_smul' := fun c x => smul_comm _ c x }
  map_add' m n := by ext x; exact add_smul _ _ x
  map_smul' r m := by
    ext x
    change (regularLeftEquiv (r • m)) • x = r • (regularLeftEquiv m • x)
    rw [map_smul,smul_eq_mul,mul_smul]

def regularEval : evalObj X (regular (k := k) (R := R)) ⟶ X :=
  ModuleCat.ofHom (BalancedTensor.lift (regularEvalBilinear X) (by
    intro r m x
    change (1 * ((show R from m) * r)) • x = (show R from m) • (r • x)
    rw [one_mul,mul_smul]))

lemma regularTensor_move (r : R) (x : X) :
    BalancedTensor.mk (k := k) (R := R) (S := R)
      (M := Obj (regular (k := k) (R := R))) (N := X)
      (show Obj (regular (k := k) (R := R)) from r) x =
    BalancedTensor.mk (show Obj (regular (k := k) (R := R)) from (1:R)) (r • x) := by
  have hb := BalancedTensor.balance (k := k) (S := R)
    (M := Obj (regular (k := k) (R := R))) (N := X) r
    (show Obj (regular (k := k) (R := R)) from (1:R)) x
  have hm : MulOpposite.op r • (show Obj (regular (k := k) (R := R)) from (1:R)) =
      (show Obj (regular (k := k) (R := R)) from r) := by
    change 1 * (1 * r) = r
    rw [one_mul,one_mul]
  rw [hm] at hb
  exact hb

def regularEvalInv : X ⟶ evalObj X (regular (k := k) (R := R)) :=
  ModuleCat.ofHom
    { toFun := fun x => BalancedTensor.mk (show Obj (regular (k := k) (R := R)) from (1:R)) x
      map_add' := fun x y => map_add _ x y
      map_smul' := fun r x => by
        change BalancedTensor.mk (show Obj (regular (k := k) (R := R)) from (1:R)) (r • x) =
          r • BalancedTensor.mk (show Obj (regular (k := k) (R := R)) from (1:R)) x
        rw [← regularTensor_move X r x]
        have hm : r • (show Obj (regular (k := k) (R := R)) from (1:R)) =
            (show Obj (regular (k := k) (R := R)) from r) := by
          change r * (1 * 1) = r
          rw [one_mul,mul_one]
        conv_lhs => rw [← hm]
        rw [LinearMap.map_smul]
        rfl }

def regularEvalIso : evalObj X (regular (k := k) (R := R)) ≅ X where
  hom := regularEval X
  inv := regularEvalInv X
  hom_inv_id := by
    apply ModuleCat.hom_ext
    apply BalancedTensor.hom_ext
    intro m x
    change BalancedTensor.mk (show Obj (regular (k := k) (R := R)) from (1:R))
      ((show R from m) • x) = BalancedTensor.mk m x
    exact (regularTensor_move X (show R from m) x).symm
  inv_hom_id := by
    apply ModuleCat.hom_ext
    ext x
    change (1:R) • x = x
    exact one_smul R x

end Tachikawa.Enveloping



namespace Tachikawa.Enveloping
open CategoryTheory HomologicalComplex
open scoped TensorProduct ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  [FiniteDimensional k R] [FiniteDimensional k S]

instance regular_left_projective : Module.Projective R (Obj (regular (k := k) (R := R))) :=
  Module.Projective.of_equiv (regularLeftEquiv (k := k) (R := R)).symm

instance leftFunctor_reflectsIsomorphisms :
    (leftFunctor (k := k) (R := R) (S := S)).ReflectsIsomorphisms := by
  rw [leftFunctor_eq]
  infer_instance

end Tachikawa.Enveloping



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Coinduction
attribute [-instance] _root_.OAI.Tachikawa.AlgebraInduction.resFinite _root_.OAI.Tachikawa.DownHom.instAddCommGroupCochain _root_.OAI.Tachikawa.DownHom.instModuleCochain _root_.OAI.Tachikawa.Triangular.instFiniteCarrierOneFree
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

instance instProjectiveMulOppositeC : Module.Projective (C k q)ᵐᵒᵖ (C k q) :=
  Module.Projective.of_equiv (MulOpposite.opLinearEquiv (C k q)ᵐᵒᵖ).symm
instance instFiniteMulOppositeC : Module.Finite (C k q)ᵐᵒᵖ (C k q) :=
  Module.Finite.equiv (MulOpposite.opLinearEquiv (C k q)ᵐᵒᵖ).symm
instance instFiniteMulOppositeCSubtypeMemSubmoduleEC : Module.Finite (C k q)ᵐᵒᵖ (C.eC q) :=
  Module.Finite.of_surjective (RightCorner.projection (C.e_idempotent q))
    (fun a => ⟨a.val, Subtype.ext a.property⟩)
instance instFiniteMulOppositeCSubtypeMemSubmoduleFC : Module.Finite (C k q)ᵐᵒᵖ (C.fC q) :=
  Module.Finite.of_surjective (RightCorner.projection (C.f_idempotent q))
    (fun a => ⟨a.val, Subtype.ext a.property⟩)

end Tachikawa.Construction



namespace Tachikawa.Construction
open CategoryTheory HomologicalComplex
open scoped TensorProduct ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q : k)

omit [CharP k 2] in
lemma cResObj_finite (n : ℕ) : Module.Finite (C k q) (C.resObj q n) := by
  cases n with
  | zero =>
    let : Module.Finite k (C.Cf q) := Module.Finite.of_injective
      ((C.Cf q).subtype.restrictScalars k) Subtype.val_injective
    exact Module.Finite.of_restrictScalars_finite k (C k q) (C.Cf q)
  | succ n =>
    let : Module.Finite k (C.Ce q) := Module.Finite.of_injective
      ((C.Ce q).subtype.restrictScalars k) Subtype.val_injective
    exact Module.Finite.of_restrictScalars_finite k (C k q) (C.Ce q)

end Tachikawa.Construction



namespace Tachikawa.Construction
open CategoryTheory
open scoped ModuleCat.Algebra

variable {k : Type} [Field k] (q H : k) (hH : H ≠ 0)

abbrev S := HomBimodule.obj (k := k) (ModuleCat.of (E q) (X q)) (ModuleCat.of (E q) (X q))

def socleBimoduleLinear :
    HomBimodule.Base (k := k) (ModuleCat.of (E q) (X q)) (ModuleCat.of (E q) (X q)) →ₗ[E q]
      AlgebraInduction.Bimod (sigma q H hH).toAlgHom where
  toFun f := (show k from f (show X q from (1:k))) • zeta q
  map_add' f g := add_smul _ _ _
  map_smul' a f := by
    change (characterE q a * (show k from f (show X q from (1:k)))) • zeta q =
      a * ((show k from f (show X q from (1:k))) • zeta q)
    rw [mul_smul_comm, zeta_left, smul_smul, mul_comm]

end Tachikawa.Construction



namespace Tachikawa.LeftCoinduced
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]

lemma iterate_injective (M : ModuleCat R) (d : ℕ) [HasInjectiveDimensionLE M d] :
    Injective ((iterate (k := k) d).obj M) := by
  let : HasInjectiveDimensionLE M (0+d) := by simpa using (inferInstance : HasInjectiveDimensionLE M d)
  let := iterate_dimension (k := k) M 0 d
  exact inferInstance

end Tachikawa.LeftCoinduced



namespace Tachikawa.Enveloping
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]

def coindObj (N : ModuleCat Sᵐᵒᵖ) : ModuleCat (Alg k R S) :=
  ofBimodule (k := k) (R := R) (S := S) (Coind (k := k) (R := R) N)

def coindUnderlying (N : ModuleCat Sᵐᵒᵖ) : coindObj (k := k) (R := R) N ≃ₗ[k] (R →ₗ[k] N) where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c f := by
    change (action (k := k) (R := R) (S := S) (Coind (k := k) (R := R) N)
      (algebraMap k (Alg k R S) c)) f = c • (show R →ₗ[k] N from f)
    rw [AlgHom.commutes]
    rfl

instance instFiniteDimensionalCarrierAlgCoindObjOfMulOpposite (N : ModuleCat Sᵐᵒᵖ) [FiniteDimensional k R] [FiniteDimensional k N] :
    FiniteDimensional k (coindObj (k := k) (R := R) N) :=
  Module.Finite.equiv (coindUnderlying (k := k) (R := R) N).symm

variable (Q : ModuleCat (Alg k R S)) (N : ModuleCat Sᵐᵒᵖ)

def coindEvaluate (f : Q ⟶ coindObj (k := k) (R := R) N) : Obj Q →ₗ[Sᵐᵒᵖ] N where
  toFun x := (show R →ₗ[k] N from f x) 1
  map_add' x y := by
    erw [map_add]; rfl
  map_smul' s x := by
    have h := f.hom.map_smul ((1:R) ⊗ₜ[k] s) x
    change (show R →ₗ[k] N from f (((1:R) ⊗ₜ[k] s) • x)) 1 = s • _
    erw [h]
    change s • (show R →ₗ[k] N from f x) (1*1) = s • _
    rw [mul_one]

def coindExtendLeft (g : Obj Q →ₗ[Sᵐᵒᵖ] N) : Obj Q →ₗ[R] Coind (k := k) (R := R) N where
  toFun x :=
    { toFun := fun r => g (r • x)
      map_add' r s := by rw [add_smul,map_add]
      map_smul' c r := by
        change (g.restrictScalars k) ((c • r) • x) = c • g (r • x)
        rw [smul_assoc,map_smul]
        rfl }
  map_add' x y := by apply LinearMap.ext; intro r; change g (r • (x+y)) = _; rw [smul_add,map_add]; rfl
  map_smul' a x := by
    apply LinearMap.ext; intro r; change g (r • a • x) = g ((r*a) • x); rw [mul_smul]

lemma coindExtendLeft_right (g : Obj Q →ₗ[Sᵐᵒᵖ] N) (s : Sᵐᵒᵖ) (x : Obj Q) :
    coindExtendLeft Q N g (s • x) = s • coindExtendLeft Q N g x := by
  apply LinearMap.ext; intro r
  change g (r • s • x) = s • g (r • x)
  rw [smul_comm,map_smul]

def coindExtend (g : Obj Q →ₗ[Sᵐᵒᵖ] N) : Q ⟶ coindObj (k := k) (R := R) N :=
  (reassembleIso Q).inv ≫ ofBimoduleHom (coindExtendLeft Q N g) (coindExtendLeft_right Q N g)

lemma coindEvaluate_extend (g : Obj Q →ₗ[Sᵐᵒᵖ] N) :
    coindEvaluate Q N (coindExtend Q N g) = g := by
  ext x
  change g ((1:R) • x) = g x
  rw [one_smul]

lemma coindExtend_evaluate (f : Q ⟶ coindObj (k := k) (R := R) N) :
    coindExtend Q N (coindEvaluate Q N f) = f := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext; intro x
  apply LinearMap.ext; intro r
  change (show R →ₗ[k] N from f (((r ⊗ₜ[k] (1:Sᵐᵒᵖ)) : Alg k R S) • x)) 1 =
    (show R →ₗ[k] N from f x) r
  rw [f.hom.map_smul]
  change (1:Sᵐᵒᵖ) • (show R →ₗ[k] N from f x) (1*r) = _
  rw [one_smul,one_mul]

def coindHomEquiv : (Q ⟶ coindObj (k := k) (R := R) N) ≃ₗ[k] (Obj Q →ₗ[Sᵐᵒᵖ] N) where
  toFun := coindEvaluate Q N
  invFun := coindExtend Q N
  left_inv := coindExtend_evaluate Q N
  right_inv := coindEvaluate_extend Q N
  map_add' f g := by ext x; rfl
  map_smul' c f := by
    ext x
    change (coindUnderlying (k := k) (R := R) N ((c • f) x)) 1 = c • _
    change (coindUnderlying (k := k) (R := R) N (c • f x)) 1 = c • _
    rw [map_smul]
    rfl

lemma coindEvaluate_natural {Q' : ModuleCat (Alg k R S)}
    (a : Q' ⟶ Q) (f : Q ⟶ coindObj (k := k) (R := R) N) :
    coindEvaluate Q' N (a ≫ f) = (coindEvaluate Q N f).comp (rightMap a) := rfl

end Tachikawa.Enveloping



namespace Tachikawa.Enveloping
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]

def coindMap {N N' : ModuleCat Sᵐᵒᵖ} (a : N ⟶ N') :
    coindObj (k := k) (R := R) N ⟶ coindObj (k := k) (R := R) N' :=
  ofBimoduleHom
    { toFun := fun f => (a.hom.restrictScalars k).comp (show R →ₗ[k] N from f)
      map_add' f g := by apply LinearMap.ext; intro x; exact map_add a.hom _ _
      map_smul' r f := by apply LinearMap.ext; intro x; rfl }
    (fun s f => by apply LinearMap.ext; intro x; exact a.hom.map_smul s (f x))

def coindFunctor : ModuleCat Sᵐᵒᵖ ⥤ ModuleCat (Alg k R S) where
  obj := coindObj (k := k) (R := R)
  map := coindMap
  map_id N := by apply ModuleCat.hom_ext; apply LinearMap.ext; intro f; apply LinearMap.ext; intro r; rfl
  map_comp a b := by apply ModuleCat.hom_ext; apply LinearMap.ext; intro f; apply LinearMap.ext; intro r; rfl

instance instAdditiveModuleCatMulOppositeAlgCoindFunctor : (coindFunctor (k := k) (R := R) (S := S)).Additive where
  map_add := by intros; apply ModuleCat.hom_ext; apply LinearMap.ext; intro f; apply LinearMap.ext; intro r; rfl

def coindEndo : ModuleCat (Alg k R S) ⥤ ModuleCat (Alg k R S) :=
  rightFunctor ⋙ coindFunctor

def coindUnit (L : ModuleCat (Alg k R S)) : L ⟶ (coindEndo (k := k)).obj L :=
  coindExtend L ((rightFunctor (k := k) (R := R) (S := S)).obj L) LinearMap.id

lemma coindUnit_injective (L : ModuleCat (Alg k R S)) : Function.Injective (coindUnit (k := k) L) := by
  intro x y h
  have h' := congrArg (fun f => coindUnderlying _ f (1:R)) h
  change (1:R) • (show Obj L from x) = (1:R) • (show Obj L from y) at h'
  change (show Obj L from x) = (show Obj L from y)
  exact (one_smul R (show Obj L from x)).symm.trans
    (h'.trans (one_smul R (show Obj L from y)))

instance instMonoModuleCatAlgCoindUnit (L : ModuleCat (Alg k R S)) : Mono (coindUnit (k := k) L) :=
  (ModuleCat.mono_iff_injective _).2 (coindUnit_injective L)

def coindUnitNat : 𝟭 (ModuleCat (Alg k R S)) ⟶ coindEndo where
  app := coindUnit
  naturality {L L'} f := by
    apply ModuleCat.hom_ext; apply LinearMap.ext; intro z
    apply LinearMap.ext; intro r
    change r • (show Obj L' from f z) = leftMap f (r • (show Obj L from z))
    exact ((leftMap f).map_smul r z).symm

def coindCoker : ModuleCat (Alg k R S) ⥤ ModuleCat (Alg k R S) :=
  cokernel (coindUnitNat (k := k) (R := R) (S := S))

def coindIterate : ℕ → ModuleCat (Alg k R S) ⥤ ModuleCat (Alg k R S)
  | 0 => 𝟭 _
  | n+1 => coindIterate n ⋙ coindCoker




instance instMonoFunctorModuleCatAlgCoindUnitNat : Mono (coindUnitNat (k := k) (R := R) (S := S)) := by
  let (L : ModuleCat (Alg k R S)) : Mono (coindUnitNat.app L) :=
    inferInstanceAs (Mono (coindUnit L))
  exact NatTrans.mono_of_mono_app _

def coindπ (L : ModuleCat (Alg k R S)) :
    (coindEndo (k := k)).obj L ⟶ (coindCoker (k := k)).obj L :=
  (cokernel.π (coindUnitNat (k := k))).app L

instance instEpiModuleCatAlgCoindπ (L : ModuleCat (Alg k R S)) : Epi (coindπ (k := k) L) :=
  inferInstanceAs (Epi ((cokernel.π (coindUnitNat (k := k))).app L))

lemma coindUnit_π (L : ModuleCat (Alg k R S)) :
    coindUnit L ≫ coindπ L = 0 := by
  exact congrArg (fun f => f.app L) (cokernel.condition (coindUnitNat (k := k)))

def coindShort (L : ModuleCat (Alg k R S)) : ShortComplex (ModuleCat (Alg k R S)) :=
  ShortComplex.mk (coindUnit L) (coindπ L) (coindUnit_π L)

lemma coindShort_exact (L : ModuleCat (Alg k R S)) : (coindShort (k := k) L).ShortExact := by
  let T : ShortComplex (ModuleCat (Alg k R S) ⥤ ModuleCat (Alg k R S)) :=
    ShortComplex.mk coindUnitNat (cokernel.π _) (cokernel.condition _)
  have hT : T.ShortExact := { exact := ShortComplex.exact_cokernel _ }
  exact hT.map ((CategoryTheory.evaluation _ _).obj L)

variable [FiniteDimensional k R]
instance coindObj_finite (N : ModuleCat Sᵐᵒᵖ) [FiniteDimensional k N] :
    FiniteDimensional k (coindObj (k := k) (R := R) N) :=
  Module.Finite.equiv (coindUnderlying N).symm

instance rightFunctor_finite (L : ModuleCat (Alg k R S)) [FiniteDimensional k L] :
    FiniteDimensional k ((rightFunctor (k := k)).obj L) :=
  Module.Finite.equiv (moduleCatUnderlyingEquiv (k := k) (R := Sᵐᵒᵖ) (Obj L)).symm

instance coindEndo_finite (L : ModuleCat (Alg k R S)) [FiniteDimensional k L] :
    FiniteDimensional k ((coindEndo (k := k)).obj L) :=
  inferInstanceAs (FiniteDimensional k (coindObj (k := k) (R := R) ((rightFunctor (k := k)).obj L)))

def coindTerm (L : ModuleCat (Alg k R S)) (n : ℕ) : ModuleCat (Alg k R S) :=
  (coindEndo (k := k)).obj ((coindIterate n).obj L)

end Tachikawa.Enveloping



namespace Tachikawa.Enveloping
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]

variable (L : ModuleCat R) (Q : ModuleCat (Alg k R S))

def rightFreeBilinear (g : L →ₗ[R] Obj Q) : L →ₗ[k] rightRegularObj (S := S) →ₗ[k] Obj Q where
  toFun x :=
    { toFun := fun s => (show Sᵐᵒᵖ from s) • g x
      map_add' s t := add_smul _ _ _
      map_smul' c s := by
        change ((algebraMap k Sᵐᵒᵖ c) * (show Sᵐᵒᵖ from s)) • g x = c • ((show Sᵐᵒᵖ from s) • g x)
        rw [mul_smul,IsScalarTower.algebraMap_smul] }
  map_add' x y := by ext s; change (show Sᵐᵒᵖ from s) • g (x+y) = _; rw [map_add,smul_add]; rfl
  map_smul' c x := by
    ext s
    change (show Sᵐᵒᵖ from s) • g (c • x) = c • (show Sᵐᵒᵖ from s) • g x
    rw [g.map_smul_of_tower,smul_comm]

end Tachikawa.Enveloping



namespace Tachikawa.Enveloping
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  [FiniteDimensional k R] [FiniteDimensional k S]
  (M : FiniteModule k (Alg k R S))

def rightResolution : ProjectiveResolution (ModuleCat.of Sᵐᵒᵖ (Obj M.obj)) :=
  resolutionOfExact _ (fun n => ModuleCat.of Sᵐᵒᵖ (Obj (ModuleCat.of (Alg k R S) (M.posTerm n))))
    (fun n => ModuleCat.ofHom (rightMap (ModuleCat.ofHom (M.posDifferential n))))
    (ModuleCat.ofHom (rightMap (ModuleCat.ofHom M.cover.map)))
    M.pos_exact M.pos_augmentation_exact M.cover.surjective
    (fun n => by
      have := freeRightProjective (k := k) (R := R) (S := S) (M.positive n).cover.rank
      infer_instance)

end Tachikawa.Enveloping



namespace Tachikawa.Enveloping
open CategoryTheory CategoryTheory.Abelian
open scoped TensorProduct ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  [FiniteDimensional k R] [FiniteDimensional k S]

lemma coind_ext_zero (M : FiniteModule k (Alg k R S))
    [Module.Projective Sᵐᵒᵖ (Obj M.obj)] (N : ModuleCat Sᵐᵒᵖ) (n : ℕ) :
    Subsingleton (Ext M.obj (coindObj (k := k) (R := R) N) (n+1)) := by
  let P := M.projectiveResolution
  let Q := rightResolution M
  have hd (i : ℕ) : P.complex.d (i+1) i = ModuleCat.ofHom (M.posDifferential i) := by
    dsimp [P, FiniteModule.projectiveResolution, resolutionOfExact]
    exact ChainComplex.of_d _ _ _
  have he (i : ℕ) : Q.complex.d (i+1) i =
      ModuleCat.ofHom (rightMap (ModuleCat.ofHom (M.posDifferential i))) := by
    dsimp [Q, rightResolution, resolutionOfExact]
    exact ChainComplex.of_d _ _ _
  let : Subsingleton (Ext (ModuleCat.of Sᵐᵒᵖ (Obj M.obj)) N (n+1)) :=
    Ext.subsingleton_of_projective _ _ n
  apply ext_subsingleton_of_boundaries P n
  intro f hf
  let f' : Q.complex.X (n+1) ⟶ N :=
    ModuleCat.ofHom (coindEvaluate (P.complex.X (n+1)) N f)
  have hf' : Q.complex.d (n+2) (n+1) ≫ f' = 0 := by
    rw [he]
    apply ModuleCat.hom_ext
    change (coindEvaluate _ N f).comp (rightMap (ModuleCat.ofHom (M.posDifferential (n+1)))) = 0
    erw [← coindEvaluate_natural]
    rw [hd (n+1)] at hf
    erw [hf]
    exact (coindHomEquiv _ N).map_zero
  obtain ⟨g,hg⟩ := boundaries_of_ext_subsingleton Q n f' hf'
  let g' : P.complex.X n ⟶ coindObj (k := k) (R := R) N :=
    coindExtend _ N g.hom
  refine ⟨g', ?_⟩
  apply (coindHomEquiv _ N).injective
  change coindEvaluate _ N (P.complex.d (n+1) n ≫ g') = coindEvaluate _ N f
  rw [coindEvaluate_natural,show coindEvaluate _ N g' = g.hom from coindEvaluate_extend _ _ _]
  rw [hd]
  rw [he] at hg
  exact ModuleCat.hom_ext_iff.mp hg

end Tachikawa.Enveloping



namespace Tachikawa.Enveloping
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]

def dualLeftObj : ModuleCat R := ModuleCat.of R (DualBimodule k R)

def dualLeftUnderlying : dualLeftObj (k := k) (R := R) ≃ₗ[k] Module.Dual k R :=
  moduleCatUnderlyingEquiv (k := k) (R := R) (DualBimodule k R)

instance instFiniteDimensionalCarrierDualLeftObj [FiniteDimensional k R] : FiniteDimensional k (dualLeftObj (k := k) (R := R)) :=
  Module.Finite.equiv (dualLeftUnderlying (k := k) (R := R)).symm
instance instFiniteCarrierDualLeftObjOfFiniteDimensional [FiniteDimensional k R] : Module.Finite R (dualLeftObj (k := k) (R := R)) :=
  Module.Finite.of_restrictScalars_finite k R _

def dualRegularObj : ModuleCat (Alg k R R) :=
  ofBimodule (k := k) (R := R) (S := R) (DualBimodule k R)

def dualRegularLeftEquiv : Obj (dualRegularObj (k := k) (R := R)) ≃ₗ[R] DualBimodule k R where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r x := by
    change r • ((1:Rᵐᵒᵖ) • (show DualBimodule k R from x)) = r • (show DualBimodule k R from x)
    rw [one_smul]

instance dualRegularLeftInjective : Module.Injective R (Obj (dualRegularObj (k := k) (R := R))) :=
  Module.Baer.injective (Module.Baer.of_equiv (dualRegularLeftEquiv (k := k) (R := R)).symm
    (Module.Baer.of_injective inferInstance))

variable [FiniteDimensional k R] (N : ModuleCat Sᵐᵒᵖ)

def dualOuterUnderlying :
    OuterTensor.Obj k R Sᵐᵒᵖ (dualLeftObj (k := k) (R := R)) N ≃ₗ[k]
      (R →ₗ[k] N) :=
  (TensorProduct.congr (dualLeftUnderlying (k := k) (R := R)) (LinearEquiv.refl k N)).trans
    (dualTensorHomEquiv k R N)

lemma dualOuterUnderlying_tmul (φ : dualLeftObj (k := k) (R := R)) (x : N) (r : R) :
    dualOuterUnderlying N (φ ⊗ₜ[k] x) r = (dualLeftUnderlying φ r) • x := rfl

def dualOuterEquiv :
    OuterTensor.Obj k R Sᵐᵒᵖ (dualLeftObj (k := k) (R := R)) N ≃ₗ[Alg k R S]
      coindObj (k := k) (R := R) N where
  __ := ((dualOuterUnderlying N).trans (coindUnderlying N).symm).toAddEquiv
  map_smul' a z := by
    apply (coindUnderlying N).injective
    change dualOuterUnderlying N ((OuterTensor.action k R Sᵐᵒᵖ _ N a) z) =
      action (k := k) (R := R) (S := S) (Coind (k := k) (R := R) N) a (dualOuterUnderlying N z)
    induction a using OAI.tensorInductionOn with
    | add a b ha hb =>
      erw [map_add,LinearMap.add_apply,map_add,map_add,LinearMap.add_apply,ha,hb]
      rfl
    | tmul r s =>
      induction z using OAI.tensorInductionOn with
      | add x y hx hy => erw [map_add,map_add,map_add,hx,hy,map_add]; rfl
      | tmul φ x =>
        apply LinearMap.ext; intro c
        change (show Module.Dual k R from φ) (c*r) • (s • x) =
          s • ((show Module.Dual k R from φ) (c*r) • x)
        exact smul_comm _ _ _

end Tachikawa.Enveloping



namespace Tachikawa.Enveloping
open CategoryTheory CategoryTheory.Abelian
open scoped TensorProduct ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R] [FiniteDimensional k R]

def dualLeftFinite : FiniteModule k R := ⟨dualLeftObj (k := k) (R := R), inferInstance⟩

end Tachikawa.Enveloping

end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Induction
attribute [-instance] _root_.OAI.Tachikawa.AlgebraInduction.resFinite _root_.OAI.Tachikawa.DownHom.instAddCommGroupCochain _root_.OAI.Tachikawa.DownHom.instModuleCochain
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

def dualRegularUnderlying : dualRegularObj (k := k) (R := R) ≃ₗ[k] Module.Dual k R where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c x := by
    change (action (k := k) (R := R) (S := R) (DualBimodule k R)
      (algebraMap k (Alg k R R) c)) (show DualBimodule k R from x) = c • (show DualBimodule k R from x)
    rw [AlgHom.commutes]
    rfl

omit [FiniteDimensional k R] in
lemma dualRegularUnderlying_left (a : R) (φ : dualRegularObj (k := k) (R := R)) :
    dualRegularUnderlying (((a ⊗ₜ[k] (1:Rᵐᵒᵖ)) : Alg k R R) • φ) =
      (dualRegularUnderlying φ).comp (LinearMap.mulRight k a) := by
  apply LinearMap.ext; intro c
  change (show Module.Dual k R from φ) ((1:R)* (c*a)) = _
  rw [one_mul]
  rfl

omit [FiniteDimensional k R] in
lemma dualRegularUnderlying_right (a : R) (φ : dualRegularObj (k := k) (R := R)) :
    dualRegularUnderlying (((1:R) ⊗ₜ[k] MulOpposite.op a : Alg k R R) • φ) =
      (dualRegularUnderlying φ).comp (LinearMap.mulLeft k a) := by
  apply LinearMap.ext; intro c
  change (show Module.Dual k R from φ) (a * (c*1)) = _
  rw [mul_one]
  rfl




end Tachikawa.Enveloping



namespace Tachikawa
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k : Type} [Field k] (q : k)

def characterBimoduleMap : Enveloping.regular (k := k) (R := B q) ⟶
    Enveloping.dualRegularObj (k := k) (R := B q) :=
  Enveloping.ofBimoduleHom
    { toFun := characterMapB q
      map_add' := (characterMapB q).map_add
      map_smul' a x := characterMapB_left q a x }
    (fun a x => characterMapB_right q x a.unop)

end Tachikawa



namespace Tachikawa.Construction
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k : Type} [Field k] (q : k)

def rho : E q →ₗ[k] DualBimodule k (B q) :=
  (TensorProduct.dualDistrib k (C k q) (C k q)).comp
    (TensorProduct.map ((TrivSqZeroExt.sndHom (C k q) (DualBimodule k (C k q))).restrictScalars k)
      ((TrivSqZeroExt.sndHom (C k q) (DualBimodule k (C k q))).restrictScalars k))

lemma rho_tmul (a b : T q) (x y : C k q) :
    rho q (a ⊗ₜ[k] b) (x ⊗ₜ[k] y) = a.snd x * b.snd y := rfl

lemma rho_zeta : rho q (zeta q) = (characterB q).toLinearMap := by
  apply TensorProduct.ext'
  intro x y
  rfl

end Tachikawa.Construction



namespace Tachikawa.Enveloping
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]

abbrev rightRestrictedRegular (φ : R →ₐ[k] S) : ModuleCat (Alg k S R) :=
  ofBimodule (k := k) (R := S) (S := R) (AlgebraInduction.Bimod φ)

def regularLeftUnitTarget (φ : R →ₐ[k] S) : regular (k := k) (R := R) ⟶
    (AlgebraInduction.res (leftEnvelopingMap (U := R) φ)).obj (rightRestrictedRegular φ) :=
  ModuleCat.ofHom (X := regular (k := k) (R := R))
    (Y := (AlgebraInduction.res (leftEnvelopingMap (U := R) φ)).obj (rightRestrictedRegular φ))
  { toFun := fun r => φ r
    map_add' := φ.map_add
    map_smul' a x := by
      change φ ((action (k := k) (R := R) (S := R) R a) x) =
        (action (k := k) (R := S) (S := R) (AlgebraInduction.Bimod φ) (leftEnvelopingMap φ a)) (φ x)
      induction a using OAI.tensorInductionOn with
      | tmul r s =>
        change φ (r * ((show R from x) * s.unop)) = φ r * (φ x * φ s.unop)
        rw [map_mul, map_mul]
      | add a b ha hb =>
        rw [map_add, map_add, map_add]
        change φ ((action (k := k) (R := R) (S := R) R a) x +
          (action (k := k) (R := R) (S := R) R b) x) = _
        exact (φ.map_add _ _).trans
          (congrArg₂ (fun x y : AlgebraInduction.Bimod φ => x+y) ha hb) }

def leftIndRegularHom (φ : R →ₐ[k] S) :
    leftIndObj φ (regular (k := k) (R := R)) ⟶ rightRestrictedRegular φ :=
  leftIndExtend φ (regularLeftUnitTarget φ)

lemma leftIndRegularHom_mk (φ : R →ₐ[k] S) (s : AlgebraInduction.Bimod φ)
    (r : Obj (regular (k := k) (R := R))) :
    (show S from leftIndRegularHom φ (BalancedTensor.mk s r)) = (show S from s) * φ r := by
  change (show S from s) * (φ r * φ (1:R)) = _
  rw [map_one, mul_one]

def leftIndRegularInvLinear (φ : R →ₐ[k] S) : S →ₗ[S]
    BalancedTensor.T (k := k) (R := R) (S := S)
      (M := AlgebraInduction.Bimod φ) (N := Obj (regular (k := k) (R := R))) :=
  (LinearMap.toSpanSingleton S _) (BalancedTensor.mk
    (show AlgebraInduction.Bimod φ from (1:S)) (show Obj (regular (k := k) (R := R)) from (1:R)))

lemma leftIndRegularInvLinear_apply (φ : R →ₐ[k] S) (s : S) :
    leftIndRegularInvLinear φ s = BalancedTensor.mk (k := k) (R := R) (S := S)
      (N := Obj (regular (k := k) (R := R)))
      (show AlgebraInduction.Bimod φ from s) (1:R) := by
  exact (AlgebraInduction.mk_one_smul φ
    (ModuleCat.of R (Obj (regular (k := k) (R := R)))) s (1:R)).symm

lemma leftIndRegularInvLinear_right (φ : R →ₐ[k] S) (r : Rᵐᵒᵖ) (s : S) :
    leftIndRegularInvLinear φ (s * φ r.unop) = r • leftIndRegularInvLinear φ s := by
  rw [leftIndRegularInvLinear_apply, leftIndRegularInvLinear_apply]
  trans BalancedTensor.mk (k := k) (R := R) (S := S)
    (M := AlgebraInduction.Bimod φ) (N := Obj (regular (k := k) (R := R)))
    (r • (show AlgebraInduction.Bimod φ from s)) (1:R)
  · rfl
  trans BalancedTensor.mk (k := k) (R := R) (S := S)
    (N := Obj (regular (k := k) (R := R)))
    (show AlgebraInduction.Bimod φ from s) (r.unop • (show Obj (regular (k := k) (R := R)) from (1:R)))
  · exact BalancedTensor.balance _ _ _
  change BalancedTensor.mk (k := k) (R := R) (S := S)
    (N := Obj (regular (k := k) (R := R)))
    (show AlgebraInduction.Bimod φ from s) (r.unop * (1 * 1)) =
    BalancedTensor.mk (k := k) (R := R) (S := S)
    (N := Obj (regular (k := k) (R := R)))
    (show AlgebraInduction.Bimod φ from s) (1 * (1 * r.unop))
  exact congrArg (fun z : R => BalancedTensor.mk (k := k) (R := R) (S := S)
    (N := Obj (regular (k := k) (R := R))) (show AlgebraInduction.Bimod φ from s)
    (show Obj (regular (k := k) (R := R)) from z)) (show r.unop * ((1:R)*1) = (1:R)*(1*r.unop) by simp only [one_mul, mul_one])

def leftIndRegularInv (φ : R →ₐ[k] S) :
    rightRestrictedRegular φ ⟶ leftIndObj φ (regular (k := k) (R := R)) :=
  ofBimoduleHom
    (show AlgebraInduction.Bimod φ →ₗ[S] _ from leftIndRegularInvLinear φ)
    (leftIndRegularInvLinear_right φ)

def rightRestrictedRegularIso (φ : R →ₐ[k] S) :
    (rightFunctor (k := k) (R := S) (S := R)).obj (rightRestrictedRegular φ) ≅
      (AlgebraInduction.res φ.op).obj (ModuleCat.of Sᵐᵒᵖ Sᵐᵒᵖ) :=
by
  let X := (rightFunctor (k := k) (R := S) (S := R)).obj (rightRestrictedRegular φ)
  let Z := (AlgebraInduction.res φ.op).obj (ModuleCat.of Sᵐᵒᵖ Sᵐᵒᵖ)
  exact LinearEquiv.toModuleIso (X₁ := X) (X₂ := Z)
    (m₁ := X.isModule) (m₂ := Z.isModule)
    { toFun := fun x : X =>
        (show (AlgebraInduction.res φ.op).obj (ModuleCat.of Sᵐᵒᵖ Sᵐᵒᵖ) from MulOpposite.op (show S from x))
      invFun := fun x => (show Sᵐᵒᵖ from x).unop
      left_inv _ := rfl
      right_inv _ := rfl
      map_add' _ _ := rfl
      map_smul' r x := by
        change MulOpposite.op ((1:S) * ((show S from x) * φ r.unop)) =
          MulOpposite.op ((show S from x) * φ r.unop)
        rw [one_mul] }

end Tachikawa.Enveloping



namespace Tachikawa.Construction
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k : Type} [Field k] (q : k)

abbrev opTensorB : ((C k q)ᵐᵒᵖ ⊗[k] (C k q)ᵐᵒᵖ) ≃ₐ[k] (B q)ᵐᵒᵖ :=
  Algebra.TensorProduct.opAlgEquiv k k (C k q) (C k q)
abbrev opTensorE : ((T q)ᵐᵒᵖ ⊗[k] (T q)ᵐᵒᵖ) ≃ₐ[k] (E q)ᵐᵒᵖ :=
  Algebra.TensorProduct.opAlgEquiv k k (T q) (T q)

abbrev opTensorRestriction := ModuleCat.restrictScalars (opTensorB q).symm.toRingHom

end Tachikawa.Construction

end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_DerivedInduction
attribute [-instance] _root_.OAI.Tachikawa.DownHom.instAddCommGroupCochain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
set_option backward.isDefEq.respectTransparency false


noncomputable section



namespace Tachikawa.Construction
open CategoryTheory
open scoped ModuleCat.Algebra TensorProduct
variable {k : Type} [Field k] [CharP k 2] (q : k)

def cSimpleCanon : ModuleCat (C k q) := ModuleCat.of (C k q) (C.Simple q)

omit [CharP k 2] in
def cSimpleUnderlying : cSimpleCanon q ≃ₗ[k] k where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c x := by
    change C.character q (algebraMap k (C k q) c) * (show k from x) = c * (show k from x)
    rw [AlgHom.commutes]
    simp

omit [CharP k 2] in
def bSimpleTensorUnderlying : OuterTensor.Obj k (C k q) (C k q)
    (cSimpleCanon q) (cSimpleCanon q) ≃ₗ[k] k :=
  (TensorProduct.congr (cSimpleUnderlying q) (cSimpleUnderlying q)).trans (TensorProduct.lid k k)

omit [CharP k 2] in
lemma bSimpleTensorUnderlying_smul (a : B q)
    (x : OuterTensor.Obj k (C k q) (C k q)
      (cSimpleCanon q) (cSimpleCanon q)) :
    bSimpleTensorUnderlying q (a • x) = characterB q a * bSimpleTensorUnderlying q x := by
  induction a using OAI.tensorInductionOn with
  | add a b ha hb => simp only [add_smul, map_add, ha, hb, add_mul]
  | tmul a b =>
    induction x using OAI.tensorInductionOn with
    | add x y hx hy => erw [smul_add, map_add, hx, hy, map_add, mul_add]
    | tmul x y =>
      change (C.character q a * cSimpleUnderlying q x) *
        (C.character q b * cSimpleUnderlying q y) =
        (C.character q a * C.character q b) * (cSimpleUnderlying q x * cSimpleUnderlying q y)
      ring

end Tachikawa.Construction



namespace Tachikawa.Enveloping
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]

def homOfLinear {M N : ModuleCat.{0} (Alg k R S)} (f : M →ₗ[k] N)
    (hf : ∀ (r : R) (s : Sᵐᵒᵖ) (x : M), f ((r ⊗ₜ[k] s) • x) = (r ⊗ₜ[k] s) • f x) :
    M ⟶ N := ModuleCat.ofHom (X := M) (Y := N)
  { toFun := f
    map_add' := f.map_add
    map_smul' a x := by
      induction a using OAI.tensorInductionOn with
      | add a b ha hb => simp only [add_smul,map_add,ha,hb]
      | tmul r s => exact hf r s x }

end Tachikawa.Enveloping



namespace Tachikawa
open CategoryTheory HomologicalComplex
variable {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]

lemma kProjective_chain_representative (K L : CochainComplex C ℤ) [K.IsKProjective]
    (a : DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj L) :
    ∃ f : K ⟶ L, DerivedCategory.Q.map f = a := by
  let e := DerivedCategory.quotientCompQhIso C
  obtain ⟨b,hb⟩ := (CochainComplex.IsKProjective.Qh_map_bijective K
    ((HomotopyCategory.quotient C (.up ℤ)).obj L)).surjective
      ((e.app K).hom ≫ a ≫ (e.app L).inv)
  obtain ⟨f,rfl⟩ := (HomotopyCategory.quotient C (.up ℤ)).map_surjective b
  refine ⟨f,?_⟩
  have ht := congrArg (fun t => (e.app K).inv ≫ t ≫ (e.app L).hom) hb
  change e.inv.app K ≫ DerivedCategory.Qh.map ((HomotopyCategory.quotient C (.up ℤ)).map f) ≫ e.hom.app L =
    e.inv.app K ≫ (e.hom.app K ≫ a ≫ e.inv.app L) ≫ e.hom.app L at ht
  simpa [e] using ht

end Tachikawa



namespace Tachikawa
open CategoryTheory HomologicalComplex

variable {C : Type*} [Category C] [Preadditive C]

lemma complex_d_transport (K : CochainComplex C ℤ) {i i' j j' : ℤ}
    (hi : i = i') (hj : j = j') :
    eqToHom (congrArg K.X hi) ≫ K.d i' j' = K.d i j ≫ eqToHom (congrArg K.X hj) := by
  subst i'; subst j'; simp

def reflectCochainIso (K : CochainComplex C ℤ) : reflectChain (reflectCochain K) ≅ K :=
  HomologicalComplex.Hom.isoOfComponents (fun i => eqToIso (by change K.X (- -i) = K.X i; rw [neg_neg]))
    (by intro i j h; exact complex_d_transport K (neg_neg i) (neg_neg j))

lemma reflectCochainIso_natural {K L : CochainComplex C ℤ} (f : K ⟶ L) :
    reflectChainMap (reflectCochainMap f) ≫ (reflectCochainIso L).hom =
      (reflectCochainIso K).hom ≫ f := by
  ext i
  change f.f (- -i) ≫ eqToHom (show L.X (- -i) = L.X i by simp) =
    eqToHom (show K.X (- -i) = K.X i by simp) ≫ f.f i
  simp

end Tachikawa



namespace Tachikawa
open CategoryTheory HomologicalComplex
variable {R S : Type} [Ring R] [Ring S]

lemma resolution_reflect_exact {M : ModuleCat.{0} R} (P : ProjectiveResolution M)
    (F : ModuleCat.{0} R ⥤ ModuleCat.{0} S) [F.Additive] (n : ℕ) (hn : 0 < n)
    (h : Function.Exact (((F.mapHomologicalComplex (.down ℕ)).obj P.complex).d (n+1) n)
      (((F.mapHomologicalComplex (.down ℕ)).obj P.complex).d n (n-1))) :
    Function.Exact ((reflectCochain ((F.mapHomologicalComplex (.up ℤ)).obj P.cochainComplex)).d
      ((n:ℤ)+1) n)
      ((reflectCochain ((F.mapHomologicalComplex (.up ℤ)).obj P.cochainComplex)).d n ((n:ℤ)-1)) := by
  let K := (F.mapHomologicalComplex (.up ℤ)).obj P.cochainComplex
  let L := (F.mapHomologicalComplex (.down ℕ)).obj P.complex
  let A : ShortComplex (ModuleCat.{0} S) :=
    ShortComplex.mk (K.d (-((n:ℤ)+1)) (-(n:ℤ))) (K.d (-(n:ℤ)) (-((n:ℤ)-1))) (by simp)
  let B : ShortComplex (ModuleCat.{0} S) :=
    ShortComplex.mk (L.d (n+1) n) (L.d n (n-1)) (by simp)
  let e₁ := F.mapIso (P.cochainComplexXIso (-((n:ℤ)+1)) (n+1) (by omega))
  let e₂ := F.mapIso (P.cochainComplexXIso (-(n:ℤ)) n)
  let e₃ := F.mapIso (P.cochainComplexXIso (-((n:ℤ)-1)) (n-1) (by omega))
  have h₁ : e₁.hom ≫ B.f = A.f ≫ e₂.hom := by
    change F.map _ ≫ F.map _ = F.map _ ≫ F.map _
    rw [P.cochainComplex_d (-((n:ℤ)+1)) (-(n:ℤ)) (n+1) n (by omega) rfl]
    simp only [← F.map_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have h₂ : e₂.hom ≫ B.g = A.g ≫ e₃.hom := by
    change F.map _ ≫ F.map _ = F.map _ ≫ F.map _
    rw [P.cochainComplex_d (-(n:ℤ)) (-((n:ℤ)-1)) n (n-1) rfl (by omega)]
    simp only [← F.map_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have he : B.Exact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact B).mpr h
  exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact A).mp
    (ShortComplex.exact_of_iso (ShortComplex.isoMk e₁ e₂ e₃ h₁ h₂).symm he)

end Tachikawa

end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Perfect
attribute [-instance] _root_.OAI.Tachikawa.DownHom.instAddCommGroupCochain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace Tachikawa
open CategoryTheory HomologicalComplex
open scoped ModuleCat.Algebra
variable {R S : Type} [Ring R] [Ring S]

namespace FiniteModule
variable {k : Type} [Field k] [Algebra k R] [FiniteDimensional k R] (M : FiniteModule k R)
lemma pos_cover_exact (n : ℕ) :
    Function.Exact (M.posDifferential n) (M.positive n).cover.map := by
  intro x
  constructor
  · intro hx
    obtain ⟨y,hy⟩ := (M.positive (n+1)).cover.surjective ⟨x,hx⟩
    exact ⟨y,congrArg Subtype.val hy⟩
  · rintro ⟨y,rfl⟩
    exact ((M.positive (n+1)).cover.map y).property

def naturalCokerPositiveEquiv (n : ℕ) :
    (M.projectiveResolution.complex.X n ⧸ LinearMap.range (M.projectiveResolution.complex.d (n+1) n).hom)
      ≃ₗ[R] (M.positive n).obj := by
  have hd : (M.projectiveResolution.complex.d (n+1) n).hom = M.posDifferential n := by
    dsimp only [projectiveResolution, resolutionOfExact]
    exact congrArg ModuleCat.Hom.hom (ChainComplex.of_d _ _ n)
  change (M.posTerm n ⧸ LinearMap.range (M.projectiveResolution.complex.d (n+1) n).hom) ≃ₗ[R] _
  exact (Submodule.quotEquivOfEq _ _ (hd ▸ (M.pos_cover_exact n).linearMap_ker_eq.symm)).trans
    ((M.positive n).cover.map.quotKerEquivOfSurjective (M.positive n).cover.surjective)

def reflectCokerPositiveEquiv (n : ℕ) :
    CokerAt (reflectCochain M.projectiveResolution.cochainComplex) n ≃ₗ[R] (M.positive n).obj :=
  (resolutionReflectCokerEquiv M.projectiveResolution (𝟭 (ModuleCat R)) n).trans
    (M.naturalCokerPositiveEquiv n)
end FiniteModule
end Tachikawa



namespace Tachikawa
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped ModuleCat.Algebra
attribute [local instance] HasDerivedCategory.standard
variable {k R : Type} [Field k] [Ring R] [Algebra k R] [FiniteDimensional k R]

lemma projectiveResolution_reflect_exact {M : ModuleCat.{0} R} (P : ProjectiveResolution M)
    (n : ℕ) (hn : 0 < n) :
    Function.Exact ((reflectCochain P.cochainComplex).d ((n:ℤ)+1) n)
      ((reflectCochain P.cochainComplex).d n ((n:ℤ)-1)) := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  have h := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp (P.exact_succ m)
  exact resolution_reflect_exact P (𝟭 (ModuleCat.{0} R)) (m+1) (by omega)
    (by
      change Function.Exact (P.complex.d (m+1+1) (m+1)) (P.complex.d (m+1) (m+1-1))
      rw [show m+1-1=m by omega]
      exact h)

end Tachikawa



namespace Tachikawa.Enveloping
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]

def resRegularUnderlying (φ : R →ₐ[k] S) :
    (AlgebraInduction.res φ).obj (ModuleCat.of S S) ≃ₗ[k] S where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c x := by
    change φ (algebraMap k R c) * (show S from x) = c • (show S from x)
    rw [AlgHom.commutes,Algebra.smul_def]

def restrictedOuterRegularUnderlying (φ : R →ₐ[k] S) :
    OuterTensor.Obj k R Rᵐᵒᵖ
      ((AlgebraInduction.res φ).obj (ModuleCat.of S S))
      ((AlgebraInduction.res φ.op).obj (ModuleCat.of Sᵐᵒᵖ Sᵐᵒᵖ)) ≃ₗ[k] Alg k S S :=
  TensorProduct.congr (resRegularUnderlying φ) (resRegularUnderlying φ.op)

end Tachikawa.Enveloping



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_DerivedDescent
attribute [-instance] _root_.OAI.Tachikawa.DownHom.instAddCommGroupCochain _root_.OAI.Tachikawa.DownHom.instModuleCochain _root_.OAI.Tachikawa.Triangular.instProjectiveCarrierOneFree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace Tachikawa
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra
attribute [local instance] Abelian.hasFiniteBiproducts
variable {R : Type} [Ring R]

lemma finiteProjective_inAdd (M : ModuleCat R) [Module.Finite R M] [Module.Projective R M] :
    InAdd (ModuleCat.of R R) M := by
  let c := finiteFreeCover (R := R) (M := M)
  obtain ⟨i,hi⟩ := Module.projective_lifting_property c.map LinearMap.id c.surjective
  let e := ModuleCat.biproductIsoPi (fun _ : Fin c.rank => ModuleCat.of R R)
  refine ⟨c.rank,⟨{ i := ModuleCat.ofHom i ≫ e.inv, r := e.hom ≫ ModuleCat.ofHom c.map, retract := ?_ }⟩⟩
  rw [Category.assoc,← Category.assoc e.inv,e.inv_hom_id,Category.id_comp]
  exact ModuleCat.hom_ext hi

end Tachikawa



namespace Tachikawa
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]

def freeEndo : ModuleCat R ⥤ ModuleCat R :=
  AlgebraInduction.res (Algebra.ofId k R) ⋙ AlgebraInduction.functor (Algebra.ofId k R)
instance instAdditiveModuleCatFreeEndo : (freeEndo (k := k) (R := R)).Additive := inferInstanceAs
  ((AlgebraInduction.res (Algebra.ofId k R) ⋙ AlgebraInduction.functor (Algebra.ofId k R)).Additive)

def freeCounit (M : ModuleCat R) : (freeEndo (k := k)).obj M ⟶ M :=
  AlgebraInduction.extend (Algebra.ofId k R) (𝟙 _)

lemma freeCounit_surjective (M : ModuleCat R) : Function.Surjective (freeCounit (k := k) M) := by
  intro x
  refine ⟨BalancedTensor.mk (k := k) (R := k) (S := R)
    (show AlgebraInduction.Bimod (Algebra.ofId k R) from (1 : R))
    (show (AlgebraInduction.res (Algebra.ofId k R)).obj M from x), ?_⟩
  change (1 : R) • x = x
  exact one_smul R x

instance instEpiModuleCatFreeCounit (M : ModuleCat R) : Epi (freeCounit (k := k) M) :=
  (ModuleCat.epi_iff_surjective _).2 (freeCounit_surjective M)

def freeCounitNat : freeEndo (k := k) (R := R) ⟶ 𝟭 _ where
  app := freeCounit
  naturality {M N} f := by
    apply ModuleCat.hom_ext
    apply BalancedTensor.hom_ext
    intro r x
    change (show R from r) • f (show M from x) = f ((show R from r) • (show M from x))
    exact (f.hom.map_smul _ _).symm

instance instEpiFunctorModuleCatFreeCounitNat : Epi (freeCounitNat (k := k) (R := R)) := by
  let (M : ModuleCat R) : Epi ((freeCounitNat (k := k)).app M) := inferInstanceAs (Epi (freeCounit (k := k) M))
  exact NatTrans.epi_of_epi_app _

def freeKernel : ModuleCat R ⥤ ModuleCat R := kernel (freeCounitNat (k := k) (R := R))
instance instAdditiveModuleCatFreeKernel : (freeKernel (k := k) (R := R)).Additive := by
  constructor
  intro X Y f g
  dsimp only [freeKernel]
  let ι := kernel.ι (freeCounitNat (k := k) (R := R))
  let : Mono (ι.app Y) := inferInstance
  apply (cancel_mono (ι.app Y)).1
  erw [ι.naturality,Functor.map_add,Preadditive.comp_add,
    Preadditive.add_comp,ι.naturality,ι.naturality]

def freeι (M : ModuleCat R) : (freeKernel (k := k)).obj M ⟶ (freeEndo (k := k)).obj M :=
  (kernel.ι (freeCounitNat (k := k))).app M

lemma freeι_counit (M : ModuleCat R) : freeι (k := k) M ≫ freeCounit M = 0 :=
  congrArg (fun f => f.app M) (kernel.condition (freeCounitNat (k := k)))

def freeShort (M : ModuleCat R) : ShortComplex (ModuleCat R) :=
  ShortComplex.mk (freeι (k := k) M) (freeCounit M) (freeι_counit M)

lemma freeShort_exact (M : ModuleCat R) : (freeShort (k := k) M).ShortExact := by
  let T : ShortComplex (ModuleCat R ⥤ ModuleCat R) :=
    ShortComplex.mk (kernel.ι (freeCounitNat (k := k))) freeCounitNat (kernel.condition _)
  have hT : T.ShortExact := { exact := ShortComplex.exact_kernel _ }
  exact hT.map ((evaluation _ _).obj M)

instance freeEndo_projective (M : ModuleCat R) [FiniteDimensional k M] :
    Projective ((freeEndo (k := k)).obj M) := by
  let : Module.Finite k ((AlgebraInduction.res (Algebra.ofId k R)).obj M) :=
    inferInstanceAs (Module.Finite k M)
  let : Module.Projective k ((AlgebraInduction.res (Algebra.ofId k R)).obj M) := inferInstance
  change Projective ((AlgebraInduction.functor (Algebra.ofId k R)).obj _)
  infer_instance

variable [FiniteDimensional k R]
instance freeEndo_finite (M : ModuleCat R) [FiniteDimensional k M] :
    FiniteDimensional k ((freeEndo (k := k)).obj M) := by
  let : FiniteDimensional k ((AlgebraInduction.res (Algebra.ofId k R)).obj M) :=
    inferInstanceAs (FiniteDimensional k M)
  change FiniteDimensional k ((AlgebraInduction.functor (Algebra.ofId k R)).obj _)
  infer_instance

instance freeKernel_finite (M : ModuleCat R) [FiniteDimensional k M] :
    FiniteDimensional k ((freeKernel (k := k)).obj M) := by
  have : Mono (freeι (k := k) M) := inferInstanceAs
    (Mono ((kernel.ι (freeCounitNat (k := k))).app M))
  have hi : Function.Injective (freeι (k := k) M) :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  exact Module.Finite.of_injective ((freeι M).hom.restrictScalars k) hi

omit [FiniteDimensional k R] in
lemma freeKernel_pd (M : ModuleCat R) [FiniteDimensional k M] (n : ℕ)
    [HasProjectiveDimensionLE M (n+1)] :
    HasProjectiveDimensionLE ((freeKernel (k := k)).obj M) n := by
  apply (freeShort_exact (k := k) M).hasProjectiveDimensionLT_X₁ (n+1)
  · change HasProjectiveDimensionLT ((freeEndo (k := k)).obj M) (n+1)
    exact hasProjectiveDimensionLT_of_ge _ 1 (n+1) (by omega)
  · exact inferInstanceAs (HasProjectiveDimensionLE M (n+1))

end Tachikawa



namespace Tachikawa
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
variable {k R : Type} [Field k] [Ring R] [Algebra k R]

abbrev freeComplex (P : CochainComplex (ModuleCat R) ℤ) :=
  ((freeEndo (k := k)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P
abbrev kernelComplex (P : CochainComplex (ModuleCat R) ℤ) :=
  ((freeKernel (k := k)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P

def freeComplexCounit (P : CochainComplex (ModuleCat R) ℤ) : freeComplex (k := k) P ⟶ P where
  f i := freeCounit (P.X i)
  comm' i j _ := ((freeCounitNat (k := k)).naturality (P.d i j)).symm

def freeComplexι (P : CochainComplex (ModuleCat R) ℤ) : kernelComplex (k := k) P ⟶ freeComplex (k := k) P where
  f i := freeι (P.X i)
  comm' i j _ := ((kernel.ι (freeCounitNat (k := k))).naturality (P.d i j)).symm

def freeComplexShort (P : CochainComplex (ModuleCat R) ℤ) :
    ShortComplex (CochainComplex (ModuleCat R) ℤ) :=
  ShortComplex.mk (freeComplexι (k := k) P) (freeComplexCounit (k := k) P) (by
    apply HomologicalComplex.Hom.ext
    funext i
    exact freeι_counit (P.X i))

lemma freeComplexShort_exact (P : CochainComplex (ModuleCat R) ℤ) :
    (freeComplexShort (k := k) P).ShortExact := by
  apply shortExact_of_degreewise_shortExact
  intro i
  exact freeShort_exact (P.X i)

end Tachikawa



namespace Tachikawa
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]

attribute [instance] IndReplacement.quasiIso

def indReplacement : (n : ℕ) → (P : CochainComplex (ModuleCat.{0} R) ℤ) → IndReplacement P
  | 0, P => ⟨P,𝟙 P,inferInstance⟩
  | n+1, P =>
    let t := indReplacement n (kernelComplex (k := k) P)
    { complex := mappingCone (t.map ≫ freeComplexι P)
      map := shortExactReplacementMapDual (freeComplexShort P) t.map
      quasiIso := by
        exact @shortExactReplacementMapDual_quasiIso _ _ _ (freeComplexShort P)
          (freeComplexShort_exact P) _ t.map t.quasiIso }

lemma indReplacement_bounded (n : ℕ) (P : CochainComplex (ModuleCat.{0} R) ℤ) (l u : ℤ)
    (hP : ∀ i, i < l ∨ u < i → IsZero (P.X i)) :
    ∀ i, i < l - n ∨ u < i → IsZero ((indReplacement (k := k) n P).complex.X i) := by
  induction n generalizing P with
  | zero => simpa only [indReplacement,Nat.cast_zero,sub_zero] using hP
  | succ n ih =>
    intro i hi
    apply mappingCone_isZero_X
    · apply ih (kernelComplex P)
      · intro j hj
        exact (freeKernel (k := k)).map_isZero (hP j hj)
      · omega
    · exact (freeEndo (k := k)).map_isZero (hP i (by omega))

variable [FiniteDimensional k R]
lemma indReplacement_terms (n : ℕ) (P : CochainComplex (ModuleCat.{0} R) ℤ)
    (hfin : ∀ i, FiniteDimensional k (P.X i))
    (hpd : ∀ i, HasProjectiveDimensionLE (P.X i) n) :
    (∀ i, Projective ((indReplacement (k := k) n P).complex.X i)) ∧
    (∀ i, FiniteDimensional k ((indReplacement (k := k) n P).complex.X i)) := by
  induction n generalizing P with
  | zero =>
    refine ⟨?_,hfin⟩
    intro i
    exact (projective_iff_hasProjectiveDimensionLE_zero (P.X i)).2 (hpd i)
  | succ n ih =>
    obtain ⟨hp,hf⟩ := ih (kernelComplex (k := k) P)
      (fun i => by let := hfin i; exact freeKernel_finite (k := k) (P.X i))
      (fun i => by let := hfin i; let := hpd i; exact freeKernel_pd (k := k) (P.X i) n)
    exact ⟨mappingCone_projective _ hp
      (fun i => by let := hfin i; exact freeEndo_projective (k := k) (P.X i)),
      mappingCone_finite _ hf
      (fun i => by let := hfin i; exact freeEndo_finite (k := k) (P.X i))⟩

theorem bounded_projective_replacement (P : CochainComplex (ModuleCat.{0} R) ℤ) (n : ℕ)
    (hfin : ∀ i, FiniteDimensional k (P.X i))
    (hpd : ∀ i, HasProjectiveDimensionLE (P.X i) n)
    (l u : ℤ) (hb : ∀ i, i < l ∨ u < i → IsZero (P.X i)) :
    ∃ (Q : CochainComplex (ModuleCat.{0} R) ℤ) (f : Q ⟶ P), QuasiIso f ∧
      (∀ i, Projective (Q.X i)) ∧ (∀ i, FiniteDimensional k (Q.X i)) ∧
      (∀ i, i < l-n ∨ u < i → IsZero (Q.X i)) :=
  ⟨(indReplacement (k := k) n P).complex,(indReplacement (k := k) n P).map,inferInstance,
    (indReplacement_terms n P hfin hpd).1,(indReplacement_terms n P hfin hpd).2,
    indReplacement_bounded n P l u hb⟩

end Tachikawa



namespace Tachikawa
open CategoryTheory HomologicalComplex CategoryTheory.Limits
variable {C : Type*} [Category C] [Abelian C] [HasExt C] [HasDerivedCategory C]
variable {X : C} (P : ProjectiveResolution X) (L : CochainComplex C ℤ)

theorem bounded_orthogonal_derived_descent (P : ProjectiveResolution X) (N : ℕ)
    (hL : ∀ j, j < -(N : ℤ) → IsZero (L.X j))
    (hExt : ∀ n : ℕ, Subsingleton (Abelian.Ext X (L.X (-(n+1 : ℤ))) (n+1)))
    (a : DerivedCategory.Q.obj ((CochainComplex.singleFunctor C 0).obj X) ⟶
      DerivedCategory.Q.obj L) :
    ∃ g : (CochainComplex.singleFunctor C 0).obj X ⟶ L,
      DerivedCategory.Q.map g = a := by
  obtain ⟨f,hf⟩ := kProjective_chain_representative P.cochainComplex L
    (DerivedCategory.Q.map P.π' ≫ a)
  obtain ⟨g,⟨H⟩⟩ := bounded_cochain_resolution_descends P N f hL hExt
  refine ⟨g, (cancel_epi (DerivedCategory.Q.map P.π')).1 ?_⟩
  rw [← Functor.map_comp, ← DerivedCategory.Q_map_eq_of_homotopy C H, hf]

end Tachikawa



namespace Tachikawa
open CategoryTheory HomologicalComplex CategoryTheory.Limits
variable {C : Type*} [Category C] [Abelian C] [HasExt C] [HasDerivedCategory C]
variable {X Y W : C}

set_option backward.isDefEq.respectTransparency false in
theorem bounded_ordinary_factorization (P : ProjectiveResolution X)
    (R : InjectiveResolution Y) (L : CochainComplex C ℤ) (l u : ℤ)
    (hbound : ∀ j, j < l ∨ u < j → IsZero (L.X j))
    (hterms : ∀ j, InAdd W (L.X j))
    (hleft : ∀ n : ℕ, Subsingleton (Abelian.Ext X W (n+1)))
    (hright : ∀ n : ℕ, Subsingleton (Abelian.Ext W Y (n+1)))
    (v : X ⟶ Y)
    (α : DerivedCategory.Q.obj ((CochainComplex.singleFunctor C 0).obj X) ⟶ DerivedCategory.Q.obj L)
    (β : DerivedCategory.Q.obj L ⟶ DerivedCategory.Q.obj ((CochainComplex.singleFunctor C 0).obj Y))
    (hv : α ≫ β = DerivedCategory.Q.map ((CochainComplex.singleFunctor C 0).map v)) :
    ∃ (a : X ⟶ L.X 0) (b : L.X 0 ⟶ Y), a ≫ b = v := by
  obtain ⟨a,ha⟩ := bounded_orthogonal_derived_descent L P l.natAbs
    (fun j hj => hbound j (Or.inl (by have h : -l ≤ ((-l).natAbs : ℤ) := Int.le_natAbs; rw [Int.natAbs_neg] at h; omega)))
    (fun n => by
      let := hleft n
      exact ext_subsingleton_inAdd_right (hterms _) _) α
  obtain ⟨b,hb⟩ := bounded_orthogonal_derived_descent_dual L R u.natAbs
    (fun j hj => hbound j (Or.inr (by have h : u ≤ (u.natAbs : ℤ) := Int.le_natAbs; omega)))
    (fun n => by
      let := hright n
      exact ext_subsingleton_inAdd_left (hterms _) _) β
  let eX := singleObjXSelf (.up ℤ) 0 X
  let eY := singleObjXSelf (.up ℤ) 0 Y
  refine ⟨eX.inv ≫ a.f 0, b.f 0 ≫ eY.hom, ?_⟩
  have hab : DerivedCategory.Q.map (a ≫ b) =
      DerivedCategory.Q.map ((CochainComplex.singleFunctor C 0).map v) := by
    rw [Functor.map_comp,ha,hb,hv]
  let S := CochainComplex.singleFunctor C 0
  let c := S.preimage (a ≫ b)
  have hcmap : S.map c = a ≫ b := S.map_preimage _
  have hc : c = v := by
    apply (DerivedCategory.singleFunctor C 0).map_injective
    change DerivedCategory.Q.map (S.map c) = DerivedCategory.Q.map (S.map v)
    rw [hcmap]
    exact hab
  have he : S.map v = a ≫ b := hc ▸ hcmap
  have he0 := congrArg (fun t => t.f 0) he
  change ((HomologicalComplex.single C (.up ℤ) 0).map v).f 0 = (a ≫ b).f 0 at he0
  rw [single_map_f_self,comp_f] at he0
  have h := congrArg (fun t => eX.inv ≫ t ≫ eY.hom) he0
  simpa only [eX,eY,Category.assoc,Iso.inv_hom_id_assoc,Iso.inv_hom_id,
    Category.comp_id] using h.symm

end Tachikawa

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



namespace Tachikawa.Enveloping
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]

attribute [instance] CoindReplacement.quasiIso

lemma mappingCocone_inAdd {W : ModuleCat (Alg k R S)}
    {K L : CochainComplex (ModuleCat (Alg k R S)) ℤ} (f : K ⟶ L)
    (hK : ∀ i, InAdd W (K.X i)) (hL : ∀ i, InAdd W (L.X i)) (i : ℤ) :
    InAdd W ((mappingCocone f).X i) := by
  let e : (mappingCocone f).X i ≅ K.X i ⊞ L.X (i + -1) :=
    shiftFunctorObjXIso (mappingCone f) (-1) i (i + -1) (by omega) ≪≫
      homotopyCofiber.XIsoBiprod f (i + -1) i (by change (i + -1) + 1 = i; omega)
  exact ((hK i).biprod (hL (i + -1))).iso e

end Tachikawa.Enveloping



namespace Tachikawa.Enveloping
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]

lemma mappingCocone_isZero_X {K L : CochainComplex (ModuleCat (Alg k R S)) ℤ}
    (f : K ⟶ L) (i : ℤ) (hK : IsZero (K.X i)) (hL : IsZero (L.X (i-1))) :
    IsZero ((mappingCocone f).X i) := by
  let e : (mappingCocone f).X i ≅ K.X i ⊞ L.X (i-1) :=
    shiftFunctorObjXIso (mappingCone f) (-1) i (i-1) (by omega) ≪≫
      homotopyCofiber.XIsoBiprod f (i-1) i (by change i-1+1=i; omega)
  exact IsZero.of_iso ((biprod_isZero_iff _ _).2 ⟨hK,hL⟩) e

end Tachikawa.Enveloping



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_StableLift
attribute [-instance] _root_.OAI.Tachikawa.DownHom.instAddCommGroupCochain _root_.OAI.Tachikawa.DownHom.instModuleCochain _root_.OAI.Tachikawa.Triangular.instProjectiveCarrierOneFree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace Tachikawa
open CategoryTheory HomologicalComplex
open scoped ModuleCat.Algebra
attribute [local instance] HasDerivedCategory.standard

lemma finiteResolutionLift {k R : Type} [Field k] [Ring R] [Algebra k R] [FiniteDimensional k R]
    (P : CochainComplex (ModuleCat.{0} R) ℤ) [P.IsKProjective] (M : FiniteModule k R)
    (v : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj M.obj)) :
    ∃ f : P ⟶ M.projectiveResolution.cochainComplex,
      DerivedCategory.Q.map f ≫ DerivedCategory.Q.map M.projectiveResolution.π' = v := by
  obtain ⟨f,hf⟩ := kProjective_chain_representative P M.projectiveResolution.cochainComplex
    (v ≫ inv (DerivedCategory.Q.map M.projectiveResolution.π'))
  refine ⟨f,?_⟩
  rw [hf]; simp only [Category.assoc,IsIso.inv_hom_id,Category.comp_id]

namespace HomBimodule
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  (X : ModuleCat R) (Z : ModuleCat S)
def underlyingLinearEquiv : obj (k := k) X Z ≃ₗ[k] (X →ₗ[k] Z) where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c f := by ext x; exact k_smul_apply X Z c f x
instance instFiniteDimensionalCarrierAlgObj [FiniteDimensional k X] [FiniteDimensional k Z] : FiniteDimensional k (obj (k := k) X Z) :=
  Module.Finite.equiv (underlyingLinearEquiv X Z).symm
end HomBimodule

end Tachikawa



namespace Tachikawa
variable {k R : Type} [Field k] [Ring R] [Algebra k R] [FiniteDimensional k R]
variable {M N L : Type} [AddCommGroup M] [AddCommGroup N] [AddCommGroup L]
  [Module R M] [Module R N] [Module R L] [Module k N] [Module k L]
  [IsScalarTower k R N] [IsScalarTower k R L]

namespace SymmetrizingForm
variable (t : SymmetrizingForm (k := k) (R := R))
variable {n : ℕ} (ε : (Fin n → R) →ₗ[R] M)

lemma syzygyPair_natural (b : L →ₗ[R] LinearMap.ker ε) (φ : N →ₗ[R] L)
    (f : M →ₗ[R] N) :
    t.syzygyPair ε (b.comp φ) f = t.syzygyPair ε b (φ.comp f) := by
  simp only [syzygyPair_apply]
  rw [← LinearMap.comp_assoc, t.freeHomDual_natural, LinearMap.comp_assoc]

include t in

theorem exists_nonzero_postcomposition
    (hε : Function.Surjective ε) {m p : ℕ}
    (i : M →ₗ[R] (Fin m → R)) (hi : Function.Injective i)
    (d : (Fin p → R) →ₗ[R] LinearMap.ker ε) (hd : Function.Surjective d)
    (b : L →ₗ[R] LinearMap.ker ε) (φ : N →ₗ[R] L)
    (hb : b.comp φ ∉ projectiveFactors (k := k)) :
    ∃ f : M →ₗ[R] N, φ.comp f ∉ projectiveFactors (k := k) := by
  have hp : t.syzygyPair ε (b.comp φ) ≠ 0 :=
    mt (t.syzygyPair_eq_zero_iff ε hε d hd (b.comp φ)).mp hb
  have hex : ∃ f, t.syzygyPair ε (b.comp φ) f ≠ 0 := by
    by_contra! hn
    exact hp (LinearMap.ext hn)
  obtain ⟨f, hf⟩ := hex
  refine ⟨f, fun hh => hf ?_⟩
  rw [syzygyPair_natural]
  exact t.syzygyPair_vanish_left ε i hi b (φ.comp f) hh

end SymmetrizingForm
end Tachikawa



namespace Tachikawa
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable {A B C D : Type} [AddCommGroup A] [AddCommGroup B]
  [AddCommGroup C] [AddCommGroup D] [Module R A] [Module R B]
  [Module R C] [Module R D] [Module k B] [Module k D]
  [IsScalarTower k R B] [IsScalarTower k R D]

namespace SymmetrizingForm
variable [FiniteDimensional k R] (t : SymmetrizingForm (k := k) (R := R))

include t in

theorem exists_syzygy_postcomposition (U M L : FiniteModule k R) (n : ℕ)
    (b : L.obj →ₗ[R] (U.positive (n+1)).obj) (phi : M.obj →ₗ[R] L.obj)
    (h : b.comp phi ∉ projectiveFactors (k := k)) :
    ∃ beta : (U.positive n).obj →ₗ[R] M.obj, phi.comp beta ∉ projectiveFactors (k := k) := by
  exact t.exists_nonzero_postcomposition (U.positive n).cover.map
    (U.positive n).cover.surjective ((U.positive n).embed t) ((U.positive n).embed_injective t)
    (U.positive (n+1)).cover.map (U.positive (n+1)).cover.surjective b phi h
end SymmetrizingForm
end Tachikawa



namespace Tachikawa.FiniteModule
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R] [FiniteDimensional k R]
variable (t : SymmetrizingForm (k := k) (R := R))

def syzygyInclusion (M : FiniteModule k R) : M.syzygy.obj →ₗ[R] (Fin M.cover.rank → R) :=
  (LinearMap.ker M.cover.map).subtype
lemma syzygyInclusion_injective (M : FiniteModule k R) : Function.Injective M.syzygyInclusion :=
  Subtype.val_injective
lemma syzygyInclusion_exact (M : FiniteModule k R) : Function.Exact M.syzygyInclusion M.cover.map := by
  intro x
  exact ⟨fun hx => ⟨⟨x,hx⟩,rfl⟩,fun ⟨y,hy⟩ => hy ▸ y.property⟩

def cosyzygyProjection (M : FiniteModule k R) :
    (Fin (Module.finrank k M) → R) →ₗ[R] (M.cosyzygy t).obj :=
  (LinearMap.range (M.embed t)).mkQ
lemma cosyzygyProjection_surjective (M : FiniteModule k R) : Function.Surjective (M.cosyzygyProjection t) :=
  Submodule.mkQ_surjective _
lemma cosyzygyProjection_exact (M : FiniteModule k R) :
    Function.Exact (M.embed t) (M.cosyzygyProjection t) := by
  intro x
  exact Submodule.Quotient.mk_eq_zero _

lemma negative_succ_left (M : FiniteModule k R) (n : ℕ) :
    (M.cosyzygy t).negative t n = M.negative t (n+1) := by
  induction n with
  | zero => rfl
  | succ n h => exact congrArg (fun L : FiniteModule k R => L.cosyzygy t) h

theorem descend_nonzero_composition (M U S : FiniteModule k R) (n : ℕ)
    (beta : (U.positive (n+1)).obj →ₗ[R] M.obj)
    (phi : M.obj →ₗ[R] (S.positive (n+2)).obj)
    (hn : phi.comp beta ∉ projectiveFactors (k := k)) :
    ∃ (g : (U.positive n).obj →ₗ[R] (M.cosyzygy t).obj)
      (psi : (M.cosyzygy t).obj →ₗ[R] (S.positive (n+1)).obj),
      psi.comp g ∉ projectiveFactors (k := k) := by
  let : Module.Injective R R := t.injective
  let PU := ModuleCat.of R (Fin (U.positive n).cover.rank → R)
  let PM := ModuleCat.of R (Fin (Module.finrank k M) → R)
  let PS := ModuleCat.of R (Fin (S.positive (n+1)).cover.rank → R)
  obtain ⟨h,g,hu,hl⟩ := exists_exact_square_down (P := PU) (Q := PM)
    (U.positive n).syzygyInclusion (U.positive n).cover.map
    (U.positive n).syzygyInclusion_injective (U.positive n).syzygyInclusion_exact
    (U.positive n).cover.surjective (M.embed t) (M.cosyzygyProjection t)
    (M.cosyzygyProjection_exact t) beta
  obtain ⟨h',psi,hu',hl'⟩ := exists_exact_square_down (P := PM) (Q := PS)
    (M.embed t) (M.cosyzygyProjection t) (M.embed_injective t)
    (M.cosyzygyProjection_exact t) (M.cosyzygyProjection_surjective t)
    (S.positive (n+1)).syzygyInclusion (S.positive (n+1)).cover.map
    (S.positive (n+1)).syzygyInclusion_exact phi
  refine ⟨g,psi,?_⟩
  apply mt (exact_square_factors_iff (P := PU) (Q := PS)
    (U.positive n).syzygyInclusion (U.positive n).cover.map
    (U.positive n).syzygyInclusion_injective (U.positive n).syzygyInclusion_exact
    (U.positive n).cover.surjective
    (S.positive (n+1)).syzygyInclusion (S.positive (n+1)).cover.map
    (S.positive (n+1)).syzygyInclusion_injective (S.positive (n+1)).syzygyInclusion_exact
    (S.positive (n+1)).cover.surjective
    (phi.comp beta) (h'.comp h) (psi.comp g) ?_ ?_).mpr hn
  · erw [LinearMap.comp_assoc,hu,← LinearMap.comp_assoc,hu',LinearMap.comp_assoc]
  · rw [← LinearMap.comp_assoc,hl',LinearMap.comp_assoc,hl,← LinearMap.comp_assoc]

theorem descend_nonzero_composition_iterated (U S : FiniteModule k R) (n : ℕ)
    (M : FiniteModule k R) (beta : (U.positive n).obj →ₗ[R] M.obj)
    (phi : M.obj →ₗ[R] (S.positive (n+1)).obj)
    (hn : phi.comp beta ∉ projectiveFactors (k := k)) :
    ∃ (g : U.obj →ₗ[R] (M.negative t n).obj)
      (psi : (M.negative t n).obj →ₗ[R] (S.positive 1).obj),
      psi.comp g ∉ projectiveFactors (k := k) := by
  induction n generalizing M with
  | zero => exact ⟨beta,phi,hn⟩
  | succ n ih =>
    obtain ⟨g,psi,hg⟩ := descend_nonzero_composition t M U S n beta phi hn
    rw [← negative_succ_left t M n]
    exact ih (M.cosyzygy t) g psi hg
end Tachikawa.FiniteModule



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_HomProfile
attribute [-instance] _root_.OAI.Tachikawa.DownHom.instAddCommGroupCochain _root_.OAI.Tachikawa.DownHom.instModuleCochain _root_.OAI.Tachikawa.Triangular.instProjectiveCarrierOneFree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace Tachikawa
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R] [FiniteDimensional k R]
variable (t : SymmetrizingForm (k := k) (R := R))
  (P : ChainComplex (ModuleCat.{0} R) ℤ) (hP : ComplexExact P)
  (fin : ∀ j, Module.Finite R (P.X j)) (proj : ∀ j, Module.Projective R (P.X j))

def cosyCokerStableEquiv (M : FiniteModule k R) (j : ℤ)
    (e : StableEquiv (k := k) M.obj (ModuleCat.of R (CokerAt P j))) :
    StableEquiv (k := k) (M.cosyzygy t).obj (ModuleCat.of R (CokerAt P (j-1))) := by
  let : Module.Injective R R := t.injective
  let := fin (j-1)
  let := proj (j-1)
  exact StableEquiv.down (P := ModuleCat.of R (Fin (Module.finrank k M) → R))
    (Q := P.X (j-1)) (M.embed t) (M.cosyzygyProjection t) (M.embed_injective t)
    (M.cosyzygyProjection_exact t) (M.cosyzygyProjection_surjective t)
    (CokerAt.δ P j (j-1)) (CokerAt.π P (j-1))
    (CokerAt.δ_injective P hP j (j-1) (by omega))
    (CokerAt.δ_π_exact P j (j-1) (by omega)) (CokerAt.π_surjective P (j-1)) e

def syzyCokerStableEquiv (M : FiniteModule k R) (j : ℤ)
    (e : StableEquiv (k := k) M.obj (ModuleCat.of R (CokerAt P j))) :
    StableEquiv (k := k) M.syzygy.obj (ModuleCat.of R (CokerAt P (j+1))) := by
  let : Module.Injective R R := t.injective
  let := fin j
  let := proj j
  exact StableEquiv.up (P := ModuleCat.of R (Fin M.cover.rank → R))
    (Q := P.X j) M.syzygyInclusion M.cover.map M.syzygyInclusion_injective
    M.syzygyInclusion_exact M.cover.surjective
    (CokerAt.δ P (j+1) j) (CokerAt.π P j)
    (CokerAt.δ_injective P hP (j+1) j rfl)
    (CokerAt.δ_π_exact P (j+1) j rfl) (CokerAt.π_surjective P j) e

def negativeCokerStableEquiv (M : FiniteModule k R) (j : ℤ)
    (e : StableEquiv (k := k) M.obj (ModuleCat.of R (CokerAt P j))) (n : ℕ) :
    StableEquiv (k := k) (M.negative t n).obj (ModuleCat.of R (CokerAt P (j-(n:ℤ)))) := by
  induction n with
  | zero =>
    change StableEquiv (k := k) M.obj (ModuleCat.of R (CokerAt P (j-0)))
    rw [sub_zero]
    exact e
  | succ n ih =>
    change StableEquiv (k := k) ((M.negative t n).cosyzygy t).obj _
    rw [show j-((n+1:ℕ):ℤ) = (j-(n:ℤ))-1 by omega]
    exact cosyCokerStableEquiv t P hP fin proj _ _ ih

def positiveCokerStableEquiv (M : FiniteModule k R) (j : ℤ)
    (e : StableEquiv (k := k) M.obj (ModuleCat.of R (CokerAt P j))) (n : ℕ) :
    StableEquiv (k := k) (M.positive n).obj (ModuleCat.of R (CokerAt P (j+(n:ℤ)))) := by
  induction n with
  | zero =>
    change StableEquiv (k := k) M.obj (ModuleCat.of R (CokerAt P (j+0)))
    rw [add_zero]
    exact e
  | succ n ih =>
    change StableEquiv (k := k) (M.positive n).syzygy.obj _
    rw [show j+((n+1:ℕ):ℤ) = (j+(n:ℤ))+1 by omega]
    exact syzyCokerStableEquiv t P hP fin proj _ _ ih

end Tachikawa



namespace Tachikawa
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R] [FiniteDimensional k R]
variable (t : SymmetrizingForm (k := k) (R := R))
  (P : ChainComplex (ModuleCat.{0} R) ℤ) (hP : ComplexExact P)
  (fin : ∀ j, Module.Finite R (P.X j)) (proj : ∀ j, Module.Projective R (P.X j))

def finiteCoker (j : ℤ) : FiniteModule k R where
  obj := ModuleCat.of R (CokerAt P j)
  finite := by
    let := fin j
    exact inferInstanceAs (Module.Finite R (P.X j ⧸ LinearMap.range (P.d (j+1) j).hom))

def completeCokerDuality (j : ℤ) (N : ModuleCat.{0} R) :
    StableMap (k := k) N (ModuleCat.of R (CokerAt P (j+1))) ≃ₗ[k]
      Module.Dual k (StableMap (k := k) (ModuleCat.of R (CokerAt P j)) N) := by
  let M := finiteCoker (k := k) P fin j
  let e := syzyCokerStableEquiv t P hP fin proj M j (StableEquiv.refl _)
  let e₀ := stablePostEquiv (k := k) (R := R) (M := N)
    (N := M.syzygy.obj) (N' := LinearMap.ker M.cover.map) (LinearEquiv.refl R _)
  exact (e.post N).symm.trans (e₀.trans
    (t.stableDualEquiv M.cover.map M.cover.surjective (M.embed t) (M.embed_injective t)
      M.syzygy.cover.map M.syzygy.cover.surjective))

end Tachikawa



namespace Tachikawa
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable (P : ChainComplex (ModuleCat R) ℤ) (hP : ComplexExact P)

variable (Q : ChainComplex (ModuleCat R) ℤ) (hQ : ComplexExact Q)
  (fP : ∀ i, Module.Finite R (P.X i)) (pP : ∀ i, Module.Projective R (P.X i))
  (fQ : ∀ i, Module.Finite R (Q.X i)) (pQ : ∀ i, Module.Projective R (Q.X i))
  [Module.Injective R R]

def cokerStableHomSucc (i j : ℤ) :
    StableMap (k := k) (ModuleCat.of R (CokerAt P i)) (ModuleCat.of R (CokerAt Q j)) ≃ₗ[k]
    StableMap (k := k) (ModuleCat.of R (CokerAt P (i+1))) (ModuleCat.of R (CokerAt Q (j+1))) := by
  let := fP i
  let := pP i
  let := fQ j
  let := pQ j
  let e := StableShift.equiv (k := k) (CokerAt.π P i) (CokerAt.π Q j)
    (CokerAt.π_surjective Q j) (CokerAt.π_surjective P i)
  let eP := StableEquiv.ofLinearEquiv (k := k)
    (M := ModuleCat.of R (CokerAt P (i+1)))
    (N := ModuleCat.of R (LinearMap.ker (CokerAt.π P i))) (cokerKernelEquiv P hP i)
  let eQ := StableEquiv.ofLinearEquiv (k := k)
    (M := ModuleCat.of R (CokerAt Q (j+1)))
    (N := ModuleCat.of R (LinearMap.ker (CokerAt.π Q j))) (cokerKernelEquiv Q hQ j)
  exact e.trans ((eP.pre _).symm.trans (eQ.post _).symm)

def cokerStableHomNat (i j : ℤ) (n : ℕ) :
    StableMap (k := k) (ModuleCat.of R (CokerAt P i)) (ModuleCat.of R (CokerAt Q j)) ≃ₗ[k]
    StableMap (k := k) (ModuleCat.of R (CokerAt P (i+(n:ℤ)))) (ModuleCat.of R (CokerAt Q (j+(n:ℤ)))) := by
  induction n with
  | zero =>
    rw [Nat.cast_zero,add_zero,add_zero]
  | succ n ih =>
    have e := cokerStableHomSucc P hP Q hQ fP pP fQ pQ (i+(n:ℤ)) (j+(n:ℤ)) (k := k)
    rw [show i+((n+1:ℕ):ℤ) = i+(n:ℤ)+1 by omega,
      show j+((n+1:ℕ):ℤ) = j+(n:ℤ)+1 by omega]
    exact ih.trans e

def cokerStableHomTranslate (i j a : ℤ) :
    StableMap (k := k) (ModuleCat.of R (CokerAt P i)) (ModuleCat.of R (CokerAt Q j)) ≃ₗ[k]
    StableMap (k := k) (ModuleCat.of R (CokerAt P (i+a))) (ModuleCat.of R (CokerAt Q (j+a))) := by
  cases a with
  | ofNat n => exact cokerStableHomNat P hP Q hQ fP pP fQ pQ i j n
  | negSucc n =>
    have e := (cokerStableHomNat P hP Q hQ fP pP fQ pQ
      (i+Int.negSucc n) (j+Int.negSucc n) (n+1) (k := k)).symm
    rw [show i+Int.negSucc n+((n+1:ℕ):ℤ)=i by omega,
      show j+Int.negSucc n+((n+1:ℕ):ℤ)=j by omega] at e
    exact e

end Tachikawa



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Delta
attribute [-instance] _root_.OAI.Tachikawa.DownHom.instAddCommGroupCochain _root_.OAI.Tachikawa.DownHom.instModuleCochain
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
  {X M F Y Q : ModuleCat R}

lemma exists_stable_kernel_lift (i : F ⟶ M) (p : M ⟶ Y) (j : Q ⟶ M)
    (hi : Function.Injective i) (he : Function.Exact i p)
    (hq : Function.Surjective (j ≫ p)) (a : X ⟶ M)
    (ha : stableClass (k := k) (a ≫ p).hom = 0) :
    ∃ (v : X ⟶ F) (b : X ⟶ Q), v ≫ i = a - b ≫ j := by
  obtain ⟨P,hfin,hproj,u,w,hw⟩ := (stableClass_eq_zero_iff _).mp ha
  let := hproj
  obtain ⟨l,hl⟩ := Module.projective_lifting_property (j ≫ p).hom w hq
  let b : X ⟶ Q := ModuleCat.ofHom (l.comp u)
  have hzero : (a - b ≫ j) ≫ p = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change p (a x - j (l (u x))) = 0
    rw [map_sub]
    have h := LinearMap.congr_fun hw x
    change w (u x) = p (a x) at h
    have h' := LinearMap.congr_fun hl (u x)
    change p (j (l (u x))) = w (u x) at h'
    rw [h',h,sub_self]
  let e := LinearEquiv.ofInjective i.hom hi
  have hr (x : X) : (a - b ≫ j) x ∈ LinearMap.range i.hom := by
    exact (he _).mp (congrArg (fun f => f x) hzero)
  let c : X →ₗ[R] LinearMap.range i.hom := (a - b ≫ j).hom.codRestrict _ hr
  refine ⟨ModuleCat.ofHom (e.symm.toLinearMap.comp c), b, ?_⟩
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact congrArg Subtype.val (e.apply_symm_apply (c x))

end Tachikawa



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_DownHom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace Tachikawa.DownHom
open CategoryTheory HomologicalComplex CategoryTheory.Preadditive
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable {P Q : ChainComplex (ModuleCat.{0} R) ℤ} {N : ModuleCat.{0} R}
  (ε : Q.X 0 ⟶ N) (hε : Q.d 1 0 ≫ ε = 0)

def evalCycle {a : ℤ} (f : Cochain P Q a) (hf : Closed f) :
    VectorSplit.Z (completeHom (k := k) P N) a :=
  ⟨f a 0 (by omega) ≫ ε, by
    apply (completeHom_memZ P N a _).mpr
    erw [← Category.assoc,← hf (a+1) 1 a 0 (by omega) (by omega),
      Category.assoc,hε,Limits.comp_zero]⟩

def evalClass {a : ℤ} (f : Cochain P Q a) (hf : Closed f) :
    VectorSplit.H (completeHom (k := k) P N) a :=
  VectorSplit.quotient _ a (evalCycle ε hε f hf)

end Tachikawa.DownHom



namespace Tachikawa.DownHom
open CategoryTheory CategoryTheory.Preadditive CategoryTheory.Limits
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R]  [Algebra k R]
variable {P Q : ChainComplex (ModuleCat.{0} R) ℤ} {N : ModuleCat.{0} R}
  (ε : Q.X 0 ⟶ N) (hε : Q.d 1 0 ≫ ε = 0)

variable (F : ModuleCat.{0} R ⥤ ModuleCat.{0} R) [F.Additive]

variable [F.Linear k] (X : ModuleCat.{0} R) (εP : P.X 0 ⟶ X)
  (hεP : P.d 1 0 ≫ εP = 0) (u : P ⟶ mapComplex F P) (u₀ : X ⟶ F.obj X)
  (hu : u.f 0 ≫ F.map εP = εP ≫ u₀)

abbrev homologyDelta (a : ℤ) :
    (VectorSplit.H (completeHom (k := k) P X) a × VectorSplit.H (completeHom (k := k) P X) a) →ₗ[k]
    VectorSplit.H (completeHom (k := k) P (F.obj X)) a :=
  (VectorSplit.Hmap (completeFunctorHom F P P X u) a).coprod
    (VectorSplit.Hmap (completeHomMap P u₀) a)

end Tachikawa.DownHom



end

end OAI
end


