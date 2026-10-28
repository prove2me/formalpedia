-- Prove2me | Definitions.Def_OAIQ66So032
-- name    : OAIQ66So032
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T02:50:37.008622+00:00
-- url     : https://prove2.me/theorems/dacb2a40-1f36-4530-8b79-d334f5355198
-- title:
--   Definitions bundle OAIQ66So032 of the split of OpenAI, Simple F-infinity overgroups of groups with decidable word problem (OpenAI result)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SimpleFInftyOvergroups.main`, carved from OpenAI's openai/math development (OpenAI, *Simple F-infinity overgroups of groups with decidable word problem (OpenAI result)*, OpenAI Math Release, September 23, 2026, result family 250, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 115 declarations of OpenAI's Lean: 47 definitions, 11 instances and 57 theorems. The definitions and types are `OAI.SimpleFInftyOvergroups.SourceModel.Astar`, `OAI.SimpleFInftyOvergroups.SourceModel.Generators`, `OAI.SimpleFInftyOvergroups.SourceModel.ProdMon`, `OAI.SimpleFInftyOvergroups.SourceModel.Relations`, `OAI.SimpleFInftyOvergroups.SourceModel.Symbols`, `OAI.SimpleFInftyOvergroups.SourceModel.actionCornerMap`, `OAI.SimpleFInftyOvergroups.SourceModel.actionEval`, `OAI.SimpleFInftyOvergroups.SourceModel.binary`, `OAI.SimpleFInftyOvergroups.SourceModel.calculus`, `OAI.SimpleFInftyOvergroups.SourceModel.code`, `OAI.SimpleFInftyOvergroups.SourceModel.codeAction`, `OAI.SimpleFInftyOvergroups.SourceModel.codeAction₀`, `OAI.SimpleFInftyOvergroups.SourceModel.codeG`, `OAI.SimpleFInftyOvergroups.SourceModel.codeProduct`, `OAI.SimpleFInftyOvergroups.SourceModel.codeProduct₀`, `OAI.SimpleFInftyOvergroups.SourceModel.cornerMap`, `OAI.SimpleFInftyOvergroups.SourceModel.e`, `OAI.SimpleFInftyOvergroups.SourceModel.groupCornerMap`, `OAI.SimpleFInftyOvergroups.SourceModel.i`, `OAI.SimpleFInftyOvergroups.SourceModel.instLinearOrderSectorSigmaProdBoolΓFamilyStateQIndex_1`, `OAI.SimpleFInftyOvergroups.SourceModel.normalPresentation`, `OAI.SimpleFInftyOvergroups.SourceModel.presentation`, `OAI.SimpleFInftyOvergroups.SourceModel.presentationMap`, `OAI.SimpleFInftyOvergroups.SourceModel.productEval`, `OAI.SimpleFInftyOvergroups.SourceModel.rawCopy`, `OAI.SimpleFInftyOvergroups.SourceModel.search`, `OAI.SimpleFInftyOvergroups.SourceModel.tests`, `OAI.SimpleFInftyOvergroups.SourceModel.value`, `OAI.SimpleFInftyOvergroups.SourceModel.κ`, `OAI.SimpleFInftyOvergroups.SourceModel.ξ`, `OAI.SimpleFInftyOvergroups.SourceModel.π`, `OAI.SimpleFInftyOvergroups.SourceModel.σ`, `OAI.SimpleFInftyOvergroups.SourceModel.φ`, `OAI.StageGeometry.compressedUnits`, `OAI.StageGeometry.conjugated`, `OAI.Steinberg.coefficients`, `OAI.Steinberg.descendCoefficients`, `OAI.Steinberg.rootSet`, `OAI.Steinberg.unitLift`, `OAI.SteinbergFinitePresentation.Universal` and 7 more.
--
--   **Sources.** They come from these modules of lean/OAI/GroupTheory, in whole or in part: [`FiniteType_AscendingHNNInnerTwist`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/FiniteType/AscendingHNNInnerTwist.lean), [`FiniteType_SteinbergFinitePresentation`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/FiniteType/SteinbergFinitePresentation.lean), [`FiniteType_SteinbergSixThree`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/FiniteType/SteinbergSixThree.lean), [`FiniteType_TorusAction`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/FiniteType/TorusAction.lean), [`SimpleOvergroups_RingModel`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/SimpleOvergroups/RingModel.lean), [`SimpleOvergroups_SemanticTests`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/SimpleOvergroups/SemanticTests.lean), [`SimpleOvergroups_SourceModel`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/SimpleOvergroups/SourceModel.lean), [`SimpleOvergroups_SourceProducer`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/SimpleOvergroups/SourceProducer.lean).
--
--   **Imports.** It imports the bundles `OAIQ66So030` and `OAIQ66So031` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ66So034`.
-- source:
--   OpenAI, Simple F-infinity overgroups of groups with decidable word problem (OpenAI result), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 250; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/ComparatorChallenges/SimpleOvergroups.lean; Apache License 2.0); definitions carved from lean/OAI/GroupTheory at commit 1581d4c

import Mathlib
import Definitions.Def_OAIQ66So030
import Definitions.Def_OAIQ66So031

section
-- module Solutions.OAIQ066_SO.FiniteType_SteinbergSixThree
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Pointwise
open scoped commutatorElement

namespace Steinberg
variable {R : Type*} [Ring R]

noncomputable def unitLift (φ : R →ₙ+* R) (D : CompressedSplittings.BinaryData φ) :
    Rˣ →* Group (Fin 6) R :=
  (descended φ D).comp (NoncommElementary.compressed φ D 0 1 (by decide))

end Steinberg

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_TorusAction
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Pointwise

namespace Steinberg
section
variable {n R : Type*} [Ring R]
variable (spare : ∀ i j : n, i≠j → ∃ k, i≠k ∧ k≠j)

def coefficients (N : Subgroup (Group n R)) [N.Normal] : TwoSidedIdeal R :=
  TwoSidedIdeal.mk' {a | ∀ i j hij, root i j hij a∈N}
    (by intro i j hij; rw [root_zero]; exact N.one_mem)
    (by intro a b ha hb i j hij; rw [← root_add]; exact N.mul_mem (ha _ _ _) (hb _ _ _))
    (by intro a ha i j hij; rw [root_neg]; exact N.inv_mem (ha _ _ _))
    (by
      intro a b hb i j hij
      obtain ⟨k,hik,hkj⟩ := spare i j hij
      rw [← root_commutator i k j hik hkj hij]
      exact Subgroup.commutator_le_right ⊤ N
        (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (hb k j hkj)))
    (by
      intro a b ha i j hij
      obtain ⟨k,hik,hkj⟩ := spare i j hij
      rw [← root_commutator i k j hik hkj hij]
      exact Subgroup.commutator_le_left N ⊤
        (Subgroup.commutator_mem_commutator (ha i k hik) (Subgroup.mem_top _)))

@[simp] lemma mem_coefficients (N : Subgroup (Group n R)) [N.Normal] (a : R) :
    a∈coefficients spare N ↔ ∀ i j hij, root i j hij a∈N := by
  simp [coefficients]

def rootSet (s : Set R) : Set (Group n R) :=
  {g | ∃ i j hij a, a∈s ∧ g=root i j hij a}

end

section
variable {n R S H : Type*} [Ring R] [Ring S] [_root_.Group H]

lemma root_sub (i j : n) (hij : i≠j) (a b : R) :
    root i j hij (a-b)=root i j hij a*(root i j hij b)⁻¹ := by
  rw [sub_eq_add_neg,← root_add,root_neg]

lemma root_image_eq (φ : R →ₙ+* S) (f : Group n R →* H)
    (hker : ∀ i j hij a, φ a=0 → f (root i j hij a)=1)
    (i j : n) (hij : i≠j) {a b : R} (hab : φ a=φ b) :
    f (root i j hij a)=f (root i j hij b) := by
  have h := hker i j hij (a-b) (by rw [map_sub,hab,sub_self])
  rw [root_sub,map_mul,map_inv] at h
  exact eq_of_mul_inv_eq_one h

def descendCoefficients (φ : R →ₙ+* S) (hφ : Function.Surjective φ)
    (f : Group n R →* H)
    (hker : ∀ i j hij a, φ a=0 → f (root i j hij a)=1) : Group n S →* H :=
  lift (fun i j hij a => f (root i j hij (Function.surjInv hφ a)))
    (by
      intro i j hij a b
      rw [← map_mul,root_add]
      apply root_image_eq φ f hker
      simp only [map_add,Function.surjInv_eq])
    (by
      intro i j k hij hjk hik a b
      rw [← map_commutatorElement,root_commutator i j k hij hjk hik]
      apply root_image_eq φ f hker
      simp only [map_mul,Function.surjInv_eq])
    (by
      intro i j k l hij hkl hil hjk a b
      exact (root_commute i j k l hij hkl hil hjk _ _).map f)

end

end Steinberg

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_SteinbergFinitePresentation
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Pointwise
section
open scoped commutatorElement
namespace SteinbergFinitePresentation
open scoped commutatorElement
variable (n α : Type*)

def letter (i j : n) (hij : i≠j) (a : Option α) : FreeGroup (Steinberg.Root n (Option α)) :=
  FreeGroup.of ⟨i,j,hij,a⟩

def relator : Index n α → FreeGroup (Steinberg.Root n (Option α))
  | .inl (q,a,b) =>
    ⁅letter n α q.1.1 q.1.2.1 q.2.1 a,
      letter n α q.1.2.2.1 q.1.2.2.2 q.2.2.1 b⁆
  | .inr (right,t,a) =>
    ⁅letter n α t.1.1 t.1.2.1 t.2.1 (if right then a else none),
      letter n α t.1.2.1 t.1.2.2 t.2.2.1 (if right then none else a)⁆*
      (letter n α t.1.1 t.1.2.2 t.2.2.2 a)⁻¹

def relations : Set (FreeGroup (Steinberg.Root n (Option α))) := Set.range (relator n α)
abbrev Universal := PresentedGroup (relations n α)

instance instFiniteRoot [Finite n] [Finite α] : Finite (Steinberg.Root n α) := by
  apply Finite.of_injective (fun r : Steinberg.Root n α => (r.i,r.j,r.coefficient))
  rintro ⟨i,j,hij,a⟩ ⟨k,l,hkl,b⟩ he
  simp only [Prod.mk.injEq] at he
  rcases he with ⟨rfl,rfl,rfl⟩
  rfl

instance instFiniteElemFreeGroupRootOptionRelations [Finite n] [Finite α] : Finite (relations n α) :=
  (Set.finite_range (relator n α)).to_subtype
instance instIsFinitelyPresentedUniversalOfFinite [Finite n] [Finite α] : Group.IsFinitelyPresented (Universal n α) := inferInstance

lemma relator_eq_one (r : Index n α) :
    PresentedGroup.mk (relations n α) (relator n α r)=1 :=
  PresentedGroup.one_of_mem ⟨r,rfl⟩

def initial : SteinbergWords.Initial (n:=n) (α:=α) (H:=Universal n α) where
  gen i j hij a := PresentedGroup.of ⟨i,j,hij,a⟩
  away i j k l hij hkl hil hjk a b := by
    apply commutatorElement_eq_one_iff_commute.mp
    exact relator_eq_one n α (.inl (⟨(i,j,k,l),⟨hij,hkl,hil,hjk⟩⟩,a,b))
  chain_left i j k hij hjk hik a := by
    have he := relator_eq_one n α (.inr (false,⟨(i,j,k),⟨hij,hjk,hik⟩⟩,a))
    simpa only [relator,Bool.false_eq_true,↓reduceIte,map_mul,map_inv,map_commutatorElement,
      letter,PresentedGroup.of,mul_inv_eq_one] using he
  chain_right i j k hij hjk hik a := by
    have he := relator_eq_one n α (.inr (true,⟨(i,j,k),⟨hij,hjk,hik⟩⟩,a))
    simpa only [relator,↓reduceIte,map_mul,map_inv,map_commutatorElement,
      letter,PresentedGroup.of,mul_inv_eq_one] using he

def toSteinberg : Universal n α →* Steinberg.Group n (Coeff α) :=
  PresentedGroup.toGroup (f:=fun r : Steinberg.Root n (Option α) =>
    Steinberg.root r.i r.j r.different (coefficient α r.coefficient)) (by
    rintro _ ⟨r,rfl⟩
    cases r with
    | inl q =>
      rcases q with ⟨q,a,b⟩
      simp only [relator,letter,map_commutatorElement,FreeGroup.lift_apply_of]
      exact (Steinberg.root_commute _ _ _ _ q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2 _ _).commutator_eq
    | inr t =>
      rcases t with ⟨right,t,a⟩
      cases right <;>
        simp only [relator,Bool.false_eq_true,↓reduceIte,letter,map_mul,map_inv,
          map_commutatorElement,FreeGroup.lift_apply_of]
      · rw [Steinberg.root_commutator _ _ _ t.2.1 t.2.2.1 t.2.2.2]
        simp only [coefficient,one_mul,mul_inv_cancel]
      · rw [Steinberg.root_commutator _ _ _ t.2.1 t.2.2.1 t.2.2.2]
        simp only [coefficient,mul_one,mul_inv_cancel])

@[simp] lemma toSteinberg_gen (i j : n) (hij : i≠j) (a : Option α) :
    toSteinberg n α ((initial n α).gen i j hij a)=
      Steinberg.root i j hij (coefficient α a) := PresentedGroup.toGroup.of _

variable (outside : ∀ i j k l : n, ∃ p, p≠i ∧ p≠j ∧ p≠k ∧ p≠l)

def fromSteinberg : Steinberg.Group n (Coeff α) →* Universal n α :=
  Steinberg.lift (SteinbergWords.polynomial outside (initial n α))
    (fun i j h a b => (SteinbergWords.polynomial_add outside (initial n α) i j h a b).symm)
    (SteinbergWords.polynomial_chain outside (initial n α))
    (SteinbergWords.polynomial_commute outside (initial n α))

lemma polynomial_coefficient (i j : n) (hij : i≠j) (a : Option α) :
    SteinbergWords.polynomial outside (initial n α) i j hij (coefficient α a)=
      (initial n α).gen i j hij a := by
  cases a with
  | none =>
    change SteinbergWords.polynomial outside (initial n α) i j hij (FreeAbelianGroup.of 1)=_
    rw [SteinbergWords.polynomial_of]
    exact SteinbergWords.word_nil outside (initial n α) i j hij
  | some a =>
    rw [coefficient,SteinbergWords.polynomial_of]
    exact SteinbergWords.word_singleton outside (initial n α) i j hij a

lemma from_to : (fromSteinberg n α outside).comp (toSteinberg n α)=MonoidHom.id _ := by
  apply PresentedGroup.ext
  rintro ⟨i,j,hij,a⟩
  change fromSteinberg n α outside (toSteinberg n α ((initial n α).gen i j hij a))=_
  rw [toSteinberg_gen,fromSteinberg,Steinberg.lift_root]
  exact polynomial_coefficient n α outside i j hij a

lemma toSteinberg_word (w : List α) (i j : n) (hij : i≠j) :
    toSteinberg n α (SteinbergWords.word outside (initial n α) i j hij w)=
      Steinberg.root (R:=Coeff α) i j hij (FreeAbelianGroup.of (FreeMonoid.ofList w)) := by
  induction w generalizing i j with
  | nil => exact toSteinberg_gen n α i j hij none
  | cons a w ih =>
    obtain ⟨k,hki,hkj,-,-⟩ := outside i j i j
    have he := SteinbergWords.word_chain outside (initial n α) [a] w i k j hki.symm hkj hij
    rw [List.singleton_append] at he
    rw [← he,map_commutatorElement,SteinbergWords.word_singleton,toSteinberg_gen,ih,
      Steinberg.root_commutator _ _ _ hki.symm hkj hij]
    change Steinberg.root i j hij (FreeAbelianGroup.of (FreeMonoid.of a)*
        FreeAbelianGroup.of (FreeMonoid.ofList w))=_
    rw [FreeAbelianGroup.of_mul_of]
    rfl

lemma toSteinberg_polynomial (i j : n) (hij : i≠j) (a : Coeff α) :
    toSteinberg n α (SteinbergWords.polynomial outside (initial n α) i j hij a)=
      Steinberg.root i j hij a := by
  induction a using FreeAbelianGroup.induction_on with
  | zero => simp
  | of w =>
    rw [SteinbergWords.polynomial_of]
    exact toSteinberg_word n α outside w i j hij
  | neg a ha =>
    rw [SteinbergWords.polynomial_neg,map_inv,ha,Steinberg.root_neg]
  | add a b ha hb =>
    rw [SteinbergWords.polynomial_add,map_mul,ha,hb,Steinberg.root_add]

lemma to_from : (toSteinberg n α).comp (fromSteinberg n α outside)=MonoidHom.id _ := by
  apply Steinberg.hom_ext
  intro i j hij a
  change toSteinberg n α (fromSteinberg n α outside (Steinberg.root i j hij a))=_
  rw [fromSteinberg,Steinberg.lift_root]
  exact toSteinberg_polynomial n α outside i j hij a

def equiv : Universal n α ≃* Steinberg.Group n (Coeff α) where
  toFun := toSteinberg n α
  invFun := fromSteinberg n α outside
  left_inv x := DFunLike.congr_fun (from_to n α outside) x
  right_inv x := DFunLike.congr_fun (to_from n α outside) x
  map_mul' := (toSteinberg n α).map_mul

end SteinbergFinitePresentation
end

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_AscendingHNNInnerTwist
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Pointwise

namespace StageGeometry
open StageConstruction

variable {R Y W : Type} [Ring R] [Group W] [MulAction W Y]
variable (φ : R →ₙ+* R) (D : CompressedSplittings.BinaryData φ)
variable (S : Y → R) (ρ : W →* Rˣ) (ι : Q R →* W) (point : X R → Y)
variable (hρS : ∀ w y, (ρ w).val*S y=S (w • y))
variable (hpoint : ∀ q x, ι q • point x=point (q • x))
variable (hφ : Function.Injective φ) (hρ : Function.Injective ρ)
variable (hι : Function.Injective ι)

variable {J : Type} (z : J → X R) (a : Q R)

abbrev compressedUnits : compressedFixing φ (fun j => S (point (z j))) a →* Rˣ :=
  (ρ.comp ι).comp (compressedFixing φ (fun j => S (point (z j))) a).subtype

variable (T : Y → R) (hTρ : ∀ w y, T y*(ρ w).val=T (w⁻¹ • y))

variable (K : Type) [CommRing K] (F : PairDiagrams K ι point)

abbrev conjugated : W →* Q R :=
  (MulAut.conj a).toMonoidHom.comp ((transitionUnits φ D).comp ρ)

end StageGeometry

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_SemanticTests
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open scoped Classical

namespace SimpleFInftyOvergroups.SemanticEncoding
open BoundedEncoding EffectiveNames NamedAction StageConstruction
namespace SemanticTests

variable {A R : Type} [Primcodable A] [Ring R] [Algebra (ZMod 2) R]
  (π : SemanticMatrix.Raw (ZMod 2) A →ₐ[ZMod 2] R)
  (σ : R → SemanticMatrix.Raw (ZMod 2) A) (hσ : Function.Injective σ)
  {m : ℕ} (C : WordCalculus (FreeMonoid A) m)

 attribute [local instance] OAI.SimpleFInftyOvergroups.SemanticEncoding.SemanticTests.instPrimcodableZModOfNatNat_solutions
attribute [local instance] OAI.SimpleFInftyOvergroups.SemanticEncoding.SemanticTests.instPrimcodableZModOfNatNat_solutions_1
theorem keys_eq_iff (u v : List (Symbols (A:=A))) :
    (N₂ C).totalTest (I π σ hσ C).gkey (I π σ hσ C).xkey u =
      (N₂ C).totalTest (I π σ hσ C).gkey (I π σ hσ C).xkey v ↔
    evaluation π σ hσ C (FreeMonoid.ofList u) = evaluation π σ hσ C (FreeMonoid.ofList v) :=
  SemanticActionMonoid.totalTest_eq_iff (I π σ hσ C)
    (SemanticDouble.groupKey_injective (baseC σ hσ (m:=m))
      (SemanticMatrix.groupKey_injective σ hσ))
    (SemanticDouble.pointKey_injective (baseC σ hσ (m:=m))
      (SemanticMatrix.pointKey_injective σ hσ)) u v

end SemanticTests
end SimpleFInftyOvergroups.SemanticEncoding
end

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_SourceModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SimpleFInftyOvergroups.SourceModel
noncomputable section
open scoped Classical FiniteAlgebraicEnvelopes.Compiler.HeadCodec
open FiniteAlgebraicEnvelopes Bootstrap Compiler Compiler.Simulator MachineRealization
open ContextualEncoding SemanticEncoding EffectiveNames

local instance instDecidableRelSigmaRel_r7e9fab_1 : DecidableRel ContextualEncoding.Source.rel := fun _ _ => inferInstanceAs (Decidable (_ < _))
abbrev Symbols (k : ℕ) := ContextualEncoding.Source.Symbols (Γ:=family.Γ) (Q:=family.Q) (P₁:=P₂) (P₂:=P₃) k
local instance (k : ℕ) (i : Fin 3) : Primcodable (Symbols k i) :=
  ContextualEncoding.Source.instPrimcodableSymbols i
abbrev code (k : ℕ) := ContextualEncoding.Source.code (Γ:=family.Γ) (Q:=family.Q) (P₁:=P₂) (P₂:=P₃) (k:=k)
abbrev search (k : ℕ) := ContextualEncoding.Source.search (Γ:=family.Γ) (Q:=family.Q) (P₁:=P₂) (P₂:=P₃) (k:=k)

variable {G : Type} [Group G] {k : ℕ} (s : Fin k → G)
variable (h : ComputablePred (fun w => FiniteAlgebraicEnvelopes.evalWord s w = 1))

abbrev tests := fun i => ContextualEncoding.Source.test s family.A family.M
  (IdempotentNames.name (k:=ZMod 2)) (IdempotentNames.name (k:=ZMod 3)) i (index s h)
abbrev value := fun i => Search.value (tests s h i)

theorem index_fixed : ContextualEncoding.Source.raw (index s h) = tableNormal (processor s h) :=
  (bootstrap s h).choose_spec.1
 theorem index_good (n : ℕ) : GoodTable (r:=ContextualEncoding.Source.rel) (processor s h) n :=
  ((bootstrap s h).choose_spec.2 n).1
 theorem index_budget (n : ℕ) : PartialBudget (ContextualEncoding.Source.raw (index s h)) n :=
  ((bootstrap s h).choose_spec.2 n).2
 attribute [local instance] OAI.SimpleFInftyOvergroups.SourceModel.instTrichotomousSigmaRel
theorem table_eq {n : ℕ} {rs : List (List Sigma × List Sigma)} (hr : rs ∈ processor s h n) :
    rs = Families.table (code k) (search k) wf (value s h) none n :=
  FamilyProgram.compute_eq (code k) (search k) none (tests s h) wf hr
 theorem index_stable : ∀ j n, j ≤ n → ∀ rj ∈ processor s h j, ∀ rn ∈ processor s h n,
    Selectors.BoundedEq rj rn j := by
  intro j n hjn rj hrj rn hrn
  exact FamilyProgram.stable (code k) (search k) none (tests s h) wf hjn hrj hrn
 theorem tables_short (n : ℕ) (rs) (hr : rs ∈ processor s h n) : ∀ p ∈ rs, 1 < p.1.length := by
  rw [table_eq s h hr]
  exact fun _ hp => Families.table_short (code k) (search k) wf (value s h) none hp
 theorem tables_absorb (n : ℕ) (rs) (hr : rs ∈ processor s h n) : Absorbs rs none := by
  rw [table_eq s h hr]
  exact Families.absorbs (code k) (search k) wf (value s h) none n
 theorem certificate (n : ℕ) (i : Fin 3) : TestCertificate (code k i) (tests s h i) n :=
  ContextualEncoding.Source.certificate s family.A family.M
    IdempotentNames.name IdempotentNames.name family.decode family.realizes
    IdempotentNames.idempotent IdempotentNames.idempotent (index s h) n
    (index_budget s h _) i
 theorem tables_isolate (i : Fin 3) (n : ℕ) (rs) (hr : rs ∈ processor s h n) :
    ∀ p ∈ rs, p ∈ CodeTable.table (code k i) (search k i) wf (value s h i) none n ∨
      ∃ a ∈ p.1, a ∉ (code k i).alphabet := by
  rw [table_eq s h hr]
  exact fun _ hp => Families.isolate (code k) (search k) wf (value s h) none i
    (ThreeCodes.zero_avoids i _) (fun j hij => ThreeCodes.disjoint hij _ _) hp
 theorem tables_static (i : Fin 3) (n : ℕ) (rs) (hr : rs ∈ processor s h n) :
    ∀ p ∈ CodeTable.table (code k i) (search k i) wf (value s h i) none n, p ∈ rs := by
  rw [table_eq s h hr]
  exact fun _ hp => (Families.mem_table (code k) (search k) wf (value s h) none).mpr (.inr ⟨i,hp⟩)

instance lMonoidWithZero : MonoidWithZero (L s h) :=
  Quotient.monoidWithZero (processor s h) none (index_good s h 2).choose_spec.1
    (tables_absorb s h 2 _ (index_good s h 2).choose_spec.1)
 theorem one_ne_zero_L : (1 : L s h) ≠ 0 :=
  Quotient.present_nil_ne_zero (processor s h) wf (index_good s h) (index_stable s h) none
    (tables_short s h)
instance lNontrivial : Nontrivial (L s h) := nontrivial_of_ne _ _ (one_ne_zero_L s h)

 theorem normal_code (i : Fin 3) (w : List (Symbols k i)) :
    Quotient.normal (processor s h) ((code k i).encode w) =
      CodeTable.output (code k i) wf (value s h i) none w :=
  CodeQuotient.normal_encode (processor s h) wf (index_good s h) (index_stable s h)
    (code k i) (search k i) wf (value s h i) none (tables_short s h)
    (tables_isolate s h i) (tables_static s h i)
    (fun n => (certificate s h n i).contextual) (fun n => (certificate s h n i).ideal)
    (certificate s h 0 i).nonzero w

 theorem code_eq_iff (i : Fin 3) (u v : List (Symbols k i)) :
    Quotient.present (processor s h) ((code k i).encode u) =
      Quotient.present (processor s h) ((code k i).encode v) ↔ value s h i u = value s h i v :=
  CodeQuotient.present_encode_iff (processor s h) wf (index_good s h) (index_stable s h)
    (code k i) (search k i) wf (value s h i) none (tables_short s h)
    (tables_isolate s h i) (tables_static s h i)
    (fun n => (certificate s h n i).contextual) (fun n => (certificate s h n i).ideal)
    (certificate s h 0 i).nonzero (ThreeCodes.zero_avoids i _) u v

 theorem code_zero (i : Fin 3) (w : List (Symbols k i)) (hw : value s h i w = none) :
    Quotient.present (processor s h) ((code k i).encode w) = (0 : L s h) := by
  apply (Quotient.present_eq_iff (processor s h) wf (index_good s h) (index_stable s h) _ _).mpr
  rw [normal_code s h i w,CodeTable.output,ite_eq_left hw]
  obtain ⟨rs,hrs,_⟩ := index_good s h 1
  symm
  exact Quotient.normal_eq_self (processor s h) wf (index_good s h) (index_stable s h) hrs
    (Quotient.irreducible_of_short (fun p hp => tables_short s h 1 rs hrs p hp))

abbrev normalPresentation := CommonCompiler.normalPresentation family.A family.M (.inr ()) KAlphabet
  (index s h) family.decode (f:=fun x => ContextualEncoding.Source.raw x.1 x.2) (index_budget s h) (family.realizes (index s h))
abbrev calculus := CommonCompiler.calculus family.A family.M (.inr ()) KAlphabet
  (index s h) family.decode (f:=fun x => ContextualEncoding.Source.raw x.1 x.2) (index_budget s h 0) (family.realizes (index s h))
instance kNontrivial : Nontrivial (K s h) :=
  CommonCompiler.nontrivial family.A family.M (.inr ()) KAlphabet
    (index s h) family.decode (f:=fun x => ContextualEncoding.Source.raw x.1 x.2) (index_budget s h) (family.realizes (index s h))

abbrev Astar := Contracted.Algebra (ZMod 2) (L s h)
instance bNontrivial : Nontrivial (B s h) := inferInstance
instance bAlgebra : Algebra (ZMod 2) (B s h) := inferInstance
instance aRing : Ring (Astar s h) := inferInstance
instance aNontrivial : Nontrivial (Astar s h) := inferInstance
instance aAlgebra : Algebra (ZMod 2) (Astar s h) := inferInstance

def π : SemanticMatrix.Raw (ZMod 2) Syntax →ₐ[ZMod 2] B s h :=
  (normalPresentation s h).algebraMap (ZMod 2)
def σ : B s h → SemanticMatrix.Raw (ZMod 2) Syntax :=
  (normalPresentation s h).sectionMap (ZMod 2)
 theorem σ_injective : Function.Injective (σ s h) := (normalPresentation s h).sectionMap_injective _
 theorem π_surjective : Function.Surjective (π s h) := (normalPresentation s h).algebraMap_surjective _
 theorem section_collect (a : SemanticMatrix.Raw (ZMod 2) Syntax) :
    σ s h (π s h a) = (calculus s h).collect (ZMod 2) a :=
  (normalPresentation s h).section_algebraMap _ (calculus s h) rfl rfl a
 theorem normal_full (w : List Syntax) :
    ((normalPresentation s h).normal (FreeMonoid.ofList w)).toList ∈
      ContextualEncoding.Source.normal family.A family.M (index s h) w :=
  CommonCompiler.service_full family.A family.M (.inr ()) KAlphabet (index s h) family.decode
    (f:=fun x => ContextualEncoding.Source.raw x.1 x.2) (index_budget s h (Word.grade w)) (family.realizes (index s h)) w le_rfl

 theorem value_eq_of_mem {i : Fin 3} {w : List (Symbols k i)} {q : Option (Keys k i)}
    (hq : q ∈ tests s h i w) : value s h i w = q :=
  Part.mem_unique (Search.value_mem (Part.dom_iff_mem.mpr ⟨q,hq⟩)) hq

 theorem group_value (w : List (Symbols k 0)) :
    value s h 0 w = some (WordProblem.testedClass s w) :=
  value_eq_of_mem s h (Part.mem_some _)

 theorem group_code_eq_iff (u v : List (Symbols k 0)) :
    Quotient.present (processor s h) ((code k 0).encode u) =
      Quotient.present (processor s h) ((code k 0).encode v) ↔
      FiniteAlgebraicEnvelopes.evalWord s u = FiniteAlgebraicEnvelopes.evalWord s v := by
  rw [code_eq_iff s h,group_value,group_value,Option.some.injEq,WordProblem.testedClass_eq_iff]

 def codeG (hs : Subgroup.closure (Set.range s) = ⊤) : G →* L s h :=
  CodeQuotient.descendCode (code k 0) (Bootstrap.Source.groupEval s)
    (Bootstrap.Source.groupEval_surjective s hs) (group_code_eq_iff s h)
 theorem codeG_injective (hs : Subgroup.closure (Set.range s) = ⊤) :
    Function.Injective (codeG s h hs) :=
  CodeQuotient.descendCode_injective (code k 0) (Bootstrap.Source.groupEval s)
    (Bootstrap.Source.groupEval_surjective s hs) (group_code_eq_iff s h)

 abbrev ProdMon := SemanticProduct.Mon (K:=K s h)
 abbrev productEval := SemanticProduct.evaluation (normalPresentation s h)
 theorem product_value (w : List (Symbols k 1)) :
    value s h 1 w = SemanticProduct.value (normalPresentation s h) w :=
  value_eq_of_mem s h (SemanticProduct.full (normalPresentation s h)
    (ContextualEncoding.Source.normal family.A family.M (index s h)) (normal_full s h) w)
 theorem product_code_eq_iff (u v : List (Symbols k 1)) :
    Quotient.present (processor s h) ((code k 1).encode u) =
      Quotient.present (processor s h) ((code k 1).encode v) ↔
      productEval s h (FreeMonoid.ofList u) = productEval s h (FreeMonoid.ofList v) := by
  rw [code_eq_iff s h,product_value,product_value,SemanticProduct.value_eq_iff]
 def codeProduct : ProdMon s h →* L s h :=
  CodeQuotient.descendCode (code k 1) (productEval s h)
    (SemanticProduct.evaluation_surjective (normalPresentation s h)) (product_code_eq_iff s h)
 theorem codeProduct_injective : Function.Injective (codeProduct s h) :=
  CodeQuotient.descendCode_injective (code k 1) (productEval s h)
    (SemanticProduct.evaluation_surjective (normalPresentation s h)) (product_code_eq_iff s h)
 theorem codeProduct_zero : codeProduct s h 0 = 0 := by
  obtain ⟨w,hw⟩ := SemanticProduct.evaluation_surjective (normalPresentation s h) 0
  rw [←hw]
  change codeProduct s h ((productEval s h) (FreeMonoid.ofList w.toList))=0
  rw [codeProduct,CodeQuotient.descendCode_apply]
  apply code_zero
  rw [product_value]
  exact (SemanticProduct.value_eq_none (normalPresentation s h) w.toList).mpr hw
 def codeProduct₀ : ProdMon s h →*₀ L s h :=
  { codeProduct s h with map_zero' := codeProduct_zero s h }

 def actionEval : FreeMonoid (Symbols k 2) →* ActionMon s h :=
  SemanticTests.evaluation (π s h) (σ s h) (σ_injective s h) (calculus s h)
 theorem action_value (w : List (Symbols k 2)) :
    value s h 2 w = (SemanticTests.N₂ (calculus s h)).totalTest
      (SemanticTests.I (π s h) (σ s h) (σ_injective s h) (calculus s h)).gkey
      (SemanticTests.I (π s h) (σ s h) (σ_injective s h) (calculus s h)).xkey w :=
  value_eq_of_mem s h (SemanticTests.full (π s h) (σ s h) (σ_injective s h) (calculus s h)
    (section_collect s h) (ContextualEncoding.Source.normal family.A family.M (index s h))
    (normal_full s h) w)
 theorem action_code_eq_iff (u v : List (Symbols k 2)) :
    Quotient.present (processor s h) ((code k 2).encode u) =
      Quotient.present (processor s h) ((code k 2).encode v) ↔
      actionEval s h (FreeMonoid.ofList u) = actionEval s h (FreeMonoid.ofList v) := by
  apply (code_eq_iff s h 2 u v).trans
  have hk := SemanticTests.keys_eq_iff (π s h) (σ s h) (σ_injective s h) (calculus s h) u v
  exact ((congrArg₂ Eq (action_value s h u) (action_value s h v)).to_iff).trans hk
 theorem actionEval_surjective : Function.Surjective (actionEval s h) :=
  SemanticTests.evaluation_surjective (π s h) (σ s h) (σ_injective s h) (calculus s h)
    (π_surjective s h)
 def codeAction : ActionMon s h →* L s h :=
  CodeQuotient.descendCode (code k 2) (actionEval s h)
    (actionEval_surjective s h) (action_code_eq_iff s h)
 theorem codeAction_injective : Function.Injective (codeAction s h) :=
  CodeQuotient.descendCode_injective (code k 2) (actionEval s h)
    (actionEval_surjective s h) (action_code_eq_iff s h)
 theorem codeAction_zero : codeAction s h 0 = 0 := by
  have hw : actionEval s h (FreeMonoid.ofList [.inr (.inr none)])=0 := rfl
  calc
    codeAction s h 0 = codeAction s h (actionEval s h
        (FreeMonoid.ofList [.inr (.inr none)])) := congrArg (codeAction s h) hw.symm
    _ = Quotient.present (processor s h) ((code k 2).encode [.inr (.inr none)]) :=
      CodeQuotient.descendCode_apply (code k 2) (actionEval s h)
        (actionEval_surjective s h) (action_code_eq_iff s h) _
    _ = 0 := code_zero s h 2 _ (by rw [action_value]; rfl)
 def codeAction₀ : ActionMon s h →*₀ L s h :=
  { codeAction s h with map_zero' := codeAction_zero s h }

end
end SimpleFInftyOvergroups.SourceModel

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_RingModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace SimpleFInftyOvergroups.SourceModel
open scoped Classical TensorProduct FiniteAlgebraicEnvelopes.Compiler.HeadCodec
open FiniteAlgebraicEnvelopes Bootstrap Compiler Compiler.Simulator MachineRealization
open ContextualEncoding SemanticEncoding EffectiveNames RingAssembly

variable {G : Type} [Group G] {k : ℕ} (s : Fin k → G)
variable (h : ComputablePred (fun w => FiniteAlgebraicEnvelopes.evalWord s w = 1))
local instance instLinearOrderSectorSigmaProdBoolΓFamilyStateQIndex_1 : LinearOrder (Control.Sector Sigma (Bool × family.Γ) (ParameterMachine.State family.Q (index s h))) :=
  ParameterCode.finiteOrder (index s h)

 theorem realizes_processor : Word.Realizes KAlphabet (KMachine s h) (tableNormal (processor s h)) :=
  index_fixed s h ▸ family.realizes (index s h)

def rawCopy : L s h →ₙ* K s h :=
  Quotient.rawMap (processor s h) wf (index_good s h) (index_stable s h)
    KAlphabet (KMachine s h) family.decode (realizes_processor s h)
 theorem rawCopy_injective : Function.Injective (rawCopy s h) :=
  Quotient.rawMap_injective (processor s h) wf (index_good s h) (index_stable s h)
    KAlphabet (KMachine s h) family.decode (realizes_processor s h)
 theorem rawCopy_ne_zero (x : L s h) : rawCopy s h x ≠ 0 :=
  Quotient.rawMap_ne_zero (processor s h) wf (index_good s h) (index_stable s h)
    KAlphabet (KMachine s h) family.decode (realizes_processor s h) x

def i : Astar s h →ₙₐ[ZMod 2] B s h := Contracted.embedding (rawCopy s h)
 theorem i_injective : Function.Injective (i s h) :=
  Contracted.embedding_injective (rawCopy s h) (rawCopy_injective s h) (rawCopy_ne_zero s h)

def κ : B s h ⊗[ZMod 2] MonoidAlgebra (ZMod 2) PartialAffine.monoid →ₐ[ZMod 2] Astar s h :=
  (Contracted.map (codeProduct₀ s h)).comp (ZeroProduct.tensorMap (ZMod 2) (K s h) PartialAffine.monoid)
 theorem κ_injective : Function.Injective (κ s h) :=
  (Contracted.map_injective (codeProduct₀ s h) (codeProduct_injective s h)).comp
    (ZeroProduct.tensorMap_bijective (ZMod 2) (K s h) PartialAffine.monoid).1

def ξ : B s h ⊗[ZMod 2] MonoidAlgebra (ZMod 2) PartialAffine.monoid →ₙₐ[ZMod 2] B s h :=
  (i s h).comp (κ s h).toNonUnitalAlgHom
 theorem ξ_injective : Function.Injective (ξ s h) := (i_injective s h).comp (κ_injective s h)

def φ : B s h →ₙ+* B s h := binaryPhi (ξ s h)
 theorem φ_injective : Function.Injective (φ s h) := binaryPhi_injective (ξ s h) (ξ_injective s h)
def binary : CompressedSplittings.BinaryData (φ s h) := binaryData (ξ s h)

def e : B s h := i s h 1
 theorem e_idempotent : IsIdempotentElem (e s h) := supportIdempotent (i s h : Astar s h →ₙ+* B s h)
 theorem e_nonzero : e s h ≠ 0 := by
  intro he
  exact one_ne_zero (i_injective s h (he.trans (map_zero (i s h)).symm))

def cornerMap : Astar s h →+* (e_idempotent s h).Corner := toCorner (i s h : Astar s h →ₙ+* B s h)
 theorem cornerMap_injective : Function.Injective (cornerMap s h) := toCorner_injective _ (i_injective s h)

abbrev Generators := CommonCompiler.FiniteLetter Sigma family.Γ family.Q (index s h)
def Relations : FreeAlgebra (ZMod 2) (Generators s h) → FreeAlgebra (ZMod 2) (Generators s h) → Prop :=
  ContractedPresentation.Rel (ZMod 2) (Generators s h) (Word.Rel KAlphabet (KMachine s h)) [.zero]

def presentation : RingQuot (Relations s h) ≃ₐ[ZMod 2] B s h :=
  ContractedPresentation.equivalence (ZMod 2) (Generators s h) (Word.Rel KAlphabet (KMachine s h))
    (MulEquiv.refl (K s h)) [.zero] rfl
 theorem relations_finite : {p : FreeAlgebra (ZMod 2) (Generators s h) × FreeAlgebra (ZMod 2) (Generators s h) |
      Relations s h p.1 p.2}.Finite :=
  ContractedPresentation.finite_relations (ZMod 2) (Generators s h) (Word.Rel KAlphabet (KMachine s h))
    [.zero] (Word.rules_finite KAlphabet (KMachine s h))

def presentationMap : FreeAlgebra (ZMod 2) (Generators s h) →ₐ[ZMod 2] B s h :=
  (presentation s h).toAlgHom.comp (RingQuot.mkAlgHom (ZMod 2) (Relations s h))
 theorem presentationMap_surjective : Function.Surjective (presentationMap s h) :=
  (presentation s h).surjective.comp (RingQuot.mkAlgHom_surjective (ZMod 2) (Relations s h))
 theorem presentationMap_kernel : TwoSidedIdeal.ker (presentationMap s h).toRingHom =
      TwoSidedIdeal.span (differences (Relations s h)) := by
  rw [←ker_ringQuot]
  ext a
  simp only [TwoSidedIdeal.mem_ker]
  change presentation s h (RingQuot.mkAlgHom (ZMod 2) (Relations s h) a)=0 ↔
    RingQuot.mkRingHom (Relations s h) a=0
  rw [←RingQuot.mkAlgHom_coe (ZMod 2) (Relations s h)]
  exact (presentation s h).map_eq_zero_iff

end SimpleFInftyOvergroups.SourceModel
end

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_SourceProducer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace SimpleFInftyOvergroups
namespace SourceModel
open scoped Classical
open FiniteAlgebraicEnvelopes RingAssembly

variable {G : Type} [Group G] {k : ℕ} (s : Fin k → G)
variable (h : ComputablePred (fun w => FiniteAlgebraicEnvelopes.evalWord s w = 1))

def actionCornerMap : ActionMon s h →*₀ (e_idempotent s h).Corner :=
  (cornerMap s h).toMonoidWithZeroHom.comp
    ((monoidBasis₀ (k:=ZMod 2) (M:=L s h)).comp (codeAction₀ s h))

theorem actionCornerMap_injective : Function.Injective (actionCornerMap s h) :=
  (cornerMap_injective s h).comp
    ((monoidBasis_injective (k:=ZMod 2) (M:=L s h)).comp (codeAction_injective s h))

def groupCornerMap (hs : Subgroup.closure (Set.range s)=⊤) : G →* (e_idempotent s h).Corner :=
  (cornerMap s h).toMonoidHom.comp ((ContractedPresentation.monoidBasis (ZMod 2)).comp (codeG s h hs))

theorem groupCornerMap_injective (hs : Subgroup.closure (Set.range s)=⊤) :
    Function.Injective (groupCornerMap s h hs) :=
  (cornerMap_injective s h).comp
    ((monoidBasis_injective (k:=ZMod 2) (M:=L s h)).comp (codeG_injective s h hs))

end SourceModel

universe u

end SimpleFInftyOvergroups
end

end OAI
end


