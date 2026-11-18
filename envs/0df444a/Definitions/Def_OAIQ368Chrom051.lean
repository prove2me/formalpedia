-- Prove2me | Definitions.Def_OAIQ368Chrom051
-- name    : OAIQ368Chrom051
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-17T19:33:21.371214+00:00
-- url     : https://prove2.me/theorems/a5d46c55-072e-4b0f-8be0-49e1c21a7693
-- title:
--   Definitions bundle OAIQ368Chrom051 of the split of OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.elementaryPositivityWitness_exists`, carved from OpenAI's openai/math development (OpenAI, *Elementary Positivity of Chromatic Quasisymmetric Functions*, OpenAI Math Release, September 24, 2026, result family 169, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 19 declarations of OpenAI's Lean: 7 definitions and 12 theorems. The definitions and types are `OAI.ElementaryPositivity.RawShuffle.globalStringFamily`, `OAI.ElementaryPositivity.RawShuffle.globalStringPBWBasis`, `OAI.ElementaryPositivity.RawShuffle.homogeneousPrimitiveStringBasis`, `OAI.ElementaryPositivity.RawShuffle.instAddCommGroupSubtypeSourceAssociatedGradeMemSubmoduleRatPrimitiveSpace_1`, `OAI.ElementaryPositivity.RawShuffle.localPrimitiveGlobal`, `OAI.ElementaryPositivity.RawShuffle.localPrimitiveInclusion`, `OAI.ElementaryPositivity.RawShuffle.localPrimitiveSumToGlobal`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: [`Chromatic_Shuffle_GlobalLocalPrimitives`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/GlobalLocalPrimitives.lean), [`Chromatic_Shuffle_GlobalPrimitiveStrings`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/GlobalPrimitiveStrings.lean), [`Chromatic_Walls_DirectSumSubtype`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Walls/DirectSumSubtype.lean).
--
--   **Imports.** It imports the bundles `OAIQ368Chrom049` and `OAIQ368Chrom050` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ368Chrom054`; the statement `OAI.ElementaryPositivity.RawShuffle.stringPBWBasis_component`; the proofs of `OAI.ElementaryPositivity.RawShuffle.slopeStringCoefficient_bounds` and `OAI.ElementaryPositivity.RawShuffle.stringPBWBasis_component`.
-- source:
--   OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 169; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ368Chrom049
import Definitions.Def_OAIQ368Chrom050

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_GlobalLocalPrimitives
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.globalStringIndexLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable
variable (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i) (θ : ℝ)
  (hχ : SlopeEulerSymmetric a c η θ) (d : I → ℕ) (W : ℤ)

attribute [local instance] OAI.ElementaryPositivity.RawShuffle.instAddCommGroupSubtypeSourceAssociatedGradeMemSubmoduleRatPrimitiveSpace
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.instModuleRatSubtypeSourceAssociatedGradeMemSubmodulePrimitiveSpace
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.instAddCommGroupSubtypeSourceAssociatedGradeMemSubmoduleRatPrimitiveSpaceKerPrimitiveDerivative
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.instModuleRatSubtypeSourceAssociatedGradeMemSubmodulePrimitiveSpaceKerPrimitiveDerivative
noncomputable def homogeneousPrimitiveStringBasis (hd : d≠0) :
    Module.Basis (Σ _ : ℕ,StringBaseIndex a c η hc θ hχ d W) ℚ
      (primitiveSpace a c η hc θ hχ d W) :=
  (Finsupp.basis (fun _ : ℕ=>homogeneousStringBaseBasis a c η hc θ hχ d W)).map
    (primitiveStringDecomposition a c η hc θ hχ d hd W)

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_DirectSumSubtype
attribute [-instance] _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.degreesDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity
open scoped DirectSum
universe u v
variable {K : Type u} [DecidableEq K] (M : K → Type v) [∀ k,AddCommGroup (M k)] [∀ k,Module ℚ (M k)]
  (p : K → Prop)
attribute [local instance] Classical.propDecidable

lemma component_subfamilyInclusion (k : {k // p k}) (x : ⨁ k : {k // p k},M k.val) :
    DirectSum.component ℚ K M k.val (subfamilyInclusion M p x)=
      DirectSum.component ℚ _ (fun k : {k // p k}=>M k.val) k x := by
  induction x using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add,hx,hy]
  | of j x =>
    change DirectSum.component ℚ K M k.val (subfamilyInclusion M p
      (DirectSum.lof ℚ _ (fun k : {k // p k}=>M k.val) j x))=
      DirectSum.component ℚ _ (fun k : {k // p k}=>M k.val) k
        (DirectSum.lof ℚ _ (fun k : {k // p k}=>M k.val) j x)
    rw [subfamilyInclusion_lof]
    by_cases h : j=k
    · subst j; simp
    · rw [DirectSum.component.of,DirectSum.component.of]
      simp only [dite_eq_right (fun he=>h (Subtype.ext he)),dite_eq_right h]

lemma subfamilyInclusion_injective : Function.Injective (subfamilyInclusion M p) := by
  intro x y h
  apply DirectSum.ext_component ℚ
  intro k
  rw [←component_subfamilyInclusion M p,←component_subfamilyInclusion M p,h]

end ElementaryPositivity

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_GlobalPrimitiveStrings
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct DirectSum
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable
variable (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i) (θ : ℝ)
  [Fact (SlopeEulerSymmetric a c η θ)]

noncomputable local instance instAddCommGroupSubtypeSourceAssociatedGradeMemSubmoduleRatPrimitiveSpace_1 (d : I → ℕ) (W : ℤ) : AddCommGroup (primitiveSpace a c η hc θ Fact.out d W) := Submodule.addCommGroup _

attribute [local instance] OAI.ElementaryPositivity.RawShuffle.instModuleRatSubtypeSourceAssociatedGradeMemSubmodulePrimitiveSpace_1
noncomputable def localPrimitiveInclusion (k : NonzeroSlopeWeight c η hc θ) :
    primitiveSpace a c η hc θ Fact.out k.val.1.val k.val.2 →ₗ[ℚ]
      unitalComponent a c η hc θ k.val :=
  (unitalGradeNonzeroEquiv a c η hc θ k.val.1.val k.property k.val.2).symm.toLinearMap ∘ₗ
    (primitiveSpace a c η hc θ Fact.out k.val.1.val k.val.2).subtype

lemma localPrimitiveInclusion_injective (k : NonzeroSlopeWeight c η hc θ) :
    Function.Injective (localPrimitiveInclusion a c η hc θ k) :=
  (unitalGradeNonzeroEquiv a c η hc θ k.val.1.val k.property k.val.2).symm.injective.comp Subtype.val_injective

noncomputable def localPrimitiveGlobal (k : NonzeroSlopeWeight c η hc θ) :
    primitiveSpace a c η hc θ Fact.out k.val.1.val k.val.2 →ₗ[ℚ] UnitalShuffle a c η hc θ :=
  DirectSum.lof ℚ _ (unitalComponent a c η hc θ) k.val ∘ₗ localPrimitiveInclusion a c η hc θ k

lemma localPrimitiveGlobal_mem (k : NonzeroSlopeWeight c η hc θ)
    (x : primitiveSpace a c η hc θ Fact.out k.val.1.val k.val.2) :
    localPrimitiveGlobal a c η hc θ k x ∈ globalPrimitives a c η hc θ := by
  apply (globalPrimitive_iff_local a c η hc θ k.val.1 k.property k.val.2 _).mpr
  change unitalGradeNonzeroEquiv a c η hc θ k.val.1.val k.property k.val.2
    ((unitalGradeNonzeroEquiv a c η hc θ k.val.1.val k.property k.val.2).symm x.val)∈_
  rw [LinearEquiv.apply_symm_apply]
  exact x.property

noncomputable def localPrimitiveSumToGlobal :
    (⨁ k : NonzeroSlopeWeight c η hc θ,primitiveSpace a c η hc θ Fact.out k.val.1.val k.val.2) →ₗ[ℚ]
      UnitalShuffle a c η hc θ :=
  subfamilyInclusion (unitalComponent a c η hc θ) (fun k=>k.1.val≠0) ∘ₗ
    DirectSum.lmap (localPrimitiveInclusion a c η hc θ)

lemma localPrimitiveSumToGlobal_injective : Function.Injective (localPrimitiveSumToGlobal a c η hc θ) :=
  (subfamilyInclusion_injective (unitalComponent a c η hc θ) (fun k=>k.1.val≠0)).comp
    ((DirectSum.lmap_injective _).mpr (localPrimitiveInclusion_injective a c η hc θ))

lemma localPrimitiveSumToGlobal_lof (k : NonzeroSlopeWeight c η hc θ)
    (x : primitiveSpace a c η hc θ Fact.out k.val.1.val k.val.2) :
    localPrimitiveSumToGlobal a c η hc θ (DirectSum.lof ℚ _
      (fun k : NonzeroSlopeWeight c η hc θ=>primitiveSpace a c η hc θ Fact.out k.val.1.val k.val.2) k x)=
      localPrimitiveGlobal a c η hc θ k x := by
  change subfamilyInclusion (unitalComponent a c η hc θ) (fun k=>k.1.val≠0)
    (DirectSum.lmap (localPrimitiveInclusion a c η hc θ)
      (DirectSum.lof ℚ _ _ k x))=_
  rw [DirectSum.lmap_lof]
  simp only [subfamilyInclusion,DirectSum.toModule_lof,localPrimitiveGlobal,LinearMap.comp_apply]

noncomputable def globalStringFamily (i : GlobalStringIndex a c η hc θ) : UnitalShuffle a c η hc θ :=
  localPrimitiveGlobal a c η hc θ i.1
    (homogeneousPrimitiveStringBasis a c η hc θ Fact.out i.1.val.1.val i.1.val.2 i.1.property i.2)

lemma globalStringFamily_mem (i : GlobalStringIndex a c η hc θ) :
    globalStringFamily a c η hc θ i ∈ globalPrimitives a c η hc θ :=
  localPrimitiveGlobal_mem a c η hc θ i.1 _

lemma globalStringFamily_weight (i : GlobalStringIndex a c η hc θ) :
    globalStringFamily a c η hc θ i ∈ globalHomogeneous a c η hc θ i.1.val :=
  ⟨localPrimitiveInclusion a c η hc θ i.1 _,rfl⟩

lemma globalStringFamily_independent : LinearIndependent ℚ (globalStringFamily a c η hc θ) := by
  have hh := directSum_map_independent
    (fun k : NonzeroSlopeWeight c η hc θ=>primitiveSpace a c η hc θ Fact.out k.val.1.val k.val.2)
    (fun k=>homogeneousPrimitiveStringBasis a c η hc θ Fact.out k.val.1.val k.val.2 k.property)
    (fun k=>(homogeneousPrimitiveStringBasis a c η hc θ Fact.out k.val.1.val k.val.2 k.property).linearIndependent)
    (localPrimitiveSumToGlobal a c η hc θ) (localPrimitiveSumToGlobal_injective a c η hc θ)
  have he : globalStringFamily a c η hc θ=(fun i : GlobalStringIndex a c η hc θ=>
      localPrimitiveSumToGlobal a c η hc θ (DirectSum.lof ℚ _ _ i.1
      (homogeneousPrimitiveStringBasis a c η hc θ Fact.out i.1.val.1.val i.1.val.2 i.1.property i.2))) := by
    funext i
    exact (localPrimitiveSumToGlobal_lof a c η hc θ i.1 _).symm
  rw [he]
  exact hh

lemma localPrimitiveGlobal_mem_span (k : NonzeroSlopeWeight c η hc θ)
    (x : primitiveSpace a c η hc θ Fact.out k.val.1.val k.val.2) :
    localPrimitiveGlobal a c η hc θ k x∈Submodule.span ℚ (Set.range (globalStringFamily a c η hc θ)) := by
  have he := congrArg (Submodule.map (localPrimitiveGlobal a c η hc θ k))
    (homogeneousPrimitiveStringBasis a c η hc θ Fact.out k.val.1.val k.val.2 k.property).span_eq
  rw [Submodule.map_span,Submodule.map_top] at he
  have hx : localPrimitiveGlobal a c η hc θ k x∈LinearMap.range (localPrimitiveGlobal a c η hc θ k) := ⟨x,rfl⟩
  rw [←he] at hx
  apply Submodule.span_mono (s:=_) (t:=Set.range (globalStringFamily a c η hc θ)) ?_ hx
  rintro y ⟨z,⟨i,rfl⟩,rfl⟩
  exact ⟨⟨k,i⟩,rfl⟩

lemma homogeneousPrimitive_mem_stringSpan (k : SlopeWeight c η hc θ)
    (x : unitalComponent a c η hc θ k)
    (hx : DirectSum.lof ℚ _ (unitalComponent a c η hc θ) k x∈globalPrimitives a c η hc θ) :
    DirectSum.lof ℚ _ (unitalComponent a c η hc θ) k x∈Submodule.span ℚ (Set.range (globalStringFamily a c η hc θ)) := by
  by_cases hd : k.1.val=0
  · rw [zeroDimension_lof_scalar a c η hc θ k hd x,globalPrimitive_counit a c η hc θ hx,zero_smul]
    exact Submodule.zero_mem _
  · let y : primitiveSpace a c η hc θ Fact.out k.1.val k.2 :=
      ⟨unitalGradeNonzeroEquiv a c η hc θ k.1.val hd k.2 x,
        (globalPrimitive_iff_local a c η hc θ k.1 hd k.2 x).mp hx⟩
    have h:=localPrimitiveGlobal_mem_span a c η hc θ ⟨k,hd⟩ y
    change DirectSum.lof ℚ _ (unitalComponent a c η hc θ) k
      ((unitalGradeNonzeroEquiv a c η hc θ k.1.val hd k.2).symm
        (unitalGradeNonzeroEquiv a c η hc θ k.1.val hd k.2 x))∈_ at h
    rwa [LinearEquiv.symm_apply_apply] at h

lemma globalStringFamily_span :
    Submodule.span ℚ (Set.range (globalStringFamily a c η hc θ))=globalPrimitives a c η hc θ := by
  apply le_antisymm
  · exact Submodule.span_le.mpr (fun x hx=>by obtain ⟨i,rfl⟩:=hx; exact globalStringFamily_mem a c η hc θ i)
  · intro x hx
    rw [←globalPrimitiveLog_on_primitive a c η hc θ hx]
    have hm : ∀ y : UnitalShuffle a c η hc θ,globalPrimitiveLog a c η hc θ y∈
        Submodule.span ℚ (Set.range (globalStringFamily a c η hc θ)) := by
      intro y
      induction y using DirectSum.induction_on with
      | zero => simpa only [map_zero] using (Submodule.span ℚ (Set.range (globalStringFamily a c η hc θ))).zero_mem
      | add y z hy hz => simpa only [map_add] using (Submodule.span ℚ (Set.range (globalStringFamily a c η hc θ))).add_mem hy hz
      | of k y =>
        obtain ⟨z,hz⟩ := globalPrimitiveLog_homogeneous a c η hc θ k y
        change globalPrimitiveLog a c η hc θ (DirectSum.lof ℚ _ (unitalComponent a c η hc θ) k y)∈_
        change DirectSum.lof ℚ _ (unitalComponent a c η hc θ) k z=globalPrimitiveLog a c η hc θ _ at hz
        rw [←hz]
        apply homogeneousPrimitive_mem_stringSpan a c η hc θ k z
        rw [hz]
        exact (mem_globalPrimitives a c η hc θ _).mpr (globalPrimitiveLog_primitive a c η hc θ _)
    exact hm x

end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i) (θ : ℝ)
  [Fact (SlopeEulerSymmetric a c η θ)]

noncomputable def globalStringPBWBasis :
    Module.Basis (PBWWord a c η hc θ (fun i : GlobalStringIndex a c η hc θ=>i.1.val)) ℚ
      (UnitalShuffle a c η hc θ) :=
  primitiveBasisPBW a c η hc θ (globalStringFamily a c η hc θ) (fun i=>i.1.val)
    (globalStringFamily_weight a c η hc θ) (globalStringFamily_mem a c η hc θ)
    (globalStringFamily_span a c η hc θ) (globalStringFamily_independent a c η hc θ)

end ElementaryPositivity.RawShuffle

end

end OAI
end


