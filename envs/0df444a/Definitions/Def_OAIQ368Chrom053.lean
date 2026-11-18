-- Prove2me | Definitions.Def_OAIQ368Chrom053
-- name    : OAIQ368Chrom053
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-17T19:41:31.34938+00:00
-- url     : https://prove2.me/theorems/d062bc40-7083-4d25-a4bc-e6c49848d6ab
-- title:
--   Definitions bundle OAIQ368Chrom053 of the split of OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.elementaryPositivityWitness_exists`, carved from OpenAI's openai/math development (OpenAI, *Elementary Positivity of Chromatic Quasisymmetric Functions*, OpenAI Math Release, September 24, 2026, result family 169, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 4 declarations of OpenAI's Lean: 1 definition and 3 theorems. The definitions and types are `OAI.ElementaryPositivity.RawShuffle.globalOriginalComponent`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: [`Chromatic_Shuffle_GlobalHilbertGrading`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/GlobalHilbertGrading.lean), [`Chromatic_Shuffle_UnitalOriginalDegree`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/UnitalOriginalDegree.lean).
--
--   **Imports.** It imports the bundle `OAIQ368Chrom052` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ368Chrom054`; the statement `OAI.ElementaryPositivity.RawShuffle.stringPBWBasis_component`; the proof of `OAI.ElementaryPositivity.RawShuffle.stringPBWBasis_component`.
-- source:
--   OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 169; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ368Chrom052

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_UnitalOriginalDegree
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open ElementaryPositivity.SlopeArithmetic
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i) (θ : ℝ)

lemma unitalAssociatedComponent_twice (d : I → ℕ) (W ℓ m : ℤ)
    (f : UnitalSourceGrade a c η hc θ d W) :
    unitalAssociatedComponent a c η hc θ d W ℓ (unitalAssociatedComponent a c η hc θ d W m f)=
      if ℓ=m then unitalAssociatedComponent a c η hc θ d W m f else 0 := by
  classical
  by_cases h : ℓ=m
  · rw [ite_eq_left h]
    induction f using Submodule.Quotient.induction_on with
    | H f =>
      simp only [unitalAssociatedComponent_mk]
      apply congrArg Submodule.Quotient.mk
      apply Subtype.ext
      exact (componentB_componentB a _ d ℓ m f.val).trans (ite_eq_left h)
  · rw [ite_eq_right h]
    induction f using Submodule.Quotient.induction_on with
    | H f =>
      rw [unitalAssociatedComponent_mk,unitalAssociatedComponent_mk]
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      change componentB a _ d ℓ (componentB a _ d m f.val)∈unitalSourceFiltration a c η hc θ d (W+1)
      rw [componentB_componentB,ite_eq_right h]
      exact Submodule.zero_mem _

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_GlobalHilbertGrading
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped DirectSum
open ElementaryPositivity.SlopeArithmetic
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i) (θ : ℝ)
  [Fact (SlopeEulerSymmetric a c η θ)]

noncomputable def globalOriginalComponent (k : SlopeWeight c η hc θ) (ℓ : ℤ) :
    Module.End ℚ (UnitalShuffle a c η hc θ) :=
  (DirectSum.lof ℚ _ (unitalComponent a c η hc θ) k).comp
    ((unitalAssociatedComponent a c η hc θ k.1.val k.2 ℓ).comp
      (DirectSum.component ℚ _ (unitalComponent a c η hc θ) k))

omit [Fact (SlopeEulerSymmetric a c η θ)] in
lemma globalOriginalComponent_lof (k : SlopeWeight c η hc θ) (ℓ : ℤ)
    (x : unitalComponent a c η hc θ k) :
    globalOriginalComponent a c η hc θ k ℓ (DirectSum.lof ℚ _ (unitalComponent a c η hc θ) k x)=
      DirectSum.lof ℚ _ (unitalComponent a c η hc θ) k
        (unitalAssociatedComponent a c η hc θ k.1.val k.2 ℓ x) := by
  simp only [globalOriginalComponent,LinearMap.comp_apply,DirectSum.component.lof_self]

lemma globalOriginalComponent_of_mem {k l : SlopeWeight c η hc θ} {m : ℤ}
    {x : UnitalShuffle a c η hc θ} (hx : x∈globalOriginalHomogeneous a c η hc θ l m) (n : ℤ) :
    globalOriginalComponent a c η hc θ k n x=if (l,m)=(k,n) then x else 0 := by
  obtain ⟨y,hy,rfl⟩:=hx
  by_cases hl : l=k
  · subst l
    rw [globalOriginalComponent_lof]
    have hy' := (mem_unitalOriginalHomogeneous a c η hc θ k.1.val k.2 m y).mp hy
    rw [←hy',unitalAssociatedComponent_twice]
    by_cases h : n=m
    · subst n
      simp [hy']
    · simp only [ite_eq_right h,Prod.mk.injEq,true_and,Ne.symm h,ite_false, if_false,map_zero]
  · simp only [globalOriginalComponent,LinearMap.comp_apply,DirectSum.component.of,
      map_zero,Prod.mk.injEq,hl,false_and,ite_false, if_false,dite_false]

end ElementaryPositivity.RawShuffle

end

end OAI
end


