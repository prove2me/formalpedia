-- Prove2me | Definitions.Def_OAIQ368Chrom050
-- name    : OAIQ368Chrom050
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-17T19:30:16.759255+00:00
-- url     : https://prove2.me/theorems/23391577-ce0a-4ba0-81a4-a5bd8cbfea18
-- title:
--   Definitions bundle OAIQ368Chrom050 of the split of OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.elementaryPositivityWitness_exists`, carved from OpenAI's openai/math development (OpenAI, *Elementary Positivity of Chromatic Quasisymmetric Functions*, OpenAI Math Release, September 24, 2026, result family 169, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 3 declarations of OpenAI's Lean: 1 definition and 2 theorems. The definitions and types are `OAI.ElementaryPositivity.RawShuffle.primitiveBasisPBW`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: [`Chromatic_Shuffle_GlobalPBWBasis`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/GlobalPBWBasis.lean), [`Chromatic_Shuffle_Interaction`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/Interaction.lean), [`Chromatic_Walls_DirectSumSubtype`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Walls/DirectSumSubtype.lean).
--
--   **Imports.** It imports the bundle `OAIQ368Chrom040` of this split; the published statements `OAI.ElementaryPositivity.RawShuffle.primitiveBasisFamilyWords_independent` and `OAI.ElementaryPositivity.RawShuffle.primitiveBasisFamilyWords_span`.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ368Chrom051`.
-- source:
--   OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 169; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ368Chrom040
import Theorems.Thm_OAI_ElementaryPositivity_RawShuffle_primitiveBasisFamilyWords_independent
import Theorems.Thm_OAI_ElementaryPositivity_RawShuffle_primitiveBasisFamilyWords_span

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_Interaction
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersFintype _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open scoped TensorProduct
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

theorem sourceFiltration_upper (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (d : I → ℕ) (hd : d≠0) (hθ : SlopeArithmetic.slope c η d=θ)
    (k W : ℤ) (hw : 2*k+eulerForm a d d<W) :
    gradeB a (SlopeArithmetic.slope c η) d k ⊓ sourceFiltration a c η hc θ d W=⊥ := by
  apply bot_unique
  intro f hf
  obtain ⟨hf,hg⟩ := hf
  have h := hg (.leaf d) trivial ⟨hd,hθ⟩ rfl k 0 hw
  rw [restrictionTest_leaf_zero,(mem_gradeB_iff a _ d k f).mp hf] at h
  exact h

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_GlobalPBWBasis
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct DirectSum
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable Classical.decEq
variable (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i) (θ : ℝ)
  [Fact (SlopeEulerSymmetric a c η θ)]
variable {J : Type*} [LinearOrder J] (b : J → UnitalShuffle a c η hc θ)
  (w : J → SlopeWeight c η hc θ)
  (hw : ∀ i,b i∈globalHomogeneous a c η hc θ (w i))
  (hp : ∀ i,b i∈globalPrimitives a c η hc θ)
  (hspan : Submodule.span ℚ (Set.range b)=globalPrimitives a c η hc θ)
  (hli : LinearIndependent ℚ b)

noncomputable def primitiveBasisPBW : Module.Basis (PBWWord a c η hc θ w) ℚ (UnitalShuffle a c η hc θ) :=
  Module.Basis.mk (primitiveBasisFamilyWords_independent a c η hc θ b w hw hp hspan hli)
    (le_of_eq (primitiveBasisFamilyWords_span a c η hc θ b w hw hp hspan).symm)

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_DirectSumSubtype
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
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

lemma directSum_map_independent {J : K → Type*} (f : ∀ k,J k → M k)
    (hf : ∀ k,LinearIndependent ℚ (f k)) {V : Type*} [AddCommGroup V] [Module ℚ V]
    (L : (⨁ k,M k) →ₗ[ℚ] V) (hL : Function.Injective L) :
    LinearIndependent ℚ (fun i : Σ k,J k=>L (DirectSum.lof ℚ K M i.1 (f i.1 i.2))) := by
  exact (DFinsupp.linearIndependent_single f hf).map' L ((LinearMap.ker_eq_bot).mpr hL)

end ElementaryPositivity

end

end OAI
end


