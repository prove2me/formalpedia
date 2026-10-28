-- Prove2me | Definitions.Def_OAIQ039C036
-- name    : OAIQ039C036
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T06:20:29.491534+00:00
-- url     : https://prove2.me/theorems/0ae24a46-7bcb-4fec-9a07-cd0ed5fc51f7
-- title:
--   Definitions bundle OAIQ039C036 of the split of OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 45 declarations of OpenAI's Lean: 23 definitions, 1 instance and 21 theorems. The definitions and types are `OAI.Kadison.FiniteTest.column`, `OAI.Kadison.FiniteTest.matrixSignSum`, `OAI.Kadison.FiniteTest.signProjection`, `OAI.Kadison.FreeBlocks.aLetters`, `OAI.Kadison.FreeBlocks.blockShuffle`, `OAI.Kadison.FreeBlocks.dLetters`, `OAI.Kadison.FreeBlocks.endpointIsometry`, `OAI.Kadison.FreeBlocks.endpointShuffle`, `OAI.Kadison.FreeBlocks.factorGNSIso`, `OAI.Kadison.FreeBlocks.factorOf`, `OAI.Kadison.FreeBlocks.factorPreIso`, `OAI.Kadison.FreeBlocks.factorPreMap`, `OAI.Kadison.FreeBlocks.letterOf`, `OAI.Kadison.FreeBlocks.levelEmbedding`, `OAI.Kadison.FreeBlocks.levelShuffle`, `OAI.Kadison.FreeBlocks.multiplicityLevel`, `OAI.Kadison.FreeBlocks.multiplicityTensor`, `OAI.Kadison.FreeBlocks.paramD`, `OAI.Kadison.FreeBlocks.paramJ`, `OAI.Kadison.FreeBlocks.pullbackState`, `OAI.Kadison.FreeBlocks.scalarLevel`, `OAI.Kadison.FreeWordTensor.generatedOperators`, `OAI.Kadison.FreeWordTensor.wordInclusion`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/Commutator, in whole or in part: `Commutator_FiniteTestPatching`, `Commutator_FreeAction`, `Commutator_FreeBlockTensor`, `Commutator_FreeBlockTensor2`, `Commutator_FreeBlockTensor3`, `Commutator_FreeBlockWords`, `Commutator_FreeBlockWords2`, `Commutator_FreeCreation`, `Commutator_FreeSymmetry10`, `Commutator_FreeWordDecomposition`, `Commutator_FreeWordTensor`, `Commutator_HankelAlgebra`, `Commutator_Regroup`.
--
--   **Imports.** It imports the bundles `OAIQ039C024`, `OAIQ039C025` and `OAIQ039C026` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ039C046` and `OAIQ039C047`; the proof of `OAI.Kadison.LocalQuantization.exists_small_projection`.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/Commutator at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ039C024
import Definitions.Def_OAIQ039C025
import Definitions.Def_OAIQ039C026

section
-- module Solutions.OAIQ039_CM.Commutator_FiniteTestPatching
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace

namespace Kadison.FiniteTest

section MatrixSigns

variable {I H : Type*} [Fintype I] [LinearOrder I]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def matrixSignSum (x : I → I → H) (σ : I → Bool) : H :=
  ∑ i, ∑ j, (sign (σ i) * sign (σ j)) • x i j

end MatrixSigns

section MatrixAlgebra

open Matrix

variable {A I : Type*} [CStarAlgebra A] [Fintype I] [DecidableEq I]

variable (φ : Matrix I I ℂ →⋆ₐ[ℂ] A)

def column (i₀ : I) (σ : I → Bool) : A := ∑ i, sign (σ i) • unit φ i i₀

variable (τ : A →ₗ[ℝ] ℝ) (hτ : ∀ a b : A, τ (a*b) = τ (b*a))

def signProjection (i₀ : I) (σ : I → Bool) : A :=
  (Fintype.card I : ℝ)⁻¹ • (column φ i₀ σ * star (column φ i₀ σ))

end MatrixAlgebra

section FiniteFamily

open Matrix

variable {A I J H : Type*} [CStarAlgebra A] [Fintype I] [LinearOrder I]
  [Fintype J] [NormedAddCommGroup H] [InnerProductSpace ℝ H]

variable (φ : Matrix I I ℂ →⋆ₐ[ℂ] A) (τ : A →ₗ[ℝ] ℝ)
  (hτ : ∀ a b : A, τ (a*b) = τ (b*a))
  (v : A →ₗ[ℝ] H) (hv : ∀ a, ‖v a‖^2 = traceSquare τ a)

@[simp] lemma column_family (i₀ : I) (σ : I → Bool) (t : J) :
    column (familyHom (J := J) φ) i₀ σ t = column φ i₀ σ := by
  simp [column]

@[simp] lemma signProjection_family (i₀ : I) (σ : I → Bool) (t : J) :
    signProjection (familyHom (J := J) φ) i₀ σ t = signProjection φ i₀ σ := by
  simp only [signProjection, Pi.smul_apply, Pi.mul_apply, Pi.star_apply, column_family]

@[simp] lemma expectation_family (x : J → A) (t : J) :
    expectation (familyHom (J := J) φ) x t = expectation φ (x t) := by
  simp only [expectation, Pi.smul_apply, Finset.sum_apply, Pi.mul_apply, unit_family]

end FiniteFamily

end Kadison.FiniteTest

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FreeWordTensor
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct
open scoped TensorProduct InnerProductSpace Topology
open UniformSpace Completion Filter
open scoped TensorProduct
open UniformSpace Completion
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open scoped InnerProductSpace TensorProduct ComplexOrder
open UniformSpace

namespace Kadison.FreeWordTensor

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (t : FaithfulState A)

variable {ι : Type*} (S : ι → StarSubalgebra ℂ A)

attribute [instance] Space.normed Space.inner

variable (hfree : FreeMoments.Free S t.functional.toLinearMap)

include hfree

noncomputable def wordInclusion (is : ColorSeq ι) : wordSpace t S is →ₗᵢ[ℂ] t.functional.GNS :=
  wordEmbedding t S hfree is.val is.property

end Kadison.FreeWordTensor
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FreeWordDecomposition
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct
open scoped TensorProduct InnerProductSpace Topology
open UniformSpace Completion Filter
open scoped TensorProduct
open UniformSpace Completion
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open scoped InnerProductSpace TensorProduct ComplexOrder
open UniformSpace
open scoped InnerProductSpace _root_.Topology

namespace Kadison.FreeWordTensor

open scoped InnerProductSpace _root_.Topology

open UniformSpace

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (t : FaithfulState A) {ι : Type*} (S : ι → StarSubalgebra ℂ A)

variable (hfree : FreeMoments.Free S t.functional.toLinearMap)

def generatedOperators : StarSubalgebra ℂ (t.functional.GNS →L[ℂ] t.functional.GNS) :=
  (iSup S).map t.functional.gnsStarAlgHom

end Kadison.FreeWordTensor
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FreeAction
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace TensorProduct

open UniformSpace

namespace Kadison.FreeWordAction

open FreeWordTensor FreeMoments

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (t : FaithfulState A) {ι : Type*} (S : ι → StarSubalgebra ℂ A)

variable (α : ι → A ≃⋆ₐ[ℂ] A)
  (hmem : ∀ i a, a∈S i → α i a∈S i)
  (hτ : ∀ i a, t.functional (α i a)=t.functional a)

@[simp] lemma letter_val (a : Letter S t.functional.toLinearMap) :
    (letter t S α hmem hτ a).val=α a.color a.val := rfl

end Kadison.FreeWordAction

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FreeCreation
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct
open scoped TensorProduct InnerProductSpace Topology
open UniformSpace Completion Filter
open scoped TensorProduct
open UniformSpace Completion
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open scoped InnerProductSpace TensorProduct ComplexOrder
open UniformSpace
open scoped InnerProductSpace _root_.Topology

namespace Kadison.FreeCreation

open FreeMoments FreeWordTensor

open scoped InnerProductSpace

open UniformSpace

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (t : FaithfulState A) {ι : Type*} (S : ι → StarSubalgebra ℂ A)

variable (hfree : Free S t.functional.toLinearMap)

instance instIsClosedGNSFunctionalCoeSubmoduleComplexHeadSpace (i : ι) : IsClosed ((headSpace t S i : Submodule ℂ t.functional.GNS) : Set t.functional.GNS) :=
  (headSpan t S i).isClosed_topologicalClosure

end Kadison.FreeCreation
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FreeBlockWords
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct
open scoped TensorProduct InnerProductSpace Topology
open UniformSpace Completion Filter
open scoped TensorProduct
open UniformSpace Completion
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open scoped InnerProductSpace TensorProduct ComplexOrder
open UniformSpace
open scoped InnerProductSpace _root_.Topology

namespace Kadison.FreeCreation

open FreeMoments FreeWordTensor UniformSpace

open scoped InnerProductSpace

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (t : FaithfulState A) {ι : Type*} (S : ι → StarSubalgebra ℂ A)

variable (hfree : Free S t.functional.toLinearMap)

include hfree in
lemma inner_mul_two_wordVector {i : ι} {w z : List (Letter t S)}
    (hw : Reduced w) (hz : Reduced z)
    (hiw : CanPrepend t S i w) (hiz : CanPrepend t S i z)
    {a b : A} (ha : a ∈ S i) (hb : b ∈ S i) :
    inner ℂ (t.functional.gnsStarAlgHom a (wordVector t S w))
      (t.functional.gnsStarAlgHom b (wordVector t S z)) =
      t.functional (star a*b)*inner ℂ (wordVector t S w) (wordVector t S z) := by
  rw [mul_wordVector, mul_wordVector, Completion.inner_coe, inner_wordVector]
  change t.functional (star (a*word w)*(b*word z))=_
  simpa only [star_mul, mul_assoc] using
    middle_factor t S hfree hw hz hiw hiz (mul_mem (star_mem ha) hb)

include hfree in
lemma inner_mul_two_tailSpan (i : ι) {a b : A} (ha : a ∈ S i) (hb : b ∈ S i)
    {x y : t.functional.GNS} (hx : x ∈ tailSpan t S i) (hy : y ∈ tailSpan t S i) :
    inner ℂ (t.functional.gnsStarAlgHom a x) (t.functional.gnsStarAlgHom b y) =
      t.functional (star a*b)*inner ℂ x y := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, hw, hiw, rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨z, hz, hiz, rfl⟩ := hy
      exact inner_mul_two_wordVector t S hfree hw hz hiw hiz ha hb
    | zero => simp
    | add y z _ _ hy hz => simp only [map_add, inner_add_right, hy, hz, mul_add]
    | smul c y _ hy => simp only [map_smul, inner_smul_right, hy]; ring
  | zero => simp
  | add x z _ _ hx hz => simp only [map_add, inner_add_left, hx, hz, mul_add]
  | smul c x _ hx => simp only [map_smul, inner_smul_left, hx]; ring

include hfree in
lemma inner_mul_two_tailSpace (i : ι) {a b : A} (ha : a ∈ S i) (hb : b ∈ S i)
    {x y : t.functional.GNS} (hx : x ∈ tailSpace t S i) (hy : y ∈ tailSpace t S i) :
    inner ℂ (t.functional.gnsStarAlgHom a x) (t.functional.gnsStarAlgHom b y) =
      t.functional (star a*b)*inner ℂ x y := by
  apply closure_minimal (s := (tailSpan t S i : Set _))
    (t := {x | inner ℂ (t.functional.gnsStarAlgHom a x) (t.functional.gnsStarAlgHom b y) =
      t.functional (star a*b)*inner ℂ x y}) ?_ ?_ hx
  · intro x hx
    apply closure_minimal (s := (tailSpan t S i : Set _))
      (t := {y | inner ℂ (t.functional.gnsStarAlgHom a x) (t.functional.gnsStarAlgHom b y) =
        t.functional (star a*b)*inner ℂ x y}) ?_ ?_ hy
    · intro y hy
      exact inner_mul_two_tailSpan t S hfree i ha hb hx hy
    · apply isClosed_eq <;> fun_prop
  · apply isClosed_eq <;> fun_prop

end Kadison.FreeCreation
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FreeBlockWords2
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct
open scoped TensorProduct InnerProductSpace Topology
open UniformSpace Completion Filter
open scoped TensorProduct
open UniformSpace Completion
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open scoped InnerProductSpace TensorProduct ComplexOrder
open UniformSpace
open scoped InnerProductSpace _root_.Topology

namespace Kadison.FreeBlocks

open FreeMoments FreeWordTensor FreeCreation UniformSpace

open scoped InnerProductSpace

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (t : FaithfulState A) {ι : Type*} (S : ι → StarSubalgebra ℂ A)

variable (hfree : Free S t.functional.toLinearMap) {i j : ι} (hij : i ≠ j)

include hfree hij in
lemma blockVector_cons_gram (x y : Letters t S i j)
    (xs ys : List (Letters t S i j)) {z v : A} (hz : z ∈ S j) (hv : v ∈ S j) :
    inner ℂ (blockVector t S (x::xs) z) (blockVector t S (y::ys) v) =
      (inner ℂ x.1 y.1 * inner ℂ x.2 y.2)*
        inner ℂ (blockVector t S xs z) (blockVector t S ys v) := by
  rw [blockVector_cons, blockVector_cons]
  have hx := blockVector_mem_tail t S hij xs hz
  have hy := blockVector_mem_tail t S hij ys hv
  rw [inner_mul_two_tailSpace t S hfree j (a := letterValue t S j x.1) (b := letterValue t S j y.1) x.1.property.1 y.1.property.1
      (headSpace_le_other_tailSpace t S hij
        (creation_mem_headSpace t S i (a := letterValue t S i x.2) x.2.property.1 x.2.property.2 hx))
      (headSpace_le_other_tailSpace t S hij
        (creation_mem_headSpace t S i (a := letterValue t S i y.2) y.2.property.1 y.2.property.2 hy)),
    inner_mul_two_tailSpace t S hfree i (a := letterValue t S i x.2) (b := letterValue t S i y.2) x.2.property.1 y.2.property.1 hx hy]
  rw [inner_letter, inner_letter, mul_assoc]

end Kadison.FreeBlocks
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FreeBlockTensor
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct
open scoped TensorProduct InnerProductSpace Topology
open UniformSpace Completion Filter
open scoped TensorProduct
open UniformSpace Completion
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open scoped InnerProductSpace TensorProduct ComplexOrder
open UniformSpace
open scoped InnerProductSpace _root_.Topology

namespace Kadison.FreeBlocks

open FreeMoments FreeWordTensor FreeCreation UniformSpace

open scoped InnerProductSpace TensorProduct

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (t : FaithfulState A) {ι : Type*} (S : ι → StarSubalgebra ℂ A)

variable {i j : ι}

variable (hfree : Free S t.functional.toLinearMap) (hij : i≠j)

include hfree hij

lemma inner_blockReadPre_pure : ∀ n (x y : BlockParams t S i j n),
    inner ℂ (blockReadPre t S n (blockPure t S n x))
      (blockReadPre t S n (blockPure t S n y)) =
      inner ℂ (blockPure t S n x) (blockPure t S n y)
  | 0, x, y => by
    change inner ℂ (t.functional.toPreGNS (t.functional.ofPreGNS (x : preSpace t)))
      (t.functional.toPreGNS (t.functional.ofPreGNS (y : preSpace t))) = inner ℂ x y
    simp
  | n+1, x, y => by
    rw [←Completion.inner_coe, blockReadPre_pure, blockReadPre_pure]
    change inner ℂ (blockVector t S (x.1::paramLetters t S n x.2)
      (factorValue t S j (paramEnd t S n x.2)))
      (blockVector t S (y.1::paramLetters t S n y.2)
        (factorValue t S j (paramEnd t S n y.2))) = _
    rw [blockVector_cons_gram t S hfree hij _ _ _ _
      (z := factorValue t S j (paramEnd t S n x.2))
      (v := factorValue t S j (paramEnd t S n y.2))
      (paramEnd t S n x.2).property (paramEnd t S n y.2).property]
    rw [←blockReadPre_pure, ←blockReadPre_pure, Completion.inner_coe,
      inner_blockReadPre_pure n x.2 y.2]
    simp only [blockPure, TensorProduct.inner_tmul, mul_assoc]

lemma inner_blockReadPre (n : ℕ) (x y : blockTensor t S i j n) :
    inner ℂ (blockReadPre t S n x) (blockReadPre t S n y) = inner ℂ x y := by
  have hx : x ∈ Submodule.span ℂ (Set.range (blockPure t S (i := i) (j := j) n)) := by rw [span_blockPure]; trivial
  have hy : y ∈ Submodule.span ℂ (Set.range (blockPure t S (i := i) (j := j) n)) := by rw [span_blockPure]; trivial
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v,rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy => obtain ⟨w,rfl⟩ := hy; exact inner_blockReadPre_pure t S hfree hij n v w
    | zero => simp
    | add x y _ _ hx hy => simp only [map_add, inner_add_right, hx, hy]
    | smul c y _ hy => simp only [map_smul, inner_smul_right, hy]
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add, inner_add_left, hx, hy]
  | smul c x _ hx => simp only [map_smul, inner_smul_left, hx]

end Kadison.FreeBlocks
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FreeBlockTensor2
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct
open scoped TensorProduct InnerProductSpace Topology
open UniformSpace Completion Filter
open scoped TensorProduct
open UniformSpace Completion
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open scoped InnerProductSpace TensorProduct ComplexOrder
open UniformSpace
open scoped InnerProductSpace _root_.Topology

namespace Kadison.FreeBlocks

open FreeMoments FreeWordTensor FreeCreation UniformSpace

open scoped InnerProductSpace TensorProduct

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (t : FaithfulState A) {ι : Type*} (S : ι → StarSubalgebra ℂ A)

variable (hfree : Free S t.functional.toLinearMap) {i j : ι} (hij : i≠j)

include hfree hij in
lemma inner_endpointRead_tmul (n : ℕ) (a b : factorSpace t S i)
    (x y : blockTensor t S i j n) :
    inner ℂ (endpointRead t S n (a ⊗ₜ[ℂ] x)) (endpointRead t S n (b ⊗ₜ[ℂ] y)) =
      inner ℂ (a ⊗ₜ[ℂ] x) (b ⊗ₜ[ℂ] y) := by
  rw [←Completion.inner_coe, endpointRead_tmul, endpointRead_tmul,
    inner_mul_two_tailSpace t S hfree i (a := factorValue t S i a)
      (b := factorValue t S i b) a.property b.property
      (blockReadPre_mem_tail t S hij n x) (blockReadPre_mem_tail t S hij n y),
    Completion.inner_coe, inner_blockReadPre t S hfree hij]
  rw [TensorProduct.inner_tmul]
  rfl

include hfree hij in
lemma inner_endpointRead (n : ℕ) (x y : endpointTensor t S i j n) :
    inner ℂ (endpointRead t S n x) (endpointRead t S n y)=inner ℂ x y := by
  induction x using endpointTensor_induction_on t S n with
  | h0 => simp
  | ha x z hx hz => simpa only [map_add, inner_add_left] using congrArg₂ (·+·) hx hz
  | ht a x =>
    change inner ℂ (endpointRead t S n (a ⊗ₜ[ℂ] x)) (endpointRead t S n y) =
      inner ℂ (a ⊗ₜ[ℂ] x : endpointTensor t S i j n) y
    induction y using endpointTensor_induction_on t S n with
    | h0 =>
      rw [map_zero, inner_zero_right]
      exact (inner_zero_right (𝕜 := ℂ) (E := endpointTensor t S i j n) (a ⊗ₜ[ℂ] x)).symm
    | ha y z hy hz =>
      rw [map_add, inner_add_right]
      exact (congrArg₂ (·+·) hy hz).trans
        (inner_add_right (𝕜 := ℂ) (E := endpointTensor t S i j n) (a ⊗ₜ[ℂ] x) y z).symm
    | ht b y => exact inner_endpointRead_tmul t S hfree hij n a b x y

def endpointIsometry (n : ℕ) : endpointTensor t S i j n →ₗᵢ[ℂ] preSpace t :=
  (endpointRead t S n).isometryOfInner (inner_endpointRead t S hfree hij n)

def levelEmbedding (n : ℕ) : Completion (endpointTensor t S i j n) →ₗᵢ[ℂ] t.functional.GNS where
  toLinearMap := (endpointIsometry t S hfree hij n).toContinuousLinearMap.completion.toLinearMap
  norm_map' x := by
    induction x using Completion.induction_on with
    | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
    | ih x => simp

@[simp] lemma levelEmbedding_coe (n : ℕ) (x : endpointTensor t S i j n) :
    levelEmbedding t S hfree hij n (x : Completion (endpointTensor t S i j n)) =
      (endpointRead t S n x : t.functional.GNS) := by
  change (endpointIsometry t S hfree hij n).toContinuousLinearMap.completion _ = _
  simp [endpointIsometry]

end Kadison.FreeBlocks
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FreeBlockTensor3
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct
open scoped TensorProduct InnerProductSpace Topology
open UniformSpace Completion Filter
open scoped TensorProduct
open UniformSpace Completion
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open scoped InnerProductSpace TensorProduct ComplexOrder
open UniformSpace
open scoped InnerProductSpace _root_.Topology

namespace Kadison.FreeBlocks

open FreeMoments FreeWordTensor FreeCreation UniformSpace

open scoped InnerProductSpace TensorProduct

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (t : FaithfulState A) {ι : Type*} (S : ι → StarSubalgebra ℂ A)

variable {i j : ι} (hcolors : ∀ c : ι, c=i ∨ c=j)

def factorOf (i : ι) (a : A) (ha : a∈S i) : factorSpace t S i :=
  ⟨t.functional.toPreGNS a, by simpa [factorSpace] using ha⟩

def letterOf (i : ι) (a : A) (ha : a∈S i) (ha0 : t.functional a=0) : letterSpace t S i :=
  ⟨t.functional.toPreGNS a, by simpa [letterSpace] using And.intro ha ha0⟩

@[simp] lemma factorValue_factorOf (i : ι) (a : A) (ha : a∈S i) :
    factorValue t S i (factorOf t S i a ha)=a := by simp [factorValue, factorOf]

@[simp] lemma letterValue_letterOf (i : ι) (a : A) (ha : a∈S i) (ha0 : t.functional a=0) :
    letterValue t S i (letterOf t S i a ha ha0)=a := by simp [letterValue, letterOf]

end Kadison.FreeBlocks
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FreeSymmetry10
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct
open scoped TensorProduct InnerProductSpace Topology
open UniformSpace Completion Filter
open scoped TensorProduct
open UniformSpace Completion
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open scoped InnerProductSpace TensorProduct ComplexOrder
open UniformSpace
open scoped InnerProductSpace _root_.Topology
open scoped TensorProduct
open UniformSpace
open scoped TensorProduct InnerProductSpace

namespace Kadison.FreeBlocks

open FreeWordTensor UniformSpace

open scoped ComplexOrder InnerProductSpace

variable {A D : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable (t : FaithfulState A) (f : D →⋆ₐ[ℂ] A) (hf : Function.Injective f)

include hf in
def pullbackState : FaithfulState D where
  functional :=
    { toLinearMap := t.functional.toLinearMap.comp f.toLinearMap
      monotone' := fun _ _ hab => t.functional.monotone
        ((OAI.nonUnitalStarRingHomOfClass f).map_le_map_of_map_star hab) }
  normalized := by change t.functional (f 1)=1; simpa using t.normalized
  faithful := by
    intro a ha
    apply hf
    rw [map_zero]
    apply t.faithful
    change t.functional (f (star a*a))=0 at ha
    simpa only [map_mul, map_star] using ha

@[simp] lemma pullbackState_apply (a : D) :
    (pullbackState t f hf).functional a = t.functional (f a) := rfl

variable {ι : Type*} (S : ι → StarSubalgebra ℂ A) (i : ι) (hS : S i=f.range)

def factorPreMap : preSpace (pullbackState t f hf) →ₗᵢ[ℂ] factorSpace t S i where
  toLinearMap :=
    { toFun := fun x => ⟨t.functional.toPreGNS (f ((pullbackState t f hf).functional.ofPreGNS x)), by
        change f _ ∈ S i
        rw [hS]
        exact ⟨_,rfl⟩⟩
      map_add' := by intro x y; apply Subtype.ext; simp
      map_smul' := by intro c x; apply Subtype.ext; simp }
  norm_map' x := by
    change ‖t.functional.toPreGNS (f ((pullbackState t f hf).functional.ofPreGNS x))‖ = ‖x‖
    simp only [PositiveLinearMap.preGNS_norm_def, PositiveLinearMap.ofPreGNS_toPreGNS,
      pullbackState_apply, map_mul, map_star]

lemma factorPreMap_surjective : Function.Surjective (factorPreMap t f hf S i hS) := by
  intro y
  have hy : t.functional.ofPreGNS (y : preSpace t) ∈ f.range := hS ▸ y.property
  obtain ⟨x,hx⟩ := hy
  refine ⟨(pullbackState t f hf).functional.toPreGNS x, ?_⟩
  apply Subtype.ext
  change t.functional.toPreGNS (f x)=(y : preSpace t)
  change f x=t.functional.ofPreGNS (y : preSpace t) at hx
  rw [hx, PositiveLinearMap.toPreGNS_ofPreGNS]

def factorPreIso : preSpace (pullbackState t f hf) ≃ₗᵢ[ℂ] factorSpace t S i :=
  LinearIsometryEquiv.ofSurjective (factorPreMap t f hf S i hS)
    (factorPreMap_surjective t f hf S i hS)

def factorGNSIso : Completion (factorSpace t S i) ≃ₗᵢ[ℂ]
    (pullbackState t f hf).functional.GNS :=
  (HilbertCompletion.congr (factorPreIso t f hf S i hS)).symm

@[simp] lemma factorGNSIso_coe (a : D) :
    factorGNSIso t f hf S i hS
      ((⟨t.functional.toPreGNS (f a), by exact (factorPreMap t f hf S i hS
        ((pullbackState t f hf).functional.toPreGNS a)).property⟩ : factorSpace t S i) :
        Completion (factorSpace t S i)) =
      ((pullbackState t f hf).functional.toPreGNS a : (pullbackState t f hf).functional.GNS) := by
  apply (HilbertCompletion.congr (factorPreIso t f hf S i hS)).injective
  simp only [factorGNSIso, LinearIsometryEquiv.apply_symm_apply, HilbertCompletion.congr_coe]
  rfl

end Kadison.FreeBlocks
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_HankelAlgebra
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

namespace Kadison.FreeMoments

variable {A : Type*} [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]

variable {ι : Type*} {S : ι → StarSubalgebra ℂ A} {τ : A →ₗ[ℂ] ℂ}

@[simp] lemma paired_cons (s a : Letter S τ) (v : List (Letter S τ)) :
    paired s (a::v)=a::s::paired s v := rfl

end Kadison.FreeMoments

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_Regroup
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct
open scoped TensorProduct InnerProductSpace Topology
open UniformSpace Completion Filter
open scoped TensorProduct
open UniformSpace Completion
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open scoped InnerProductSpace TensorProduct ComplexOrder
open UniformSpace
open scoped InnerProductSpace _root_.Topology
open scoped TensorProduct
open UniformSpace
open scoped TensorProduct InnerProductSpace

namespace Kadison.FreeBlocks

open FreeMoments FreeWordTensor FreeCreation UniformSpace

open scoped TensorProduct InnerProductSpace

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (t : FaithfulState A) {ι : Type*} (S : ι → StarSubalgebra ℂ A)

variable {i j : ι}

def dLetters (i : ι) : PreHilbert := ⟨letterSpace t S i⟩

def aLetters (i : ι) : PreHilbert := ⟨factorSpace t S i⟩

@[reducible] def multiplicityTensor (j : ι) : ℕ → Space
  | 0 => ⟨factorSpace t S j⟩
  | n+1 => spaceTensor ⟨letterSpace t S j⟩ (multiplicityTensor j n)

def paramD : ∀ n, BlockParams t S i j n → (Fin n → letterSpace t S i)
  | 0, _ => Fin.elim0
  | n+1, x => Fin.cons x.1.2 (paramD n x.2)

def paramJ : ∀ n, BlockParams t S i j n → multiplicityTensor t S j n
  | 0, z => z
  | n+1, x => x.1.1 ⊗ₜ[ℂ] paramJ n x.2

def blockShuffle : ∀ n, blockTensor t S i j n ≃ₗᵢ[ℂ]
    (PreHilbert.power (dLetters t S i) n ⊗[ℂ] multiplicityTensor t S j n)
  | 0 => (TensorProduct.lidIsometry ℂ (aLetters t S j)).symm
  | n+1 =>
    (TensorProduct.congrIsometry (.refl ℂ (dLetters t S j))
      (TensorProduct.congrIsometry (.refl ℂ (dLetters t S i)) (blockShuffle n))) |>.trans
    (TensorProduct.congrIsometry (.refl ℂ (dLetters t S j))
      (TensorProduct.assocIsometry ℂ (dLetters t S i)
        (PreHilbert.power (dLetters t S i) n) (multiplicityTensor t S j n)).symm) |>.trans
    HilbertCompletion.leftSwap

@[simp] lemma blockShuffle_pure : ∀ n (x : BlockParams t S i j n),
    blockShuffle t S n (blockPure t S n x) =
      PreHilbert.pure (dLetters t S i) n (paramD t S n x) ⊗ₜ[ℂ] paramJ t S n x
  | 0, x => by rfl
  | n+1, x => by
    change HilbertCompletion.leftSwap
      ((TensorProduct.congrIsometry (.refl ℂ (dLetters t S j))
        (TensorProduct.assocIsometry ℂ (dLetters t S i)
          (PreHilbert.power (dLetters t S i) n) (multiplicityTensor t S j n)).symm)
        ((x.1.1 : dLetters t S j) ⊗ₜ[ℂ]
          ((x.1.2 : dLetters t S i) ⊗ₜ[ℂ] blockShuffle t S n (blockPure t S n x.2)))) = _
    rw [blockShuffle_pure n x.2]
    change HilbertCompletion.leftSwap
      ((x.1.1 : dLetters t S j) ⊗ₜ[ℂ]
        (((x.1.2 : dLetters t S i) ⊗ₜ[ℂ] PreHilbert.pure (dLetters t S i) n (paramD t S n x.2)) ⊗ₜ[ℂ]
          paramJ t S n x.2)) = _
    rw [HilbertCompletion.leftSwap_tmul]
    rfl

def endpointShuffle (n : ℕ) : endpointTensor t S i j n ≃ₗᵢ[ℂ]
    ((aLetters t S i ⊗[ℂ] PreHilbert.power (dLetters t S i) n) ⊗[ℂ]
      multiplicityTensor t S j n) :=
  (TensorProduct.congrIsometry (.refl ℂ (aLetters t S i)) (blockShuffle t S n)) |>.trans
    (TensorProduct.assocIsometry ℂ (aLetters t S i)
      (PreHilbert.power (dLetters t S i) n) (multiplicityTensor t S j n)).symm

@[simp] lemma endpointShuffle_pure (n : ℕ) (a : factorSpace t S i) (x : BlockParams t S i j n) :
    endpointShuffle t S n (a ⊗ₜ[ℂ] blockPure t S n x) =
      (a ⊗ₜ[ℂ] PreHilbert.pure (dLetters t S i) n (paramD t S n x)) ⊗ₜ[ℂ] paramJ t S n x := by
  change (TensorProduct.assocIsometry ℂ (aLetters t S i)
      (PreHilbert.power (dLetters t S i) n) (multiplicityTensor t S j n)).symm
        ((a : aLetters t S i) ⊗ₜ[ℂ] blockShuffle t S n (blockPure t S n x)) = _
  rw [blockShuffle_pure]
  rfl

abbrev scalarLevel (i : ι) (n : ℕ) := Completion
  (aLetters t S i ⊗[ℂ] PreHilbert.power (dLetters t S i) n)

abbrev multiplicityLevel (j : ι) (n : ℕ) := Completion (multiplicityTensor t S j n)

def levelShuffle (n : ℕ) : Completion (endpointTensor t S i j n) ≃ₗᵢ[ℂ]
    Completion (scalarLevel t S i n ⊗[ℂ] multiplicityLevel t S j n) :=
  (HilbertCompletion.congr (endpointShuffle t S n)).trans HilbertCompletion.tensor

end Kadison.FreeBlocks
end

end OAI
end


