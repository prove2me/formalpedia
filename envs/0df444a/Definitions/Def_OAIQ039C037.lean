-- Prove2me | Definitions.Def_OAIQ039C037
-- name    : OAIQ039C037
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T06:21:14.925045+00:00
-- url     : https://prove2.me/theorems/a41a6d0d-4fe0-406c-b2c8-1216e22d48fb
-- title:
--   Definitions bundle OAIQ039C037 of the split of OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 50 declarations of OpenAI's Lean: 15 definitions, 4 instances and 31 theorems. The definitions and types are `OAI.Kadison.FreeMoments.liftLetter`, `OAI.Kadison.FreeWordTensor.restrictedState`, `OAI.Kadison.HilbertModuleSB.intertwinerAlgebra`, `OAI.Kadison.HilbertModuleSB.offDiagonal`, `OAI.Kadison.HilbertModuleSB.offDiagonalReverse`, `OAI.Kadison.HilbertSequence.Space`, `OAI.Kadison.HilbertSequence.act`, `OAI.Kadison.HilbertSequence.actPre`, `OAI.Kadison.HilbertSequence.actPreLinear`, `OAI.Kadison.HilbertSequence.constant`, `OAI.Kadison.HilbertSequence.constantPre`, `OAI.Kadison.HilbertSequence.constantPreMap`, `OAI.Kadison.HilbertSequence.form`, `OAI.Kadison.HilbertSequence.mapPre`, `OAI.Kadison.VectorGNS.subalgebraTrace`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/Commutator, in whole or in part: `Commutator_BoundedSequenceClosed`, `Commutator_FreeCompressionNorm`, `Commutator_FreeCreation`, `Commutator_FreeInnerFamily`, `Commutator_FreeWordTensor`, `Commutator_GeneratedFreePair`, `Commutator_GeneratedMatrixBicommutant`, `Commutator_HilbertModuleSchroederBernstein`, `Commutator_HilbertSequence`, `Commutator_HilbertSequenceOperator`, `Commutator_MatrixTowerGNS`, `Commutator_TracialVectorSubalgebra`.
--
--   **Imports.** It imports the bundles `OAIQ039C012`, `OAIQ039C020`, `OAIQ039C022`, `OAIQ039C025` and `OAIQ039C026` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ039C046`, `OAIQ039C047`, `OAIQ039C048`, `OAIQ039C052` and `OAIQ039C053`; the proofs of `OAI.Kadison.CentralSpectral.separable_uniform_bound`, `OAI.Kadison.CentralSpectral.stable_model_bound`, `OAI.Kadison.CentralSpectral.stable_model_center`, `OAI.Kadison.GeneratedMatrixBicommutant.factor`, `OAI.Kadison.HilbertModuleSB.exists_unitary_of_embeddings` and `OAI.Kadison.SeparableTest.bound_of_separable_bound`.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/Commutator at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ039C012
import Definitions.Def_OAIQ039C020
import Definitions.Def_OAIQ039C022
import Definitions.Def_OAIQ039C025
import Definitions.Def_OAIQ039C026

section
-- module Solutions.OAIQ039_CM.Commutator_HilbertSequence
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology InnerProductSpace BoundedContinuousFunction

open Filter UniformSpace Completion

namespace Kadison.HilbertSequence

variable (ω : Ultrafilter ℕ) (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]

omit [InnerProductSpace ℂ H] in
@[simp] lemma seq_zero (i : ℕ) : (0 : Pre ω H).seq i=0 := rfl

lemma inner_bounded (x y : Pre ω H) : ∃ C : ℝ, ∀ i,
    ‖inner ℂ (x.seq i) (y.seq i)‖≤C := by
  refine ⟨‖x.seq‖*‖y.seq‖,fun i => ?_⟩
  exact (norm_inner_le_norm _ _).trans (mul_le_mul (x.seq.norm_coe_le_norm i)
    (y.seq.norm_coe_le_norm i) (norm_nonneg _) (norm_nonneg _))

def form (x y : Pre ω H) : ℂ :=
  ScalarUltralimit.limit ω (fun i => inner ℂ (x.seq i) (y.seq i)) (inner_bounded ω H x y)

lemma tendsto_form (x y : Pre ω H) :
    Tendsto (fun i => inner ℂ (x.seq i) (y.seq i)) (ω : Filter ℕ) (𝓝 (form ω H x y)) :=
  ScalarUltralimit.tendsto_limit ω _ _

instance core : PreInnerProductSpace.Core ℂ (Pre ω H) where
  inner := form ω H
  conj_inner_symm x y := by
    apply tendsto_nhds_unique _ (tendsto_form ω H x y)
    simpa only [RCLike.star_def,inner_conj_symm] using (tendsto_form ω H y x).star
  re_inner_nonneg x := by
    apply ge_of_tendsto (Complex.continuous_re.tendsto _ |>.comp (tendsto_form ω H x x))
    exact Filter.Eventually.of_forall (fun i => (inner_self_nonneg (𝕜 := ℂ) (x := x.seq i)))
  add_left x y z := by
    apply tendsto_nhds_unique (tendsto_form ω H (x+y) z)
    simpa only [seq_add,inner_add_left] using (tendsto_form ω H x z).add (tendsto_form ω H y z)
  smul_left x y r := by
    apply tendsto_nhds_unique (tendsto_form ω H (r • x) y)
    simpa only [seq_smul,inner_smul_left] using tendsto_const_nhds.mul (tendsto_form ω H x y)

instance instSeminormedAddCommGroupPre : SeminormedAddCommGroup (Pre ω H) :=
  InnerProductSpace.Core.toSeminormedAddCommGroup (c := core ω H)

instance instInnerProductSpaceComplexPre : InnerProductSpace ℂ (Pre ω H) := InnerProductSpace.ofCore (core ω H)

@[simp] lemma pre_inner (x y : Pre ω H) : inner ℂ x y=form ω H x y := rfl

lemma tendsto_inner (x y : Pre ω H) :
    Tendsto (fun i => inner ℂ (x.seq i) (y.seq i)) (ω : Filter ℕ) (𝓝 (inner ℂ x y)) :=
  tendsto_form ω H x y

lemma tendsto_norm (x : Pre ω H) :
    Tendsto (fun i => ‖x.seq i‖) (ω : Filter ℕ) (𝓝 ‖x‖) := by
  have h := (Complex.continuous_re.tendsto _ |>.comp (tendsto_inner ω H x x)).sqrt
  simpa only [Function.comp_apply, ← RCLike.re_to_complex, inner_self_eq_norm_sq,Real.sqrt_sq (norm_nonneg _)] using h

abbrev Space := Completion (Pre ω H)

def constantPre (x : H) : Pre ω H := ⟨BoundedContinuousFunction.const ℕ x⟩

lemma norm_constantPre (x : H) : ‖constantPre ω H x‖=‖x‖ :=
  tendsto_nhds_unique (tendsto_norm ω H _) tendsto_const_nhds

def constantPreMap : H →ₗᵢ[ℂ] Pre ω H where
  toFun := constantPre ω H
  map_add' := by
    intro x y
    apply (equiv ω H).injective
    apply BoundedContinuousFunction.ext
    intro i
    rfl
  map_smul' := by
    intro r x
    apply (equiv ω H).injective
    apply BoundedContinuousFunction.ext
    intro i
    rfl
  norm_map' := norm_constantPre ω H

def constant : H →ₗᵢ[ℂ] Space ω H :=
  (toComplₗᵢ : Pre ω H →ₗᵢ[ℂ] Space ω H).comp (constantPreMap ω H)

@[simp] lemma constant_apply (x : H) : constant ω H x=(constantPre ω H x : Space ω H) := rfl

end Kadison.HilbertSequence

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_BoundedSequenceClosed
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology InnerProductSpace BoundedContinuousFunction

open Filter UniformSpace Completion

namespace Kadison.HilbertSequence

variable {A H : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

variable (ω : Ultrafilter ℕ) (v : A →L[ℂ] H)

def mapPre (a : ℕ →ᵇ A) : Pre ω H :=
  ⟨BoundedContinuousFunction.comp v v.lipschitz a⟩

end Kadison.HilbertSequence

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FreeWordTensor
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
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

lemma inner_readPre_pure_ne (is js : List ι)
    (his : is.IsChain (· ≠ ·)) (hjs : js.IsChain (· ≠ ·)) (hne : is ≠ js)
    (x : Params t S is) (y : Params t S js) :
    inner ℂ (readPre t S is (pure t S is x)) (readPre t S js (pure t S js y)) = 0 := by
  rw [readPre_pure, readPre_pure]
  change t.functional.toLinearMap (star (FreeMoments.word (letters t S is x)) *
    FreeMoments.word (letters t S js y)) = 0
  rw [FreeMoments.gram_word (fun a => map_star t.functional a) t.normalized hfree _ _
    (letters_reduced t S is x his) (letters_reduced t S js y hjs)]
  apply FreeMoments.gram_zero_of_colors_ne
  simpa only [letters_colors] using hne

lemma inner_readPre_ne (is js : List ι)
    (his : is.IsChain (· ≠ ·)) (hjs : js.IsChain (· ≠ ·)) (hne : is ≠ js)
    (x : tensor t S is) (y : tensor t S js) :
    inner ℂ (readPre t S is x) (readPre t S js y) = 0 := by
  have hx : x ∈ Submodule.span ℂ (Set.range (pure t S is)) := by rw [span_pure]; trivial
  have hy : y ∈ Submodule.span ℂ (Set.range (pure t S js)) := by rw [span_pure]; trivial
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨w, rfl⟩ := hy
      exact inner_readPre_pure_ne t S hfree is js his hjs hne v w
    | zero => simp
    | add y z _ _ hy hz => simp only [map_add, inner_add_right, hy, hz, add_zero]
    | smul c y _ hy => simp only [map_smul, inner_smul_right, hy, mul_zero]
  | zero => simp
  | add x z _ _ hx hz => simp only [map_add, inner_add_left, hx, hz, add_zero]
  | smul c x _ hx => simp only [map_smul, inner_smul_left, hx, mul_zero]

lemma wordEmbedding_orthogonal (is js : List ι)
    (his : is.IsChain (· ≠ ·)) (hjs : js.IsChain (· ≠ ·)) (hne : is ≠ js)
    (x : Completion (tensor t S is)) (y : Completion (tensor t S js)) :
    inner ℂ (wordEmbedding t S hfree is his x) (wordEmbedding t S hfree js hjs y) = 0 := by
  induction x, y using Completion.induction_on₂ with
  | hp => apply isClosed_eq <;> fun_prop
  | ih x y =>
    rw [wordEmbedding_coe, wordEmbedding_coe, Completion.inner_coe]
    exact inner_readPre_ne t S hfree is js his hjs hne x y

end Kadison.FreeWordTensor
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FreeCreation
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
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

instance instIsClosedGNSFunctionalCoeSubmoduleComplexTailSpace (i : ι) : IsClosed ((tailSpace t S i : Submodule ℂ t.functional.GNS) : Set t.functional.GNS) :=
  (tailSpan t S i).isClosed_topologicalClosure

end Kadison.FreeCreation
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FreeCompressionNorm
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder

namespace Kadison.FreeMoments

variable {A B : Type*} [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]
  [Ring B] [Algebra ℂ B] [StarRing B] [StarModule ℂ B]

variable {ι : Type*} (S : ι → StarSubalgebra ℂ A) (τ : A →ₗ[ℂ] ℂ)
  (f : B →⋆ₐ[ℂ] A)

def liftLetter (a : Letter (fun i => (S i).comap f) (τ.comp f.toLinearMap)) : Letter S τ :=
  ⟨a.color,f a.val,a.mem,a.centered⟩

@[simp] lemma liftLetter_color (a) : (liftLetter S τ f a).color=a.color := rfl

@[simp] lemma liftLetter_val (a) : (liftLetter S τ f a).val=f a.val := rfl

end Kadison.FreeMoments

namespace Kadison.FreeWordTensor

open scoped ComplexOrder

variable {A D : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable (t : FaithfulState A) (f : D →⋆ₐ[ℂ] A) (hf : Function.Injective f)

def restrictedState : FaithfulState D where
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
    simpa only [map_mul,map_star] using ha

end Kadison.FreeWordTensor

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FreeInnerFamily
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.FreeCreation.instIsClosedGNSFunctionalCoeSubmoduleComplexTailSpace _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace TensorProduct CStarAlgebra

open UniformSpace

namespace Kadison.FreeWordAction

open FreeWordTensor FreeMoments

variable {A D : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable (t : FaithfulState A) (ht : ∀ a b : A, t.functional (a*b)=t.functional (b*a))

variable (f : D →⋆ₐ[ℂ] A) {ι : Type*} (S : ι → StarSubalgebra ℂ A) (i : ι)
  (hS : S i=f.range)

omit [PartialOrder D] [StarOrderedRing D] in
include ht in
lemma innerFamily_trace (u : unitary D) (k : ι) (a : A) :
    t.functional (innerFamily f i u k a)=t.functional a := by
  by_cases hk : k=i
  · subst k
    rw [innerFamily_self,ht,←mul_assoc,←map_mul,Unitary.star_mul_self_of_mem u.property,
      map_one,one_mul]
  · rw [innerFamily_other f i u hk a]

end Kadison.FreeWordAction

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_HilbertSequenceOperator
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology InnerProductSpace BoundedContinuousFunction

open Filter UniformSpace Completion

namespace Kadison.HilbertSequence

variable (ω : Ultrafilter ℕ)

variable {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G]

lemma point_action_bound (T : ℕ →ᵇ (E →L[ℂ] F)) (x : Pre ω E) (i : ℕ) :
    ‖T i (x.seq i)‖≤‖T‖*‖x.seq‖ :=
  (T i).le_of_opNorm_le (T.norm_coe_le_norm i) _ |>.trans
    (mul_le_mul_of_nonneg_left (x.seq.norm_coe_le_norm i) (norm_nonneg _))

def actPreLinear (T : ℕ →ᵇ (E →L[ℂ] F)) : Pre ω E →ₗ[ℂ] Pre ω F where
  toFun x := ⟨BoundedContinuousFunction.mkOfDiscrete (fun i => T i (x.seq i))
    (2*(‖T‖*‖x.seq‖)) (by
      intro i j
      exact (dist_le_norm_add_norm _ _).trans (by
        have hi := point_action_bound ω T x i
        have hj := point_action_bound ω T x j
        linarith))⟩
  map_add' x y := by
    apply (equiv ω F).injective
    apply BoundedContinuousFunction.ext
    intro i
    exact map_add (T i) _ _
  map_smul' r x := by
    apply (equiv ω F).injective
    apply BoundedContinuousFunction.ext
    intro i
    exact map_smul (T i) r _

@[simp] lemma actPreLinear_seq (T : ℕ →ᵇ (E →L[ℂ] F)) (x : Pre ω E) (i : ℕ) :
    (actPreLinear ω T x).seq i=T i (x.seq i) := rfl

lemma norm_actPreLinear_le (T : ℕ →ᵇ (E →L[ℂ] F)) (x : Pre ω E) :
    ‖actPreLinear ω T x‖≤‖T‖*‖x‖ := by
  apply le_of_tendsto_of_tendsto (tendsto_norm ω F (actPreLinear ω T x))
    (tendsto_const_nhds.mul (tendsto_norm ω E x))
  exact Filter.Eventually.of_forall (fun i => (T i).le_of_opNorm_le (T.norm_coe_le_norm i) _)

def actPre (T : ℕ →ᵇ (E →L[ℂ] F)) : Pre ω E →L[ℂ] Pre ω F :=
  (actPreLinear ω T).mkContinuous ‖T‖ (norm_actPreLinear_le ω T)

def act (T : ℕ →ᵇ (E →L[ℂ] F)) : Space ω E →L[ℂ] Space ω F :=
  (actPre ω T).completion

@[simp] lemma act_coe (T : ℕ →ᵇ (E →L[ℂ] F)) (x : Pre ω E) :
    act ω T x=(actPreLinear ω T x : Space ω F) :=
  ContinuousLinearMap.completion_apply_coe _ _

lemma act_eq_of_coe (S T : Space ω E →L[ℂ] Space ω F)
    (h : ∀ x : Pre ω E, S x=T x) : S=T := by
  ext x
  induction x using Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih x => exact h x

lemma act_add (S T : ℕ →ᵇ (E →L[ℂ] F)) : act ω (S+T)=act ω S+act ω T := by
  apply act_eq_of_coe ω
  intro x
  rw [add_apply,act_coe,act_coe,act_coe,← Completion.coe_add]
  congr 1

lemma act_smul (r : ℂ) (T : ℕ →ᵇ (E →L[ℂ] F)) : act ω (r • T)=r • act ω T := by
  apply act_eq_of_coe ω
  intro x
  rw [smul_apply,act_coe,act_coe,← Completion.coe_smul]
  congr 1

lemma act_zero : act ω (0 : ℕ →ᵇ (E →L[ℂ] F))=0 := by
  apply act_eq_of_coe ω
  intro x
  rw [act_coe,zero_apply,← Completion.coe_zero]
  congr 1

lemma act_mul (S T : ℕ →ᵇ (E →L[ℂ] E)) : act ω (S*T)=act ω S*act ω T := by
  apply act_eq_of_coe ω
  intro x
  rw [mul_apply_eq_comp,act_coe,act_coe,act_coe]
  congr 1

lemma act_one : act ω (1 : ℕ →ᵇ (E →L[ℂ] E))=1 := by
  apply act_eq_of_coe ω
  intro x
  rw [act_coe,one_apply_eq_self]
  congr 1

variable [CompleteSpace E]

lemma act_star (T : ℕ →ᵇ (E →L[ℂ] E)) : act ω (star T)=star (act ω T) := by
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  induction x using Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih x =>
    induction y using Completion.induction_on with
    | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
    | ih y =>
      rw [act_coe,act_coe,Completion.inner_coe,Completion.inner_coe]
      apply tendsto_nhds_unique (tendsto_inner ω E (actPreLinear ω (star T) x) y)
      have h := tendsto_inner ω E x (actPreLinear ω T y)
      simpa only [actPreLinear_seq,BoundedContinuousFunction.star_apply,
        ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_left] using h

end Kadison.HilbertSequence

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixTowerGNS
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder

namespace Kadison.NormalGNS

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

lemma subset_bicommutant (S : StarSubalgebra ℂ (K →L[ℂ] K)) : S≤(bicommutant S).toStarSubalgebra := by
  intro a ha
  exact (mem_bicommutant S a).mpr (Set.subset_centralizer_centralizer ha)

end Kadison.NormalGNS

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_TracialVectorSubalgebra
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped InnerProductSpace ComplexOrder

namespace Kadison.VectorGNS

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def subalgebraTrace (M : VonNeumannAlgebra H) (ξ : H) : M →ₚ[ℂ] ℂ where
  toLinearMap := (VectorFunctional.functional ξ).toLinearMap.comp M.toStarSubalgebra.subtype.toLinearMap
  monotone' := fun _ _ h => (VectorFunctional.functional ξ).monotone h

@[simp] lemma subalgebraTrace_apply (M : VonNeumannAlgebra H) (ξ : H) (a : M) :
    subalgebraTrace M ξ a=inner ℂ ξ ((a:H →L[ℂ] H) ξ) := rfl

end Kadison.VectorGNS

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_GeneratedFreePair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped ComplexOrder InnerProductSpace

namespace Kadison.GeneratedFreePair

open FreeMoments

variable {H A : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [CStarAlgebra A]

variable (D : VonNeumannAlgebra H) (k : A →⋆ₐ[ℂ] (H →L[ℂ] H))

lemma left_mem (d : D) : (d:H →L[ℂ] H)∈algebra D k :=
  NormalGNS.subset_bicommutant _ ((show D.toStarSubalgebra ≤ D.toStarSubalgebra ⊔ k.range from le_sup_left) d.property)

lemma right_mem (a : A) : k a∈algebra D k :=
  NormalGNS.subset_bicommutant _ ((show k.range ≤ D.toStarSubalgebra ⊔ k.range from le_sup_right) ⟨a,rfl⟩)

lemma left_le : D.toStarSubalgebra≤(algebra D k).toStarSubalgebra := fun a ha =>
  left_mem D k ⟨a,ha⟩

end Kadison.GeneratedFreePair

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_GeneratedMatrixBicommutant
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped ComplexOrder Matrix.Norms.L2Operator

namespace Kadison.GeneratedMatrixBicommutant

variable {H A : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [CStarAlgebra A]

variable (size : ℕ → ℕ)

variable (stage : ∀ n,Matrix (Fin (size n+1)) (Fin (size n+1)) ℂ →⋆ₐ[ℂ] A)

variable (φ : A →⋆ₐ[ℂ] (H →L[ℂ] H))

lemma stage_mem (n : ℕ) (a : Matrix (Fin (size n+1)) (Fin (size n+1)) ℂ) :
    φ (stage n a)∈algebra size stage φ :=
  NormalGNS.subset_bicommutant _ ((le_iSup (fun n => (φ.comp (stage n)).range) n) ⟨a,rfl⟩)

end Kadison.GeneratedMatrixBicommutant

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_HilbertModuleSchroederBernstein
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace Kadison.HilbertModuleSB

open HilbertBiprod PartialIsometryOrder

variable {H G : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

variable {A : Type*} [CStarAlgebra A]

variable (φ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ψ : A →⋆ₐ[ℂ] (G →L[ℂ] G))

def intertwinerAlgebra : VonNeumannAlgebra (Space H G) where
  toStarSubalgebra := StarSubalgebra.centralizer ℂ ((diagHom φ ψ).range : Set _)
  centralizer_centralizer' := by
    change Set.centralizer (Set.centralizer (Set.centralizer
      (((diagHom φ ψ).range : Set (Space H G →L[ℂ] Space H G)) ∪ star ((diagHom φ ψ).range : Set (Space H G →L[ℂ] Space H G))))) = _
    exact Set.centralizer_centralizer_centralizer _

def offDiagonal (V : H →ₗᵢ[ℂ] G) : Space H G →L[ℂ] Space H G :=
  inrL.comp (V.toContinuousLinearMap.comp inlL.adjoint)

def offDiagonalReverse (V : G →ₗᵢ[ℂ] H) : Space H G →L[ℂ] Space H G :=
  inlL.comp (V.toContinuousLinearMap.comp inrL.adjoint)

end Kadison.HilbertModuleSB

end

end
end

end OAI
end


