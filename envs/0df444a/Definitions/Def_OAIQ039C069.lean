-- Prove2me | Definitions.Def_OAIQ039C069
-- name    : OAIQ039C069
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T09:19:44.714958+00:00
-- url     : https://prove2.me/theorems/c54dee3e-244f-45b3-aa3a-4c26a2cddc40
-- title:
--   Definitions bundle OAIQ039C069 of the split of OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 14 declarations of OpenAI's Lean: 3 definitions and 11 theorems. The definitions and types are `OAI.Kadison.FreeBlocks.faithfulWordActions`, `OAI.Kadison.TracialSequence.sequenceTrace`, `OAI.Kadison.TracialSequence.sequenceUnitary`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/Commutator, in whole or in part: `Commutator_FreeActualStructure`, `Commutator_RelativeSequenceRange`, `Commutator_TracialDoubleCompression`, `Commutator_TracialSequenceRight`, `Commutator_TracialSequenceTrace`, `Commutator_UnitarySequence`.
--
--   **Imports.** It imports the bundles `OAIQ039C058`, `OAIQ039C063`, `OAIQ039C064` and `OAIQ039C065` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ039C072`; the statements `OAI.Kadison.TracialSequence.bicommutant_trace_mul`, `OAI.Kadison.TracialSequence.freeCornerPosition_of_unitary_abstract`, `OAI.Kadison.TracialSequence.sequenceUnitary_free`, `OAI.Kadison.TracialSequence.small_corner_bound`, `OAI.Kadison.TracialSequence.small_projection_lift`, `OAI.Kadison.TracialSequence.trace_mul` and `OAI.Kadison.TracialSequence.trace_sequence_word`; the proofs of `OAI.Kadison.FreeBlocks.free_word_structure`, `OAI.Kadison.TracialSequence.bicommutant_norm_lift`, `OAI.Kadison.TracialSequence.bicommutant_trace_mul`, `OAI.Kadison.TracialSequence.constant_bicommutant_contraction`, `OAI.Kadison.TracialSequence.exists_freeCornerPosition_of_equiv_tower`, `OAI.Kadison.TracialSequence.represented_corner_bound`, `OAI.Kadison.TracialSequence.sequenceUnitary_free`, `OAI.Kadison.TracialSequence.small_corner_bound`, `OAI.Kadison.TracialSequence.small_projection_lift`, `OAI.Kadison.TracialSequence.trace_mul` and `OAI.Kadison.TracialSequence.trace_sequence_word`.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/Commutator at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ039C058
import Definitions.Def_OAIQ039C063
import Definitions.Def_OAIQ039C064
import Definitions.Def_OAIQ039C065

section
-- module Solutions.OAIQ039_CM.Commutator_FreeActualStructure
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped ComplexOrder InnerProductSpace TensorProduct

open UniformSpace

namespace Kadison.FreeBlocks

open FreeWordTensor FreeMoments FreeWordAction

variable {A D : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable (t : FaithfulState A) (ht : ∀ a b : A, t.functional (a*b)=t.functional (b*a))

variable (f : D →⋆ₐ[ℂ] A) (hf : Function.Injective f)

variable {ι : Type*} (S : ι → StarSubalgebra ℂ A) (i j : ι) (hS : S i=f.range)

variable (hfree : Free S t.functional.toLinearMap)
  (hgen : ∀ a : A, t.functional.gnsStarAlgHom a ∈
    Set.centralizer (Set.centralizer (generatedOperators t S : Set _)))

variable (hij : i≠j) (hcolors : ∀ c : ι, c=i ∨ c=j)

variable (I : ℕ → Type*) [∀ n, Fintype (I n)] [∀ n, DecidableEq (I n)] [∀ n, Nonempty (I n)]

variable (φ : ∀ n, Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] D)

variable (e : ∀ {n m : ℕ}, n ≤ m → Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] Matrix (I m) (I m) ℂ)

variable (he : ∀ n m (h : n ≤ m) a, φ m (e h a)=φ n a)

variable (hsize : ∀ n q : ℕ, ∃ m, n ≤ m ∧ q ≤ Fintype.card (I m))

variable (hDgen : ∀ a : D, (factorTrace t f hf).gnsStarAlgHom a ∈
  Set.centralizer (Set.centralizer
    (TracialGNS.stageAlgebra (factorTrace t f hf) I φ : Set _)))

variable (G : t.functional.GNS →L[ℂ] t.functional.GNS)

variable (hGL : ∀ a : D, G.comp (t.functional.gnsStarAlgHom (f a))=
  (t.functional.gnsStarAlgHom (f a)).comp G)

def faithfulWordActions (state : FaithfulState D)
    (tracial : ∀ first second : D, state.functional (first * second) =
      state.functional (second * first)) : WordActions D where
  full := ⟨state.functional.GNS⟩
  centered := ⟨HilbertCompletion.centered
    ((state.functional.toPreGNS 1 : preSpace state) : state.functional.GNS)⟩
  left := state.functional.gnsStarAlgHom
  conjugation := TracialGNS.conjugation state.functional tracial
  centeredConjugation unitary := centeredIsometry (TracialGNS.vacuum state.functional)
    (TracialGNS.conjugation state.functional tracial unitary)
    (TracialGNS.conjugation_vacuum state.functional tracial unitary)

end Kadison.FreeBlocks

end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_TracialSequenceRight
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology InnerProductSpace BoundedContinuousFunction ComplexOrder

open Filter UniformSpace Completion

namespace Kadison.TracialSequence

open TracialGNS HilbertSequence

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ)

lemma operator_ext (S T : boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω)
    (h : ∀ a : ℕ →ᵇ A, S (vectorIn τ ω a)=T (vectorIn τ ω a)) : S=T := by
  apply ContinuousLinearMap.ext
  intro x
  let P := (boundedSubspace τ ω).orthogonalProjectionOnto
  have hc : IsClosed {y : Space ω τ.GNS | S (P y)=T (P y)} :=
    isClosed_eq (S.continuous.comp P.continuous) (T.continuous.comp P.continuous)
  have hm : (LinearMap.range (vector τ ω) : Set (Space ω τ.GNS))⊆
      {y | S (P y)=T (P y)} := by
    rintro _ ⟨a,rfl⟩
    have hp : P (vector τ ω a)=vectorIn τ ω a :=
      (boundedSubspace τ ω).orthogonalProjectionOnto_mem_subspace_eq_self (vectorIn τ ω a)
    simpa only [Set.mem_ofPred_eq,hp] using h a
  have hx := closure_minimal hm hc x.property
  change S (P (x:Space ω τ.GNS))=T (P (x:Space ω τ.GNS)) at hx
  simpa only [P,Submodule.orthogonalProjectionOnto_mem_subspace_eq_self] using hx

variable (hτ : ∀ a b : A, τ (a*b)=τ (b*a))

lemma left_right (a b : ℕ →ᵇ A) :
    leftRestricted τ ω a*rightRestricted τ ω hτ b=
      rightRestricted τ ω hτ b*leftRestricted τ ω a := by
  apply operator_ext τ ω
  intro c
  simp only [mul_apply_eq_comp,leftRestricted_vector,rightRestricted_vector,mul_assoc]

lemma right_mem_commutant (a : ℕ →ᵇ A) :
    rightRestricted τ ω hτ a∈Set.centralizer (Set.range (leftRestricted τ ω)) := by
  rintro _ ⟨b,rfl⟩
  exact left_right τ ω hτ b a

include hτ in
lemma bicommutant_eq_of_vacuum (S T : boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω)
    (hS : S∈Set.centralizer (Set.centralizer (Set.range (leftRestricted τ ω))))
    (hT : T∈Set.centralizer (Set.centralizer (Set.range (leftRestricted τ ω))))
    (h : S (sequenceVacuum τ ω)=T (sequenceVacuum τ ω)) : S=T := by
  apply operator_ext τ ω
  intro a
  have hs := congrArg (fun R : boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω =>
    R (sequenceVacuum τ ω)) (hS _ (right_mem_commutant τ ω hτ a))
  have ht := congrArg (fun R : boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω =>
    R (sequenceVacuum τ ω)) (hT _ (right_mem_commutant τ ω hτ a))
  simp only [mul_apply_eq_comp,rightRestricted_vacuum] at hs ht
  rw [h] at hs
  exact hs.symm.trans ht

end Kadison.TracialSequence

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_TracialSequenceTrace
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology InnerProductSpace BoundedContinuousFunction ComplexOrder

open Filter UniformSpace Completion

namespace Kadison

namespace TracialSequence

open TracialGNS HilbertSequence

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ)

def sequenceTrace : (boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω) →ₚ[ℂ] ℂ :=
  VectorFunctional.functional (sequenceVacuum τ ω)

lemma tendsto_trace (a : ℕ →ᵇ A) : Tendsto (fun i => τ (a i)) (ω : Filter ℕ)
    (𝓝 (sequenceTrace τ ω (leftRestricted τ ω a))) := by
  change Tendsto _ _ (𝓝 (inner ℂ (sequenceVacuum τ ω) (leftRestricted τ ω a (sequenceVacuum τ ω))))
  rw [leftRestricted_vacuum]
  change Tendsto _ _ (𝓝 (inner ℂ (vector τ ω 1) (vector τ ω a)))
  change Tendsto _ _ (𝓝 (inner ℂ (vectorPre τ ω 1 : Space ω τ.GNS) (vectorPre τ ω a : Space ω τ.GNS)))
  rw [Completion.inner_coe]
  simpa only [vectorPre_seq,BoundedContinuousFunction.coe_one,Pi.one_apply,inner_algebraVector,star_one,one_mul] using
    tendsto_inner ω τ.GNS (vectorPre τ ω 1) (vectorPre τ ω a)

lemma trace_one : sequenceTrace τ ω 1=τ 1 := by
  have h := tendsto_trace τ ω (1 : ℕ →ᵇ A)
  simp only [map_one] at h
  exact tendsto_nhds_unique h tendsto_const_nhds

end TracialSequence

end Kadison

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_RelativeSequenceRange
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped ComplexOrder Topology BoundedContinuousFunction

open Filter

namespace Kadison.TracialSequence

open HilbertSequence

variable {A B : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B]

variable (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ) (j : B →⋆ₐ[ℂ] A)

lemma relative_vector_unitball_isClosed (hω : (ω : Filter ℕ)≤atTop) :
    IsClosed {x : boundedSubspace τ ω | ∃ a : ℕ →ᵇ B, ‖a‖≤1 ∧
      vectorIn τ ω (mapSequence j a)=x} := by
  have hc := (bounded_image_isClosed ω (relativeVectorCLM τ j) hω {b : B | ‖b‖≤1} 1
    (fun _ h => h)).preimage (continuous_subtype_val (p := fun x => x∈boundedSubspace τ ω))
  convert hc using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  constructor
  · rintro ⟨a,ha,hax⟩
    refine ⟨a,fun i => (a.norm_coe_le_norm i).trans ha,?_⟩
    exact congrArg Subtype.val hax
  · rintro ⟨a,ha,hax⟩
    refine ⟨a,(BoundedContinuousFunction.norm_le (by norm_num : (0:ℝ)≤1)).mpr ha,?_⟩
    exact Subtype.ext hax

lemma relative_bicommutant_natural {T : boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω}
    (hT : T∈Set.centralizer (Set.centralizer (Set.range ((leftRestricted τ ω).comp (mapSequence j))))) :
    T∈Set.centralizer (Set.centralizer (Set.range (leftRestricted τ ω))) := by
  intro c hc
  apply hT c
  rintro _ ⟨a,rfl⟩
  exact hc _ ⟨mapSequence j a,rfl⟩

variable (hτ : ∀ a b : A,τ (a*b)=τ (b*a))

include hτ in
lemma relative_bicommutant_contraction (hω : (ω : Filter ℕ)≤atTop)
    {T : boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω}
    (hT : T∈Set.centralizer (Set.centralizer (Set.range ((leftRestricted τ ω).comp (mapSequence j)))))
    (hsT : IsSelfAdjoint T) (hnT : ‖T‖≤1) :
    ∃ a : ℕ →ᵇ B, ‖a‖≤1 ∧ leftRestricted τ ω (mapSequence j a)=T := by
  let φ := (leftRestricted τ ω).comp (mapSequence j)
  have hx : T (sequenceVacuum τ ω)∈closure
      {x : boundedSubspace τ ω | ∃ a : ℕ →ᵇ B, ‖a‖≤1 ∧ vectorIn τ ω (mapSequence j a)=x} := by
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨a,_,hna,ha⟩ := Kaplansky.range_selfAdjoint_contraction_finite_approx
      Unit φ hT hsT hnT (fun _ => sequenceVacuum τ ω) ε hε
    refine ⟨vectorIn τ ω (mapSequence j a),⟨a,hna,rfl⟩,?_⟩
    simpa only [dist_eq_norm,norm_sub_rev,φ,StarAlgHom.comp_apply,leftRestricted_vacuum] using ha ()
  rw [(relative_vector_unitball_isClosed τ ω j hω).closure_eq] at hx
  obtain ⟨a,hna,ha⟩ := hx
  refine ⟨a,hna,bicommutant_eq_of_vacuum τ ω hτ _ _ ?_
    (relative_bicommutant_natural τ ω j hT) ?_⟩
  · exact Set.subset_centralizer_centralizer (Set.mem_range_self (mapSequence j a))
  · simpa only [leftRestricted_vacuum] using ha

end Kadison.TracialSequence

end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_TracialDoubleCompression
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped InnerProductSpace ComplexOrder BoundedContinuousFunction

open Filter UniformSpace ContinuousLinearMap

namespace Kadison.TracialSequence

open TracialGNS FreeWordTensor FreeBlocks

lemma trace_constant {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ) (a : A) :
    sequenceTrace τ ω (leftRestricted τ ω (constantSequence a))=τ a := by
  exact (tendsto_nhds_unique (tendsto_trace τ ω (constantSequence a)) tendsto_const_nhds)

lemma constant_trace {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ)
  (M : VonNeumannAlgebra (boundedSubspace τ ω))
  (hconst : ∀ a : A,leftRestricted τ ω (constantSequence a)∈M) (a : A) :
    τ a=VectorGNS.subalgebraTrace M (sequenceVacuum τ ω) (constantHom τ ω M hconst a) :=
  (trace_constant τ ω a).symm

end Kadison.TracialSequence

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_UnitarySequence
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped ComplexOrder Topology BoundedContinuousFunction

open Filter

namespace Kadison.TracialSequence

open FinitePatching FinitePatching.Words

variable {A : Type} [CStarAlgebra A]

def sequenceUnitary {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ) (u : ℕ → unitary A) :
    unitary (boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω) :=
  ⟨leftRestricted τ ω (boundedUnitary u),Unitary.map_mem (leftRestricted τ ω) (boundedUnitary u).property⟩

end Kadison.TracialSequence

end

end OAI
end


