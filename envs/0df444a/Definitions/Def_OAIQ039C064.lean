-- Prove2me | Definitions.Def_OAIQ039C064
-- name    : OAIQ039C064
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T09:14:36.512508+00:00
-- url     : https://prove2.me/theorems/e1e7cd55-7b70-432d-9492-bb229bb50136
-- title:
--   Definitions bundle OAIQ039C064 of the split of OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 29 declarations of OpenAI's Lean: 12 definitions, 1 inductive type or structure, 1 instance and 15 theorems. The definitions and types are `OAI.Kadison.TracialSequence.FreeCornerPositionData`, `OAI.Kadison.TracialSequence.boundedSubspace`, `OAI.Kadison.TracialSequence.compressed`, `OAI.Kadison.TracialSequence.constantHom`, `OAI.Kadison.TracialSequence.constantIn`, `OAI.Kadison.TracialSequence.leftHom`, `OAI.Kadison.TracialSequence.leftRestricted`, `OAI.Kadison.TracialSequence.rightAction`, `OAI.Kadison.TracialSequence.rightRestricted`, `OAI.Kadison.TracialSequence.sequenceVacuum`, `OAI.Kadison.TracialSequence.vector`, `OAI.Kadison.TracialSequence.vectorIn`, `OAI.Kadison.VectorGNS.GeneratedByStages`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/Commutator, in whole or in part: `Commutator_TracialDoubleCompression`, `Commutator_TracialFreePositionCriterion`, `Commutator_TracialSequence`, `Commutator_TracialSequenceCompression`, `Commutator_TracialSequenceRight`, `Commutator_VectorStageGeneration`.
--
--   **Imports.** It imports the bundles `OAIQ039C052`, `OAIQ039C054`, `OAIQ039C055` and `OAIQ039C056` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ039C067` and `OAIQ039C069`; the statements `OAI.Kadison.TracialSequence.bicommutant_norm_lift`, `OAI.Kadison.TracialSequence.compressed_commutes_of_range`, `OAI.Kadison.TracialSequence.constant_bicommutant_contraction`, `OAI.Kadison.TracialSequence.constant_range_bicommutant_of_closed`, `OAI.Kadison.TracialSequence.constant_range_bicommutant_of_equiv`, `OAI.Kadison.TracialSequence.projection_rep_lift`, `OAI.Kadison.TracialSequence.represented_corner_bound`, `OAI.Kadison.TracialSequence.subalgebra_tracial`, `OAI.Kadison.VectorGNS.factorTrace_generated`, `OAI.Kadison.VectorGNS.free_original_bound`, `OAI.Kadison.VectorGNS.free_original_bound_represented` and `OAI.Kadison.VectorGNS.generatedByStages_of_represented`; the proofs of `OAI.Kadison.TracialSequence.compressed_commutes_of_range`, `OAI.Kadison.TracialSequence.constant_range_bicommutant_of_closed`, `OAI.Kadison.TracialSequence.constant_range_bicommutant_of_equiv`, `OAI.Kadison.TracialSequence.projection_rep_lift`, `OAI.Kadison.TracialSequence.subalgebra_tracial`, `OAI.Kadison.VectorGNS.factorTrace_generated`, `OAI.Kadison.VectorGNS.free_original_bound`, `OAI.Kadison.VectorGNS.free_original_bound_represented`, `OAI.Kadison.VectorGNS.generatedByStages_of_represented` and `OAI.Kadison.uniform_commutator_separable_factor`.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/Commutator at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ039C052
import Definitions.Def_OAIQ039C054
import Definitions.Def_OAIQ039C055
import Definitions.Def_OAIQ039C056

section
-- module Solutions.OAIQ039_CM.Commutator_TracialSequence
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

def vector : (ℕ →ᵇ A) →ₗ[ℂ] Space ω τ.GNS where
  toFun a := (vectorPre τ ω a : Space ω τ.GNS)
  map_add' a b := by
    rw [←Completion.coe_add]
    congr 1
    apply (equiv ω τ.GNS).injective
    apply BoundedContinuousFunction.ext
    intro i
    exact map_add (algebraVector τ) _ _
  map_smul' r a := by
    rw [←Completion.coe_smul]
    congr 1
    apply (equiv ω τ.GNS).injective
    apply BoundedContinuousFunction.ext
    intro i
    exact map_smul (algebraVector τ) _ _

def boundedSubspace : Submodule ℂ (Space ω τ.GNS) := (LinearMap.range (vector τ ω)).topologicalClosure

instance instCompleteSpaceSubtypeSpaceGNSMemSubmoduleComplexBoundedSubspace : CompleteSpace (boundedSubspace τ ω) :=
  (Submodule.isClosed_topologicalClosure _).completeSpace_coe

lemma vector_mem (a : ℕ →ᵇ A) : vector τ ω a∈boundedSubspace τ ω :=
  Submodule.le_topologicalClosure _ (LinearMap.mem_range_self _ a)

def leftHom : (ℕ →ᵇ A) →⋆ₐ[ℂ] (Space ω τ.GNS →L[ℂ] Space ω τ.GNS) :=
  (actionHom ω).comp {
    toFun := leftFamily τ
    map_one' := by apply BoundedContinuousFunction.ext; intro i; exact map_one τ.gnsStarAlgHom
    map_zero' := by apply BoundedContinuousFunction.ext; intro i; exact map_zero τ.gnsStarAlgHom
    map_add' := by intro a b; apply BoundedContinuousFunction.ext; intro i; exact map_add τ.gnsStarAlgHom _ _
    map_mul' := by intro a b; apply BoundedContinuousFunction.ext; intro i; exact map_mul τ.gnsStarAlgHom _ _
    map_star' := by intro a; apply BoundedContinuousFunction.ext; intro i; exact map_star τ.gnsStarAlgHom _
    commutes' := by intro r; apply BoundedContinuousFunction.ext; intro i; exact τ.gnsStarAlgHom.commutes r }

lemma leftHom_vector (a b : ℕ →ᵇ A) : leftHom τ ω a (vector τ ω b)=vector τ ω (a*b) := by
  change act ω (leftFamily τ a) (vectorPre τ ω b : Space ω τ.GNS)=_
  rw [act_coe]
  change (actPreLinear ω (leftFamily τ a) (vectorPre τ ω b) : Space ω τ.GNS)=
    (vectorPre τ ω (a*b) : Space ω τ.GNS)
  congr 1
  apply (equiv ω τ.GNS).injective
  apply BoundedContinuousFunction.ext
  intro i
  change τ.gnsStarAlgHom (a i) (algebraVector τ (b i))=algebraVector τ (a i*b i)
  exact left_coe τ _ _

lemma leftHom_preserves (a : ℕ →ᵇ A) (x : Space ω τ.GNS) (hx : x∈boundedSubspace τ ω) :
    leftHom τ ω a x∈boundedSubspace τ ω := by
  apply (Submodule.topologicalClosure_minimal (LinearMap.range (vector τ ω))
    (t := (boundedSubspace τ ω).comap (leftHom τ ω a).toLinearMap) ?_
    ((Submodule.isClosed_topologicalClosure _).preimage (leftHom τ ω a).continuous)) hx
  rintro _ ⟨b,rfl⟩
  change leftHom τ ω a (vector τ ω b)∈boundedSubspace τ ω
  rw [leftHom_vector]
  exact vector_mem τ ω _

def leftRestricted : (ℕ →ᵇ A) →⋆ₐ[ℂ] (boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω) :=
  ReducingRepresentation.restrict (leftHom τ ω) (boundedSubspace τ ω) (leftHom_preserves τ ω)

@[simp] lemma leftRestricted_apply (a : ℕ →ᵇ A) (x : boundedSubspace τ ω) :
    (leftRestricted τ ω a x:Space ω τ.GNS)=leftHom τ ω a x := rfl

end Kadison.TracialSequence

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_TracialSequenceCompression
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action
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

open TracialGNS HilbertSequence ReducingRepresentation

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ)

lemma vector_const (a : A) : vector τ ω (BoundedContinuousFunction.const ℕ a)=
    constant ω τ.GNS (algebraVector τ a) := by
  rw [constant_apply]
  change (vectorPre τ ω _ : Space ω τ.GNS)=(constantPre ω τ.GNS _ : Space ω τ.GNS)
  congr 1

lemma constant_mem (x : τ.GNS) : constant ω τ.GNS x∈boundedSubspace τ ω := by
  refine (algebraVector_dense τ).induction_on
    (p := fun y => constant ω τ.GNS y∈boundedSubspace τ ω) x ?_ ?_
  · exact (Submodule.isClosed_topologicalClosure _).preimage (constant ω τ.GNS).continuous
  · intro a
    rw [←vector_const]
    exact vector_mem τ ω _

def constantIn : τ.GNS →ₗᵢ[ℂ] boundedSubspace τ ω where
  toFun x := ⟨constant ω τ.GNS x,constant_mem τ ω x⟩
  map_add' := by intro x y; apply Subtype.ext; exact map_add (constant ω τ.GNS) x y
  map_smul' := by intro r x; apply Subtype.ext; exact map_smul (constant ω τ.GNS) r x
  norm_map' := (constant ω τ.GNS).norm_map

@[simp] lemma constantIn_coe (x : τ.GNS) : (constantIn τ ω x:Space ω τ.GNS)=constant ω τ.GNS x := rfl

def compressed (S : τ.GNS →L[ℂ] τ.GNS) : boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω :=
  compression (boundedSubspace τ ω) (act ω (BoundedContinuousFunction.const ℕ S))

end Kadison.TracialSequence

end

end
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

def vectorIn (a : ℕ →ᵇ A) : boundedSubspace τ ω := ⟨vector τ ω a,vector_mem τ ω a⟩

@[simp] lemma vectorIn_coe (a : ℕ →ᵇ A) : (vectorIn τ ω a : Space ω τ.GNS)=vector τ ω a := rfl

lemma leftRestricted_vector (a b : ℕ →ᵇ A) :
    leftRestricted τ ω a (vectorIn τ ω b)=vectorIn τ ω (a*b) := by
  apply Subtype.ext
  exact leftHom_vector τ ω a b

def sequenceVacuum : boundedSubspace τ ω := vectorIn τ ω 1

@[simp] lemma leftRestricted_vacuum (a : ℕ →ᵇ A) :
    leftRestricted τ ω a (sequenceVacuum τ ω)=vectorIn τ ω a := by
  rw [sequenceVacuum,leftRestricted_vector,mul_one]

variable (hτ : ∀ a b : A, τ (a*b)=τ (b*a))

def rightAction (a : ℕ →ᵇ A) : Space ω τ.GNS →L[ℂ] Space ω τ.GNS :=
  act ω (rightFamily τ hτ a)

lemma rightAction_vector (a b : ℕ →ᵇ A) :
    rightAction τ ω hτ a (vector τ ω b)=vector τ ω (b*a) := by
  change act ω (rightFamily τ hτ a) (vectorPre τ ω b : Space ω τ.GNS)=_
  rw [act_coe]
  change (actPreLinear ω (rightFamily τ hτ a) (vectorPre τ ω b) : Space ω τ.GNS)=
    (vectorPre τ ω (b*a) : Space ω τ.GNS)
  congr 1
  apply (equiv ω τ.GNS).injective
  apply BoundedContinuousFunction.ext
  intro i
  change rightMul τ hτ (a i) (algebraVector τ (b i))=algebraVector τ (b i*a i)
  exact rightMul_coe τ hτ (a i) (τ.toPreGNS (b i))

lemma rightAction_preserves (a : ℕ →ᵇ A) (x : Space ω τ.GNS) (hx : x∈boundedSubspace τ ω) :
    rightAction τ ω hτ a x∈boundedSubspace τ ω := by
  apply (Submodule.topologicalClosure_minimal (LinearMap.range (vector τ ω))
    (t := (boundedSubspace τ ω).comap (rightAction τ ω hτ a).toLinearMap) ?_
    ((Submodule.isClosed_topologicalClosure _).preimage (rightAction τ ω hτ a).continuous)) hx
  rintro _ ⟨b,rfl⟩
  change rightAction τ ω hτ a (vector τ ω b)∈boundedSubspace τ ω
  rw [rightAction_vector]
  exact vector_mem τ ω _

def rightRestricted (a : ℕ →ᵇ A) : boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω :=
  (rightAction τ ω hτ a).restrict (rightAction_preserves τ ω hτ a)

lemma rightRestricted_vector (a b : ℕ →ᵇ A) :
    rightRestricted τ ω hτ a (vectorIn τ ω b)=vectorIn τ ω (b*a) := by
  apply Subtype.ext
  exact rightAction_vector τ ω hτ a b

@[simp] lemma rightRestricted_vacuum (a : ℕ →ᵇ A) :
    rightRestricted τ ω hτ a (sequenceVacuum τ ω)=vectorIn τ ω a := by
  rw [sequenceVacuum,rightRestricted_vector,one_mul]

end Kadison.TracialSequence

end

end
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

def constantHom {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ)
  (M : VonNeumannAlgebra (boundedSubspace τ ω))
  (hconst : ∀ a : A,leftRestricted τ ω (constantSequence a)∈M) : A →⋆ₐ[ℂ] M :=
  ((leftRestricted τ ω).comp constantSequence).codRestrict M.toStarSubalgebra hconst

@[simp] lemma constantHom_coe {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ)
  (M : VonNeumannAlgebra (boundedSubspace τ ω))
  (hconst : ∀ a : A,leftRestricted τ ω (constantSequence a)∈M) (a : A) :
    (constantHom τ ω M hconst a : boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω)=
      leftRestricted τ ω (constantSequence a) := rfl

end Kadison.TracialSequence

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_VectorStageGeneration
attribute [-instance] _root_.OAI.Kadison.UnitaryDualAction.action
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

namespace Kadison.VectorGNS

open FreeWordTensor FreeBlocks

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (D : VonNeumannAlgebra H) (ξ : H)
  (I : ℕ → Type*) [∀ n,Fintype (I n)] [∀ n,DecidableEq (I n)]
  (φ : ∀ n,Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] D)

def GeneratedByStages : Prop := ∀ a : D,(subalgebraTrace D ξ).gnsStarAlgHom a∈
  Set.centralizer (Set.centralizer (TracialGNS.stageAlgebra (subalgebraTrace D ξ) I φ : Set _))

end Kadison.VectorGNS

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_TracialFreePositionCriterion
attribute [-instance] _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator

open Filter

namespace Kadison.TracialSequence

open FreeMoments

variable {A K : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

structure FreeCornerPositionData {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (ξ : H)
    (action : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (operatorRange : Set (H →L[ℂ] H)) where
  algebra : VonNeumannAlgebra H
  size : ℕ → ℕ
  stage : ∀ n,Matrix (Fin (size n+1)) (Fin (size n+1)) ℂ →⋆ₐ[ℂ] algebra
  inclusion : ∀ {n m : ℕ}, n ≤ m →
    Matrix (Fin (size n+1)) (Fin (size n+1)) ℂ →⋆ₐ[ℂ]
      Matrix (Fin (size m+1)) (Fin (size m+1)) ℂ
  compatible : ∀ n m (h : n ≤ m) a,stage m (inclusion h a)=stage n a
  unbounded : ∀ n q : ℕ,∃ m, n ≤ m ∧ q ≤ size m+1
  generated : VectorGNS.GeneratedByStages algebra ξ
    (fun n => Fin (size n+1)) stage
  free : Free (GeneratedFreePair.ambient algebra action)
    (VectorFunctional.functional ξ).toLinearMap
  in_range : ∀ d : algebra,(d:H →L[ℂ] H)∈operatorRange
  diffuse : DiffuseProjection.HasNoMinimalProjections algebra

end Kadison.TracialSequence

end

end OAI
end


