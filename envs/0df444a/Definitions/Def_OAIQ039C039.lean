-- Prove2me | Definitions.Def_OAIQ039C039
-- name    : OAIQ039C039
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T06:23:24.116553+00:00
-- url     : https://prove2.me/theorems/a48c0154-ecf5-42e7-9c70-01abb15b9f91
-- title:
--   Definitions bundle OAIQ039C039 of the split of OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 15 declarations of OpenAI's Lean: 6 definitions and 9 theorems. The definitions and types are `OAI.Kadison.MatrixGNS.representation`, `OAI.Kadison.NormalOperatorHom.BoundedNormal`, `OAI.Kadison.NormalPredual.BoundedWOTContinuous`, `OAI.Kadison.OrbitStateHull.hull`, `OAI.Kadison.ProjectionJoin.join`, `OAI.Kadison.VectorGNS.equivalence`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/Commutator, in whole or in part: `Commutator_GNSVectorUnitary`, `Commutator_MatrixStageExtension`, `Commutator_MatrixVectorTrace`, `Commutator_NormalBiprodGNS`, `Commutator_NormalOperatorHom`, `Commutator_NormalPredual`, `Commutator_NormalSubalgebra`, `Commutator_OrbitStateHull`, `Commutator_ProjectionJoin`.
--
--   **Imports.** It imports the bundles `OAIQ039C022`, `OAIQ039C024`, `OAIQ039C025`, `OAIQ039C026`, `OAIQ039C028` and `OAIQ039C029` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ039C049`, `OAIQ039C050`, `OAIQ039C051` and `OAIQ039C052`; the statements `OAI.Kadison.OrbitStateHull.exists_tracial_hull_of_norm_separable` and `OAI.Kadison.OrbitStateHull.hull_norm_separable`; the proof of `OAI.Kadison.OrbitStateHull.exists_tracial_hull_of_norm_separable`.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/Commutator at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ039C022
import Definitions.Def_OAIQ039C024
import Definitions.Def_OAIQ039C025
import Definitions.Def_OAIQ039C026
import Definitions.Def_OAIQ039C028
import Definitions.Def_OAIQ039C029

section
-- module Solutions.OAIQ039_CM.Commutator_GNSVectorUnitary
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace ComplexOrder

namespace Kadison.VectorGNS

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (τ : A →ₚ[ℂ] ℂ) (φ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
  (hτ : ∀ a,τ a=inner ℂ ξ (φ a ξ)) (hcyc : DenseRange (fun a : A => φ a ξ))

include hcyc in
lemma embedding_surjective : Function.Surjective (embedding τ φ ξ hτ) := by
  have hd : DenseRange (embedding τ φ ξ hτ) := by
    apply hcyc.mono
    rintro y ⟨a,rfl⟩
    exact ⟨TracialGNS.algebraVector τ a,embedding_coe τ φ ξ hτ a⟩
  intro y
  exact (embedding τ φ ξ hτ).isometry.isClosedEmbedding.isClosed_range.closure_subset (hd y)

def equivalence : τ.GNS ≃ₗᵢ[ℂ] H :=
  LinearIsometryEquiv.ofSurjective (embedding τ φ ξ hτ) (embedding_surjective τ φ ξ hτ hcyc)

end Kadison.VectorGNS

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_NormalSubalgebra
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder Topology InnerProductSpace

namespace Kadison.NormalSubalgebra

open TracialGNS

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M N : VonNeumannAlgebra H) (hNM : N≤M)

variable (τ : M →ₚ[ℂ] ℂ)

lemma normal (hτ : NormalGNS.BoundedWOTContinuous M τ) :
    NormalGNS.BoundedWOTContinuous N (trace M N hNM τ) := by
  intro C
  let f : {T : H →WOT[ℂ] H // T.toCLM∈N ∧ ‖T.toCLM‖≤C} →
      {T : H →WOT[ℂ] H // T.toCLM∈M ∧ ‖T.toCLM‖≤C} :=
    fun a => ⟨a.val,hNM a.property.1,a.property.2⟩
  have hf : Continuous f := continuous_subtype_val.subtype_mk _
  exact (hτ C).comp hf

lemma tracial (hτ : ∀ a b : M,τ (a*b)=τ (b*a)) (a b : N) :
    trace M N hNM τ (a*b)=trace M N hNM τ (b*a) := by
  simpa only [trace_apply,map_mul] using hτ (inclusion M N hNM a) (inclusion M N hNM b)

lemma one (hone : τ 1=1) : trace M N hNM τ 1=1 := by rw [trace_apply,map_one,hone]

lemma faithful (hfaith : ∀ a : M,τ (star a*a)=0 → a=0) (a : N)
    (ha : trace M N hNM τ (star a*a)=0) : a=0 := by
  have he := hfaith (inclusion M N hNM a) (by simpa only [trace_apply,map_mul,map_star] using ha)
  apply Subtype.ext
  exact congrArg (fun x : M => (x : H →L[ℂ] H)) he

lemma vector_norm (a : N) :
    ‖algebraVector (trace M N hNM τ) a‖=‖algebraVector τ (inclusion M N hNM a)‖ := by
  have hi : inner ℂ (algebraVector (trace M N hNM τ) a) (algebraVector (trace M N hNM τ) a)=
      inner ℂ (algebraVector τ (inclusion M N hNM a)) (algebraVector τ (inclusion M N hNM a)) := by
    exact (inner_algebraVector (trace M N hNM τ) a a).trans
      (inner_algebraVector τ (inclusion M N hNM a) (inclusion M N hNM a)).symm
  have hr := congrArg (RCLike.re : ℂ → ℝ) hi
  have hs := (norm_sq_eq_re_inner (𝕜:=ℂ) (algebraVector (trace M N hNM τ) a)).trans
    (hr.trans (norm_sq_eq_re_inner (𝕜:=ℂ) (algebraVector τ (inclusion M N hNM a))).symm)
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hs

end Kadison.NormalSubalgebra

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixStageExtension
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder BigOperators InnerProductSpace

namespace Kadison.MatrixStageExtension

open TracialGNS MatrixExpectation

lemma expectation_map {A B I : Type*} [CStarAlgebra A] [CStarAlgebra B]
    [Fintype I] [DecidableEq I] (f : A →⋆ₐ[ℂ] B)
    (φ : Matrix I I ℂ →⋆ₐ[ℂ] A) (a : A) :
    f (expectation φ a)=expectation (f.comp φ) (f a) := by
  rw [expectation_apply,expectation_apply]
  simp only [map_smul,map_sum,map_mul,StarAlgHom.comp_apply]

end Kadison.MatrixStageExtension

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixVectorTrace
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace ComplexOrder

open ContinuousLinearMap

namespace Kadison.MatrixGNS

variable {A ι : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [Fintype ι]

attribute [local instance] OAI.Kadison.MatrixGNS.matrixVectorTraceDecidableEq
variable (τ : A →ₚ[ℂ] ℂ)

def representation : CStarMatrix ι ι A →⋆ₐ[ℂ] (ArraySpace (ι:=ι) τ →L[ℂ] ArraySpace (ι:=ι) τ) :=
  CyclicColumns.matrixRepresentation ((OperatorAmplification.diagonal ι).comp τ.gnsStarAlgHom)

@[simp] lemma representation_apply (X : CStarMatrix ι ι A) (v : ArraySpace (ι:=ι) τ) (i j : ι) :
    representation τ X v i j=∑ k, τ.gnsStarAlgHom (X i k) (v k j) := by
  simp [representation,CyclicColumns.matrixRepresentation,CyclicColumns.matrixAction_apply]

end Kadison.MatrixGNS

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_NormalOperatorHom
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped Topology

open Filter ContinuousLinearMapWOT

namespace Kadison.NormalOperatorHom

variable {H G : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

variable (M : VonNeumannAlgebra H) (φ : M →⋆ₐ[ℂ] (G →L[ℂ] G))

def BoundedNormal : Prop :=
  ∀ (C : ℝ) (x y : G), Continuous
    (fun a : {T : H →WOT[ℂ] H // T.toCLM∈M ∧ ‖T.toCLM‖≤C} =>
      inner ℂ x (φ ⟨a.val.toCLM,a.property.1⟩ y))

end Kadison.NormalOperatorHom

end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_NormalBiprodGNS
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

open scoped Topology ComplexOrder NNReal

open Filter ContinuousLinearMapWOT

namespace Kadison.NormalOperatorHom

variable {H G : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

variable (M : VonNeumannAlgebra H)

lemma subtype_normal : BoundedNormal M M.toStarSubalgebra.subtype := by
  intro C x y
  exact ContinuousLinearMapWOT.continuous_inner_apply continuous_subtype_val y x

end Kadison.NormalOperatorHom

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_NormalPredual
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open Filter ContinuousLinearMapWOT

open scoped Topology InnerProductSpace

namespace Kadison.NormalPredual

open FiniteStrongTest

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def BoundedWOTContinuous (M : VonNeumannAlgebra H) (f : StrongDual ℂ M) : Prop :=
  ∀ C : ℝ,Continuous (fun a : {T : H →WOT[ℂ] H // T.toCLM∈M ∧ ‖T.toCLM‖≤C} =>
    f ⟨a.val.toCLM,a.property.1⟩)

end Kadison.NormalPredual

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_ProjectionJoin
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace Kadison.ProjectionJoin

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def join (p q : H →L[ℂ] H) : H →L[ℂ] H := p+remainder p q

open PartialIsometryOrder PartialIsometryOrder.DyadicPartition

end Kadison.ProjectionJoin

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_OrbitStateHull
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open Filter

open scoped ComplexOrder InnerProductSpace Topology

namespace Kadison.OrbitStateHull

open PartialIsometryOrder PartialIsometryOrder.DyadicPartition

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H)

def hull (x : H) : Set (WeakDual ℂ M) := WeakDualHull.hull (orbit M x)

end Kadison.OrbitStateHull

end

end
end

end OAI
end


