-- Prove2me | Definitions.Def_OAIQ039C056
-- name    : OAIQ039C056
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T06:31:43.567772+00:00
-- url     : https://prove2.me/theorems/6b560966-f125-4872-8de9-3340af71bcd4
-- title:
--   Definitions bundle OAIQ039C056 of the split of OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 32 declarations of OpenAI's Lean: 17 definitions and 15 theorems. The definitions and types are `OAI.Kadison.FreeBlocks.endpointCoordinate`, `OAI.Kadison.FreeBlocks.factorFull`, `OAI.Kadison.FreeBlocks.factorZero`, `OAI.Kadison.FreeBlocks.levelWord`, `OAI.Kadison.FreeBlocks.mapBlockD`, `OAI.Kadison.FreeBlocks.originalEmbedding`, `OAI.Kadison.FreeBlocks.scalarGNSIso`, `OAI.Kadison.FreeBlocks.sourceLeft`, `OAI.Kadison.FreeBlocks.sourceLevel`, `OAI.Kadison.FreeBlocks.sourceLevelEmbedding`, `OAI.Kadison.FreeBlocks.sourceLevelShuffle`, `OAI.Kadison.FreeBlocks.sourceScalar`, `OAI.Kadison.FreeMoments.dihedralBlocks`, `OAI.Kadison.FreeMoments.flattenPairs`, `OAI.Kadison.Kaplansky.fullNet`, `OAI.Kadison.OrbitStateHull.positive`, `OAI.Kadison.TracialSequence.vectorPre`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/Commutator, in whole or in part: `Commutator_FreeActionBlock`, `Commutator_FreeBaseCompression`, `Commutator_FreeCovariance`, `Commutator_FreeLetterIntertwine`, `Commutator_FreeSymmetry13`, `Commutator_FreeSymmetry14`, `Commutator_HankelAlgebra`, `Commutator_KaplanskyFullRange`, `Commutator_KaplanskyStarHomNet`, `Commutator_MatrixApproximation`, `Commutator_MatrixScalarApproximation`, `Commutator_OrbitStateHull`, `Commutator_ProjectionRounding`, `Commutator_TracialSequence`.
--
--   **Imports.** It imports the bundles `OAIQ039C027`, `OAIQ039C043`, `OAIQ039C046`, `OAIQ039C047` and `OAIQ039C050` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ039C059`, `OAIQ039C060`, `OAIQ039C061`, `OAIQ039C062`, `OAIQ039C063`, `OAIQ039C064` and `OAIQ039C065`; the statements `OAI.Kadison.FreeBlocks.normal_free_original_bound`, `OAI.Kadison.FreeBlocks.sourceLevelIsHilbertSum` and `OAI.Kadison.OrbitStateHull.hull_projectionContinuousAtOne`; the proofs of `OAI.Kadison.Decomposable.exists_common_tests`, `OAI.Kadison.FreeBlocks.normal_free_original_bound`, `OAI.Kadison.FreeBlocks.sourceLevelIsHilbertSum`, `OAI.Kadison.MatrixTower.scalar_of_commutes`, `OAI.Kadison.OrbitStateHull.hull_norm_separable`, `OAI.Kadison.OrbitStateHull.hull_projectionContinuousAtOne` and `OAI.Kadison.SeparableTest.seminorm_bound`.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/Commutator at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ039C027
import Definitions.Def_OAIQ039C043
import Definitions.Def_OAIQ039C046
import Definitions.Def_OAIQ039C047
import Definitions.Def_OAIQ039C050

section
-- module Solutions.OAIQ039_CM.Commutator_FreeActionBlock
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
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

namespace Kadison.FreeBlocks

open FreeWordTensor FreeMoments FreeWordAction

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (t : FaithfulState A) {ι : Type*} (S : ι → StarSubalgebra ℂ A) (i j : ι)

def mapBlockD (T : letterSpace t S i → letterSpace t S i) :
    ∀ n, BlockParams t S i j n → BlockParams t S i j n
  | 0,x => x
  | n+1,x => ((x.1.1,T x.1.2),mapBlockD T n x.2)

end Kadison.FreeBlocks

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_HankelAlgebra
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
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

@[simp] lemma word_paired_replicate (s d : Letter S τ) (n : ℕ) :
    word (paired s (List.replicate n d))=(d.val*s.val)^n := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate_succ, ih, pow_succ', mul_assoc]

def dihedralBlocks (d : Letter S τ) (v : List (Letter S τ × ℕ)) : List (Letter S τ) :=
  v.flatMap (fun x => x.1 :: List.replicate x.2 d)

end Kadison.FreeMoments

namespace Kadison.FreeMoments

variable {A : Type*} [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]

variable {S : Bool → StarSubalgebra ℂ A} {τ : A →ₗ[ℂ] ℂ}

def flattenPairs (v : List (Letter S τ × Letter S τ)) : List (Letter S τ) :=
  v.flatMap (fun x => [x.1,x.2])

@[simp] lemma flattenPairs_nil : flattenPairs ([] : List (Letter S τ × Letter S τ))=[] := rfl

@[simp] lemma flattenPairs_cons (x : Letter S τ × Letter S τ) (v) :
    flattenPairs (x::v)=x.1::x.2::flattenPairs v := rfl

end Kadison.FreeMoments

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FreeBaseCompression
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

namespace Kadison.FreeBlocks

open FreeWordTensor FreeMoments ContinuousLinearMap

variable {A B : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

variable (τ : B →ₚ[ℂ] ℂ) (t : FaithfulState A) (f : B →⋆ₐ[ℂ] A)
  (htrace : ∀ a,τ a=t.functional (f a))

omit [StarOrderedRing B] in
include htrace in
lemma pullback_vector_trace (a : B) :
    τ a=inner ℂ (TracialGNS.vacuum t.functional)
      ((t.functional.gnsStarAlgHom.comp f) a (TracialGNS.vacuum t.functional)) := by
  change τ a=inner ℂ (TracialGNS.vacuum t.functional)
    (t.functional.gnsStarAlgHom (f a) (TracialGNS.vacuum t.functional))
  rw [TracialGNS.left_vacuum]
  change τ a=inner ℂ (TracialGNS.vacuum t.functional) (TracialGNS.algebraVector t.functional (f a))
  rw [TracialGNS.inner_vacuum_algebraVector]
  exact htrace a

def originalEmbedding : τ.GNS →ₗᵢ[ℂ] t.functional.GNS :=
  VectorGNS.embedding τ (t.functional.gnsStarAlgHom.comp f) (TracialGNS.vacuum t.functional)
    (pullback_vector_trace τ t f htrace)

@[simp] lemma originalEmbedding_coe (a : B) :
    originalEmbedding τ t f htrace (TracialGNS.algebraVector τ a)=
      TracialGNS.algebraVector t.functional (f a) := by
  rw [originalEmbedding,VectorGNS.embedding_coe]
  exact TracialGNS.left_vacuum _ _

end Kadison.FreeBlocks

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FreeSymmetry13
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
open scoped TensorProduct
open UniformSpace
open scoped TensorProduct InnerProductSpace

namespace Kadison.FreeBlocks

open FreeWordTensor UniformSpace

open scoped ComplexOrder InnerProductSpace TensorProduct

variable {A D : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable (t : FaithfulState A) (f : D →⋆ₐ[ℂ] A) (hf : Function.Injective f)

variable {ι : Type*} (S : ι → StarSubalgebra ℂ A) (i : ι) (hS : S i=f.range)

abbrev factorFull : PreHilbert := ⟨(pullbackState t f hf).functional.GNS⟩

abbrev factorZero : PreHilbert := ⟨HilbertCompletion.centered
  (((pullbackState t f hf).functional.toPreGNS 1 : preSpace (pullbackState t f hf)) :
    (pullbackState t f hf).functional.GNS)⟩

def scalarGNSIso (n : ℕ) : scalarLevel t S i n ≃ₗᵢ[ℂ]
    Completion (factorFull t f hf ⊗[ℂ] PreHilbert.power (factorZero t f hf) n) :=
  HilbertCompletion.wordEquiv (aLetters t S i) (dLetters t S i)
    (factorFull t f hf) (factorZero t f hf)
    ((factorGNSIso t f hf S i hS).trans HilbertCompletion.completeEquiv)
    ((letterGNSIso t f hf S i hS).trans HilbertCompletion.completeEquiv) n

end Kadison.FreeBlocks
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FreeSymmetry14
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
open scoped TensorProduct
open UniformSpace
open scoped TensorProduct InnerProductSpace

namespace Kadison.FreeBlocks

open FreeWordTensor UniformSpace PreHilbert

open scoped ComplexOrder InnerProductSpace TensorProduct

variable {A D : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable (t : FaithfulState A) (f : D →⋆ₐ[ℂ] A) (hf : Function.Injective f)

variable {ι : Type*} (S : ι → StarSubalgebra ℂ A) (i j : ι) (hS : S i=f.range)

abbrev sourceScalar (n : ℕ) := PreHilbert.wordSpace
  (factorFull t f hf) (factorZero t f hf) n

abbrev sourceLevel (n : ℕ) := Completion (sourceScalar t f hf n ⊗[ℂ] multiplicityLevel t S j n)

def sourceLevelShuffle (n : ℕ) : Completion (endpointTensor t S i j n) ≃ₗᵢ[ℂ]
    sourceLevel t f hf S j n :=
  (levelShuffle t S n).trans (HilbertCompletion.congr
    (TensorProduct.congrIsometry (scalarGNSIso t f hf S i hS n)
      (.refl ℂ (multiplicityLevel t S j n))))

variable (hfree : FreeMoments.Free S t.functional.toLinearMap) (hij : i≠j)

def sourceLevelEmbedding (n : ℕ) : sourceLevel t f hf S j n →ₗᵢ[ℂ] t.functional.GNS :=
  (levelEmbedding t S hfree hij n).comp
    (sourceLevelShuffle t f hf S i j hS n).symm.toLinearIsometry

end Kadison.FreeBlocks
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FreeCovariance
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
open scoped TensorProduct
open UniformSpace
open scoped TensorProduct InnerProductSpace
open scoped InnerProductSpace ENNReal
open ContinuousLinearMap
open scoped InnerProductSpace ENNReal
open scoped ComplexOrder InnerProductSpace TensorProduct
open UniformSpace ContinuousLinearMap

namespace Kadison.FreeBlocks

open FreeWordTensor UniformSpace PreHilbert

open scoped ComplexOrder InnerProductSpace TensorProduct

variable {A D : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable (t : FaithfulState A) (f : D →⋆ₐ[ℂ] A) (hf : Function.Injective f)

variable {ι : Type*} (S : ι → StarSubalgebra ℂ A) (i j : ι) (hS : S i=f.range)

def levelWord (d : D) (n : ℕ) (x : BlockParams t S i j n) : sourceLevel t f hf S j n :=
  HilbertTensor.pair (E := sourceScalar t f hf n) (J := multiplicityLevel t S j n)
    (by
      exact PreHilbert.word (factorFull t f hf)
        (factorZero t f hf) n
        (TracialGNS.algebraVector (factorTrace t f hf) d)
        (fun k => letterGNSIso t f hf S i hS
          (HilbertCompletion.coeIsometry (dLetters t S i) (paramD t S n x k))))
    (paramJ t S n x : multiplicityLevel t S j n)

def endpointCoordinate (n : ℕ) : endpointTensor t S i j n →ₗ[ℂ] sourceLevel t f hf S j n :=
  (sourceLevelShuffle t f hf S i j hS n).toLinearMap.comp
    (HilbertCompletion.coeIsometry (endpointTensor t S i j n)).toLinearMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

variable (hfree : FreeMoments.Free S t.functional.toLinearMap) (hij : i≠j)

def sourceLeft (a : D) (n : ℕ) : sourceLevel t f hf S j n →L[ℂ] sourceLevel t f hf S j n :=
  HilbertTensor.map
    (HilbertTensor.map ((factorTrace t f hf).gnsStarAlgHom a)
      (1 : power (factorZero t f hf) n →L[ℂ] power (factorZero t f hf) n))
    (1 : multiplicityLevel t S j n →L[ℂ] multiplicityLevel t S j n)

end Kadison.FreeBlocks
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FreeLetterIntertwine
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
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

namespace Kadison.FreeBlocks

open FreeWordTensor FreeMoments FreeWordAction

variable {A D : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable (t : FaithfulState A) (f : D →⋆ₐ[ℂ] A) (hf : Function.Injective f)

variable {ι : Type*} (S : ι → StarSubalgebra ℂ A) (i : ι) (hS : S i=f.range)

variable (ht : ∀ a b : A, t.functional (a*b)=t.functional (b*a))

include ht in
lemma factorTrace_tracial (a b : D) :
    factorTrace t f hf (a*b)=factorTrace t f hf (b*a) := by
  change t.functional (f (a*b))=t.functional (f (b*a))
  simp only [map_mul,ht]

end Kadison.FreeBlocks

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_KaplanskyFullRange
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace Topology

open Filter

namespace Kadison.Kaplansky

open OperatorAmplification CyclicColumns CyclicSpatial

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

attribute [local instance] OAI.Kadison.Kaplansky.instDecidableEqFinOfNatNat_solutions_1
variable (φ : A →⋆ₐ[ℂ] (H →L[ℂ] H))

theorem range_contraction_finite_approx (ι : Type*) [Fintype ι] [DecidableEq ι]
    {T : H →L[ℂ] H} (hT : T∈Set.centralizer (Set.centralizer (Set.range φ)))
    (hnT : ‖T‖≤1) (x : ι → H) (ε : ℝ) (hε : 0<ε) :
    ∃ a : A,‖a‖≤1 ∧ ∀ i,‖φ a (x i)-T (x i)‖<ε := by
  obtain ⟨X,_,hnX,he⟩ := range_selfAdjoint_contraction_finite_approx ι
    (matrixRepresentation (ι:=Fin 2) φ) (offDiagonal_matrixRange_bicommutant φ hT)
    (offDiagonal_selfAdjoint T) (offDiagonal_norm_le hnT)
    (fun i => single (Fin 2) 1 (x i)) ε hε
  refine ⟨X 0 1,CStarMatrix.norm_entry_le_norm.trans hnX,?_⟩
  intro i
  have h := (PiLp.norm_apply_le
    (matrixRepresentation φ X (single (Fin 2) 1 (x i))-offDiagonal T (single (Fin 2) 1 (x i))) 0).trans_lt (he i)
  simpa [represented_matrix_apply,single_apply,apply_ite] using h

variable (T : H →L[ℂ] H)
  (hT : T∈Set.centralizer (Set.centralizer (Set.range φ))) (hnT : ‖T‖≤1)

include hT hnT in
lemma fullNet_exists (j : Finset H × ℕ) : ∃ a : A,
    ‖a‖≤1 ∧ ∀ x∈j.1,‖φ a x-T x‖<(j.2+1:ℝ)⁻¹ := by
  classical
  obtain ⟨a,ha,he⟩ := range_contraction_finite_approx φ j.1 hT hnT
    (fun x => (x:H)) ((j.2+1:ℝ)⁻¹) (by positivity)
  exact ⟨a,ha,fun x hx => he ⟨x,hx⟩⟩

def fullNet (j : Finset H × ℕ) : A := (fullNet_exists φ T hT hnT j).choose

end Kadison.Kaplansky

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_KaplanskyStarHomNet
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology

open Filter

namespace Kadison.Kaplansky

variable {A H : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (φ : A →⋆ₐ[ℂ] (H →L[ℂ] H))

variable (T : H →L[ℂ] H)
  (hT : T∈Set.centralizer (Set.centralizer (Set.range φ)))
  (hsT : IsSelfAdjoint T) (hnT : ‖T‖ ≤ 1)

lemma starHomNet_tendsto (x : H) :
    Tendsto (fun j => φ (starHomNet φ T hT hsT hnT j) x) atTop (𝓝 (T x)) := by
  classical
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨N,hN⟩ := exists_nat_one_div_lt hε
  filter_upwards [eventually_ge_atTop (({x}:Finset H),N)] with j hj
  rw [dist_eq_norm]
  have hxj : x∈j.1 := hj.1 (Finset.mem_singleton_self x)
  apply (starHomNet_spec φ T hT hsT hnT j).2 x hxj |>.trans_le
  have hnj : (N+1:ℝ) ≤ j.2+1 := by exact_mod_cast Nat.succ_le_succ hj.2
  exact (inv_anti₀ (by positivity) hnj).trans (by simpa only [one_div] using hN.le)

end Kadison.Kaplansky

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_TracialSequence
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
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

@[simp] lemma vectorCLM_apply (a : A) : vectorCLM τ a=algebraVector τ a := rfl

def vectorPre (a : ℕ →ᵇ A) : Pre ω τ.GNS :=
  ⟨BoundedContinuousFunction.comp (vectorCLM τ) (vectorCLM τ).lipschitz a⟩

@[simp] lemma vectorPre_seq (a : ℕ →ᵇ A) (i : ℕ) :
    (vectorPre τ ω a).seq i=algebraVector τ (a i) := rfl

end Kadison.TracialSequence

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_ProjectionRounding
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace Topology BigOperators

namespace Kadison.ProjectionSum

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {I : Type*} [Fintype I]

lemma vector_projection_norm_sq (τ : A →ₚ[ℂ] ℂ) {p : A} (hp : IsStarProjection p) :
    ‖TracialGNS.algebraVector τ p‖^2=(τ p).re := by
  rw [norm_sq_eq_re_inner (𝕜:=ℂ),TracialGNS.inner_algebraVector,
    hp.isSelfAdjoint.star_eq,hp.isIdempotentElem.eq]
  rfl

end Kadison.ProjectionSum

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixApproximation
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder BigOperators

namespace Kadison.MatrixApproximation

open TracialGNS ProjectionSum

section Norm

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ)

lemma vector_norm_le (hone : τ 1=1) (a : A) : ‖algebraVector τ a‖≤‖a‖ := by
  rw [algebraVector_apply,←left_vacuum]
  calc
    _≤‖τ.gnsStarAlgHom a‖*‖vacuum τ‖ := ContinuousLinearMap.le_opNorm _ _
    _≤‖a‖ := by rw [vacuum_norm τ hone,mul_one]; exact NonUnitalStarAlgHom.norm_apply_le _ a

lemma step_error {J : Type*} [Fintype J] (p s : J → A) (c : J → ℝ)
    (hp : ∀ j,IsStarProjection (p j)) (hs : ∀ j,IsStarProjection (s j))
    (hsp : ∀ j,s j ≤ p j) {d : ℝ} (hd : 0≤d)
    (ht : ∀ j,(τ (p j-s j)).re≤d^2) :
    ‖algebraVector τ ((∑ j,(c j:ℂ) • p j)-(∑ j,(c j:ℂ) • s j))‖≤(∑ j,‖c j‖)*d := by
  have hn (j : J) : ‖algebraVector τ (p j-s j)‖≤d := by
    have hproj := ((hs j).le_iff_sub (hp j)).mp (hsp j)
    have hsq := vector_projection_norm_sq τ hproj
    have hn0 := norm_nonneg (algebraVector τ (p j-s j))
    nlinarith [ht j]
  rw [←Finset.sum_sub_distrib]
  simp only [←smul_sub,map_sum,map_smul]
  calc
    _≤∑ j,‖(c j:ℂ) • algebraVector τ (p j-s j)‖ := norm_sum_le _ _
    _≤∑ j,‖c j‖*d := Finset.sum_le_sum (fun j _ => by
      rw [norm_smul,Complex.norm_real]
      exact mul_le_mul_of_nonneg_left (hn j) (norm_nonneg _))
    _=(∑ j,‖c j‖)*d := (Finset.sum_mul _ _ _).symm

end Norm

end Kadison.MatrixApproximation

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixScalarApproximation
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

namespace Kadison.MatrixApproximation

open TracialGNS

section Norm

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ)

lemma trace_norm_le_vector (hone : τ 1=1) (a : A) : ‖τ a‖≤‖algebraVector τ a‖ := by
  have hi : inner ℂ (algebraVector τ 1) (algebraVector τ a)=τ a := by
    simp only [inner_algebraVector,star_one,one_mul]
  rw [←hi]
  have h1 : ‖algebraVector τ 1‖=1 := by
    exact vacuum_norm τ hone
  simpa only [h1,one_mul] using norm_inner_le_norm (𝕜:=ℂ) (algebraVector τ 1) (algebraVector τ a)

end Norm

end Kadison.MatrixApproximation

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

def positive (x : H) (f : WeakDual ℂ M) (hf : f∈hull M x) : M →ₚ[ℂ] ℂ where
  toLinearMap := f.toStrongDual.toLinearMap
  monotone' := by
    intro a b hab
    apply sub_nonneg.mp
    change 0≤f.toStrongDual b-f.toStrongDual a
    rw [←map_sub]
    exact hull_nonneg M x hf (sub_nonneg.mpr hab)

end Kadison.OrbitStateHull

end

end
end

end OAI
end


