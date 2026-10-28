-- Prove2me | Definitions.Def_OAIQ039C025
-- name    : OAIQ039C025
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T06:16:38.464477+00:00
-- url     : https://prove2.me/theorems/718a3430-fa50-468f-978f-733c2b18ac93
-- title:
--   Definitions bundle OAIQ039C025 of the split of OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 86 declarations of OpenAI's Lean: 41 definitions, 1 instance and 44 theorems. The definitions and types are `OAI.Kadison.FinitePatching.ConjugatedWords.transition`, `OAI.Kadison.FinitePatching.Words.Letter`, `OAI.Kadison.FinitePatching.Words.NonzeroSlot`, `OAI.Kadison.FinitePatching.Words.Valid`, `OAI.Kadison.FinitePatching.Words.slotCost`, `OAI.Kadison.FiniteStrongTest.evaluation`, `OAI.Kadison.FiniteStrongTest.testMap`, `OAI.Kadison.FiniteTest.expectation`, `OAI.Kadison.FiniteTest.flipEquiv`, `OAI.Kadison.FiniteTest.label`, `OAI.Kadison.FiniteTest.matrixCoefficient`, `OAI.Kadison.FiniteTrace.restrict`, `OAI.Kadison.FreeBlocks.BlockParams`, `OAI.Kadison.FreeBlocks.Letters`, `OAI.Kadison.FreeBlocks.blockPure`, `OAI.Kadison.FreeBlocks.blockRead`, `OAI.Kadison.FreeBlocks.blockReadPre`, `OAI.Kadison.FreeBlocks.blockTensor`, `OAI.Kadison.FreeBlocks.blockValue`, `OAI.Kadison.FreeBlocks.blockVector`, `OAI.Kadison.FreeBlocks.endpointRead`, `OAI.Kadison.FreeBlocks.endpointTensor`, `OAI.Kadison.FreeBlocks.factorSpace`, `OAI.Kadison.FreeBlocks.factorValue`, `OAI.Kadison.FreeBlocks.paramEnd`, `OAI.Kadison.FreeBlocks.paramLetters`, `OAI.Kadison.FreeBlocks.spaceTensor`, `OAI.Kadison.FreeCreation.CanPrepend`, `OAI.Kadison.FreeCreation.Letter`, `OAI.Kadison.FreeCreation.Starts`, `OAI.Kadison.FreeCreation.headSpace`, `OAI.Kadison.FreeCreation.headSpan`, `OAI.Kadison.FreeCreation.tailSpace`, `OAI.Kadison.FreeCreation.tailSpan`, `OAI.Kadison.FreeCreation.wordVector`, `OAI.Kadison.FreeWordAction.letter`, `OAI.Kadison.FreeWordTensor.boundedLetter`, `OAI.Kadison.FreeWordTensor.paramsOfLetters`, `OAI.Kadison.FreeWordTensor.readIsometry`, `OAI.Kadison.FreeWordTensor.wordEmbedding` and 1 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/Commutator, in whole or in part: `Commutator_ConjugatedWordAlgebra`, `Commutator_FiniteFactorComparison`, `Commutator_FiniteStrongTest`, `Commutator_FiniteTestPatching`, `Commutator_FiniteTrace`, `Commutator_FreeAction`, `Commutator_FreeBlockTensor`, `Commutator_FreeBlockTensor2`, `Commutator_FreeBlockWords`, `Commutator_FreeBlockWords2`, `Commutator_FreeCreation`, `Commutator_FreeMoments`, `Commutator_FreeWordDecomposition`, `Commutator_FreeWordTensor`, `Commutator_HankelAlgebra`, `Commutator_PartialIsometryOrder`, `Commutator_PartialUnitaryAlgebra`, `Commutator_PartialUnitaryWords`, `Commutator_PartialWordContinuity`.
--
--   **Imports.** It imports the bundles `OAIQ039C001`, `OAIQ039C002`, `OAIQ039C004`, `OAIQ039C006`, `OAIQ039C008`, `OAIQ039C009` and `OAIQ039C010` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ039C035`, `OAIQ039C036`, `OAIQ039C037`, `OAIQ039C039` and `OAIQ039C040`.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/Commutator at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ039C001
import Definitions.Def_OAIQ039C002
import Definitions.Def_OAIQ039C004
import Definitions.Def_OAIQ039C006
import Definitions.Def_OAIQ039C008
import Definitions.Def_OAIQ039C009
import Definitions.Def_OAIQ039C010

section
-- module Solutions.OAIQ039_CM.Commutator_PartialUnitaryAlgebra
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder

namespace Kadison.FinitePatching

variable (A : Type*) [CStarAlgebra A]

namespace PartialUnitary

variable {A}

lemma norm_le_one (v : PartialUnitary A) : ‖v.val‖ ≤ 1 := by
  have h := v.projection.norm_le v.support
  rw [←v.star_mul,CStarRing.norm_star_mul_self] at h
  nlinarith [_root_.norm_nonneg v.val]

end PartialUnitary

end Kadison.FinitePatching

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_PartialUnitaryWords
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder BigOperators

namespace Kadison.FinitePatching

namespace Words

variable {A J K : Type*} [CStarAlgebra A]

abbrev Letter (J K : Type*) := J × Slot K

def NonzeroSlot (s : Slot K) : Prop := ∃ k,s=some (some k)

def Valid (l : List (Letter J K)) : Prop :=
  ∀ s i t,l=s++i::t → t≠[] → NonzeroSlot i.2

end Words

end Kadison.FinitePatching

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_ConjugatedWordAlgebra
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder

namespace Kadison.FinitePatching.ConjugatedWords

open Words

variable {B J : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

def transition (c d : Bool) : Slot Bool := if c=d then none else some (some c)

end Kadison.FinitePatching.ConjugatedWords

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_PartialIsometryOrder
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.PartialIsometryOrder.instCompleteSpaceSubtypeMemSubmoduleComplexFamilySpace _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace Topology

open Filter

namespace Kadison.PartialIsometryOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace Link

variable {M : VonNeumannAlgebra H} {e f : H →L[ℂ] H}

lemma norm_le_one (v : Link M e f) : ‖v.val‖≤1 := by
  have h := (v.initial_projection).norm_le v.initial
  change ‖star v.val*v.val‖≤1 at h
  rw [CStarRing.norm_star_mul_self] at h
  nlinarith [norm_nonneg v.val]

instance instPartialOrder : PartialOrder (Link M e f) where
  le v w := v.initial≤w.initial ∧ w.val*v.initial=v.val
  le_refl v := ⟨le_rfl,v.mul_initial⟩
  le_trans v w u hvw hwu := by
    refine ⟨hvw.1.trans hwu.1,?_⟩
    have h := (v.initial_projection.le_iff_mul_eq_right w.initial_projection).mp hvw.1
    calc
      _=u.val*(w.initial*v.initial) := by rw [h]
      _=v.val := by rw [←mul_assoc,hwu.2,hvw.2]
  le_antisymm v w hvw hwv := by
    apply ext
    have h := le_antisymm hvw.1 hwv.1
    calc
      v.val=w.val*v.initial := hvw.2.symm
      _=w.val := by rw [h,w.mul_initial]

lemma le_def (v w : Link M e f) : v≤w ↔ v.initial≤w.initial ∧ w.val*v.initial=v.val := Iff.rfl

end Link

end Kadison.PartialIsometryOrder

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FiniteFactorComparison
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace Topology

namespace Kadison.PartialIsometryOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma faithful_projection (M : VonNeumannAlgebra H) (τ : M →ₚ[ℂ] ℂ)
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
    {p : H →L[ℂ] H} (hpM : p∈M) (hp : IsStarProjection p)
    (hz : τ ⟨p,hpM⟩=0) : p=0 := by
  have hsq : star (⟨p,hpM⟩ : M)*⟨p,hpM⟩=⟨p,hpM⟩ := by
    apply Subtype.ext
    change star p*p=p
    rw [hp.isSelfAdjoint.star_eq,hp.isIdempotentElem.eq]
  have hzero := hfaith ⟨p,hpM⟩ (by rw [hsq]; exact hz)
  exact congrArg Subtype.val hzero

end Kadison.PartialIsometryOrder

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FiniteStrongTest
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

open scoped Topology

namespace Kadison.FiniteStrongTest

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def evaluation (M : VonNeumannAlgebra H) (x : H) : M →L[ℂ] H :=
  LinearMap.mkContinuous
    { toFun := fun a => (a : H →L[ℂ] H) x
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
    ‖x‖ (fun a => by
      change ‖(a : H →L[ℂ] H) x‖≤‖x‖*‖(a:H →L[ℂ] H)‖
      rw [mul_comm]
      exact (a : H →L[ℂ] H).le_opNorm x)

def testMap (M : VonNeumannAlgebra H) (v : ℕ → H) (N : ℕ) : M →L[ℂ] PiLp 2 (fun _ : Fin N => H) :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin N => H)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun j : Fin N => evaluation M (v j)))

@[simp] lemma testMap_apply (M : VonNeumannAlgebra H) (v : ℕ → H) (N : ℕ) (a : M)
    (j : Fin N) : testMap M v N a j=(a : H →L[ℂ] H) (v j) := rfl

end Kadison.FiniteStrongTest

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FiniteTestPatching
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass
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

section Signs

variable {I : Type*} [DecidableEq I]

lemma flip_involutive (i : I) : Function.Involutive (flip i) := by
  intro σ
  funext j
  by_cases h : j = i
  · subst j; simp [flip]
  · simp [flip, h]

def flipEquiv (i : I) : (I → Bool) ≃ (I → Bool) := (flip_involutive i).toPerm

end Signs

section UpperTriangle

variable {I : Type*} [Fintype I] [LinearOrder I]

def label : Option (Upper (I := I)) → Finset I
  | none => ∅
  | some p => {p.val.1, p.val.2}

end UpperTriangle

section MatrixSigns

variable {I H : Type*} [Fintype I] [LinearOrder I]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def matrixCoefficient (x : I → I → H) : Option (Upper (I := I)) → H
  | none => ∑ i, x i i
  | some p => x p.val.1 p.val.2 + x p.val.2 p.val.1

end MatrixSigns

section MatrixAlgebra

open Matrix

variable {A I : Type*} [CStarAlgebra A] [Fintype I] [DecidableEq I]

variable (φ : Matrix I I ℂ →⋆ₐ[ℂ] A)

@[simp] lemma unit_star (i j : I) : star (unit φ i j) = unit φ j i := by
  simp [unit, ← map_star, Matrix.star_eq_conjTranspose]

@[simp] lemma unit_mul (i j k l : I) :
    unit φ i j * unit φ k l = if j = k then unit φ i l else 0 := by
  by_cases h : j = k
  · subst k; simp [unit, ← map_mul]
  · simp [unit, ← map_mul, h]

@[simp] lemma unit_sum : ∑ i, unit φ i i = 1 := by
  simp only [unit, ← map_sum, Matrix.sum_single_one, map_one]

variable (τ : A →ₗ[ℝ] ℝ) (hτ : ∀ a b : A, τ (a*b) = τ (b*a))

def expectation (x : A) : A :=
  (Fintype.card I : ℝ)⁻¹ • ∑ i, ∑ j, unit φ i j * x * unit φ j i

end MatrixAlgebra

section FiniteFamily

open Matrix

variable {A I J H : Type*} [CStarAlgebra A] [Fintype I] [LinearOrder I]
  [Fintype J] [NormedAddCommGroup H] [InnerProductSpace ℝ H]

variable (φ : Matrix I I ℂ →⋆ₐ[ℂ] A) (τ : A →ₗ[ℝ] ℝ)
  (hτ : ∀ a b : A, τ (a*b) = τ (b*a))
  (v : A →ₗ[ℝ] H) (hv : ∀ a, ‖v a‖^2 = traceSquare τ a)

@[simp] lemma familyTrace_apply (x : J → A) : familyTrace τ x = ∑ j, τ (x j) := by
  simp [familyTrace]

@[simp] lemma unit_family (i j : I) (t : J) : unit (familyHom (J := J) φ) i j t = unit φ i j := rfl

end FiniteFamily

section ActualGNS

open scoped ComplexOrder

open UniformSpace

variable {A I J : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [Fintype I] [LinearOrder I] [Fintype J]

variable (τ : A →ₚ[ℂ] ℂ)

omit [StarOrderedRing A] in
@[simp] lemma realTrace_apply (a : A) : realTrace τ a = (τ a).re := rfl

end ActualGNS

end Kadison.FiniteTest

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FiniteTrace
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

namespace Kadison.FiniteTrace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (τ : (H →L[ℂ] H) →ₚ[ℂ] ℂ)

def restrict : M →ₚ[ℂ] ℂ where
  toLinearMap := τ.toLinearMap.comp M.toStarSubalgebra.subtype.toLinearMap
  monotone' := fun _ _ h => τ.monotone h

@[simp] lemma restrict_apply (a : M) : restrict M τ a=τ (a : H →L[ℂ] H) := rfl

end Kadison.FiniteTrace

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FreeMoments
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass
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

namespace Kadison.FreeMoments

attribute [local instance] Classical.propDecidable

variable {A : Type*} [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]

variable {ι : Type*} (S : ι → StarSubalgebra ℂ A) (τ : A →ₗ[ℂ] ℂ)

variable {S τ}

variable (hstar : ∀ a : A, τ (star a) = star (τ a))

variable (h1 : τ 1 = 1)

include hstar h1 in
theorem gram_word (hfree : Free S τ) (w z : List (Letter S τ))
    (hw : Reduced w) (hz : Reduced z) :
    τ (star (word w) * word z) = gram w z := by
  classical
  induction w generalizing z with
  | nil =>
    cases z with
    | nil => simpa [gram] using h1
    | cons b z => simpa [gram] using hfree (b :: z) hz (by simp)
  | cons a w ih =>
    cases z with
    | nil =>
      rw [word_nil, mul_one, hstar, hfree (a :: w) hw (by simp)]
      simp only [star_zero, gram]
    | cons b z =>
      by_cases hab : a.color = b.color
      · rw [gram, ite_eq_left hab, gram_same_head hstar h1 hfree hw hz hab,
          ih z hw.tail hz.tail]
      · rw [gram, ite_eq_right hab, gram_different_head hstar hfree hw hz hab]

lemma gram_zero_of_colors_ne (w z : List (Letter S τ))
    (h : w.map Letter.color ≠ z.map Letter.color) : gram w z = 0 := by
  induction w generalizing z with
  | nil => cases z <;> simp_all [gram]
  | cons a w ih =>
    cases z with
    | nil => rfl
    | cons b z =>
      by_cases hab : a.color = b.color
      · rw [gram, ite_eq_left hab]
        have ht : w.map Letter.color ≠ z.map Letter.color := by
          intro ht
          exact h (by simp [hab, ht])
        rw [ih z ht, mul_zero]
      · simp only [gram, ite_eq_right hab]

end Kadison.FreeMoments
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FreeWordTensor
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass
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

lemma inner_readPre_pure (is : List ι) (his : is.IsChain (· ≠ ·))
    (x y : Params t S is) :
    inner ℂ (readPre t S is (pure t S is x)) (readPre t S is (pure t S is y)) =
      inner ℂ (pure t S is x) (pure t S is y) := by
  rw [readPre_pure, readPre_pure, inner_pure]
  exact FreeMoments.gram_word (fun a => map_star t.functional a) t.normalized hfree _ _
    (letters_reduced t S is x his) (letters_reduced t S is y his)

lemma inner_readPre (is : List ι) (his : is.IsChain (· ≠ ·))
    (x y : tensor t S is) :
    inner ℂ (readPre t S is x) (readPre t S is y) = inner ℂ x y := by
  have hx : x ∈ Submodule.span ℂ (Set.range (pure t S is)) := by rw [span_pure]; trivial
  have hy : y ∈ Submodule.span ℂ (Set.range (pure t S is)) := by rw [span_pure]; trivial
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨w, rfl⟩ := hy
      exact inner_readPre_pure t S hfree is his v w
    | zero => simp
    | add y z _ _ hy hz => simp only [map_add, inner_add_right, hy, hz]
    | smul c y _ hy => simp only [map_smul, inner_smul_right, hy]
  | zero => simp
  | add x z _ _ hx hz => simp only [map_add, inner_add_left, hx, hz]
  | smul c x _ hx => simp only [map_smul, inner_smul_left, hx]

noncomputable def readIsometry (is : List ι) (his : is.IsChain (· ≠ ·)) :
    tensor t S is →ₗᵢ[ℂ] preSpace t :=
  (readPre t S is).isometryOfInner (inner_readPre t S hfree is his)

noncomputable def wordEmbedding (is : List ι) (his : is.IsChain (· ≠ ·)) :
    Completion (tensor t S is) →ₗᵢ[ℂ] t.functional.GNS where
  toLinearMap := (readIsometry t S hfree is his).toContinuousLinearMap.completion.toLinearMap
  norm_map' x := by
    induction x using Completion.induction_on with
    | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
    | ih x => simp

@[simp] lemma wordEmbedding_coe (is : List ι) (his : is.IsChain (· ≠ ·))
    (x : tensor t S is) :
    wordEmbedding t S hfree is his (x : Completion (tensor t S is)) =
      (readPre t S is x : t.functional.GNS) := by
  change (readIsometry t S hfree is his).toContinuousLinearMap.completion _ = _
  simp [readIsometry]

abbrev wordSpace (is : ColorSeq ι) := Completion (tensor t S is.val)

end Kadison.FreeWordTensor
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FreeWordDecomposition
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass
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

def boundedLetter (a : FreeMoments.Letter S t.functional.toLinearMap) :
    letterSpace t S a.color :=
  ⟨t.functional.toPreGNS a.val, by exact ⟨a.mem, a.centered⟩⟩

@[simp] lemma asLetter_boundedLetter (a : FreeMoments.Letter S t.functional.toLinearMap) :
    asLetter t S a.color (boundedLetter t S a) = a := by cases a; rfl

def paramsOfLetters : (w : List (FreeMoments.Letter S t.functional.toLinearMap)) →
    Params t S (w.map FreeMoments.Letter.color)
  | [] => PUnit.unit
  | a :: w => (boundedLetter t S a, paramsOfLetters w)

@[simp] lemma letters_paramsOfLetters :
    ∀ w : List (FreeMoments.Letter S t.functional.toLinearMap),
      letters t S (w.map FreeMoments.Letter.color) (paramsOfLetters t S w) = w
  | [] => rfl
  | a :: w => by
    change asLetter t S a.color (boundedLetter t S a) ::
      letters t S (w.map FreeMoments.Letter.color) (paramsOfLetters t S w) = a :: w
    rw [asLetter_boundedLetter, letters_paramsOfLetters w]

end Kadison.FreeWordTensor
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FreeAction
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass
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

def letter (a : Letter S t.functional.toLinearMap) : Letter S t.functional.toLinearMap where
  color := a.color
  val := α a.color a.val
  mem := hmem _ _ a.mem
  centered := (hτ _ _).trans a.centered

@[simp] lemma letter_color (a : Letter S t.functional.toLinearMap) :
    (letter t S α hmem hτ a).color=a.color := rfl

end Kadison.FreeWordAction

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FreeCreation
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass
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

abbrev Letter := FreeMoments.Letter S t.functional.toLinearMap

def wordVector (w : List (Letter t S)) : t.functional.GNS :=
  (t.functional.toPreGNS (word w) : t.functional.GNS)

lemma inner_wordVector (w z : List (Letter t S)) :
    inner ℂ (wordVector t S w) (wordVector t S z) =
      t.functional (star (word w) * word z) := by
  rw [wordVector, wordVector, Completion.inner_coe]
  rfl

lemma mul_wordVector (a : A) (w : List (Letter t S)) :
    t.functional.gnsStarAlgHom a (wordVector t S w) =
      (t.functional.toPreGNS (a * word w) : t.functional.GNS) := by
  simp [wordVector, PositiveLinearMap.gnsStarAlgHom]

def CanPrepend (i : ι) (w : List (Letter t S)) : Prop :=
  ∀ a ∈ w.head?, i ≠ a.color

lemma reduced_prepend {i : ι} {w : List (Letter t S)} (hw : Reduced w)
    (hi : CanPrepend t S i w) (a : Letter t S) (ha : a.color = i) :
    Reduced (a :: w) := by
  cases w with
  | nil => exact reduced_singleton a
  | cons b w =>
    exact List.isChain_cons_cons.mpr ⟨by simpa [ha] using hi b (by simp), hw⟩

lemma colors_ne_prepend {i : ι} {w z : List (Letter t S)}
    (hi : CanPrepend t S i w) (a : Letter t S) (ha : a.color = i) :
    w.map FreeMoments.Letter.color ≠ (a :: z).map FreeMoments.Letter.color := by
  cases w with
  | nil => simp
  | cons b w =>
    intro h
    have hc : b.color = a.color := (List.cons.inj h).1
    exact hi b (by simp) (ha ▸ hc.symm)

include hfree in
lemma centered_middle_zero {i : ι} {w z : List (Letter t S)}
    (hw : Reduced w) (hz : Reduced z)
    (hiw : CanPrepend t S i w) (hiz : CanPrepend t S i z)
    (a : Letter t S) (ha : a.color = i) :
    t.functional (star (word w) * (a.val * word z)) = 0 := by
  change t.functional.toLinearMap (star (word w) * word (a :: z)) = 0
  rw [gram_word (fun a => map_star t.functional a) t.normalized hfree _ _ hw
    (reduced_prepend t S hz hiz a ha)]
  exact gram_zero_of_colors_ne _ _ (colors_ne_prepend t S hiw a ha)

include hfree in
lemma middle_factor {i : ι} {w z : List (Letter t S)}
    (hw : Reduced w) (hz : Reduced z)
    (hiw : CanPrepend t S i w) (hiz : CanPrepend t S i z)
    {a : A} (ha : a ∈ S i) :
    t.functional (star (word w) * (a * word z)) =
      t.functional a * t.functional (star (word w) * word z) := by
  let a0 : Letter t S :=
    ⟨i, a - t.functional a • (1 : A),
      sub_mem ha (SMulMemClass.smul_mem _ (one_mem (S i))),
      by simp [map_sub, map_smul, t.normalized]⟩
  have h := centered_middle_zero t S hfree hw hz hiw hiz a0 rfl
  change t.functional (star (word w) *
    ((a - t.functional a • (1 : A)) * word z)) = 0 at h
  simp only [sub_mul, smul_mul_assoc, one_mul, mul_sub, mul_smul_comm,
    map_sub, map_smul] at h
  exact sub_eq_zero.mp h

def tailSpan (i : ι) : Submodule ℂ t.functional.GNS :=
  Submodule.span ℂ {x | ∃ w : List (Letter t S),
    Reduced w ∧ CanPrepend t S i w ∧ wordVector t S w = x}

def tailSpace (i : ι) : Submodule ℂ t.functional.GNS :=
  (tailSpan t S i).topologicalClosure

def Starts (i : ι) (w : List (Letter t S)) : Prop :=
  ∃ a z, w = a :: z ∧ a.color = i

def headSpan (i : ι) : Submodule ℂ t.functional.GNS :=
  Submodule.span ℂ {x | ∃ w : List (Letter t S),
    Reduced w ∧ Starts t S i w ∧ wordVector t S w = x}

def headSpace (i : ι) : Submodule ℂ t.functional.GNS :=
  (headSpan t S i).topologicalClosure

lemma headSpace_le_other_tailSpace {i j : ι} (hij : i ≠ j) :
    headSpace t S i ≤ tailSpace t S j := by
  apply Submodule.topologicalClosure_mono
  apply Submodule.span_le.mpr
  rintro x ⟨w, hw, ⟨a, z, rfl, ha⟩, rfl⟩
  apply Submodule.subset_span
  refine ⟨a :: z, hw, ?_, rfl⟩
  intro b hb
  have hb' : b = a := (by simpa using hb : a = b).symm
  subst b
  simpa [ha] using hij.symm

lemma creation_mem_headSpan (i : ι) {a : A} (ha : a ∈ S i)
    (ha0 : t.functional a = 0) {x : t.functional.GNS} (hx : x ∈ tailSpan t S i) :
    t.functional.gnsStarAlgHom a x ∈ headSpan t S i := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, hw, hiw, rfl⟩ := hx
    let b : Letter t S := ⟨i, a, ha, ha0⟩
    apply Submodule.subset_span
    refine ⟨b :: w, reduced_prepend t S hw hiw b rfl, ⟨b, w, rfl, rfl⟩, ?_⟩
    rw [mul_wordVector]
    rfl
  | zero => simp
  | add x y _ _ hx hy => simpa using (headSpan t S i).add_mem hx hy
  | smul c x _ hx => simpa using (headSpan t S i).smul_mem c hx

lemma creation_mem_headSpace (i : ι) {a : A} (ha : a ∈ S i)
    (ha0 : t.functional a = 0) {x : t.functional.GNS} (hx : x ∈ tailSpace t S i) :
    t.functional.gnsStarAlgHom a x ∈ headSpace t S i := by
  apply closure_minimal (s := (tailSpan t S i : Set _))
    (t := {x | t.functional.gnsStarAlgHom a x ∈ headSpace t S i}) ?_ ?_ hx
  · intro x hx
    exact (headSpan t S i).le_topologicalClosure
      (creation_mem_headSpan t S i ha ha0 hx)
  · exact (headSpan t S i).isClosed_topologicalClosure.preimage
      (t.functional.gnsStarAlgHom a).continuous

end Kadison.FreeCreation
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FreeBlockWords
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass
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

lemma vacuum_mem_tailSpan (i : ι) : wordVector t S [] ∈ tailSpan t S i :=
  Submodule.subset_span ⟨[], reduced_nil, by simp [CanPrepend], rfl⟩

lemma factor_vector_mem_tailSpan {i j : ι} (hij : i≠j) {a : A} (ha : a∈S j) :
    (t.functional.toPreGNS a : t.functional.GNS) ∈ tailSpan t S i := by
  let a0 : Letter t S :=
    ⟨j, a-t.functional a • (1 : A),
      sub_mem ha (SMulMemClass.smul_mem _ (one_mem (S j))),
      by simp [map_sub, map_smul, t.normalized]⟩
  have hc : wordVector t S [a0] ∈ tailSpan t S i :=
    Submodule.subset_span ⟨[a0], reduced_singleton _, by simpa [CanPrepend, a0] using hij, rfl⟩
  have hh := (tailSpan t S i).add_mem hc ((tailSpan t S i).smul_mem
    (t.functional a) (vacuum_mem_tailSpan t S i))
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  simp only [wordVector, word_cons, word_nil, mul_one, a0, map_sub, map_smul,
    Completion.coe_sub, Completion.coe_smul, sub_add_cancel]

lemma factor_vector_mem_tailSpace {i j : ι} (hij : i≠j) {a : A} (ha : a∈S j) :
    (t.functional.toPreGNS a : t.functional.GNS) ∈ tailSpace t S i :=
  (tailSpan t S i).le_topologicalClosure (factor_vector_mem_tailSpan t S hij ha)

end Kadison.FreeCreation
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FreeBlockWords2
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass
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

abbrev Letters (i j : ι) := letterSpace t S j × letterSpace t S i

def blockValue : List (Letters t S i j) → A → A
  | [], z => z
  | x::xs, z => letterValue t S j x.1 *
      (letterValue t S i x.2 * blockValue xs z)

def blockVector (xs : List (Letters t S i j)) (z : A) : t.functional.GNS :=
  (t.functional.toPreGNS (blockValue t S xs z) : t.functional.GNS)

@[simp] lemma blockVector_nil (z : A) : blockVector t S ([] : List (Letters t S i j)) z =
    (t.functional.toPreGNS z : t.functional.GNS) := rfl

lemma blockVector_cons (x : Letters t S i j) (xs : List (Letters t S i j)) (z : A) :
    blockVector t S (x::xs) z = t.functional.gnsStarAlgHom (letterValue t S j x.1)
      (t.functional.gnsStarAlgHom (letterValue t S i x.2) (blockVector t S xs z)) := by
  simp [blockVector, blockValue, PositiveLinearMap.gnsStarAlgHom]

include hij in
lemma blockVector_mem_tail (xs : List (Letters t S i j)) {z : A} (hz : z ∈ S j) :
    blockVector t S xs z ∈ tailSpace t S i := by
  induction xs with
  | nil => exact factor_vector_mem_tailSpace t S hij hz
  | cons x xs ih =>
    rw [blockVector_cons]
    apply headSpace_le_other_tailSpace t S hij.symm
    apply creation_mem_headSpace t S j x.1.property.1 x.1.property.2
    apply headSpace_le_other_tailSpace t S hij
    exact creation_mem_headSpace t S i (a := letterValue t S i x.2) x.2.property.1 x.2.property.2 ih

end Kadison.FreeBlocks
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FreeBlockTensor
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass
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

def factorSpace (i : ι) : Submodule ℂ (preSpace t) where
  carrier := {x | t.functional.ofPreGNS x ∈ S i}
  zero_mem' := by simp
  add_mem' := by intro x y hx hy; simpa using add_mem hx hy
  smul_mem' := by intro c x hx; simpa using SMulMemClass.smul_mem c hx

def factorValue (i : ι) : factorSpace t S i →ₗ[ℂ] A :=
  t.functional.ofPreGNS.toLinearMap.comp (factorSpace t S i).subtype

abbrev spaceTensor (E F : Space) : Space := ⟨E ⊗[ℂ] F⟩

@[reducible] def blockTensor (i j : ι) : ℕ → Space
  | 0 => ⟨factorSpace t S j⟩
  | n+1 => spaceTensor ⟨letterSpace t S j⟩ (spaceTensor ⟨letterSpace t S i⟩ (blockTensor i j n))

@[reducible] def BlockParams (i j : ι) : ℕ → Type
  | 0 => factorSpace t S j
  | n+1 => Letters t S i j × BlockParams i j n

def blockPure : ∀ n, BlockParams t S i j n → blockTensor t S i j n
  | 0, z => z
  | n+1, x => x.1.1 ⊗ₜ[ℂ] (x.1.2 ⊗ₜ[ℂ] blockPure n x.2)

def paramLetters : ∀ n, BlockParams t S i j n → List (Letters t S i j)
  | 0, _ => []
  | n+1, x => x.1 :: paramLetters n x.2

def paramEnd : ∀ n, BlockParams t S i j n → factorSpace t S j
  | 0, z => z
  | n+1, x => paramEnd n x.2

@[simp] lemma paramLetters_length : ∀ n (x : BlockParams t S i j n),
    (paramLetters t S n x).length=n
  | 0, _ => rfl
  | n+1, x => by simp [paramLetters, paramLetters_length n x.2]

def blockRead : ∀ n, blockTensor t S i j n →ₗ[ℂ] A
  | 0 => factorValue t S j
  | n+1 => (TensorProduct.lift (LinearMap.mul ℂ A)).comp
      (TensorProduct.map (letterValue t S j)
        ((TensorProduct.lift (LinearMap.mul ℂ A)).comp
          (TensorProduct.map (letterValue t S i) (blockRead n))))

@[simp] lemma blockRead_pure : ∀ n (x : BlockParams t S i j n),
    blockRead t S n (blockPure t S n x) =
      blockValue t S (paramLetters t S n x) (factorValue t S j (paramEnd t S n x))
  | 0, _ => rfl
  | n+1, x => by
    change letterValue t S j x.1.1 * (letterValue t S i x.1.2 *
      blockRead t S n (blockPure t S n x.2)) = _
    rw [blockRead_pure n x.2]
    rfl

lemma span_blockPure (n : ℕ) :
    Submodule.span ℂ (Set.range (blockPure t S (i := i) (j := j) n))=⊤ := by
  induction n with
  | zero => simp [blockPure]
  | succ n ih =>
    apply Submodule.eq_top_iff'.mpr
    intro z
    induction z using OAI.tensorInductionOn with
    | add x y hx hy => exact Submodule.add_mem _ hx hy
    | tmul a w =>
      induction w using OAI.tensorInductionOn with
      | add x y hx hy => simpa only [TensorProduct.tmul_add] using
          (Submodule.span ℂ (Set.range (blockPure t S (i := i) (j := j) (n+1)))).add_mem hx hy
      | tmul d w =>
        have hw : w ∈ Submodule.span ℂ (Set.range (blockPure t S (i := i) (j := j) n)) := by rw [ih]; trivial
        induction hw using Submodule.span_induction with
        | mem w hw =>
          obtain ⟨v,rfl⟩ := hw
          exact Submodule.subset_span ⟨((a,d),v),rfl⟩
        | zero => simp only [TensorProduct.tmul_zero, Submodule.zero_mem]
        | add x y _ _ hx hy => simpa only [TensorProduct.tmul_add] using
            (Submodule.span ℂ (Set.range (blockPure t S (i := i) (j := j) (n+1)))).add_mem hx hy
        | smul c w _ hw => simpa only [TensorProduct.tmul_smul] using
            (Submodule.span ℂ (Set.range (blockPure t S (i := i) (j := j) (n+1)))).smul_mem c hw

def blockReadPre (n : ℕ) : blockTensor t S i j n →ₗ[ℂ] preSpace t :=
  t.functional.toPreGNS.toLinearMap.comp (blockRead t S n)

@[simp] lemma blockReadPre_pure (n : ℕ) (x : BlockParams t S i j n) :
    (blockReadPre t S n (blockPure t S n x) : t.functional.GNS) =
      blockVector t S (paramLetters t S n x) (factorValue t S j (paramEnd t S n x)) := by
  change (t.functional.toPreGNS (blockRead t S n (blockPure t S n x)) : t.functional.GNS)=_
  rw [blockRead_pure]
  rfl

end Kadison.FreeBlocks
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FreeBlockTensor2
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass
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

include hij in
lemma blockReadPre_mem_tail (n : ℕ) (x : blockTensor t S i j n) :
    (blockReadPre t S n x : t.functional.GNS) ∈ tailSpace t S i := by
  have hx : x ∈ Submodule.span ℂ (Set.range (blockPure t S (i := i) (j := j) n)) := by rw [span_blockPure]; trivial
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v,rfl⟩ := hx
    rw [blockReadPre_pure]
    exact blockVector_mem_tail t S hij _ (paramEnd t S n v).property
  | zero => simp only [map_zero, Completion.coe_zero, Submodule.zero_mem]
  | add x y _ _ hx hy => simpa only [map_add, Completion.coe_add] using
      (tailSpace t S i).add_mem hx hy
  | smul c x _ hx => simpa only [map_smul, Completion.coe_smul] using
      (tailSpace t S i).smul_mem c hx

def endpointTensor (i j : ι) (n : ℕ) : Space :=
  spaceTensor ⟨factorSpace t S i⟩ (blockTensor t S i j n)

def endpointRead (n : ℕ) : endpointTensor t S i j n →ₗ[ℂ] preSpace t :=
  t.functional.toPreGNS.toLinearMap.comp
    ((TensorProduct.lift (LinearMap.mul ℂ A)).comp
      (TensorProduct.map (factorValue t S i) (blockRead t S n)))

lemma endpointRead_tmul (n : ℕ) (a : factorSpace t S i) (x : blockTensor t S i j n) :
    (endpointRead t S n (a ⊗ₜ[ℂ] x) : t.functional.GNS) =
      t.functional.gnsStarAlgHom (factorValue t S i a)
        (blockReadPre t S n x : t.functional.GNS) := by
  change (t.functional.toPreGNS (factorValue t S i a * blockRead t S n x) :
    t.functional.GNS) = _
  simp [blockReadPre, PositiveLinearMap.gnsStarAlgHom]

lemma endpointTensor_induction_on (n : ℕ) {P : endpointTensor t S i j n → Prop}
    (x : endpointTensor t S i j n) (h0 : P 0)
    (ht : ∀ a : factorSpace t S i, ∀ b : blockTensor t S i j n, P (a ⊗ₜ[ℂ] b))
    (ha : ∀ x y : endpointTensor t S i j n, P x → P y → P (x+y)) : P x := by
  by_cases hx : x = 0
  · simpa only [hx] using h0
  · exact OAI.tensorInductionOn x ht ha

end Kadison.FreeBlocks
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_HankelAlgebra
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass
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

@[simp] lemma paired_nil (s : Letter S τ) : paired s []=[] := rfl

end Kadison.FreeMoments

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_PartialWordContinuity
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder Topology

open Filter

namespace Kadison.FinitePatching

variable {A J K : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b : A,τ (a*b)=τ (b*a))

namespace Words

variable (x : J → A) (k : K → ℤ)

def slotCost : Slot K → ℕ
  | none => 0
  | some none => 2
  | some (some i) => (k i).natAbs+2

end Words

end Kadison.FinitePatching

end

end
end

end OAI
end


