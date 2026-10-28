-- Prove2me | Definitions.Def_OAIQ63Br003
-- name    : OAIQ63Br003
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T00:07:30.708727+00:00
-- url     : https://prove2.me/theorems/9061821b-bb35-4e9e-870b-08877c52e5dd
-- title:
--   Definitions bundle OAIQ63Br003 of the split of OpenAI, Balanced counterexamples to Ryser's conjecture at prime orders (result family 162)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Balanced.main_result`, carved from OpenAI's openai/math development (OpenAI, *Balanced counterexamples to Ryser's conjecture at prime orders (result family 162)*, OpenAI Math Release, September 27, 2026, result family 162, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 51 declarations of OpenAI's Lean: 31 definitions, 1 instance and 19 theorems. The definitions and types are `OAI.Balanced.ConditionalRestriction.uniformArrayModel`, `OAI.Balanced.Selection.Process.postcheckTail`, `OAI.Balanced.Selection.Process.sourceDegreeCensorBound`, `OAI.Balanced.StabilityPolynomial.nonverticalSkewCodes`, `OAI.Balanced.StabilityPolynomial.redeiLeadingProduct`, `OAI.Balanced.TupleAlignment.alignedDistinctOffsetsEquiv`, `OAI.Balanced.TupleAlignment.commonLineSuccessPairs`, `OAI.Balanced.TupleAlignment.invalidSuccessCount`, `OAI.Balanced.TupleAlignment.rootFiberSquareCount`, `OAI.Balanced.TupleAlignment.rootOverlapCount`, `OAI.Balanced.TupleAlignment.rootPatternModel`, `OAI.Balanced.TupleAlignment.successfulChoices`, `OAI.Balanced.TupleAlignment.successfulOffsetsEquiv`, `OAI.Balanced.TupleAlignment.validPrescriptions`, `OAI.Balanced.UniformDeletionEnumeration.arrayRelabel`, `OAI.Balanced.UniformDeletionEnumeration.canonicalOffsets`, `OAI.Balanced.UniformDeletionEnumeration.deletionOutcome`, `OAI.Balanced.UniformDeletionEnumeration.lineRelabel`, `OAI.Balanced.UniformDeletionEnumeration.orderingEquiv`, `OAI.Balanced.UniformDeletionEnumeration.timeOrderingEquiv`, `OAI.Balanced.UniformDeletionEnumeration.tokenEquiv`, `OAI.Balanced.UnusedOffsetIncidence.Noncollinear`, `OAI.Balanced.deletionEventCard`, `OAI.Balanced.distinctConstituentProbability`, `OAI.Balanced.globalTupleCodeTargetMass`, `OAI.Balanced.mergedPairsEquivConstituentOffsets`, `OAI.Balanced.missedAffine`, `OAI.Balanced.missedProjective`, `OAI.Balanced.partitionHypergraph_edgeEquiv`, `OAI.Balanced.representedDirections`, `OAI.Balanced.survivingLineOccupancy`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `BalancedRyser_Candidates_CandidateDistinctLaw`, `BalancedRyser_Candidates_CandidateRootFibers`, `BalancedRyser_Candidates_ConstituentOffsets`, `BalancedRyser_Construction_Construction`, `BalancedRyser_Construction_PartitionEncoding`, `BalancedRyser_Construction_PartitionHypergraph`, `BalancedRyser_Deletion_Deletion`, `BalancedRyser_Deletion_UniformDeletionEnumeration`, `BalancedRyser_Incidence_Projective`, `BalancedRyser_Incidence_RedeiPolynomial`, `BalancedRyser_Incidence_StabilityLeadingPart`, `BalancedRyser_Incidence_UnusedOffsetIncidence`, `BalancedRyser_Local_ReuseGlobalExtension`, `BalancedRyser_Local_TupleAlignment`, `BalancedRyser_Probability_FiniteExposureTower`, `BalancedRyser_Probability_RootPatternModel`, `BalancedRyser_Probability_TailConditioning2`, `BalancedRyser_Probability_TailEvents2`, `BalancedRyser_Probability_TailGraphWeights`, `BalancedRyser_Probability_TailWeights`, `BalancedRyser_Profiles_ProfileEmpirical`, `BalancedRyser_Selection_OccupancyFailureClass`, `BalancedRyser_Selection_SelectionPostcheckTail`, `BalancedRyser_Selection_SelectionSourceConcentration`.
--
--   **Imports.** It imports the published bundle `Def_BalancedRyser`; the bundles `OAIQ63Br000` and `OAIQ63Br001` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ63Br004`; the statement `OAI.Balanced.CandidateAbundanceAssembly.tendsto_square_fibers`; the proofs of `OAI.Balanced.CandidateAbundanceAssembly.tendsto_square_fibers`, `OAI.Balanced.CandidateAbundanceAssembly.tendsto_successful_roots`, `OAI.Balanced.CandidateIncidenceTests.candidateGraphResult_of_incidence_estimates`, `OAI.Balanced.CandidateIncidenceTests.candidateGraphResult_of_size_estimate`, `OAI.Balanced.CandidateIncidenceTests.tendsto_smallGood`, `OAI.Balanced.ExternalWitnessTail.candidateSlots_of_uniform_moment`, `OAI.Balanced.Selection.Process.exists_uniformConcentratedPath_estimate` and `OAI.Balanced.candidateGraph_proof`.
-- source:
--   OpenAI, Balanced counterexamples to Ryser's conjecture at prime orders (result family 162), OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 162; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Balanced-Counterexamples-to-Rysers-Conjecture-at-Prime-Orders-September-27-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_BalancedRyser
import Definitions.Def_OAIQ63Br000
import Definitions.Def_OAIQ63Br001

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Construction_Construction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced

noncomputable section
attribute [local instance] Classical.propDecidable

instance instFintypeConfiguration {F : Type*} [Fintype F] : Fintype (Configuration F) :=
  Fintype.ofEquiv (MergedPairs F × (Slot F → SplitChoice F))
    { toFun := fun p => ⟨p.1, p.2⟩
      invFun := fun t => (t.merged, t.choice)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

end
end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_ConstituentOffsets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced
open scoped _root_.Balanced

noncomputable def distinctConstituentProbability (q : ℕ) : ℝ :=
  finiteUniformProbability
    (AllConstituentPairsDistinct (D := Fin (q + 1)) (K := Fin q))

end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_CandidateDistinctLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced
open scoped _root_.Balanced

open Filter Topology

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def mergedPairsEquivConstituentOffsets :
    MergedPairs F ≃ ConstituentOffsets (Direction F) F where
  toFun M d := (M d false, M d true)
  invFun M d b := if b then (M d).2 else (M d).1
  left_inv M := by
    funext d b
    cases b <;> rfl
  right_inv M := by
    funext d
    rfl

end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_TupleAlignment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.TupleAlignment

variable {F : Type*} [Field F]

theorem aligned_injective_iff (d : Fin 4 → Direction F)
    (hd : ∀ i, d i ≠ d (i + 1)) (σ : Fin 4 → Bool)
    (g : Direction F) (c : F)
    (o : {o : Fin 4 → Bool → F //
      ∀ i, OnLine (tuplePositionEquiv d hd σ o i) (g,c)}) :
    Function.Injective (tuplePositionEquiv d hd σ o.1) ↔
      Function.Injective (alignedOffsetsEquiv d hd σ g c o) := by
  constructor
  · intro h i j hij
    apply h
    have hsub :
        (⟨tuplePositionEquiv d hd σ o.1 i, o.2 i⟩ : {p // OnLine p (g,c)}) =
        ⟨tuplePositionEquiv d hd σ o.1 j, o.2 j⟩ :=
      (linePointEquiv g c).injective hij
    exact congrArg Subtype.val hsub
  · intro h i j hij
    apply h
    exact congrArg (linePointEquiv g c) (Subtype.ext hij)

def alignedDistinctOffsetsEquiv (d : Fin 4 → Direction F)
    (hd : ∀ i, d i ≠ d (i + 1)) (σ : Fin 4 → Bool)
    (g : Direction F) (c : F) :
    {o : {o : Fin 4 → Bool → F //
      ∀ i, OnLine (tuplePositionEquiv d hd σ o i) (g,c)} //
      Function.Injective (tuplePositionEquiv d hd σ o.1)} ≃ (Fin 4 ↪ F) :=
  ((alignedOffsetsEquiv d hd σ g c).subtypeEquiv
    (aligned_injective_iff d hd σ g c)).trans
      (Equiv.subtypeInjectiveEquivEmbedding (Fin 4) F)

def successfulOffsetsEquiv (d : Fin 4 → Direction F)
    (hd : ∀ i, d i ≠ d (i + 1)) (σ : Fin 4 → Bool)
    (g : Direction F) :
    {o : Fin 4 → Bool → F //
      (∃ c, ∀ i, OnLine (tuplePositionEquiv d hd σ o i) (g,c)) ∧
      Function.Injective (tuplePositionEquiv d hd σ o)} ≃
    Σ c : F, {o : {o : Fin 4 → Bool → F //
      ∀ i, OnLine (tuplePositionEquiv d hd σ o i) (g,c)} //
      Function.Injective (tuplePositionEquiv d hd σ o.1)} where
  toFun o := ⟨lineEval g (tuplePositionEquiv d hd σ o.1 0),
    ⟨o.1, by
      rcases o.2.1 with ⟨c,h⟩
      intro i
      exact (h i).trans (h 0).symm⟩, o.2.2⟩
  invFun s := ⟨s.2.1.1, ⟨s.1,s.2.1.2⟩, s.2.2⟩
  left_inv o := by apply Subtype.ext; rfl
  right_inv s := by
    rcases s with ⟨c, ⟨o,ho⟩,hi⟩
    have h0 : lineEval g (tuplePositionEquiv d hd σ o 0) = c := ho 0
    cases h0
    rfl

end Balanced.TupleAlignment

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_CandidateRootFibers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.TupleAlignment

noncomputable section
open scoped Classical BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def successfulChoices (M : MergedPairs F) (g : Direction F) : Finset (SplitChoice F) :=
  (successfulPrescriptions M g).image (fun a => a.choice M)

def validPrescriptions (M : MergedPairs F) (g : Direction F) :
    Finset (RootPrescription g) :=
  (successfulPrescriptions M g).filter (fun a => ValidChoice M g (a.choice M))

def invalidSuccessCount (M : MergedPairs F) (g : Direction F) : ℕ :=
  ((successfulPrescriptions M g).filter (fun a => ¬ ValidChoice M g (a.choice M))).card

def rootFiberSquareCount (M : MergedPairs F) (g : Direction F) : ℕ :=
  ∑ l : Line F,
    ((successfulPrescriptions M g).filter (fun a => (a.choice M).line = l)).card ^ 2

def commonLineSuccessPairs (M : MergedPairs F) (g : Direction F) :
    Finset (RootPrescription g × RootPrescription g) :=
  ((successfulPrescriptions M g).product (successfulPrescriptions M g)).filter
    (fun ab => (ab.1.choice M).line = (ab.2.choice M).line)

end
end Balanced.TupleAlignment

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Construction_PartitionEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced
open scoped _root_.Balanced

theorem encodeAssignment_eq_iff
    {G X : Type*} {Label : G → Type*} {r n : ℕ}
    (eG : G ≃ Fin r) (eL : ∀ g, Label g ≃ Fin n)
    (label : (g : G) → X → Label g) (x y : X) :
    encodeAssignment eG eL label x = encodeAssignment eG eL label y ↔
      (fun g => label g x) = (fun g => label g y) := by
  constructor
  · intro h
    funext g
    apply (eL g).injective
    simpa using congrFun h (eG g)
  · intro h
    funext i
    exact congrArg (eL (eG.symm i)) (congrFun h (eG.symm i))

theorem encodeAssignment_injective
    {G X : Type*} {Label : G → Type*} {r n : ℕ}
    (eG : G ≃ Fin r) (eL : ∀ g, Label g ≃ Fin n)
    (label : (g : G) → X → Label g)
    (h : Function.Injective (fun x g => label g x)) :
    Function.Injective (encodeAssignment eG eL label) := by
  intro x y hxy
  exact h ((encodeAssignment_eq_iff eG eL label x y).mp hxy)

end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Construction_PartitionHypergraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced
open scoped _root_.Balanced

variable {G X : Type*} [Fintype X] {Label : G → Type*} {r n : ℕ}

noncomputable def partitionHypergraph_edgeEquiv
    (eG : G ≃ Fin r) (eL : ∀ g, Label g ≃ Fin n)
    (label : (g : G) → X → Label g)
    (hinj : Function.Injective (fun x g => label g x)) :
    X ≃ {e // e ∈ (partitionHypergraph eG eL label).edges} :=
  Equiv.ofBijective
    (fun x => ⟨encodeAssignment eG eL label x,
      (mem_partitionHypergraph_edges eG eL label _).mpr ⟨x, rfl⟩⟩)
    (by
      constructor
      · intro x y hxy
        exact encodeAssignment_injective eG eL label hinj (congrArg Subtype.val hxy)
      · intro e
        obtain ⟨x, hx⟩ := (mem_partitionHypergraph_edges eG eL label e.val).mp e.property
        exact ⟨x, Subtype.ext hx⟩)

end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Deletion_Deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped NNReal

noncomputable section

namespace Balanced
open scoped _root_.Balanced

universe u

variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]

noncomputable def deletionEventCard {k : ℕ} (E : DeletionSet F k → Prop) : ℕ := by
  classical
  exact (Finset.univ.filter E).card

end Balanced

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Deletion_UniformDeletionEnumeration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace Balanced.UniformDeletionEnumeration

noncomputable section
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {k : ℕ}

omit [Field F] in

theorem selectedLines_filter (f : Direction F → Fin k ↪ F) (d : Direction F) :
    (selectedLines f).filter (fun l => l.1 = d) =
      Finset.univ.map ((f d).trans
        ⟨Prod.mk d, fun _ _ h => congrArg Prod.snd h⟩) := by
  ext l
  simp only [Finset.mem_filter, mem_selectedLines, Finset.mem_map,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨j, hj⟩, hd⟩
    refine ⟨j, ?_⟩
    change (d, f d j) = l
    apply Prod.ext hd.symm
    simpa only [hd] using hj
  · rintro ⟨j, hj⟩
    change (d, f d j) = l at hj
    have hd : d = l.1 := congrArg Prod.fst hj
    refine ⟨⟨j, ?_⟩, hd.symm⟩
    simpa only [← hd] using congrArg Prod.snd hj

omit [Field F] in

theorem selectedLines_isDeletionSet (f : Direction F → Fin k ↪ F) :
    IsDeletionSet k (selectedLines f) := by
  intro d
  rw [selectedLines_filter]
  simp

def deletionOutcome (f : Direction F → Fin k ↪ F) : DeletionSet F k :=
  ⟨selectedLines f, selectedLines_isDeletionSet f⟩

def lineRelabel (τ : Direction F → Equiv.Perm F) : Line F ≃ Line F where
  toFun l := (l.1, τ l.1 l.2)
  invFun l := (l.1, (τ l.1).symm l.2)
  left_inv l := by cases l; simp
  right_inv l := by cases l; simp

def arrayRelabel (τ : Direction F → Equiv.Perm F) :
    (Direction F → Fin k ↪ F) ≃ (Direction F → Fin k ↪ F) :=
  Equiv.piCongrRight fun d => InjectionExposureLaw.postcompose (τ d)

def tokenEquiv (f : Direction F → Fin k ↪ F) :
    (Direction F × Fin k) ≃ (deletionOutcome f).val :=
  Equiv.ofBijective
    (fun t => (⟨lineEmbedding f t, Finset.mem_map.mpr ⟨t, Finset.mem_univ _, rfl⟩⟩ :
      (deletionOutcome f).val))
    ⟨fun _ _ he => (lineEmbedding f).injective (congrArg Subtype.val he), by
      intro l
      obtain ⟨t, _, ht⟩ := Finset.mem_map.mp l.property
      exact ⟨t, Subtype.ext ht⟩⟩

def orderingEquiv (f : Direction F → Fin k ↪ F) :
    Equiv.Perm (Direction F × Fin k) ≃
      ((Direction F × Fin k) ≃ (deletionOutcome f).val) where
  toFun π := π.trans (tokenEquiv f)
  invFun e := e.trans (tokenEquiv f).symm
  left_inv π := by
    apply Equiv.ext
    intro t
    exact (tokenEquiv f).symm_apply_apply (π t)
  right_inv e := by
    apply Equiv.ext
    intro t
    exact (tokenEquiv f).apply_symm_apply (e t)

def canonicalOffsets (hk : k ≤ Fintype.card F) : Direction F → Fin k ↪ F :=
  fun _ => (Fin.castLEEmb hk).trans (Fintype.equivFin F).symm.toEmbedding

def timeOrderingEquiv (D : DeletionSet F k) :
    ((Direction F × Fin k) ≃ D.val) ≃ (Fin (k * (Fintype.card F + 1)) ≃ D.val) where
  toFun e := timeToToken.trans e
  invFun e := timeToToken.symm.trans e
  left_inv e := by
    apply Equiv.ext
    intro t
    exact congrArg e (timeToToken.apply_symm_apply t)
  right_inv e := by
    apply Equiv.ext
    intro t
    exact congrArg e (timeToToken.symm_apply_apply t)

end
end Balanced.UniformDeletionEnumeration

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_Projective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced

variable {F : Type*} [Field F]

variable [Fintype F] [DecidableEq F]

def missedAffine (C : Finset (Line F)) : Finset (Point F) :=
  Finset.univ.filter (fun p => ∀ l ∈ C, ¬ OnLine p l)

def missedProjective (C : Finset (Line F)) : Finset (ProjectivePoint F) :=
  Finset.univ.filter (fun P => ∀ l ∈ C, ¬ ThroughProjective l P)

def representedDirections (C : Finset (Line F)) : Finset (Direction F) :=
  C.image Prod.fst

end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_RedeiPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.StabilityPolynomial

open MvPolynomial
open scoped BigOperators

variable {F : Type*} [Field F]

variable [Fintype F]

noncomputable def nonverticalSkewCodes (U : Finset (Point F)) : Finset (Fin 2 → F) := by
  classical
  exact Finset.univ.filter fun z => ∀ p ∈ U, ¬ OnLine p (some (z 1), z 0)

end Balanced.StabilityPolynomial

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_StabilityLeadingPart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.StabilityPolynomial

open MvPolynomial
open scoped BigOperators

variable {F σ : Type*} [Field F]

noncomputable def redeiLeadingProduct (U : Finset (Point F)) : Polynomial F :=
  ∏ p ∈ U, (Polynomial.X + Polynomial.C p.1)

end Balanced.StabilityPolynomial

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_UnusedOffsetIncidence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open scoped Classical

namespace Balanced.UnusedOffsetIncidence

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def Noncollinear (x y z : Point F) : Prop :=
  ¬ ∃ l : Line F, OnLine x l ∧ OnLine y l ∧ OnLine z l

end Balanced.UnusedOffsetIncidence

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_ReuseGlobalExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced
open scoped _root_.Balanced
open PartialAlignment TupleAlignment

noncomputable section
open scoped Classical

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def globalTupleCodeTargetMass (old : Finset (Direction F)) (a : MergedPairs F)
    (p : Point F) (c : (Fin 4 → Direction F) × (Fin 4 → Bool)) : ℝ :=
  if Function.Injective c.1 then
    ∑ g ∈ (Finset.univ.filter (fun g : Direction F => ∀ i, c.1 i ≠ g)),
      (((offsetLaw F).filter {M | ∀ d, d ∈ old → M d = a d}
        (canonical_exposure_supported old a)).toOuterMeasure
        {M | (∀ i, OnLine (tuplePoint M ⟨c.1, c.2⟩ i) (lineThrough g p)) ∧
          ∀ i, tuplePoint M ⟨c.1, c.2⟩ i ≠ p}).toReal
  else 0

end
end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_FiniteExposureTower
attribute [-instance] _root_.OAI.Balanced.PatternModel.isProbabilityMeasure_measure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.ConditionalRestriction

noncomputable section
open scoped Classical
open MeasureTheory

universe u
variable {D A : Type u} [Fintype D] [Fintype A] [DecidableEq D] [Nonempty A]
  [MeasurableSpace A] [MeasurableSingletonClass A]

def uniformArrayModel : PatternModel.{u} where
  Color := D
  Value := fun _ => A
  law := fun _ => (PMF.uniformOfFintype A).toMeasure
  Label := PUnit
  support := fun _ => ∅
  event := fun _ => ∅
  eventMeasurable := fun _ => MeasurableSet.empty
  dependsOn := by intros; rfl

end
end Balanced.ConditionalRestriction

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_RootPatternModel
attribute [-instance] _root_.OAI.Balanced.PatternModel.isProbabilityMeasure_measure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical
open MeasureTheory

namespace Balanced.TupleAlignment

universe u
variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]

attribute [local instance] OAI.Balanced.TupleAlignment.instMeasurableSpace_solutions
abbrev rootPatternModel (g : Direction F) : PatternModel.{u} where
  Color := Direction F
  Value := fun _ => Bool → F
  law := fun _ => (PMF.uniformOfFintype (Bool → F)).toMeasure
  Label := RootPrescription g
  support := fun a => generatorSet a.tuple
  event := rootSuccessEvent g
  eventMeasurable := fun _ => (Set.toFinite _).measurableSet
  dependsOn := by
    intro a M N h
    have heq := tuplePoint_eq_of_eq_on_generators a.tuple h
    simp only [rootSuccessEvent, Set.mem_ofPred_eq, heq]

def rootOverlapCount (g : Direction F) (K₀ K : Finset (Direction F))
    (M : MergedPairs F) : ℕ :=
  (Finset.univ.filter fun a : RootPrescription g =>
    ¬ Disjoint (generatorSet a.tuple \ K₀) K ∧ M ∈ rootSuccessEvent g a).card

end Balanced.TupleAlignment

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_TailWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace Balanced
open scoped _root_.Balanced
namespace TailWeights

theorem sum_filter_exists_le {I E : Type*} [DecidableEq I] [DecidableEq E]
    (J : Finset I) (edges : Finset E) (R : I → E → Prop) [DecidableRel R]
    (w : E → ℝ) (hw : ∀ e ∈ edges, 0 ≤ w e) :
    ∑ e ∈ edges.filter (fun e => ∃ i ∈ J, R i e), w e ≤
      ∑ i ∈ J, ∑ e ∈ edges.filter (R i), w e := by
  classical
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro e he
  have he0 : 0 ≤ w e := hw e he
  by_cases h : ∃ i ∈ J, R i e
  · rw [ite_eq_left h]
    obtain ⟨i, hi, hie⟩ := h
    calc
      w e = (if R i e then w e else 0) := by simp [hie]
      _ ≤ ∑ j ∈ J, if R j e then w e else 0 := by
        apply Finset.single_le_sum (f := fun j => if R j e then w e else 0)
        · intro j hj
          split_ifs <;> positivity
        · exact hi
  · simp only [ite_eq_right h]
    apply Finset.sum_nonneg
    intro i hi
    split_ifs <;> positivity

theorem touching_weight_le {I E : Type*} [DecidableEq I] [DecidableEq E]
    (J : Finset I) (edges : Finset E) (R : I → E → Prop) [DecidableRel R]
    (w : E → ℝ) (a : ℝ) (hw : ∀ e ∈ edges, 0 ≤ w e)
    (hslot : ∀ i ∈ J, ∑ e ∈ edges.filter (R i), w e ≤ a) :
    ∑ e ∈ edges.filter (fun e => ∃ i ∈ J, R i e), w e ≤
      (J.card : ℝ) * a := by
  calc
    _ ≤ ∑ i ∈ J, ∑ e ∈ edges.filter (R i), w e :=
      sum_filter_exists_le J edges R w hw
    _ ≤ ∑ _i ∈ J, a := Finset.sum_le_sum hslot
    _ = (J.card : ℝ) * a := by simp

end TailWeights
end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_TailGraphWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace Balanced
open scoped _root_.Balanced
namespace TailGraph

variable {V I : Type*} [Fintype V] [DecidableEq V] [DecidableEq I]

theorem slot_weight_le (G : SimpleGraph V) [DecidableRel G.Adj] (slot : V → I)
    (L Δ : ℕ) (hL : 0 < L) (hsize : ∀ i, L ≤ slotSize slot i)
    (hdegree : ∀ u, G.degree u ≤ Δ) (i : I) :
    ∑ e ∈ slotEdges G slot i, edgeWeight slot e ≤ 2 * (Δ : ℝ) / (L : ℝ) := by
  classical
  have hLi : (0 : ℝ) < slotSize slot i := by
    exact_mod_cast lt_of_lt_of_le hL (hsize i)
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have hfilter : slotEdges G slot i = G.edgeFinset.filter
      (fun e => ∃ u ∈ slotVertices slot i, u ∈ e) := by
    ext e
    simp only [slotEdges, Finset.mem_filter, edgeSlots, Finset.mem_image,
      Sym2.mem_toFinset, mem_slotVertices]
    aesop
  rw [hfilter]
  calc
    _ ≤ ∑ u ∈ slotVertices slot i,
        ∑ e ∈ G.edgeFinset.filter (fun e => u ∈ e), edgeWeight slot e :=
      TailWeights.sum_filter_exists_le _ _ (fun u e => u ∈ e) _
        (fun e _ => edgeWeight_nonneg slot e)
    _ = ∑ u ∈ slotVertices slot i, ∑ e ∈ G.incidenceFinset u, edgeWeight slot e := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [G.incidenceFinset_eq_filter]
    _ ≤ ∑ _u ∈ slotVertices slot i,
        (Δ : ℝ) * (2 / ((slotSize slot i : ℝ) * (L : ℝ))) := by
      apply Finset.sum_le_sum
      intro u hu
      have hui : slot u = i := (mem_slotVertices slot i u).mp hu
      calc
        _ ≤ (G.degree u : ℝ) * (2 / ((slotSize slot (slot u) : ℝ) * (L : ℝ))) :=
          incidence_weight_le G slot L hL hsize u
        _ ≤ (Δ : ℝ) * (2 / ((slotSize slot i : ℝ) * (L : ℝ))) := by
          rw [hui]
          apply mul_le_mul_of_nonneg_right
          · exact_mod_cast hdegree u
          · positivity
    _ = 2 * (Δ : ℝ) / (L : ℝ) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      change (slotSize slot i : ℝ) * ((Δ : ℝ) *
        (2 / ((slotSize slot i : ℝ) * (L : ℝ)))) = _
      field_simp

theorem slot_weight_le_quarter (G : SimpleGraph V) [DecidableRel G.Adj] (slot : V → I)
    (L Δ : ℕ) (hL : 0 < L) (hsize : ∀ i, L ≤ slotSize slot i)
    (hdegree : ∀ u, G.degree u ≤ Δ) (hsparse : 8 * Δ ≤ L) (i : I) :
    ∑ e ∈ slotEdges G slot i, edgeWeight slot e ≤ 1 / 4 := by
  apply (slot_weight_le G slot L Δ hL hsize hdegree i).trans
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  apply (div_le_iff₀ hLr).2
  have hs : (8 : ℝ) * Δ ≤ L := by exact_mod_cast hsparse
  linarith

theorem touching_weight_le_quarter (G : SimpleGraph V) [DecidableRel G.Adj]
    (slot : V → I) (L Δ : ℕ) (hL : 0 < L)
    (hsize : ∀ i, L ≤ slotSize slot i) (hdegree : ∀ u, G.degree u ≤ Δ)
    (hsparse : 8 * Δ ≤ L) (J : Finset I) :
    ∑ e ∈ touchingEdges G slot J, edgeWeight slot e ≤ (J.card : ℝ) / 4 := by
  classical
  unfold touchingEdges
  simpa [div_eq_mul_inv] using
    TailWeights.touching_weight_le J G.edgeFinset
      (fun i e => i ∈ edgeSlots slot e) (edgeWeight slot) (1 / 4)
      (fun e _ => edgeWeight_nonneg slot e)
      (fun i _ => slot_weight_le_quarter G slot L Δ hL hsize hdegree hsparse i)

theorem dependency_weight_le_half (G : SimpleGraph V) [DecidableRel G.Adj]
    (slot : V → I) (L Δ : ℕ) (hL : 0 < L)
    (hsize : ∀ i, L ≤ slotSize slot i) (hdegree : ∀ u, G.degree u ≤ Δ)
    (hsparse : 8 * Δ ≤ L) (e : Sym2 V) :
    ∑ f ∈ dependencyEdges G slot e, edgeWeight slot f ≤ 1 / 2 := by
  classical
  have h := touching_weight_le_quarter G slot L Δ hL hsize hdegree hsparse
    (edgeSlots slot e)
  have hc : ((edgeSlots slot e).card : ℝ) ≤ 2 := by
    exact_mod_cast edgeSlots_card_le_two slot e
  have hsub : ∑ f ∈ dependencyEdges G slot e, edgeWeight slot f ≤
      ∑ f ∈ touchingEdges G slot (edgeSlots slot e), edgeWeight slot f := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
    intro f hf _
    exact edgeWeight_nonneg slot f
  linarith

end TailGraph
end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_TailEvents2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
open MeasureTheory

namespace Balanced.TailGraph

variable {I : Type*} {Q : I → Type*}
variable [Fintype I] [DecidableEq I]
variable [∀ i, Fintype (Q i)] [∀ i, DecidableEq (Q i)] [∀ i, Nonempty (Q i)]
variable [∀ i, MeasurableSpace (Q i)] [∀ i, MeasurableSingletonClass (Q i)]

omit [Fintype I] [DecidableEq I] [∀ index, Fintype (Q index)]
  [∀ index, DecidableEq (Q index)] [∀ index, Nonempty (Q index)]
  [∀ index, MeasurableSpace (Q index)] [∀ index, MeasurableSingletonClass (Q index)] in
theorem avoid_eq_biInter {E : Type*} (B : E → Set (Slots.Assignment Q)) (T : Finset E) :
    CylinderConditioning.avoid B T = ⋂ e ∈ T, (B e)ᶜ := by
  ext ω
  simp [CylinderConditioning.avoid]

theorem edgeEvent_avoidance_independent {E : Type*} (edge : E → Sym2 (Sigma Q))
    (e : E) (T : Finset E)
    (hd : ∀ f ∈ T, Disjoint (edgeSlots Sigma.fst (edge e))
      (edgeSlots Sigma.fst (edge f))) :
    (Slots.law Q).real (edgeEvent Q (edge e) ∩
      CylinderConditioning.avoid (fun f => edgeEvent Q (edge f)) T) =
    (Slots.law Q).real (edgeEvent Q (edge e)) *
      (Slots.law Q).real (CylinderConditioning.avoid (fun f => edgeEvent Q (edge f)) T) := by
  rw [avoid_eq_biInter]
  exact Slots.law_real_inter_avoidance (edgeSlots Sigma.fst (edge e))
    (edgeEvent Q (edge e)) (edgeEvent_dependsOn _) T
    (fun f => edgeSlots Sigma.fst (edge f)) (fun f => edgeEvent Q (edge f))
    (fun f _ => edgeEvent_dependsOn _) hd

theorem cylinder_avoidance_independent {E : Type*} (edge : E → Sym2 (Sigma Q))
    (J : Finset I) (a : Slots.Assignment Q) (T : Finset E)
    (hd : ∀ f ∈ T, Disjoint J (edgeSlots Sigma.fst (edge f))) :
    (Slots.law Q).real (Slots.cylinder Q J a ∩
      CylinderConditioning.avoid (fun f => edgeEvent Q (edge f)) T) =
    (Slots.law Q).real (Slots.cylinder Q J a) *
      (Slots.law Q).real (CylinderConditioning.avoid (fun f => edgeEvent Q (edge f)) T) := by
  rw [avoid_eq_biInter]
  exact Slots.law_real_inter_avoidance J (Slots.cylinder Q J a)
    (Slots.cylinder_dependsOn J a) T (fun f => edgeSlots Sigma.fst (edge f))
    (fun f => edgeEvent Q (edge f)) (fun f _ => edgeEvent_dependsOn _) hd

end Balanced.TailGraph

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_TailConditioning2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
open MeasureTheory

namespace Balanced
open scoped _root_.Balanced
namespace TailConditioning

universe u v
variable {I : Type u} {Q : I → Type v}

section Graph

variable [Fintype I] [DecidableEq I] [∀ i, Fintype (Q i)]
variable [∀ i, DecidableEq (Q i)] [∀ i, Nonempty (Q i)]
variable [∀ i, MeasurableSpace (Q i)] [∀ i, MeasurableSingletonClass (Q i)]

omit [DecidableEq I] [∀ i, DecidableEq (Q i)] [∀ i, Nonempty (Q i)]
    [∀ i, MeasurableSpace (Q i)] [∀ i, MeasurableSingletonClass (Q i)] in
theorem independentTransversals_eq_avoid (G : SimpleGraph (Sigma Q)) [DecidableRel G.Adj] :
    independentTransversals Q G =
      CylinderConditioning.avoid (fun e : G.edgeSet => TailGraph.edgeEvent Q e.val) Finset.univ := by
  ext ω
  constructor
  · intro hω e he hbad
    obtain ⟨e, heG⟩ := e
    induction e using Sym2.inductionOn with
    | _ u v =>
      have hu : ω u.1 = u.2 := hbad u (Sym2.mem_mk_left _ _)
      have hv : ω v.1 = v.2 := hbad v (Sym2.mem_mk_right _ _)
      have ha := G.mem_edgeSet.mp heG
      have hn := hω u.1 v.1
      apply hn
      simpa only [hu, hv, Sigma.eta] using ha
  · intro hω i j hij
    let e : G.edgeSet := ⟨s(⟨i, ω i⟩, ⟨j, ω j⟩), G.mem_edgeSet.mpr hij⟩
    apply hω e (Finset.mem_univ e)
    intro v hv
    change v ∈ s(⟨i, ω i⟩, ⟨j, ω j⟩) at hv
    rcases Sym2.mem_iff.mp hv with rfl | rfl <;> rfl

theorem graph_nonneighbor_independence (G : SimpleGraph (Sigma Q)) [DecidableRel G.Adj]
    (e : G.edgeSet) (T : Finset G.edgeSet) (heT : e ∉ T)
    (hTN : Disjoint T (TailGraph.liftEdges G (TailGraph.dependencyEdges G Sigma.fst e.val))) :
    (Slots.law Q).real (TailGraph.edgeEvent Q e.val ∩
      CylinderConditioning.avoid (fun f : G.edgeSet => TailGraph.edgeEvent Q f.val) T) =
      (Slots.law Q).real (TailGraph.edgeEvent Q e.val) *
        (Slots.law Q).real
          (CylinderConditioning.avoid (fun f : G.edgeSet => TailGraph.edgeEvent Q f.val) T) := by
  apply TailGraph.edgeEvent_avoidance_independent (fun f : G.edgeSet => f.val) e T
  intro f hf
  by_contra hdisj
  have hfe : f.val ≠ e.val := by
    intro heq
    have hfe' : f = e := Subtype.ext heq
    exact heT (hfe' ▸ hf)
  have hfN : f ∈ TailGraph.liftEdges G (TailGraph.dependencyEdges G Sigma.fst e.val) := by
    rw [TailGraph.mem_liftEdges, TailGraph.mem_dependencyEdges_iff]
    exact ⟨G.mem_edgeFinset.mpr f.property, hfe, hdisj⟩
  exact Finset.disjoint_left.mp hTN hf hfN

theorem graph_cylinder_independence (G : SimpleGraph (Sigma Q)) [DecidableRel G.Adj]
    (J : Finset I) (a : Slots.Assignment Q) :
    (Slots.law Q).real (Slots.cylinder Q J a ∩
      CylinderConditioning.avoid (fun f : G.edgeSet => TailGraph.edgeEvent Q f.val)
        (Finset.univ \ TailGraph.liftEdges G (TailGraph.touchingEdges G Sigma.fst J))) =
    (Slots.law Q).real (Slots.cylinder Q J a) *
      (Slots.law Q).real (CylinderConditioning.avoid
        (fun f : G.edgeSet => TailGraph.edgeEvent Q f.val)
        (Finset.univ \ TailGraph.liftEdges G (TailGraph.touchingEdges G Sigma.fst J))) := by
  apply TailGraph.cylinder_avoidance_independent (fun f : G.edgeSet => f.val) J a
  intro f hf
  have hfnot := (Finset.mem_sdiff.mp hf).2
  apply Finset.disjoint_left.mpr
  intro i hiJ hie
  apply hfnot
  rw [TailGraph.mem_liftEdges]
  exact Finset.mem_filter.mpr ⟨G.mem_edgeFinset.mpr f.property, ⟨i, hiJ, hie⟩⟩

end Graph

end TailConditioning
end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Profiles_ProfileEmpirical
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Finset

namespace Balanced
open scoped _root_.Balanced

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [Fintype F] in

theorem sum_lineMultiplicity (E : Finset (Line F)) (U : Finset (Point F)) :
    (∑ x ∈ U, lineMultiplicity E x) =
      ∑ l ∈ E, (U.filter (fun x => OnLine x l)).card := by
  classical
  simp only [lineMultiplicity, Finset.card_eq_sum_ones, Finset.sum_filter]
  exact Finset.sum_comm

omit [Field F] in

theorem profile_deletionSet_card (k : ℕ) (D : Finset (Line F)) (hD : IsDeletionSet k D) :
    D.card = k * (Fintype.card F + 1) := by
  classical
  have h := Finset.card_eq_sum_card_fiberwise
    (s := D) (t := (Finset.univ : Finset (Direction F))) (f := Prod.fst)
    (fun _ _ => Finset.mem_univ _)
  rw [h]
  change (∑ d : Direction F, (D.filter (fun l => l.1 = d)).card) = _
  unfold IsDeletionSet at hD
  simp_rw [hD]
  simp [Fintype.card_option, mul_comm]

end Balanced

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Selection_OccupancyFailureClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Balanced
open scoped _root_.Balanced

open Filter MeasureTheory
open scoped Topology

universe u

def survivingLineOccupancy {F : Type u} [Field F] [Fintype F] [DecidableEq F]
    (D : Finset (Line F)) (l : Line F) : ℝ :=
  ((linePoints l ∩ uncoveredBy D).card : ℝ) / (Fintype.card F : ℝ)

end Balanced

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Selection_SelectionPostcheckTail
attribute [-instance] _root_.OAI.Balanced.Selection.Process.snapshotPathLaw_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators Classical

namespace Balanced.Selection.Process

noncomputable section

variable {I V : Type*} [Fintype I] [Fintype V]

def postcheckTail (p : Parameters) (q : ℕ) : ℝ :=
  (Real.exp 1 * postcheckMean p / (BernoulliTail.thinningCutoff (1 / 8) q : ℝ)) ^
    BernoulliTail.thinningCutoff (1 / 8) q

end
end Balanced.Selection.Process

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Selection_SelectionSourceConcentration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
namespace Balanced.Selection.Process
attribute [local instance] Classical.propDecidable
variable {I V : Type*} [Fintype I] [Fintype V]

def sourceDegreeCensorBound (p : Parameters) (q : ℕ) : ℝ :=
  2 * (q : ℝ) ^ (1 / 8 : ℝ) /
    (p.a * p.smin * p.c * (q : ℝ) ^ 2) + postcheckTail p q

end Balanced.Selection.Process

end

end OAI
end


