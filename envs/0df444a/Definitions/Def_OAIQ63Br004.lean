-- Prove2me | Definitions.Def_OAIQ63Br004
-- name    : OAIQ63Br004
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T00:09:24.78236+00:00
-- url     : https://prove2.me/theorems/df894a89-75c1-4947-a53c-94698db54e15
-- title:
--   Definitions bundle OAIQ63Br004 of the split of OpenAI, Balanced counterexamples to Ryser's conjecture at prime orders (result family 162)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Balanced.main_result`, carved from OpenAI's openai/math development (OpenAI, *Balanced counterexamples to Ryser's conjecture at prime orders (result family 162)*, OpenAI Math Release, September 27, 2026, result family 162, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 66 declarations of OpenAI's Lean: 35 definitions, 1 inductive type or structure, 4 instances and 26 theorems. The definitions and types are `OAI.Balanced.Local.AlignedGlobal.lineScalar`, `OAI.Balanced.ProfileClassMargin.Object`, `OAI.Balanced.SelectedDeletion.fixedLawOfSelection`, `OAI.Balanced.SelectedDeletionResult`, `OAI.Balanced.Selection.Process.Tail.completionOutputLaw`, `OAI.Balanced.Selection.Process.UniformConcentrationEstimate`, `OAI.Balanced.Selection.Process.UniformOccupancyEstimate`, `OAI.Balanced.Selection.Process.UniformSuccessEstimate`, `OAI.Balanced.Selection.Process.finalLaw`, `OAI.Balanced.Selection.Process.outputLaw`, `OAI.Balanced.Selection.Process.sourceTerminalLaw`, `OAI.Balanced.Selection.Process.sourceTerminalOutcomeLaw`, `OAI.Balanced.Selection.Process.terminalLaw`, `OAI.Balanced.Selection.Process.terminalOutcomeLaw`, `OAI.Balanced.StabilityPolynomial.redeiPolynomial`, `OAI.Balanced.StabilityTangents.tangents`, `OAI.Balanced.UnusedOffsetIncidence.NoncollinearTripleInPair`, `OAI.Balanced.UnusedOffsetIncidence.PairCover`, `OAI.Balanced.UnusedOffsetIncidence.TripleCovered`, `OAI.Balanced.UnusedOffsetIncidence.TwoOneCover`, `OAI.Balanced.UnusedOffsetIncidence.constituent`, `OAI.Balanced.affineDualPoint`, `OAI.Balanced.boundedEmpiricalProfileMeasure`, `OAI.Balanced.boundedLineProfile`, `OAI.Balanced.boundedPlaneProfile`, `OAI.Balanced.dualPointSet`, `OAI.Balanced.linesThroughEquiv`, `OAI.Balanced.multiplicityFailureClass`, `OAI.Balanced.occupancyFailureClass`, `OAI.Balanced.projectiveDuality`, `OAI.Balanced.projectiveJoin`, `OAI.Balanced.projectiveLinePoints`, `OAI.Balanced.projectivePencil`, `OAI.Balanced.skewProjective`, `OAI.Balanced.skewThroughExcept`, `OAI.Balanced.tupleCodeTargetMass`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `BalancedRyser_Candidates_SelectedCandidateFixedLaw`, `BalancedRyser_Deletion_RobustDeletionAssembly`, `BalancedRyser_Deletion_SelectedDeletion`, `BalancedRyser_Incidence_AffineIncidence`, `BalancedRyser_Incidence_Projective`, `BalancedRyser_Incidence_Projective2`, `BalancedRyser_Incidence_ProjectiveIncidence`, `BalancedRyser_Incidence_RedeiPolynomial`, `BalancedRyser_Incidence_StabilitySkewCountLemmas`, `BalancedRyser_Incidence_StabilityTangents`, `BalancedRyser_Incidence_UnusedOffsetIncidence`, `BalancedRyser_Local_AlignedGlobalHistory`, `BalancedRyser_Local_ReuseExtensionSum`, `BalancedRyser_Probability_TailConditioning2`, `BalancedRyser_Profiles_ProfileClassMargin`, `BalancedRyser_Profiles_ProfileEmpirical`, `BalancedRyser_Profiles_ProfileEmpiricalMeasure`, `BalancedRyser_Selection_OccupancyFailureClass`, `BalancedRyser_Selection_SelectionFinalLaw`, `BalancedRyser_Selection_SelectionSuccessUniform`, `BalancedRyser_Selection_SelectionTailCompletion`, `BalancedRyser_Selection_SelectionTailPotential`, `BalancedRyser_Selection_SelectionUniformAssembly`.
--
--   **Imports.** It imports the bundles `OAIQ63Br002` and `OAIQ63Br003` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI.Balanced.Selection.Process.selectionStatement_of_uniform_concentration_occupancy` and `OAI.Balanced.deletion_domination`; the proofs of `OAI.Balanced.Local.injectiveUsedEventsEstimate_proof`, `OAI.Balanced.ProfileCountingAssembly.profileCounting_of_sourceRareTailBound`, `OAI.Balanced.ProfileScheduledFiniteComparison.eventually_finiteDetection_of_profileClass`, `OAI.Balanced.Selection.Process.selectionStatement_of_uniform_concentration_occupancy`, `OAI.Balanced.deletion_domination`, `OAI.Balanced.deterministic_reduction`, `OAI.Balanced.main_result`, `OAI.Balanced.pencilReuse_proof`, `OAI.Balanced.pencil_local`, `OAI.Balanced.robustDeletion_of_profileCounting` and `OAI.Balanced.robust_deletion`.
-- source:
--   OpenAI, Balanced counterexamples to Ryser's conjecture at prime orders (result family 162), OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 162; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Balanced-Counterexamples-to-Rysers-Conjecture-at-Prime-Orders-September-27-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ63Br002
import Definitions.Def_OAIQ63Br003

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_AffineIncidence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced
open scoped _root_.Balanced

variable {F : Type*} [Field F]

section Finite

variable [Fintype F] [DecidableEq F]

def linesThroughEquiv (p : Point F) : {l : Line F // OnLine p l} ≃ Direction F where
  toFun l := l.val.1
  invFun d := ⟨lineThrough d p, onLine_lineThrough d p⟩
  left_inv l := by
    apply Subtype.ext
    exact (line_eq_lineThrough p l.val l.property).symm
  right_inv _ := rfl

theorem linePoints_inter_card_le_one (l m : Line F) (hne : l ≠ m) :
    (linePoints l ∩ linePoints m).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro p hp r hr
  simp only [Finset.mem_inter, linePoints, Finset.mem_filter,
    Finset.mem_univ, true_and] at hp hr
  exact common_point_eq_of_lines_ne l m hne p r hp.1 hp.2 hr.1 hr.2

end Finite

end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Deletion_SelectedDeletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Filter
open scoped Topology
attribute [local instance] Classical.propDecidable

namespace Balanced
open scoped _root_.Balanced

universe u

def SelectedDeletionResult : Prop :=
  ∃ c C K ρ a₀ C₀ : ℝ, ∃ ε : ℕ → ℝ, ∃ N : ℕ,
    0 < c ∧ 0 < C ∧ 1 ≤ K ∧ 0 < ρ ∧ ρ < 1 ∧
    0 < a₀ ∧ 0 < C₀ ∧ 4 ≤ N ∧
    (∀ q, 0 ≤ ε q) ∧ Tendsto ε atTop (𝓝 0) ∧
    ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
      N ≤ Fintype.card F →
      ∃ κ : SelectedDeletion.Kernel F,
        SelectedDeletion.IsExperiment κ c C ∧
        (∀ M, SelectedDeletion.InitialGood M c C →
          1 - ε (Fintype.card F) ≤ SelectedDeletion.fixedSuccessMass κ M) ∧
        (∀ M (J : Finset (Slot F)) (prescribed : SelectedDeletion.Output F),
          SelectedDeletion.fixedCylinderMass κ M J prescribed ≤
            (K / (Fintype.card F : ℝ)) ^ J.card) ∧
        a₀ ≤ SelectedDeletion.successMass κ ∧
        SelectedDeletion.occupancyFailureMass κ ρ ≤ ε (Fintype.card F) ∧
        ∃ Q : PMF (DeletionSet F 3),
          SelectedDeletion.RealizesConditionalLaw κ Q ∧ DeletionDominated 3 C₀ Q

end Balanced

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_SelectedCandidateFixedLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.SelectedDeletion

noncomputable section
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [eqF : DecidableEq F]

attribute [local instance] OAI.Balanced.SelectedDeletion.instDecidableEqSlot
def fixedLawOfSelection (M : MergedPairs F) {c C K ρ ε : ℝ}
    (hc : 0 < c) (hgood : CandidateGraphGood M c C) (hd : DistinctConstituents M)
    (J : AvailableCandidate M → Finset (CandidateVertex F))
    (law : Selection.OutputLaw (candidateSelectionInput M J))
    (hsuccess : 1 - ε ≤ Selection.successMass law)
    (hcylinder : ∀ (S : Finset (Slot F)) (a : Slot F → AvailableCandidate M),
      Selection.cylinderMass law S a ≤ (K / (Fintype.card F : ℝ)) ^ S.card)
    (hoccupancy : Selection.occupancyFailureMass law (coordinatePlane F)
      (fun v : AvailableCandidate M => candidateLine v.val) (candidateTrackedSets M) ρ ≤ ε) :
    FixedLaw M K ρ ε := by
  cases Subsingleton.elim eqF (Classical.decEq F)
  exact {
  weight := law.labelWeight (fun _ v => v.val.2)
  nonnegative := Selection.labelWeight_nonneg law _
  mass_le_one := by
    convert Selection.sum_labelWeight_le_one law (fun _ v => v.val.2) using 1
    all_goals try with_reducible_and_instances rfl
    apply Finset.sum_congr
    · ext f; simp
    · intro f _; rfl
  supported := by
    intro f hf
    obtain ⟨a, ha, hpos⟩ := FinitePushforward.exists_positive_preimage
      (FinitePushforward.mapChoices (fun (_ : Slot F) (v : AvailableCandidate M) => v.val.2))
      law.weight law.nonnegative f hf
    have hs := candidateSelection_configuration_of_transversal M J a hd (law.supported a hpos)
    exact ha ▸ hs
  success_lower := by
    convert hsuccess using 1
    all_goals try with_reducible_and_instances rfl
    convert Selection.sum_labelWeight law (fun _ v => v.val.2) using 1
    all_goals try with_reducible_and_instances rfl
    apply Finset.sum_congr
    · ext f; simp
    · intro f _; rfl
  cylinder_le := by
    intro S f
    convert candidateSelection_label_cylinder M hc hgood J law hcylinder S f using 1
    all_goals try with_reducible_and_instances rfl
    apply Finset.sum_congr
    · ext t; simp
    · intro t _; split_ifs <;> rfl
  occupancy_le := by
    have hevent := candidateSelection_label_event M J law
      (fun f => ¬ (selectedConfiguration M f).Occupancy
        ρ ⌈Real.log (Fintype.card F : ℝ)⌉₊)
    calc
      _ = ∑ a : Slot F → AvailableCandidate M,
          if ¬ (selectedConfiguration M (fun s => (a s).val.2)).Occupancy
            ρ ⌈Real.log (Fintype.card F : ℝ)⌉₊ then law.weight a else 0 := by
        convert hevent using 1
        all_goals try with_reducible_and_instances rfl
        all_goals
          apply Finset.sum_congr
          · ext t; simp
          · intro t _
            simp only [configuration, selectedConfiguration]
            exact (ite_eq_ite _ _ _).mpr trivial
      _ ≤ Selection.occupancyFailureMass law (coordinatePlane F)
          (fun v : AvailableCandidate M => candidateLine v.val) (candidateTrackedSets M) ρ :=
        by
          convert candidateSelection_occupancy_failure_mass_le hgood hd J law using 1
          all_goals try with_reducible_and_instances rfl
          apply Finset.sum_congr
          · ext a; simp
          · intro a _; split_ifs <;> rfl
      _ ≤ ε := hoccupancy

  }

end
end Balanced.SelectedDeletion

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Deletion_RobustDeletionAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced
open scoped _root_.Balanced

universe u

def multiplicityFailureClass (k : ℕ) (τ : ℝ) : ProfileClass.{u} :=
  fun _ _ _ _ D C => IsDeletionSet k D ∧ C = ∅ ∧ τ ≤ deletionMultiplicityTV k D

end Balanced

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

def affineDualPoint (l : Line F) : ProjectivePoint F := dualPoint (some l)

variable [Fintype F] [DecidableEq F]

instance instDecidableProjectiveIncident (P : ProjectivePoint F) (l : ProjectiveLine F) :
    Decidable (ProjectiveIncident P l) := by
  cases l with
  | some l => exact inferInstanceAs (Decidable (ThroughProjective l P))
  | none => cases P <;> simp only [ProjectiveIncident] <;> infer_instance

def dualPointSet (C : Finset (Line F)) : Finset (ProjectivePoint F) :=
  C.image affineDualPoint

def skewProjective (B : Finset (ProjectivePoint F)) : Finset (ProjectiveLine F) :=
  Finset.univ.filter (fun l => ∀ P ∈ B, ¬ ProjectiveIncident P l)

end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_Projective2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced
open scoped _root_.Balanced

variable {F : Type*} [Field F]

def projectiveDuality : ProjectivePoint F ≃ ProjectiveLine F where
  toFun := dualLine
  invFun := dualPoint
  left_inv := dualPoint_dualLine
  right_inv := dualLine_dualPoint

end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_ProjectiveIncidence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced
open scoped _root_.Balanced

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def projectiveLinePoints (l : ProjectiveLine F) : Finset (ProjectivePoint F) :=
  Finset.univ.filter (fun P => ProjectiveIncident P l)

def projectivePencil (P : ProjectivePoint F) : Finset (ProjectiveLine F) :=
  Finset.univ.filter (ProjectiveIncident P)

@[simp] theorem mem_projectiveLinePoints (l : ProjectiveLine F) (P : ProjectivePoint F) :
    P ∈ projectiveLinePoints l ↔ ProjectiveIncident P l := by
  simp [projectiveLinePoints]

@[simp] theorem mem_projectivePencil (P : ProjectivePoint F) (l : ProjectiveLine F) :
    l ∈ projectivePencil P ↔ ProjectiveIncident P l := by
  simp [projectivePencil]

def projectiveJoin : ProjectivePoint F → ProjectivePoint F → ProjectiveLine F
  | Sum.inl p, Sum.inl r => some (joiningLine p r)
  | Sum.inl p, Sum.inr d => some (lineThrough d p)
  | Sum.inr d, Sum.inl p => some (lineThrough d p)
  | Sum.inr _, Sum.inr _ => none

omit [Fintype F] in
@[simp] theorem projectiveIncident_join_left (P Q : ProjectivePoint F) :
    ProjectiveIncident P (projectiveJoin P Q) := by
  cases P <;> cases Q <;>
    simp [projectiveJoin, ProjectiveIncident, ThroughProjective]

omit [Fintype F] in
@[simp] theorem projectiveIncident_join_right (P Q : ProjectivePoint F) :
    ProjectiveIncident Q (projectiveJoin P Q) := by
  cases P <;> cases Q <;>
    simp [projectiveJoin, ProjectiveIncident, ThroughProjective]

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

noncomputable def redeiPolynomial (U : Finset (Point F)) : MvPolynomial (Fin 2) F :=
  ∏ p ∈ U, redeiFactor p

end Balanced.StabilityPolynomial

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_StabilitySkewCountLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace Balanced
open scoped _root_.Balanced

open scoped BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def skewThroughExcept (B : Finset (ProjectivePoint F)) (ell : ProjectiveLine F)
    (P : ProjectivePoint F) : Finset (ProjectiveLine F) :=
  ((projectivePencil P).erase ell).filter (fun l => l ∈ skewProjective B)

@[simp] theorem mem_skewThroughExcept (B : Finset (ProjectivePoint F))
    (ell : ProjectiveLine F) (P : ProjectivePoint F) (l : ProjectiveLine F) :
    l ∈ skewThroughExcept B ell P ↔
      l ≠ ell ∧ ProjectiveIncident P l ∧ l ∈ skewProjective B := by
  simp [skewThroughExcept, and_assoc]

end Balanced

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_StabilityTangents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.StabilityTangents

open scoped BigOperators
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def tangents (B : Finset (ProjectivePoint F)) : Finset (ProjectiveLine F) :=
  Finset.univ.filter fun l => (B.filter (fun P => ProjectiveIncident P l)).card = 1

@[simp] theorem mem_tangents (B : Finset (ProjectivePoint F)) (l : ProjectiveLine F) :
    l ∈ tangents B ↔ (B.filter (fun P => ProjectiveIncident P l)).card = 1 := by
  simp [tangents]

end Balanced.StabilityTangents

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

def constituent (D : Finset (Direction F)) (o : Offsets D)
    (d : D) (s : Bool) : Line F := (d.1, o d s)

def PairCover (D : Finset (Direction F)) (x y z : Point F)
    (s : Bool) (o : Offsets D) : Prop :=
  ∃ d : D, OnLine x (constituent D o d s) ∧
    OnLine y (constituent D o d s) ∧ OnLine z (constituent D o d (!s))

def TwoOneCover (D : Finset (Direction F)) (x y z : Point F)
    (o : Offsets D) : Prop := ∃ s : Bool, PairCover D x y z s o

def TripleCovered (D : Finset (Direction F)) (x y z : Point F)
    (o : Offsets D) : Prop :=
  ∃ d : D, (∃ s : Bool, OnLine x (constituent D o d s)) ∧
    (∃ s : Bool, OnLine y (constituent D o d s)) ∧
    (∃ s : Bool, OnLine z (constituent D o d s))

def NoncollinearTripleInPair (D : Finset (Direction F))
    (P : Finset (Point F)) (o : Offsets D) : Prop :=
  ∃ x ∈ P, ∃ y ∈ P, ∃ z ∈ P,
    Noncollinear x y z ∧ TripleCovered D x y z o

end Balanced.UnusedOffsetIncidence

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_AlignedGlobalHistory
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Local.AlignedGlobal

open RootChildPartition TupleAlignment PrescribedGeometry
noncomputable section
open scoped Classical

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {b κ : ℕ}

def lineScalar (g : Direction F) (x : Point F) : F :=
  match g with | none => x.2 | some _ => x.1

end
end Balanced.Local.AlignedGlobal

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Local_ReuseExtensionSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced
open scoped _root_.Balanced
open PartialAlignment

noncomputable section
open scoped Classical

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def tupleCodeTargetMass (old : Finset (Direction F)) (M : MergedPairs F)
    (p : Point F) (c : (Fin 4 → Direction F) × (Fin 4 → Bool)) : ℝ :=
  if hinj : Function.Injective c.1 then
    ∑ g ∈ (Finset.univ.filter (fun g : Direction F => ∀ i, c.1 i ≠ g)),
      externalAlignmentProbability c.1
        (fun i h => cyclic_index_ne_next i (hinj h)) c.2 p g
        (oldGeneratorIndices ⟨c.1, c.2⟩ old) (fun i => M (c.1 i))
  else 0

end
end Balanced

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

theorem tail_conditioning_of_bounds (G : SimpleGraph (Sigma Q)) [DecidableRel G.Adj]
    (hno : TailGraph.NoWithinSlotEdges G Sigma.fst)
    (L Δ : ℕ) (hL : 3 ≤ L) (hsize : ∀ i, L ≤ Fintype.card (Q i))
    (hdegree : ∀ u, G.degree u ≤ Δ) (hsparse : 8 * Δ ≤ L) :
    0 < (Slots.law Q).real (independentTransversals Q G) ∧
      ∀ (J : Finset I) (a : Slots.Assignment Q),
        conditionalCylinder Q G J a ≤
          Real.exp ((J.card : ℝ) / 2) * ∏ i ∈ J, (Fintype.card (Q i) : ℝ)⁻¹ := by
  classical
  let B : G.edgeSet → Set (Slots.Assignment Q) := fun e => TailGraph.edgeEvent Q e.val
  let N : G.edgeSet → Finset G.edgeSet :=
    fun e => TailGraph.liftEdges G (TailGraph.dependencyEdges G Sigma.fst e.val)
  let x : G.edgeSet → ℝ := fun e => TailGraph.edgeWeight Sigma.fst e.val
  have hslot : ∀ i, L ≤ TailGraph.slotSize (Sigma.fst : Sigma Q → I) i := by
    intro i
    rw [slotSize_sigma]
    exact hsize i
  have hx0 : ∀ e, 0 ≤ x e := fun e => TailGraph.edgeWeight_nonneg Sigma.fst e.val
  have hxhalf : ∀ e, x e ≤ 1 / 2 := fun e =>
    TailGraph.edgeWeight_le_half Sigma.fst (fun i => hL.trans (hslot i)) e.val
  have hB : ∀ e, MeasurableSet (B e) := fun e => (Set.toFinite (B e)).measurableSet
  have hp : ∀ e, (Slots.law Q).real (B e) ≤ x e / 2 := by
    intro e
    exact (TailGraph.law_real_edgeEvent G hno e.val e.property).le
  have hweight : ∀ e, ∑ f ∈ N e, x f ≤ 1 / 2 := by
    intro e
    dsimp [N, x]
    rw [TailGraph.sum_liftEdges G _ (TailGraph.dependencyEdges_subset G Sigma.fst e.val)]
    exact TailGraph.dependency_weight_le_half G Sigma.fst L Δ (by omega)
      hslot hdegree hsparse e.val
  have hind : ∀ e T, e ∉ T → Disjoint T (N e) →
      (Slots.law Q).real (B e ∩ CylinderConditioning.avoid B T) =
        (Slots.law Q).real (B e) * (Slots.law Q).real (CylinderConditioning.avoid B T) := by
    intro e T heT hTN
    exact graph_nonneighbor_independence G e T heT hTN
  have hlocal := CylinderConditioning.local_lemma_of_half_weight
    (Slots.law Q) B hB N x hx0 hxhalf hp hweight hind
  constructor
  · rw [independentTransversals_eq_avoid]
    exact (hlocal Finset.univ).1
  · intro J a
    let U := TailGraph.liftEdges G (TailGraph.touchingEdges G Sigma.fst J)
    let T : Finset G.edgeSet := Finset.univ \ U
    have hTU : T ∪ U = Finset.univ := Finset.sdiff_union_of_subset (Finset.subset_univ U)
    have hd : Disjoint T U := by
      exact Finset.disjoint_left.mpr (fun e heT heU => (Finset.mem_sdiff.mp heT).2 heU)
    have hC : (Slots.law Q).real (Slots.cylinder Q J a ∩ CylinderConditioning.avoid B T) =
        (Slots.law Q).real (Slots.cylinder Q J a) *
          (Slots.law Q).real (CylinderConditioning.avoid B T) :=
      graph_cylinder_independence G J a
    have hsum : ∑ e ∈ U, x e ≤ (J.card : ℝ) / 4 := by
      dsimp [U, x]
      rw [TailGraph.sum_liftEdges G _ (TailGraph.touchingEdges_subset G Sigma.fst J)]
      exact TailGraph.touching_weight_le_quarter G Sigma.fst L Δ (by omega)
        hslot hdegree hsparse J
    have hc := (CylinderConditioning.local_lemma_cylinder_exp (Slots.law Q)
      B hB N x hx0 hxhalf hp hweight hind (Slots.cylinder Q J a) T U hd hC
      (J.card : ℝ) hsum).2
    rw [hTU] at hc
    change (Slots.law Q).real (Slots.cylinder Q J a ∩
      CylinderConditioning.avoid (fun e : G.edgeSet => TailGraph.edgeEvent Q e.val) Finset.univ) /
      (Slots.law Q).real (CylinderConditioning.avoid
        (fun e : G.edgeSet => TailGraph.edgeEvent Q e.val) Finset.univ) ≤ _ at hc
    rw [← independentTransversals_eq_avoid G, Slots.law_real_cylinder] at hc
    exact hc

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

theorem planeProfile_nonneg (D C : Finset (Line F)) (ij : ℕ × ℕ) :
    0 ≤ planeProfile D C ij := by
  unfold planeProfile
  positivity

theorem planeProfile_hasSum (D C : Finset (Line F)) :
    HasSum (planeProfile D C) 1 := by
  have h := hasSum_normalized_card_fibers
    (Finset.univ : Finset (Point F)) Finset.univ_nonempty
    (fun x => (lineMultiplicity D x, lineMultiplicity C x))
  convert! h using 1
  all_goals try with_reducible_and_instances rfl
  funext ij
  rcases ij with ⟨i, j⟩
  simp only [planeProfile, Prod.mk.injEq, Finset.card_univ, Point,
    Fintype.card_prod, Nat.cast_mul, pow_two]

theorem lineProfile_nonneg (D C : Finset (Line F)) (l : Line F) (ij : ℕ × ℕ) :
    0 ≤ lineProfile D C l ij := by
  unfold lineProfile
  positivity

theorem lineProfile_hasSum_of_card (D C : Finset (Line F)) (l : Line F)
    (hcard : (linePoints l).card = Fintype.card F) :
    HasSum (lineProfile D C l) 1 := by
  have hnonempty : (linePoints l).Nonempty := by
    apply Finset.card_pos.mp
    rw [hcard]
    exact Fintype.card_pos
  have h := hasSum_normalized_card_fibers (linePoints l) hnonempty
    (fun x => (lineMultiplicity D x, lineMultiplicity C x))
  convert! h using 1
  all_goals try with_reducible_and_instances rfl
  funext ij
  rcases ij with ⟨i, j⟩
  simp only [lineProfile, Prod.mk.injEq, hcard]

theorem lineProfile_hasSum (D C : Finset (Line F)) (l : Line F) :
    HasSum (lineProfile D C l) 1 :=
  lineProfile_hasSum_of_card D C l (linePoints_card l)

theorem planeProfile_weighted_hasSum (D C : Finset (Line F)) (w : ℕ × ℕ → ℝ) :
    HasSum (fun ij => w ij * planeProfile D C ij)
      ((∑ x : Point F, w (lineMultiplicity D x, lineMultiplicity C x)) /
        (Fintype.card F : ℝ) ^ 2) := by
  have h := (hasSum_weighted_card_fibers (Finset.univ : Finset (Point F))
    (fun x => (lineMultiplicity D x, lineMultiplicity C x)) w).div_const
      ((Fintype.card F : ℝ) ^ 2)
  convert! h using 1
  all_goals try with_reducible_and_instances rfl
  funext ij
  rcases ij with ⟨i, j⟩
  simp only [planeProfile, Prod.mk.injEq]
  ring

theorem lineProfile_weighted_hasSum (D C : Finset (Line F)) (l : Line F)
    (w : ℕ × ℕ → ℝ) :
    HasSum (fun ij => w ij * lineProfile D C l ij)
      ((∑ x ∈ linePoints l, w (lineMultiplicity D x, lineMultiplicity C x)) /
        (Fintype.card F : ℝ)) := by
  have h := (hasSum_weighted_card_fibers (linePoints l)
    (fun x => (lineMultiplicity D x, lineMultiplicity C x)) w).div_const
      (Fintype.card F : ℝ)
  convert! h using 1
  all_goals try with_reducible_and_instances rfl
  funext ij
  rcases ij with ⟨i, j⟩
  simp only [lineProfile, Prod.mk.injEq]
  ring

theorem sum_univ_lineMultiplicity (E : Finset (Line F)) :
    (∑ x : Point F, lineMultiplicity E x) = E.card * Fintype.card F := by
  rw [sum_lineMultiplicity]
  change (∑ l ∈ E, (linePoints l).card) = _
  simp [linePoints_card]

theorem planeProfile_firstMoment_hasSum (D C : Finset (Line F)) :
    HasSum (fun ij => ((ij.1 + ij.2 : ℕ) : ℝ) * planeProfile D C ij)
      (((D.card : ℝ) + C.card) / (Fintype.card F : ℝ)) := by
  have h := planeProfile_weighted_hasSum D C (fun ij => ((ij.1 + ij.2 : ℕ) : ℝ))
  have hq : (Fintype.card F : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  convert! h using 1
  all_goals try with_reducible_and_instances rfl
  simp only [Nat.cast_add, Finset.sum_add_distrib, ← Nat.cast_sum,
    sum_univ_lineMultiplicity, Nat.cast_mul]
  field_simp

theorem planeProfile_isBounded (k : ℕ) (D C : Finset (Line F))
    (hD : IsDeletionSet k D) (hC : C.card ≤ Fintype.card F) :
    IsBoundedProfile (2 * (k : ℝ) + 4) (planeProfile D C) := by
  have hm := planeProfile_firstMoment_hasSum D C
  refine ⟨planeProfile_nonneg D C, planeProfile_hasSum D C, hm.summable, ?_⟩
  rw [hm.tsum_eq]
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hqone : (1 : ℝ) ≤ Fintype.card F := by
    exact_mod_cast Fintype.card_pos (α := F)
  have hc : (C.card : ℝ) ≤ Fintype.card F := by exact_mod_cast hC
  have hd : (D.card : ℝ) = (k : ℝ) * ((Fintype.card F : ℝ) + 1) := by
    exact_mod_cast profile_deletionSet_card k D hD
  rw [hd]
  apply (div_le_iff₀ hq).2
  have hkq : 0 ≤ (k : ℝ) * ((Fintype.card F : ℝ) - 1) :=
    mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr hqone)
  nlinarith

theorem sum_on_line_lineMultiplicity_le (E : Finset (Line F)) (l : Line F) :
    (∑ x ∈ linePoints l, lineMultiplicity E x) ≤ Fintype.card F + E.card := by
  classical
  rw [sum_lineMultiplicity]
  have hfilter (m : Line F) :
      (linePoints l).filter (fun x => OnLine x m) = linePoints l ∩ linePoints m := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_inter, linePoints,
      Finset.mem_univ, true_and]
  simp_rw [hfilter]
  calc
    (∑ m ∈ E, (linePoints l ∩ linePoints m).card) ≤
        ∑ m ∈ E, ((if m = l then Fintype.card F else 0) + 1) := by
      apply Finset.sum_le_sum
      intro m hm
      by_cases hml : m = l
      · subst m
        simp [linePoints_card]
      · simp only [ite_eq_right hml, zero_add]
        exact linePoints_inter_card_le_one l m (Ne.symm hml)
    _ = (if l ∈ E then Fintype.card F else 0) + E.card := by
      simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_const,
        Nat.smul_one_eq_cast, Nat.cast_id]
    _ ≤ Fintype.card F + E.card := by
      split_ifs <;> omega

theorem lineProfile_isBounded (k : ℕ) (D C : Finset (Line F)) (l : Line F)
    (hD : IsDeletionSet k D) (hC : C.card ≤ Fintype.card F) :
    IsBoundedProfile (2 * (k : ℝ) + 4) (lineProfile D C l) := by
  have hm := lineProfile_weighted_hasSum D C l
    (fun ij => ((ij.1 + ij.2 : ℕ) : ℝ))
  refine ⟨lineProfile_nonneg D C l, lineProfile_hasSum D C l, hm.summable, ?_⟩
  rw [hm.tsum_eq]
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hqone : (1 : ℝ) ≤ Fintype.card F := by
    exact_mod_cast Fintype.card_pos (α := F)
  have hc : (C.card : ℝ) ≤ Fintype.card F := by exact_mod_cast hC
  have hd : (D.card : ℝ) = (k : ℝ) * ((Fintype.card F : ℝ) + 1) := by
    exact_mod_cast profile_deletionSet_card k D hD
  have hsd : (∑ x ∈ linePoints l, (lineMultiplicity D x : ℝ)) ≤
      (Fintype.card F : ℝ) + D.card := by
    exact_mod_cast sum_on_line_lineMultiplicity_le D l
  have hsc : (∑ x ∈ linePoints l, (lineMultiplicity C x : ℝ)) ≤
      (Fintype.card F : ℝ) + C.card := by
    exact_mod_cast sum_on_line_lineMultiplicity_le C l
  simp only [Nat.cast_add, Finset.sum_add_distrib]
  apply (div_le_iff₀ hq).2
  have hkq : 0 ≤ (k : ℝ) * ((Fintype.card F : ℝ) - 1) :=
    mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr hqone)
  nlinarith

end Balanced

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Profiles_ProfileEmpiricalMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Finset MeasureTheory Filter
open scoped NNReal Topology

namespace Balanced
open scoped _root_.Balanced

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem isBoundedProfile_iff_mem_profiles (M : ℝ) (P : Profile) :
    IsBoundedProfile M P ↔ P ∈ ProfileMomentCompactness.profiles M := by
  rw [ProfileMomentCompactness.mem_profiles_iff]
  simp only [IsBoundedProfile, ProfileMomentCompactness.weight, Nat.cast_add]

def boundedLineProfile (k : ℕ) (D C : Finset (Line F)) (l : Line F)
    (hD : IsDeletionSet k D) (hC : C.card ≤ Fintype.card F) :
    BoundedProfile (2 * (k : ℝ) + 4) :=
  ⟨lineProfile D C l, (isBoundedProfile_iff_mem_profiles _ _).mp
    (lineProfile_isBounded k D C l hD hC)⟩

def boundedEmpiricalProfileMeasure (k : ℕ) (D C E : Finset (Line F))
    (hD : IsDeletionSet k D) (hC : C.card ≤ Fintype.card F) :
    FiniteMeasure (BoundedProfile (2 * (k : ℝ) + 4)) := by
  let a : ℝ≥0 := ⟨(Fintype.card F : ℝ)⁻¹, by positivity⟩
  let ν : FiniteMeasure (BoundedProfile (2 * (k : ℝ) + 4)) :=
    ∑ l ∈ E, ⟨Measure.dirac (boundedLineProfile k D C l hD hC), inferInstance⟩
  exact a • ν

def boundedPlaneProfile (k : ℕ) (D C : Finset (Line F))
    (hD : IsDeletionSet k D) (hC : C.card ≤ Fintype.card F) :
    BoundedProfile (2 * (k : ℝ) + 4) :=
  ⟨planeProfile D C, (isBoundedProfile_iff_mem_profiles _ _).mp
    (planeProfile_isBounded k D C hD hC)⟩

end Balanced

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Profiles_ProfileClassMargin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter MeasureTheory
open scoped Topology

namespace Balanced.ProfileClassMargin

open ProfileDetection ProfileDetectionLimit ProfileParameterLaw

universe u

structure Object (A : ProfileClass.{u}) where
  Carrier : Type u
  field : Field Carrier
  fintype : Fintype Carrier
  decEq : DecidableEq Carrier
  D : Finset (Line Carrier)
  C : Finset (Line Carrier)
  mem : @A Carrier field fintype decEq D C

instance instFieldCarrier {A : ProfileClass.{u}} (x : Object A) : Field x.Carrier := x.field
instance instFintypeCarrier {A : ProfileClass.{u}} (x : Object A) : Fintype x.Carrier := x.fintype
instance instDecidableEqCarrier {A : ProfileClass.{u}} (x : Object A) : DecidableEq x.Carrier := x.decEq

end Balanced.ProfileClassMargin

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Selection_OccupancyFailureClass
attribute [-instance] _root_.OAI.Balanced.ProfileClassMargin.instDecidableEqCarrier _root_.OAI.Balanced.ProfileClassMargin.instFieldCarrier _root_.OAI.Balanced.ProfileClassMargin.instFintypeCarrier
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

def occupancyFailureClass (k : ℕ) (a lam : ℝ) (ε : ℕ → ℝ)
    (high : Bool) : ProfileClass.{u} :=
  fun F _ _ _ D C =>
    IsProfilePair k D C ∧
    a * (Fintype.card F : ℝ) ≤ (C.card : ℝ) ∧
    deletionMultiplicityTV k D ≤ ε (Fintype.card F) ∧
    ∀ l ∈ C, if high then Real.exp (-(k : ℝ)) + lam ≤ survivingLineOccupancy D l
      else survivingLineOccupancy D l ≤ Real.exp (-(k : ℝ)) - lam

end Balanced

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Selection_SelectionTailCompletion
attribute [-instance] _root_.OAI.Balanced.Selection.Process.snapshotPathLaw_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory

namespace Balanced.Selection.Process.Tail

variable {I V : Type*} [Fintype I] [Fintype V]

omit [Fintype I] in

theorem tail_conditioning [MeasurableSpace V] [MeasurableSingletonClass V]
    (G : Input I V) (S : State I V)
    (hno : ∀ v w, G.slot v = G.slot w → ¬ G.graph.Adj v w)
    (L Δ : ℕ) (hL : 3 ≤ L)
    (hsize : ∀ i ∈ S.remaining, L ≤ (domain G S i).card)
    (hdegree : ∀ v ∈ currentVertices G S, degree G S v ≤ Δ)
    (hsparse : 8 * Δ ≤ L) :
    0 < (Slots.law (Domain G S)).real
      (TailConditioning.independentTransversals (Domain G S) (graph G S)) ∧
    ∀ (J : Finset (Slot S)) (a : Slots.Assignment (Domain G S)),
      TailConditioning.conditionalCylinder (Domain G S) (graph G S) J a ≤
        Real.exp ((J.card : ℝ) / 2) *
          ∏ i ∈ J, ((domain G S i.1).card : ℝ)⁻¹ := by
  classical
  let : ∀ i : Slot S, Nonempty (Domain G S i) := fun i =>
    Fintype.card_pos_iff.mp (by rw [card_domain]; exact lt_of_lt_of_le (by omega) (hsize i.1 i.2))
  simpa only [card_domain] using
    TailConditioning.tail_conditioning_of_bounds (graph G S) (noWithinSlotEdges G S hno)
      L Δ hL (fun i => by simpa only [card_domain] using hsize i.1 i.2)
      (fun v => (degree_le G S v).trans (hdegree _ (value_mem_current G S v))) hsparse

omit [Fintype I] in

theorem successfulAssignments_nonempty [MeasurableSpace V] [MeasurableSingletonClass V]
    (G : Input I V) (S : State I V)
    (hno : ∀ v w, G.slot v = G.slot w → ¬ G.graph.Adj v w)
    (L Δ : ℕ) (hL : 3 ≤ L)
    (hsize : ∀ i ∈ S.remaining, L ≤ (domain G S i).card)
    (hdegree : ∀ v ∈ currentVertices G S, degree G S v ≤ Δ)
    (hsparse : 8 * Δ ≤ L) : (successfulAssignments G S).Nonempty := by
  classical
  let : ∀ i : Slot S, Nonempty (Domain G S i) := fun i =>
    Fintype.card_pos_iff.mp (by rw [card_domain]; exact lt_of_lt_of_le (by omega) (hsize i.1 i.2))
  apply (Slots.law_real_pos_iff_nonempty (successfulAssignments G S)).mp
  have h := (tail_conditioning G S hno L Δ hL hsize hdegree hsparse).1
  have he : (successfulAssignments G S : Set (Slots.Assignment (Domain G S))) =
      TailConditioning.independentTransversals (Domain G S) (graph G S) := by
    ext a
    exact mem_successfulAssignments G S a
  rwa [he]

omit [Fintype I] [Fintype V] in
theorem completionPMF_supported (G : Input I V) (S : State I V) (fixed : I → V)
    (hslot : ∀ i ∉ S.remaining, G.slot (fixed i) = i)
    (hind : ∀ i ∉ S.remaining, ∀ j ∉ S.remaining, i ≠ j →
      ¬ G.graph.Adj (fixed i) (fixed j))
    (hcross : ∀ i ∉ S.remaining, ∀ v ∈ currentVertices G S,
      ¬ G.graph.Adj (fixed i) v)
    (hG : (successfulAssignments G S).Nonempty) (a : I → V)
    (ha : a ∈ (completionPMF G S fixed hG).support) :
    IsIndependentTransversal G a := by
  rcases (PMF.mem_support_map_iff _ _ _).mp ha with ⟨b, hb, rfl⟩
  apply complete_isIndependentTransversal G S fixed hslot hind hcross b
  exact (mem_successfulAssignments G S b).mp (by simpa using hb)

def completionOutputLaw (G : Input I V) (S : State I V) (fixed : I → V)
    (hslot : ∀ i ∉ S.remaining, G.slot (fixed i) = i)
    (hind : ∀ i ∉ S.remaining, ∀ j ∉ S.remaining, i ≠ j →
      ¬ G.graph.Adj (fixed i) (fixed j))
    (hcross : ∀ i ∉ S.remaining, ∀ v ∈ currentVertices G S,
      ¬ G.graph.Adj (fixed i) v)
    (hG : (successfulAssignments G S).Nonempty) : OutputLaw G where
  weight a := (completionPMF G S fixed hG a).toReal
  nonnegative _ := ENNReal.toReal_nonneg
  mass_le_one := (sum_pmf_real _).le
  supported a ha := completionPMF_supported G S fixed hslot hind hcross hG a
    ((PMF.apply_pos_iff _ _).mp (ENNReal.toReal_pos_iff.mp ha).1)

end Balanced.Selection.Process.Tail

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Selection_SelectionFinalLaw
attribute [-instance] _root_.OAI.Balanced.Selection.Process.snapshotPathLaw_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Selection.Process

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators

variable {I V : Type*} [Fintype I] [Fintype V]

section Nonempty
variable [Nonempty V]

def terminalLaw (G : Input I V)
    (hno : ∀ v w, G.slot v = G.slot w → ¬ G.graph.Adj v w)
    (S : State I V) : OutputLaw G := by
  classical
  letI : MeasurableSpace V := ⊤
  let : MeasurableSingletonClass V := ⟨fun _ => trivial⟩
  by_cases h : StateInvariant G S ∧ TailCheck G S
  · have hs : ∀ i ∉ S.remaining, G.slot (recordedAssignment S i) = i := by
      intro i hi
      exact h.1.2.2.1 i _ (recordedAssignment_recorded G S h.1 i hi)
    have hind : ∀ i ∉ S.remaining, ∀ j ∉ S.remaining, i ≠ j →
        ¬ G.graph.Adj (recordedAssignment S i) (recordedAssignment S j) := by
      intro i hi j hj hij
      exact h.1.2.2.2.1 i j _ _ (recordedAssignment_recorded G S h.1 i hi)
        (recordedAssignment_recorded G S h.1 j hj) hij
    have hc : ∀ i ∉ S.remaining, ∀ v ∈ currentVertices G S,
        ¬ G.graph.Adj (recordedAssignment S i) v := by
      intro i hi v hv
      exact h.1.2.2.2.2 i _ (recordedAssignment_recorded G S h.1 i hi)
        v (Finset.mem_filter.mp hv).1
    have hne : (Tail.successfulAssignments G S).Nonempty := by
      obtain ⟨L, Δ, hL, hsize, hdegree, hsparse⟩ := h.2
      exact Tail.successfulAssignments_nonempty G S hno L Δ hL hsize hdegree hsparse
    exact Tail.completionOutputLaw G S (recordedAssignment S) hs hind hc hne
  · exact failureLaw G

def terminalOutcomeLaw (G : Input I V)
    (hno : ∀ v w, G.slot v = G.slot w → ¬ G.graph.Adj v w) :
    Option (State I V) → OutputLaw G
  | none => failureLaw G
  | some S => terminalLaw G hno S

def sourceTerminalLaw (p : Parameters) (q : ℕ) (G : Input I V)
    (hno : ∀ v w, G.slot v = G.slot w → ¬ G.graph.Adj v w)
    (S : State I V) : OutputLaw G :=
  if SourceTailCheck p q G S then terminalLaw G hno S else failureLaw G

def sourceTerminalOutcomeLaw (p : Parameters) (q : ℕ) (G : Input I V)
    (hno : ∀ v w, G.slot v = G.slot w → ¬ G.graph.Adj v w) :
    Option (State I V) → OutputLaw G
  | none => failureLaw G
  | some S => sourceTerminalLaw p q G hno S

def finalLaw (p : Parameters) (q : ℕ) (G : Input I V)
    (hno : ∀ v w, G.slot v = G.slot w → ¬ G.graph.Adj v w) : OutputLaw G where
  weight a := ∑ out, mainStageWeight p q G out * (sourceTerminalOutcomeLaw p q G hno out).weight a
  nonnegative a := Finset.sum_nonneg (fun out _ =>
    mul_nonneg (historyWeight_nonnegative p q G _ out) ((sourceTerminalOutcomeLaw p q G hno out).nonnegative a))
  mass_le_one := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    calc
      _ ≤ ∑ out, mainStageWeight p q G out * 1 := Finset.sum_le_sum (fun out _ =>
        mul_le_mul_of_nonneg_left (sourceTerminalOutcomeLaw p q G hno out).mass_le_one
          (historyWeight_nonnegative p q G _ out))
      _ = 1 := by simp only [mul_one]; exact sum_historyWeight p q G _
  supported a ha := by
    by_contra hn
    have hz : ∀ out, (sourceTerminalOutcomeLaw p q G hno out).weight a = 0 :=
      fun out => weight_eq_zero_of_not_transversal (sourceTerminalOutcomeLaw p q G hno out) a hn
    simp only [hz, mul_zero, Finset.sum_const_zero, lt_self_iff_false] at ha

end Nonempty

def outputLaw (p : Parameters) (q : ℕ) (G : Input I V)
    (hno : ∀ v w, G.slot v = G.slot w → ¬ G.graph.Adj v w) : OutputLaw G :=
  if h : Nonempty V then @finalLaw I V _ _ h p q G hno else failureLaw G

@[simp] theorem outputLaw_eq_finalLaw [Nonempty V]
    (p : Parameters) (q : ℕ) (G : Input I V)
    (hno : ∀ v w, G.slot v = G.slot w → ¬ G.graph.Adj v w) :
    outputLaw p q G hno = finalLaw p q G hno := by
  simp [outputLaw, show Nonempty V from inferInstance]

end
end Balanced.Selection.Process

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Selection_SelectionTailPotential
attribute [-instance] _root_.OAI.Balanced.Selection.Process.snapshotPathLaw_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Selection.Process

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators

variable {I V : Type*} [Fintype I] [Fintype V]

@[simp] theorem cylinderMass_failureLaw (G : Input I V) (J : Finset I) (a : I → V) :
    cylinderMass (failureLaw G) J a = 0 := by
  simp [cylinderMass, failureLaw]

end
end Balanced.Selection.Process

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Selection_SelectionUniformAssembly
attribute [-instance] _root_.OAI.Balanced.Selection.Process.snapshotPathLaw_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter
open scoped Topology

namespace Balanced.Selection.Process

noncomputable section
universe u v w

def UniformSuccessEstimate (p : Parameters) (ε : ℕ → ℝ) (q : ℕ) : Prop :=
  ∀ (I : Type u) (V : Type v) [Fintype I] [Fintype V],
    ∀ G : Input I V, ∀ hG : GraphBounds G q p.c p.C,
      1 - ε q ≤ successMass (outputLaw p q G hG.2.1)

def UniformOccupancyEstimate (p : Parameters) (ε : ℕ → ℝ) (q : ℕ) : Prop :=
  ∀ (I : Type u) (V : Type v) [Fintype I] [Fintype V],
    ∀ G : Input I V, ∀ hG : GraphBounds G q p.c p.C,
      ∀ (P D L : Type w) [Fintype P] [Fintype D] [Fintype L],
        ∀ (A : FiniteAffine.Plane q P D L) (index : I ≃ (D × Bool)) (line : V → L),
          LineAssignment G A index line →
          ∀ T : L → Finset P, TrackedSets A T p.c₀ →
            occupancyFailureMass (outputLaw p q G hG.2.1) A line T p.rho ≤ ε q

end
end Balanced.Selection.Process

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Selection_SelectionSuccessUniform
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Filter MeasureTheory
open scoped Topology

namespace Balanced.Selection.Process

universe u v w

def UniformConcentrationEstimate (p : Parameters) (ε : ℕ → ℝ) (q : ℕ) : Prop :=
  ∀ (I : Type u) (V : Type v) [Fintype I] [Fintype V],
    ∀ G : Input I V, GraphBounds G q p.c p.C →
      (snapshotPathLaw p q G).real
        {ω | ¬ FirstAbort.ConcentratedPath p q G
          (p.lastMainTime q (Fintype.card I)) ω} ≤ ε q

end Balanced.Selection.Process

end

end OAI
end


