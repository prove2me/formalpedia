-- Prove2me | Definitions.Def_Q238L010
-- name    : Q238L010
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T11:22:01.98561+00:00
-- url     : https://prove2.me/theorems/768b49b4-329c-40d0-be20-a827c13ada21
-- title:
--   Definitions bundle Q238L010 of the split of OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 107 declarations of OpenAI's Lean: 79 definitions, 5 inductive types or structures, 4 instances and 19 theorems. The definitions and types are `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.Correction.Bounded`, `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.Correction.Keys`, `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.LowCertificate`, `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.NormalCertificate`, `OAI.MetricKMedianRecovery.CanonicalDelete.Bounds`, `OAI.MetricKMedianRecovery.CanonicalDelete.step`, `OAI.MetricKMedianRecovery.CanonicalLengthSearch.Result.Bounded`, `OAI.MetricKMedianRecovery.CanonicalLengthSearch.Result.Spec`, `OAI.MetricKMedianRecovery.CanonicalLengthSearch.run`, `OAI.MetricKMedianRecovery.CanonicalLengthView.candidates`, `OAI.MetricKMedianRecovery.CanonicalMatch.step`, `OAI.MetricKMedianRecovery.CanonicalMergeCrossing.directed`, `OAI.MetricKMedianRecovery.CanonicalMergeCrossing.edge`, `OAI.MetricKMedianRecovery.CanonicalMergeCrossing.scan`, `OAI.MetricKMedianRecovery.CanonicalMergeCrossing.transition`, `OAI.MetricKMedianRecovery.CanonicalMergeRefinement.Jump.expand`, `OAI.MetricKMedianRecovery.CanonicalMergeRefinement.Jump.labels`, `OAI.MetricKMedianRecovery.CanonicalMergeRefinement.Jump.source`, `OAI.MetricKMedianRecovery.CanonicalMergeRefinement.Jump.target`, `OAI.MetricKMedianRecovery.CanonicalMergeRefinement.accepts`, `OAI.MetricKMedianRecovery.CanonicalMergeRefinement.candidates`, `OAI.MetricKMedianRecovery.CanonicalMergeRefinement.refinePath`, `OAI.MetricKMedianRecovery.CanonicalMergeRefinement.refinedEdge`, `OAI.MetricKMedianRecovery.CanonicalMergeRefinement.regularChain`, `OAI.MetricKMedianRecovery.CanonicalMergeRefinement.view`, `OAI.MetricKMedianRecovery.Categorical.BoundedMarginals`, `OAI.MetricKMedianRecovery.Categorical.Diminishing`, `OAI.MetricKMedianRecovery.Categorical.GreedyInvariant`, `OAI.MetricKMedianRecovery.Categorical.Selected.binaryGreedyOutput`, `OAI.MetricKMedianRecovery.Categorical.Selected.greedyOutput`, `OAI.MetricKMedianRecovery.Categorical.allMarginals`, `OAI.MetricKMedianRecovery.Categorical.batch`, `OAI.MetricKMedianRecovery.Categorical.derivative`, `OAI.MetricKMedianRecovery.Categorical.direction`, `OAI.MetricKMedianRecovery.Categorical.estimationBad`, `OAI.MetricKMedianRecovery.Categorical.evaluate`, `OAI.MetricKMedianRecovery.Categorical.tableValue`, `OAI.MetricKMedianRecovery.CertifiedRegularStep`, `OAI.MetricKMedianRecovery.ClippingTransfer.clippedBid`, `OAI.MetricKMedianRecovery.ClippingTransfer.effectiveBid` and 44 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedianRecovery_Algorithms_FinalBudgetPos`, `KMedianRecovery_Branching_CategoricalRule`, `KMedianRecovery_Branching_CopyComparison`, `KMedianRecovery_Encoding_LabelRange`, `KMedianRecovery_Encoding_UniformBits`, `KMedianRecovery_Machines_CorrectionSize`, `KMedianRecovery_Machines_DeleteFold`, `KMedianRecovery_Machines_FirstSize`, `KMedianRecovery_Machines_MatchFold`, `KMedianRecovery_Machines_MergeResources`, `KMedianRecovery_Recovery_AllBad`, `KMedianRecovery_Recovery_Ball`, `KMedianRecovery_Recovery_ClassSlotsMem`, `KMedianRecovery_Recovery_CoordinateRow`, `KMedianRecovery_Recovery_CountedTrace`, `KMedianRecovery_Recovery_DyadicGrid`, `KMedianRecovery_Recovery_Entry`, `KMedianRecovery_Recovery_EntryReplay`, `KMedianRecovery_Recovery_FiniteCross`, `KMedianRecovery_Recovery_InitialProject`, `KMedianRecovery_Recovery_LengthHeight`, `KMedianRecovery_Recovery_LengthSearch`, `KMedianRecovery_Recovery_MergeCross`, `KMedianRecovery_Recovery_MergeRefine`, `KMedianRecovery_Recovery_Pool`, `KMedianRecovery_Recovery_Produce`, `KMedianRecovery_Recovery_RawCount`, `KMedianRecovery_Recovery_RefineMath`, `KMedianRecovery_Recovery_RegularChain`, `KMedianRecovery_Recovery_Removal`, `KMedianRecovery_Recovery_ReverseRow`, `KMedianRecovery_Recovery_Row`, `KMedianRecovery_Recovery_Score`, `KMedianRecovery_Recovery_SetFunction`, `KMedianRecovery_Recovery_StoredForms`, `KMedianRecovery_Recovery_Table`, `KMedianRecovery_Recovery_TableValue`, `KMedianRecovery_Sampling_RealizedKernel`, `KMedianRecovery_Sampling_SamplerContext`, `KMedianRecovery_Sampling_SamplingPotential`, `KMedianRecovery_Sampling_SamplingRate`, `KMedianRecovery_Strictness_Clipped`, `KMedianRecovery_Strictness_ClippedBid`, `KMedianRecovery_Strictness_Dual`, `KMedianRecovery_Strictness_IndexedPaymentCoeff`, `KMedianRecovery_Strictness_LinearPayment`.
--
--   **Imports.** It imports the bundles `Q238L000`, `Q238L002`, `Q238L003` and `Q238L004` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q238L020` and `Q238L021`; the statements `OAI.MetricKMedianRecovery.Anchoring.anchoring_s238r`, `OAI.MetricKMedianRecovery.Anchoring.total_assignment_excess_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.result_guarantee_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionAlgorithm.sixtyTwoFin_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionFair.result_guarantee_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryObservableBranch.fair_color_label_completion_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryObservableBranch.successful_probability_s238r`, `OAI.MetricKMedianRecovery.Categorical.Selected.binaryGreedyOutput_expected_s238r`, `OAI.MetricKMedianRecovery.Categorical.Selected.greedyRun_good_s238r`, `OAI.MetricKMedianRecovery.Ellipsoid.boundedRationalDecide_correct_s238r`, `OAI.MetricKMedianRecovery.Ellipsoid.finalFace_feasible_s238r`, `OAI.MetricKMedianRecovery.Ellipsoid.iterate_contains_s238r`, `OAI.MetricKMedianRecovery.Ellipsoid.selectFace_spec_s238r`, `OAI.MetricKMedianRecovery.Ellipsoid.weakSolve_complete_diameters_s238r`, `OAI.MetricKMedianRecovery.IntegralCandidates.separated_comparison_s238r`, `OAI.MetricKMedianRecovery.LocalSearch.local_combined_cost_bound_s238r`, `OAI.MetricKMedianRecovery.LocalSearch.local_five_approx_s238r`, `OAI.MetricKMedianRecovery.LocalSearch.optimum_attained_exact_s238r`, `OAI.MetricKMedianRecovery.LocalSearch.optimum_attained_s238r`, `OAI.MetricKMedianRecovery.PhaseParameterTransfer.prefix_map_s238r`, `OAI.MetricKMedianRecovery.PhaseSurplusProducer.normal_cost_s238r`, `OAI.MetricKMedianRecovery.RationalSampling.trace_probability_s238r`, `OAI.MetricKMedianRecovery.Sensitivity.sensitive_optimum_s238r` and `OAI.MetricKMedianRecovery.Surplus.protected_partition_cost_s238r`; the proofs of `OAI.MetricKMedianRecovery.Anchoring.anchoring_s238r`, `OAI.MetricKMedianRecovery.Anchoring.total_assignment_excess_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.result_guarantee_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionAlgorithm.sixtyTwoFin_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionFair.result_guarantee_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryObservableBranch.fair_color_label_completion_s238r`, `OAI.MetricKMedianRecovery.Categorical.Selected.binaryGreedyOutput_expected_s238r`, `OAI.MetricKMedianRecovery.Categorical.Selected.greedyRun_good_s238r`, `OAI.MetricKMedianRecovery.Ellipsoid.finalFace_feasible_s238r`, `OAI.MetricKMedianRecovery.Ellipsoid.iterate_contains_s238r`, `OAI.MetricKMedianRecovery.Ellipsoid.selectFace_spec_s238r`, `OAI.MetricKMedianRecovery.IntegralCandidates.separated_comparison_s238r`, `OAI.MetricKMedianRecovery.LocalSearch.local_combined_cost_bound_s238r`, `OAI.MetricKMedianRecovery.LocalSearch.local_five_approx_s238r`, `OAI.MetricKMedianRecovery.LocalSearch.optimum_attained_exact_s238r`, `OAI.MetricKMedianRecovery.LocalSearch.optimum_attained_s238r`, `OAI.MetricKMedianRecovery.PhaseParameterTransfer.prefix_map_s238r`, `OAI.MetricKMedianRecovery.PhaseSurplusProducer.normal_cost_s238r`, `OAI.MetricKMedianRecovery.Sensitivity.sensitive_optimum_s238r` and `OAI.MetricKMedianRecovery.Surplus.protected_partition_cost_s238r`.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_Q238L000
import Definitions.Def_Q238L002
import Definitions.Def_Q238L003
import Definitions.Def_Q238L004

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Row
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalLinearFeasibility

noncomputable def Row.realValue {n : ℕ} (r : Row n) (x : Fin n → ℝ) : ℝ :=
  ∑ i, (r.coeff i : ℝ) * x i

noncomputable def Row.RealHolds {n : ℕ} (r : Row n) (x : Fin n → ℝ) : Prop := r.realValue x ≤ r.bound

end MetricKMedianRecovery.RationalLinearFeasibility

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Strictness_LinearPayment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.OpenabilityLinearization
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X]

noncomputable def linearPayment (loc : D → X) (t v z : ℝ) (W : Finset X) (i : X)
    (tau : D → ℝ) : ℝ := by
  classical
  exact ∑ j, if activeAt loc t z W j then
    if dist i (loc j) ≤ v*z then tau j-t*dist i (loc j)
    else max (z-t*dist i (loc j)) 0
    else max (t*nearestDistance (loc j) W-t*dist i (loc j)) 0

noncomputable def dualTerm (loc : D → X) (t z : ℝ) (W : Finset X) (i₀ : X)
    (tau : D → ℝ) (a j : D) : ℝ := by
  classical
  exact if activeAt loc t z W j then tau j-dist i₀ (loc j)
    else tau a-2*dist i₀ (loc j)-dist i₀ (loc a)

noncomputable def Feasible (loc : D → X) (F W : Finset X) (v z lam eta : ℝ) (i : X)
    (tau : D → ℝ) (y : F → D → D → ℝ) : Prop :=
  admissibleBids loc (1-3*v) (1+v^2) v z W i tau ∧
  lam-(Fintype.card D:ℝ)*eta ≤ linearPayment loc (1-3*v) v z W i tau ∧
  (∀ f : F, ∀ a, activeAt loc (1-3*v) z W a →
    (∀ j, 0 ≤ y f a j ∧ dualTerm loc (1-3*v) z W f tau a j ≤ y f a j) ∧
    ∑ j, y f a j ≤ lam)

end MetricKMedianRecovery.OpenabilityLinearization

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_ReverseRow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Ellipsoid
open Matrix RationalLinearFeasibility PolytopeCertificate
open scoped BigOperators

noncomputable def Face {n : ℕ} (rows picked : List (Row n)) (B : ℕ) (x : Fin n → ℝ) : Prop :=
  (∀ q∈rows, q.RealHolds x) ∧ (∀ q∈picked, q.realValue x=(q.bound:ℝ)) ∧
    (∀ j, |x j|≤(B:ℝ))

end MetricKMedianRecovery.Ellipsoid

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_CoordinateRow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Ellipsoid
open Matrix RationalLinearFeasibility PolytopeCertificate
open scoped BigOperators

def rowMatrix {n : ℕ} (rows : List (Row n)) : Matrix (Fin rows.length) (Fin n) ℚ :=
  fun i j => rows[i].coeff j

def rowBounds {n : ℕ} (rows : List (Row n)) : Fin rows.length → ℚ :=
  fun i => rows[i].bound

end MetricKMedianRecovery.Ellipsoid

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_CountedTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery

namespace OrdinaryProducer
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

def PlainOpening (loc : D → X) (F : Finset X) (v lam : ℝ)
    (s e : ExecutionState D X) : Prop :=
  ∃ i ∈ F, i ∉ s.opened ∧ ∃ tau : D → ℝ,
    admissibleBids loc (1-3*v) (1+v^2) v s.phase s.opened i tau ∧
    lam ≤ openingPayment loc (1-3*v) s.phase s.opened i tau ∧
    (∀ i₀ ∈ F, ∀ a, activeAt loc (1-3*v) s.phase s.opened a →
      openingDual loc (1-3*v) s.phase s.opened i₀ tau a ≤ lam) ∧
    e = regularUpdate loc (1-3*v) s i s.opened tau

def PhaseMaximal (loc : D → X) (F : Finset X) (v lam : ℝ) (s : ExecutionState D X) : Prop :=
  ∀ i ∈ F, i ∉ s.opened → ¬etaOpenable loc F s.opened (1-3*v) (1+v^2) v s.phase lam 0 i

end OrdinaryProducer
end MetricKMedianRecovery

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_StoredForms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalPhase
open EffectiveOpenability OrdinaryProducer OpenabilityLinearization

def update {m d : ℕ} (distance : Fin m → Fin d → ℚ) (v : ℚ)
    (s : State m d) (e : Event m d) : State m d :=
  ⟨insert e.facility s.opened,s.phase,
    Vector.ofFn (fun j => if active distance v s.phase s.opened j then e.bid[j] else s.budget[j])⟩

end MetricKMedianRecovery.RationalPhase

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Strictness_Clipped
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalPhase
open EffectiveOpenability OrdinaryProducer

def clipped {m d : ℕ} (distance : Fin m → Fin d → ℚ) (v z : ℚ)
    (W : Finset (Fin m)) (j : Fin d) : ℚ :=
  if W.Nonempty then min z ((1-3*v)*RationalOpenability.nearest distance W j) else z

def advance {m d : ℕ} (distance : Fin m → Fin d → ℚ) (v : ℚ)
    (s : State m d) : State m d :=
  ⟨s.opened,(1+v^2)*s.phase,Vector.ofFn (fun j =>
    if active distance v s.phase s.opened j then
      clipped distance v ((1+v^2)*s.phase) s.opened j else s.budget[j])⟩

inductive Instruction (m d : ℕ) where
  | opening : Event m d → Instruction m d
  | advance : Instruction m d

end MetricKMedianRecovery.RationalPhase

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Entry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery
namespace PhaseSequence
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

def Entry (loc : D → X) (F B Q : Finset X) (v z lam eta : ℝ) (i : X) : Prop :=
  i ∉ Q ∧ (i ∈ B ∨ (i ∈ F ∧ ∃ W : Finset X, Q ⊆ W ∧ W ⊆ F ∪ B ∧
    etaOpenable loc F W (1-3*v) (1+v^2) v z lam eta i))

inductive Prefix (loc : D → X) (F B : Finset X) (v z lam eta : ℝ) :
    Finset X → List X → Prop
  | nil (Q) : Prefix loc F B v z lam eta Q []
  | cons {Q : Finset X} {i : X} {H : List X}
      (hi : Entry loc F B Q v z lam eta i)
      (htail : Prefix loc F B v z lam eta (insert i Q) H) :
      Prefix loc F B v z lam eta Q (i::H)

end PhaseSequence
end MetricKMedianRecovery

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Strictness_ClippedBid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery
namespace ClippingTransfer
variable {D X : Type*} [PseudoMetricSpace X]

noncomputable def clippedBid (loc : D → X) (t : ℝ) (W : Finset X)
    (tau : D → ℝ) (j : D) : ℝ := min (tau j) (t*nearestDistance (loc j) W)

noncomputable def effectiveBid (loc : D → X) (t z : ℝ) (W : Finset X)
    (tau : D → ℝ) (j : D) : ℝ := by
  classical
  exact if activeAt loc t z W j then tau j else t*nearestDistance (loc j) W

end ClippingTransfer
end MetricKMedianRecovery

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Pool
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.PhaseMergePath
open PhaseSequence
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

inductive Step (loc : D → X) (F B Q : Finset X) (copy : X → X) (v z lam : ℝ) :
    List X → List X → Prop
  | add (H : List X) (i : X) (hi : i ∈ F) : Step loc F B Q copy v z lam H (H++[copy i])
  | remove (C T A : List X) (i : X) (hi : i ∈ F)
      (hA : Prefix loc F (pool F B copy) v z lam 0 (Q ∪ (C++T).toFinset) A)
      (hreg : ∀ x ∈ A, x ∈ F) :
      Step loc F B Q copy v z lam (C++i::T) ((C++T)++A)
  | replace (C T : List X) (i : X) (hi : i ∈ F)
      (hnot : i ∉ Q ∪ (C++T).toFinset) :
      Step loc F B Q copy v z lam (C++copy i::T) (C++i::T)

end MetricKMedianRecovery.PhaseMergePath

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_MergeRefine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CanonicalMergeRefinement
open PhaseSequence PhaseMergePath PhaseMergeRefinement
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

def Jump.source (copy : X → X) (H : List X) : Jump X → List X
  | .add _ => H
  | .remove C T _ i => C++i::T
  | .replace C T i => C++copy i::T

def Jump.target (copy : X → X) (H : List X) : Jump X → List X
  | .add i => H++[copy i]
  | .remove C T A _ => (C++T)++A
  | .replace C T i => C++i::T

def Jump.labels (F : Finset X) : Jump X → Prop
  | .add i => i∈F
  | .remove _ _ A i => i∈F ∧ ∀ a∈A,a∈F
  | .replace _ _ i => i∈F

instance instDecidableLabels (F : Finset X) (J : Jump X) : Decidable (J.labels F) := by
  cases J <;> dsimp only [Jump.labels] <;> infer_instance

def candidates (R : List X) (H G : List X) : List (Jump X) :=
  (R.map Jump.add) ++
  ((cuts H).map (fun p => Jump.remove p.1 p.2.2 (G.drop (H.length-1)) p.2.1)) ++
  ((cuts G).map (fun p => Jump.replace p.1 p.2.2 p.2.1))

def accepts (F : Finset X) (copy : X → X) (H G : List X) (J : Jump X) : Prop :=
  J.source copy H=H ∧ J.target copy H=G ∧ J.labels F

instance instDecidableAccepts (F : Finset X) (copy : X → X) (H G : List X) (J : Jump X) :
    Decidable (accepts F copy H G J) := by unfold accepts; infer_instance

def view (F : Finset X) (R : List X) (copy : X → X) (H G : List X) : Option (Jump X) :=
  (candidates R H G).find? (fun J => decide (accepts F copy H G J))

def Jump.expand (spare : X → X) (G : List X) : Jump X → List (List X)
  | .add _ => [G]
  | .remove C T A i => removeVertices C T A (spare i)
  | .replace _ _ _ => [G]

def refinePath (F : Finset X) (R : List X) (copy spare : X → X) :
    List X → List (List X) → List (List X)
  | _,[] => []
  | H,G::T =>
    match view F R copy H G with
    | none => G::refinePath F R copy spare G T
    | some J => J.expand spare G ++ refinePath F R copy spare G T

def regularChain (F : Finset X) (R : List X) (complete : Finset X → List X)
    (Q : Finset X) (copy spare : X → X) (H G : List X) : List (List X) :=
  refinePath F R copy spare H (CanonicalMergePath.regularPath complete Q copy G H)

end MetricKMedianRecovery.CanonicalMergeRefinement

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_MergeCross
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CanonicalMergeCrossing
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion PhaseMergeRefinement PhaseCountCrossing
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

def directed (F Q : Finset X) (k : ℕ) (H G : List X) (T U : List (List X)) : Result X :=
  if H.length=G.length then
    if finalCount F Q G T=k then .success G T else .common G T U
  else .sensitive H G T U

def edge (F Q : Finset X) (k : ℕ) (H G : List X) (T U : List (List X)) : Result X :=
  if forward F Q H G then directed F Q k H G T U else directed F Q k G H U T

def scan (F Q : Finset X) (k : ℕ) (complete : Finset X → List (List X))
    (U : List (List X)) : List X → List (List X) → List (List X) → Result X
  | H,T,[] => .common H T U
  | H,T,J::S =>
    let V := complete (Q ∪ J.toFinset)
    if finalCount F Q J V = k then .success J V
    else if Sandwich k (finalCount F Q H T) (finalCount F Q J V) then edge F Q k H J T V
    else scan F Q k complete U J V S

end MetricKMedianRecovery.CanonicalMergeCrossing

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Removal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery

def CertifiedRegularStep {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]
    (loc : D → X) (F : Finset X) (v lam eta : ℝ)
    (s s' : ExecutionState D X) : Prop :=
  ∃ i : X, ∃ W : Finset X, ∃ tau : D → ℝ,
    i ∈ F ∧ s.opened ⊆ W ∧
    admissibleBids loc (1 - 3 * v) (1 + v ^ 2) v s.phase W i tau ∧
    lam - (Fintype.card D : ℝ) * eta ≤ openingPayment loc (1 - 3 * v) s.phase W i tau ∧
    (∀ i₀ ∈ F, ∀ a, activeAt loc (1 - 3 * v) s.phase W a →
      openingDual loc (1 - 3 * v) s.phase W i₀ tau a ≤ lam) ∧
    s' = regularUpdate loc (1 - 3 * v) s i W tau

end MetricKMedianRecovery

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_EntryReplay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CountedHistoryExecution
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

def Step (loc : D → X) (F : Finset X) (v lam eta : ℝ)
    (s s' : ExecutionState D X) : Prop :=
  AtomicStep loc F v lam eta s s' ∧
  ((s.opened ∩ F).card < (s'.opened ∩ F).card →
    CertifiedRegularStep loc F v lam eta s s')

end MetricKMedianRecovery.CountedHistoryExecution

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_FinalBudgetPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.PhaseMergeCertificate
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion HistoryPhaseBound
universe uD uX
variable {D : Type uD} {X : Type uX} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

def Budget (loc : D → X) (F Q : Finset X) (v lam eta : ℝ) : Prop :=
  ∃ alpha : D → ℝ,
    (∀ j, 0 < alpha j) ∧
    (∀ i ∈ F, (∑ j, max (alpha j-2*dist i (loc j)) 0) ≤ lam) ∧
    ((1-3*v)*(∑ j, nearestDistance (loc j) Q) +
      ((Q ∩ F).card:ℝ)*(lam-(Fintype.card D:ℝ)*eta) ≤ ∑ j, alpha j) ∧
    (∀ (C : Finset D), C.Nonempty → ∀ i ∈ F, ∀ b : ℝ, 0 < b →
      0 < (∑ j ∈ C, dist i (loc j)) → lam ≤ b*(∑ j ∈ C, dist i (loc j)) →
      v^2 ≤ strictnessGap b/(6*(b+2)) →
      (∑ j ∈ C, alpha j) ≤ lam+(2-strictnessGap b/2)*(∑ j ∈ C, dist i (loc j)))

end MetricKMedianRecovery.PhaseMergeCertificate

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_SetFunction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery
namespace Categorical

variable {E : Type*} [Fintype E] [DecidableEq E]

noncomputable def evaluate : Batch E → SetFunction E → SetFunction E
  | [], g => g
  | (w, _) :: tail, g => evaluate tail (operator w g)

noncomputable def direction : Batch E → SetFunction E → SetFunction E
  | [], _ => fun _ => 0
  | (w, e) :: tail, g => fun S => evaluate tail (marginal g e) S + direction tail (operator w g) S

def BoundedMarginals (g : SetFunction E) (M : ℝ) : Prop :=
  ∀ e S, 0 ≤ marginal g e S ∧ marginal g e S ≤ M

def Diminishing (g : SetFunction E) : Prop :=
  ∀ U V, U ⊆ V → ∀ e, marginal g e V ≤ marginal g e U

noncomputable def allMarginals : Batch E → SetFunction E → SetFunction E
  | [], _ => fun _ => 0
  | (_, e) :: tail, g => fun S => marginal g e S + allMarginals tail g S

end Categorical
end MetricKMedianRecovery

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Table
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery
namespace Categorical

open FiniteSampling
variable {E Ω : Type*} [Fintype E] [DecidableEq E] [Fintype Ω] [Nonempty Ω]

noncomputable def batch {a : ℕ} (r : Fin a → Table Ω E) (c : Fin a → E) : Batch E :=
  List.ofFn (fun j => (tableWeights (r j), c j))

noncomputable def derivative {a : ℕ} (r : Fin a → Table Ω E) (c : Fin a → E)
    (j : Fin a) (e : E) (g : SetFunction E) (S : Finset E) : ℝ :=
  evaluate (batch (Function.update r j (fun _ => none)) c) (marginal g e) S

end Categorical
end MetricKMedianRecovery

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_TableValue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Categorical
open FiniteSampling

noncomputable def tableValue {E Ω : Type*} [DecidableEq E] [Fintype Ω]
    {a : ℕ} (g : SetFunction E) (r : Fin a → Table Ω E) : ℝ :=
  average (fun seed : Fin a → Ω => g (draw a r seed ∅))

section GreedyStep
variable {E : Type*} [Fintype E] [DecidableEq E] {a T L : ℕ}

def GreedyInvariant (part : E → Fin a) (s : GreedyState E a T) : Prop :=
  (∀ j ω e, s.2 j ω = some e → part e = j) ∧
    (∀ j ω, s.1 ≤ ω.val → s.2 j ω = none)

end GreedyStep
end MetricKMedianRecovery.Categorical

namespace MetricKMedianRecovery.Categorical
open FiniteSampling

section StepBound
variable {E : Type*} [Fintype E] [DecidableEq E] {a T L : ℕ} [NeZero T]

def estimationBad (part : E → Fin a) (g : SetFunction E) (M tau : ℝ)
    (s : GreedyState E a T) (seed : OracleSeed E a T L) : Prop :=
  ∃ e, tau*M/a < |scores part g s.2 seed e - average (marginalSample part g s.2 e)|

end StepBound
end MetricKMedianRecovery.Categorical

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_UniformBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Categorical
open FiniteSampling

instance binaryOracleIndexFintype {E : Type*} [Fintype E] {a b L : ℕ} :
    Fintype (BinaryOracleIndex E a b L) :=
  inferInstanceAs (Fintype (((Fin (2^b) × E × Fin L × Fin a) ⊕ Fin a) × Fin b))

instance binaryOracleIndexDecidableEq {E : Type*} [DecidableEq E] {a b L : ℕ} :
    DecidableEq (BinaryOracleIndex E a b L) :=
  inferInstanceAs (DecidableEq (((Fin (2^b) × E × Fin L × Fin a) ⊕ Fin a) × Fin b))

end MetricKMedianRecovery.Categorical

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CategoricalRule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Categorical.Selected
open FiniteSampling
variable {E : Type*} [Fintype E] [DecidableEq E] {a T L : ℕ}

noncomputable def greedyOutput (part : E → Fin a) (rule : Rule part)
    (g : SetFunction E) (seed : (Fin T → OracleSeed E a T L) × (Fin a → Fin T)) : Finset E :=
  draw a (greedyRun part rule g seed.1).2 seed.2 ∅

noncomputable def binaryGreedyOutput {E : Type*} [Fintype E] [DecidableEq E]
    {a b L : ℕ} (part : E → Fin a) (rule : Rule part)
    (g : SetFunction E) (bits : BinaryOracleIndex E a b L → Bool) : Finset E :=
  greedyOutput part rule g (binarySeedEquiv E a b L bits)

end MetricKMedianRecovery.Categorical.Selected

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Score
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Completion

variable {E R : Type*} [Fintype R]

variable {P : Type*} [Fintype P]

noncomputable def saving (K : ℝ) (q : ℕ)
    (base : P → ℝ) (distance : P → E → ℝ)
    (weight redBase : R → ℝ) (redDistance : R → E → ℝ) (X : Finset E) : ℝ :=
  surrogate K q base distance weight redBase redDistance ∅ -
    surrogate K q base distance weight redBase redDistance X

@[simp] lemma saving_empty (K : ℝ) (q : ℕ)
    (base : P → ℝ) (distance : P → E → ℝ)
    (weight redBase : R → ℝ) (redDistance : R → E → ℝ) :
    saving K q base distance weight redBase redDistance ∅ = 0 := sub_self _

end MetricKMedianRecovery.Completion

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Strictness_IndexedPaymentCoeff
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.EffectiveOpenability
open RationalLinearFeasibility RationalOpenability

def indexedPaymentCoeff {m d : ℕ} (distances : Fin m → Fin d → ℚ) (F W : Finset (Fin m))
    (v z : ℚ) (i : Fin m) : Variables (Fin d) F → ℚ
  | .inl b=>if active distances v z W b then if distances i b≤v*z then 1 else 0 else 0
  | .inr _=>0

def indexedDualCoeff {m d : ℕ} (F : Finset (Fin m)) (f : F) (a : Fin d) : Variables (Fin d) F → ℚ
  | .inl _=>0
  | .inr (g,b,_)=>if g=f ∧ b=a then 1 else 0

def indexedCoeff {m d : ℕ} (distances : Fin m → Fin d → ℚ) (F W : Finset (Fin m))
    (v z : ℚ) (i : Fin m) (r : Kind (Fin d) W F) (u : Variables (Fin d) F) : ℚ :=
  match r with
  | .lower j=>if active distances v z W j then -(if u=.inl j then 1 else 0) else 0
  | .upper j=>if active distances v z W j then (if u=.inl j then 1 else 0) else 0
  | .cap j _=>if active distances v z W j then (if u=.inl j then 1 else 0) else 0
  | .far j=>if active distances v z W j then
      if distances i j≤v*z then 0 else (if u=.inl j then 1 else 0) else 0
  | .payment=>-indexedPaymentCoeff distances F W v z i u
  | .slackZero f a j=>if active distances v z W a then -(if u=.inr (f,a,j) then 1 else 0) else 0
  | .slackTerm f a j=>if active distances v z W a then
      (if active distances v z W j then (if u=.inl j then 1 else 0) else (if u=.inl a then 1 else 0)) -
        (if u=.inr (f,a,j) then 1 else 0) else 0
  | .dual f a=>if active distances v z W a then indexedDualCoeff F f a u else 0

end MetricKMedianRecovery.EffectiveOpenability

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_FiniteCross
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CanonicalLengthView
open PhaseSequence PhaseMergeRefinement CanonicalMergeRefinement PhaseCountCrossing
variable {X : Type*} [DecidableEq X] {d : ℕ}

def candidates (R H G : List X) : List (Plan X) :=
  (R.flatMap (fun i=>G.map (Plan.free i))) ++ ((cuts H).map (fun p=>Plan.paid p.1 p.2.2 p.2.1))

end MetricKMedianRecovery.CanonicalLengthView

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_LengthSearch
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CanonicalLengthSearch
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion PhaseCountCrossing CanonicalMergeCrossing
variable {X : Type*} [DecidableEq X]

def run (F Q : Finset X) (leaf : ℚ  →  X) (complete : ℚ  →  List (List X))
    (T U : List (List X)) (b : ℚ) (k N : ℕ) : Result X :=
  let f := count F Q leaf complete T U b
  let J := range f k N b
  if f J.1=k then .success J.1 (chosen complete T U b J.1)
  else if f J.2=k then .success J.2 (chosen complete T U b J.2)
  else .bracket J.1 J.2 (chosen complete T U b J.1) (chosen complete T U b J.2)

def Result.Spec (F Q : Finset X) (leaf : ℚ  →  X) (R : ℚ  →  List (List X)  →  Prop)
    (b : ℚ) (k N : ℕ) : Result X  →  Prop
  | .success s T => 0 ≤ s  ∧  s ≤ b  ∧  R s T  ∧  ((after (insert (leaf s) Q) T) ∩ F).card=k
  | .bracket l u T U => 0 ≤ l  ∧  l ≤ u  ∧  u ≤ b  ∧  u-l ≤ 1/(2:ℚ)^N  ∧  R l T  ∧  R u U  ∧
      Sandwich k ((after (insert (leaf l) Q) T) ∩ F).card ((after (insert (leaf u) Q) U) ∩ F).card

end MetricKMedianRecovery.CanonicalLengthSearch

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_MergeResources
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CanonicalCoupledMerge
open RationalLeaves RationalHeight
variable {V : Type*} [DecidableEq V]

def Correction.Bounded (h : ℕ) : Correction V → Prop
  | .identity => True
  | .shorten _ _ l u => Height l h ∧ Height u h

end MetricKMedianRecovery.CanonicalCoupledMerge

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_FirstSize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RadiusMenus

lemma additiveRadius_pos (kappa q : ℝ) (j : ℕ) (hk : 0 < kappa)
    (hq : 0 < q) (hj : 0 < j) : 0 < additiveRadius kappa q j := by
  exact mul_pos (mul_pos (Nat.cast_pos.mpr hj) hk) hq

lemma geometricCap_spec (kappa : ℝ) (hk : 0 < kappa) :
    10 ≤ (1+kappa)^(geometricCap kappa hk) := Nat.find_spec (geometric_exists kappa hk)

end MetricKMedianRecovery.RadiusMenus

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Ball
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Population
variable {V : Type*} [PseudoMetricSpace V]

lemma candidate_pos (D : Finset V) (P : ℝ) (m : ℕ) (w : V)
    (hP : 0 < P) (hm : 0 < m) {p : V} (hp : p ∈ D) : 0 < candidate D P m w p := by
  have hc : (0 : ℝ) < (ball D w (dist w p)).card := by
    exact_mod_cast Finset.card_pos.mpr (ball_nonempty_at D w hp)
  exact (div_pos hP (mul_pos (Nat.cast_pos.mpr hm) hc)).trans_le (le_max_right _ _)

lemma radius_pos (D : Finset V) (hn : D.Nonempty) (P : ℝ) (m : ℕ) (w : V)
    (hP : 0 < P) (hm : 0 < m) : 0 < radius D hn P m w := by
  obtain ⟨p, hp, he⟩ := Finset.exists_mem_eq_inf' hn (candidate D P m w)
  rw [radius, he]
  exact candidate_pos D P m w hP hm hp

lemma candidate_feasible (D : Finset V) (P : ℝ) (m : ℕ) (w : V)
    (hP : 0 < P) (hm : 0 < m) {p : V} (hp : p ∈ D) :
    P / m ≤ candidate D P m w p * (ball D w (candidate D P m w p)).card := by
  let C := ball D w (dist w p)
  have hc : (0 : ℝ) < C.card := by
    exact_mod_cast Finset.card_pos.mpr (ball_nonempty_at D w hp)
  have hm' : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hlo : P / ((m : ℝ)*C.card) ≤ candidate D P m w p := le_max_right _ _
  have hsub : C ⊆ ball D w (candidate D P m w p) := ball_mono D w (le_max_left _ _)
  have hh : (C.card : ℝ) ≤ (ball D w (candidate D P m w p)).card := by
    exact_mod_cast Finset.card_le_card hsub
  have he : P / ((m : ℝ)*C.card) * C.card = P / m := by field_simp
  rw [← he]
  exact (mul_le_mul_of_nonneg_right hlo hc.le).trans
    (mul_le_mul_of_nonneg_left hh (candidate_pos D P m w hP hm hp).le)

lemma radius_feasible (D : Finset V) (hn : D.Nonempty) (P : ℝ) (m : ℕ) (w : V)
    (hP : 0 < P) (hm : 0 < m) :
    P / m ≤ radius D hn P m w * (ball D w (radius D hn P m w)).card := by
  obtain ⟨p, hp, he⟩ := Finset.exists_mem_eq_inf' hn (candidate D P m w)
  simpa only [radius, he] using candidate_feasible D P m w hP hm hp

end MetricKMedianRecovery.Population

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_LabelRange
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.ColorLabel

noncomputable def labelMass (b : ℕ) (hb : 0 < b) (j : Fin b) : ℝ :=
  ∑ x : Fin (labelRange b), if label b hb x = j then 1/(labelRange b : ℝ) else 0

noncomputable def colorMass (c : Fin 3) : ℝ :=
  ∑ x : Fin 4, if color x = c then (1/4 : ℝ) else 0

noncomputable def binaryDistinctMass (b : ℕ) (hb : 0 < b) : ℝ :=
  ∑ seed : Fin b → Fin (labelRange b),
    if Function.Injective (fun i => label b hb (seed i))
    then (1/(labelRange b : ℝ))^b else 0

end MetricKMedianRecovery.ColorLabel

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_RawCount
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Dyadic
variable {A : Type*} [Fintype A] [DecidableEq A]

omit [DecidableEq A] in
lemma rawCount_sum_le (p : A → ℝ) (hp : ∀ a, 0 ≤ p a)
    (ht : ∑ a, p a = 1) (b : ℕ) : (∑ a, rawCount p b a) ≤ 2^b := by
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset A))
    (fun a _ => Nat.floor_le (mul_nonneg (by positivity : (0:ℝ) ≤ 2^b) (hp a)))
  rw [← Finset.mul_sum,ht,mul_one] at h
  unfold rawCount
  exact_mod_cast h

noncomputable def count (p : A → ℝ) (b : ℕ) (default a : A) : ℕ :=
  rawCount p b a + if a = default then 2^b - ∑ a, rawCount p b a else 0

lemma count_total (p : A → ℝ) (hp : ∀ a, 0 ≤ p a)
    (ht : ∑ a, p a = 1) (b : ℕ) (default : A) : ∑ a, count p b default a = 2^b := by
  have h := rawCount_sum_le p hp ht b
  simp only [count,Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,ite_true, if_true]
  omega

noncomputable def weight (p : A → ℝ) (b : ℕ) (default a : A) : ℝ :=
  (count p b default a : ℝ) / 2^b

lemma weight_nonneg (p : A → ℝ) (b : ℕ) (default a : A) : 0 ≤ weight p b default a := by
  unfold weight
  positivity

lemma weight_total (p : A → ℝ) (hp : ∀ a, 0 ≤ p a)
    (ht : ∑ a, p a = 1) (b : ℕ) (default : A) : ∑ a, weight p b default a = 1 := by
  simp only [weight,← Finset.sum_div,← Nat.cast_sum,count_total p hp ht b default,Nat.cast_pow,Nat.cast_ofNat]
  exact div_self (by positivity)

noncomputable def allocation (p : A → ℝ) (hp : ∀ a, 0 ≤ p a)
    (ht : ∑ a, p a = 1) (b : ℕ) (default : A) :
    (Fin b → Bool) ≃ (Σ a, Fin (count p b default a)) :=
  Fintype.equivOfCardEq (by
    simpa only [Fintype.card_fun,Fintype.card_bool,Fintype.card_fin,Fintype.card_sigma]
      using (count_total p hp ht b default).symm)

noncomputable def draw (p : A → ℝ) (hp : ∀ a, 0 ≤ p a)
    (ht : ∑ a, p a = 1) (b : ℕ) (default : A) (bits : Fin b → Bool) : A :=
  (allocation p hp ht b default bits).1

end MetricKMedianRecovery.Dyadic

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_SamplerContext
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Dyadic.Canonical
open FiniteSampling
variable {A : Type*}
lemma select_sum (d : A) (ws : List (A×ℕ)) (T : ℕ)
    (hT : (ws.map Prod.snd).sum≤T) (f : A→ℝ) :
    (∑ v∈Finset.range T, f (select d ws v))=
      (ws.map (fun aw=>(aw.2:ℝ)*f aw.1)).sum+(T-(ws.map Prod.snd).sum)*f d := by
  induction ws generalizing T with
  | nil=>simp [select]
  | cons aw ws ih=>
    rcases aw with ⟨a,w⟩
    simp only [List.map_cons,List.sum_cons] at hT ⊢
    have hw : w≤T := by omega
    have ht : (ws.map Prod.snd).sum≤T-w := by omega
    conv_lhs => rw [show T=w+(T-w) by omega,Finset.sum_range_add]
    have hh : (∑ v∈Finset.range w,f (select d ((a,w)::ws) v))=(w:ℝ)*f a := by
      simp only [select]
      rw [Finset.sum_congr rfl (fun v hv=>congrArg f (ite_eq_left (Finset.mem_range.mp hv)))]
      simp
    rw [hh]
    have he : (∑ v∈Finset.range (T-w),f (select d ((a,w)::ws) (w+v)))=
        ∑ v∈Finset.range (T-w),f (select d ws v) := by
      apply Finset.sum_congr rfl
      intro v _
      simp [select,show ¬w+v<w by omega]
    rw [he,ih (T-w) ht]
    rw [Nat.cast_sub hw,Nat.cast_add]
    ring
variable [Fintype A] [DecidableEq A]
omit [DecidableEq A] in
lemma list_sum (p : A→ℝ) (b : ℕ) (as : List A) (h : as.Perm (Finset.univ.toList)) :
    ((list p b as).map Prod.snd).sum=∑ a,rawCount p b a := by
  simp only [list,List.map_map,Function.comp_def]
  rw [(h.map (rawCount p b)).sum_eq]
  exact Finset.sum_map_toList _ _
end MetricKMedianRecovery.Dyadic.Canonical

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_SamplingRate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Guided.FixedDyadic
open FiniteSampling
variable {S A : Type*} [Fintype A] [DecidableEq A]

noncomputable def kernel (p : Kernel S A) (b : ℕ) (default : A) : Kernel S A where
  weight s := Dyadic.weight (p.weight s) b default
  nonneg s := Dyadic.weight_nonneg (p.weight s) b default
  total s := Dyadic.weight_total (p.weight s) (p.nonneg s) (p.total s) b default

noncomputable def draw (p : Kernel S A) (b : ℕ) (default : A) (s : S)
    (bits : Fin b → Bool) : A := Dyadic.draw (p.weight s) (p.nonneg s) (p.total s) b default bits

noncomputable def actions (f : S → A → S) (p : Kernel S A) (b : ℕ) (default : A) :
    (n : ℕ) → S → (Fin n → Fin b → Bool) → (Fin n → A)
  | 0, _, _ => Fin.elim0
  | n+1, s, bits =>
    let a := draw p b default s (bits 0)
    Fin.cons a (actions f p b default n (f s a) (Fin.tail bits))

end MetricKMedianRecovery.Guided.FixedDyadic

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_RealizedKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Guided.Realized
open FiniteSampling
variable {S A Ω : Type*} [Fintype A] [Fintype Ω]

structure Draw (p : Kernel S A) where
  run : S→Ω→A
  law : ∀ s (g : A→ℝ), average (fun ω=>g (run s ω))=∑ a,p.weight s a*g a
noncomputable def actions (f : S→A→S) (p : Kernel S A) (r : Draw (Ω:=Ω) p) :
    (n : ℕ)→S→(Fin n→Ω)→(Fin n→A)
  | 0,_,_=>Fin.elim0
  | n+1,s,bits=>let a:=r.run s (bits 0); Fin.cons a (actions f p r n (f s a) (Fin.tail bits))
end MetricKMedianRecovery.Guided.Realized

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CopyComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Completion.CopyGround
variable {n a : ℕ}
noncomputable def transversal (H : Fin a→Finset (Fin n)) (v : Fin a→Fin n) (hv : ∀ i,v i∈H i) : Finset (Fin (a*n)) :=
  Finset.univ.image (fun i=>embed H ⟨i,⟨v i,hv i⟩⟩)
end MetricKMedianRecovery.Completion.CopyGround

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_DyadicGrid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.DyadicGrid
def interval (a b : ℚ) (g : State) : ℚ×ℚ := (point a b g.1 g.2.2,point a b g.2.1 g.2.2)
def advance (count : ℚ→ℕ) (k : ℕ) (a b : ℚ) (g : State) : State :=
  if k ≤ count (point a b (g.1+g.2.1) (2*g.2.2)) then (g.1+g.2.1,2*g.2.1,2*g.2.2)
  else (2*g.1,g.1+g.2.1,2*g.2.2)
end MetricKMedianRecovery.DyadicGrid

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_CorrectionSize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CanonicalCoupledMerge
open RationalLeaves
variable {V : Type*} [LinearOrder V] {d : ℕ}
def Correction.Keys (q : ℕ) : Correction V→Prop
  | .identity=>True
  | .shorten key _ _ _=>key<3*q
end MetricKMedianRecovery.CanonicalCoupledMerge

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_DeleteFold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CanonicalDelete
open PhaseSequence CanonicalMergePath
variable {X : Type*} [DecidableEq X]

def step (complete : Finset X → List X) (Q : Finset X) (C : List X) (ci : X)
    (s : Acc X) (_ : X) : Acc X :=
  let U:=s.remaining.tail
  let E:=s.extras++complete (Q∪(C++U++ci::s.extras).toFinset)
  ⟨U,E,s.vertices++[C++U++ci::E]⟩

structure Bounds (P : X → Prop) (N n : ℕ) (s : Acc X) : Prop where
  remaining : s.remaining.length≤N
  extras : s.extras.length≤N+n*N
  vertices : s.vertices.length≤N+n
  vertex : ∀ H∈s.vertices,H.length≤3*N+1+n*N
  rem_mem : ∀ x∈s.remaining,P x
  ext_mem : ∀ x∈s.extras,P x
  vert_mem : ∀ H∈s.vertices,∀ x∈H,P x

end MetricKMedianRecovery.CanonicalDelete

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_MatchFold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CanonicalMatch
open CanonicalMergePath PhaseSequence PhaseMergePath
variable {X D : Type*} [DecidableEq X]

def step (complete : Finset X → List X) (Q : Finset X) (copy : X → X)
    (s : Acc X) (i : X) : Acc X :=
  let a:=advancePrefix complete Q copy s.front s.rest i
  ⟨s.front++[i],a.1,s.vertices++a.2⟩
end MetricKMedianRecovery.CanonicalMatch

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_ClassSlotsMem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.LocalSearch
variable {V : Type*} [PseudoMetricSpace V]

noncomputable def cost (D S : Finset V) : ℝ := ∑ p ∈ D, connection S p

lemma connection_nonneg (S : Finset V) (p : V) : 0 ≤ connection S p := by
  unfold connection
  split_ifs with h
  · exact Finset.le_inf' h _ (fun _ _ => dist_nonneg)
  · rfl
lemma connection_le {S : Finset V} {p s : V} (hs : s ∈ S) : connection S p ≤ dist p s := by
  rw [connection,dite_eq_left ⟨s,hs⟩]
  exact Finset.inf'_le _ hs
lemma cost_nonneg (D S : Finset V) : 0 ≤ cost D S :=
  Finset.sum_nonneg (fun _ _ => connection_nonneg _ _)
lemma nearest_mem (S : Finset V) (hS : S.Nonempty) (p : V) : nearest S hS p ∈ S :=
  (Classical.choose_spec (Finset.exists_min_image S (dist p) hS)).1
lemma nearest_distance (S : Finset V) (hS : S.Nonempty) (p : V) :
    dist p (nearest S hS p) = connection S p := by
  rw [connection,dite_eq_left hS]
  exact le_antisymm (Finset.le_inf' hS _
    (Classical.choose_spec (Finset.exists_min_image S (dist p) hS)).2)
    (Finset.inf'_le _ (nearest_mem S hS p))

variable [DecidableEq V]

def WidthLocalMin (F D S : Finset V) (w : ℕ) : Prop :=
  ∀ T ⊆ F, T.card = S.card → (S \ T).card ≤ w → (T \ S).card ≤ w → cost D S ≤ cost D T

end MetricKMedianRecovery.LocalSearch

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Strictness_Dual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.PhaseOriginalLedger
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion HistoryPhaseBound PhaseMergeCertificate
universe uD uX
variable {D : Type uD} {X : Type uX} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

def Dual (loc : D → X) (F : Finset X) (v lam : ℝ) (alpha : D → ℝ) : Prop :=
  (∀ j, 0 < alpha j) ∧
  (∀ i ∈ F, (∑ j, max (alpha j-2*dist i (loc j)) 0) ≤ lam) ∧
  (∀ (C : Finset D), C.Nonempty → ∀ i ∈ F, ∀ b : ℝ, 0 < b →
    0 < (∑ j ∈ C, dist i (loc j)) → lam ≤ b*(∑ j ∈ C, dist i (loc j)) →
    v^2 ≤ strictnessGap b/(6*(b+2)) →
    (∑ j ∈ C, alpha j) ≤ lam+(2-strictnessGap b/2)*(∑ j ∈ C, dist i (loc j)))

end MetricKMedianRecovery.PhaseOriginalLedger

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Produce
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.LocalSearch
variable {V : Type*} [PseudoMetricSpace V]

noncomputable def optimum (F D : Finset V) (r : ℕ) : ℝ :=
  if h : (feasibleSets F r).Nonempty then (feasibleSets F r).inf' h (cost D) else 0

end MetricKMedianRecovery.LocalSearch

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_AllBad
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.IntegralCandidates
open LocalSearch Anchoring Completion Sampling
variable {V : Type*} [MetricSpace V] [LinearOrder V] [Fintype V]

omit [LinearOrder V] [Fintype V] in
lemma comparisonCost_nearest (D O : Finset V) (hO : O.Nonempty) :
    comparisonCost D (LocalSearch.nearest O hO) = cost D O := by
  simp only [comparisonCost,cost,nearest_distance]

noncomputable def allBad (D S O : Finset V) (hO : O.Nonempty) (hcard : S.card = O.card) :
    Comparison D S O where
  assign := LocalSearch.nearest O hO
  assigned := fun p _ => nearest_mem O hO p
  nearest := fun p _ i hi => (nearest_distance O hO p).trans_le (connection_le hi)
  good := ∅
  good_subset := Finset.empty_subset _
  proxy := id
  proxy_mem := by simp
  proxy_inj := by simp
  same_card := hcard
  proxy_cost := by
    simp only [Finset.sum_empty,zero_add,comparisonCost_nearest]
    exact mul_nonneg (by norm_num) (cost_nonneg D O)

end MetricKMedianRecovery.IntegralCandidates

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_LengthHeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CanonicalLengthSearch
open RationalHeight
variable {X : Type*} [DecidableEq X]

def Result.Bounded (h : ℕ) : Result X → Prop
  | .success s _ => Height s h
  | .bracket l u _ _ => Height l h ∧ Height u h

end MetricKMedianRecovery.CanonicalLengthSearch

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_RefineMath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CanonicalMergeRefinement
variable {X Y : Type*}
variable [DecidableEq X]
def refinedEdge (F : Finset X) (R : List X) (copy spare : X → X) (H G : List X) : List (List X) :=
  match view F R copy H G with
  | none=>[G]
  | some J=>J.expand spare G
end MetricKMedianRecovery.CanonicalMergeRefinement

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_RegularChain
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CanonicalMergeCrossing
variable {A B : Type*}

variable {X : Type*} [DecidableEq X]
def transition (F Q : Finset X) (k : ℕ) (P R : List X × List (List X)) : Option (Result X) :=
  if finalCount F Q R.1 R.2=k then some (.success R.1 R.2)
  else if PhaseCountCrossing.Sandwich k (finalCount F Q P.1 P.2) (finalCount F Q R.1 R.2) then
    some (edge F Q k P.1 R.1 P.2 R.2)
  else none
end MetricKMedianRecovery.CanonicalMergeCrossing

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_InitialProject
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CanonicalCoupledMerge
open PhaseOriginalLedger HistoryPhaseBound
variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V] {d : ℕ}
def LowCertificate (loc : Fin d→V) (F S : Finset V) (v lo : ℝ) (k : ℕ) : Prop :=
  S⊆F ∧ S.Nonempty ∧ S.card≤k ∧ ∃ (Q : ℝ) (alpha : Fin d→ℝ),
    0≤Q ∧ (∑ j,nearestDistance (loc j) S)≤Q ∧ Dual loc F v lo alpha ∧
      (1-3*v)*Q≤∑ j,alpha j
def NormalCertificate (loc : Fin d→V) (F S : Finset V) (v lo hi eta : ℝ) (total k : ℕ) : Prop :=
  S⊆F ∧ S.Nonempty ∧ S.card≤k+3*total ∧ ∃ (lam Q : ℝ) (alpha : Fin d→ℝ),
    lo≤lam ∧ lam≤hi ∧ 0≤Q ∧ (∑ j,nearestDistance (loc j) S)≤Q ∧ Dual loc F v lam alpha ∧
      (1-3*v)*Q+(k:ℝ)*(lam-(d:ℝ)*eta)≤∑ j,alpha j
end MetricKMedianRecovery.CanonicalCoupledMerge

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_SamplingPotential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalSampling
open BitMachine RationalHeight
variable {n : ℕ}
def State.Bounded (m : ℕ) (s : State n) : Prop := s.leaves.length ≤ m ∧ s.deleted.card ≤ m
end MetricKMedianRecovery.RationalSampling

end OAI
end


