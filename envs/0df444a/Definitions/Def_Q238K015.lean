-- Prove2me | Definitions.Def_Q238K015
-- name    : Q238K015
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T23:14:05.262196+00:00
-- url     : https://prove2.me/theorems/842d7acb-fea8-4d32-9f32-991abc6d655a
-- title:
--   Definitions bundle Q238K015 of the split of OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 77 declarations of OpenAI's Lean: 53 definitions, 2 inductive types or structures and 22 theorems. The definitions and types are `OAI.MetricKMedianRecovery.CertifiedRegularStep`, `OAI.MetricKMedianRecovery.ClippingTransfer.effectiveBid`, `OAI.MetricKMedianRecovery.ColorLabel.binaryDistinctMass`, `OAI.MetricKMedianRecovery.ColorLabel.labelMass`, `OAI.MetricKMedianRecovery.Completion.CopyGround.transversal`, `OAI.MetricKMedianRecovery.Completion.saving`, `OAI.MetricKMedianRecovery.CountedHistoryExecution.Step`, `OAI.MetricKMedianRecovery.Dyadic.allocation`, `OAI.MetricKMedianRecovery.Dyadic.count`, `OAI.MetricKMedianRecovery.Dyadic.draw`, `OAI.MetricKMedianRecovery.Dyadic.weight`, `OAI.MetricKMedianRecovery.DyadicGrid.advance`, `OAI.MetricKMedianRecovery.DyadicGrid.interval`, `OAI.MetricKMedianRecovery.EffectiveOpenability.indexedCoeff`, `OAI.MetricKMedianRecovery.EffectiveOpenability.indexedDualCoeff`, `OAI.MetricKMedianRecovery.EffectiveOpenability.indexedPaymentCoeff`, `OAI.MetricKMedianRecovery.Ellipsoid.Face`, `OAI.MetricKMedianRecovery.Guided.FixedDyadic.actions`, `OAI.MetricKMedianRecovery.Guided.FixedDyadic.draw`, `OAI.MetricKMedianRecovery.Guided.FixedDyadic.kernel`, `OAI.MetricKMedianRecovery.Guided.Realized.Draw`, `OAI.MetricKMedianRecovery.Guided.Realized.actions`, `OAI.MetricKMedianRecovery.IntegralCandidates.allBad`, `OAI.MetricKMedianRecovery.LocalSearch.WidthLocalMin`, `OAI.MetricKMedianRecovery.LocalSearch.cost`, `OAI.MetricKMedianRecovery.LocalSearch.optimum`, `OAI.MetricKMedianRecovery.OpenabilityLinearization.Feasible`, `OAI.MetricKMedianRecovery.OpenabilityLinearization.dualTerm`, `OAI.MetricKMedianRecovery.OpenabilityLinearization.linearPayment`, `OAI.MetricKMedianRecovery.OrdinaryProducer.PhaseMaximal`, `OAI.MetricKMedianRecovery.OrdinaryProducer.PlainOpening`, `OAI.MetricKMedianRecovery.PhaseMergeCertificate.Budget`, `OAI.MetricKMedianRecovery.Population.radius`, `OAI.MetricKMedianRecovery.RadiusMenus.menuConstant`, `OAI.MetricKMedianRecovery.RationalLinearFeasibility.Row.RealHolds`, `OAI.MetricKMedianRecovery.RationalLinearFeasibility.Row.realValue`, `OAI.MetricKMedianRecovery.RationalMetricInput.outputBits`, `OAI.MetricKMedianRecovery.RationalOpenability.dualForm`, `OAI.MetricKMedianRecovery.RationalOpenability.paymentForm`, `OAI.MetricKMedianRecovery.RationalOpenability.system` and 15 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedianRecovery_Algorithms_FinalBudgetPos`, `KMedianRecovery_Branching_CopyComparison`, `KMedianRecovery_Encoding_LabelRange`, `KMedianRecovery_Geometry_Metric`, `KMedianRecovery_Geometry_Nearest`, `KMedianRecovery_Machines_FirstSize`, `KMedianRecovery_Recovery_AllBad`, `KMedianRecovery_Recovery_Ball`, `KMedianRecovery_Recovery_ClassSlotsMem`, `KMedianRecovery_Recovery_Cluster`, `KMedianRecovery_Recovery_CountedTrace`, `KMedianRecovery_Recovery_CoveredCenter`, `KMedianRecovery_Recovery_DyadicGrid`, `KMedianRecovery_Recovery_EntryReplay`, `KMedianRecovery_Recovery_Produce`, `KMedianRecovery_Recovery_RawCount`, `KMedianRecovery_Recovery_ReferenceBridge`, `KMedianRecovery_Recovery_Removal`, `KMedianRecovery_Recovery_ReverseRow`, `KMedianRecovery_Recovery_Row`, `KMedianRecovery_Recovery_Score`, `KMedianRecovery_Recovery_State2`, `KMedianRecovery_Recovery_StoredForms`, `KMedianRecovery_Recovery_VirtualCast`, `KMedianRecovery_Sampling_RealizedKernel`, `KMedianRecovery_Sampling_SamplerContext`, `KMedianRecovery_Sampling_SamplerDraw`, `KMedianRecovery_Sampling_SamplingPotential`, `KMedianRecovery_Sampling_SamplingRate`, `KMedianRecovery_Strictness_Clipped`, `KMedianRecovery_Strictness_ClippedBid`, `KMedianRecovery_Strictness_IndexedPaymentCoeff`, `KMedianRecovery_Strictness_LinearPayment`.
--
--   **Imports.** It imports the published bundle `Def_KMedianRefinedRecovery`; the bundles `Q238K000`, `Q238K002`, `Q238K003`, `Q238K004` and `Q238K005` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q238K022` and `Q238K023`; the statements `OAI.MetricKMedianRecovery.Anchoring.anchoring_s238`, `OAI.MetricKMedianRecovery.Anchoring.total_assignment_excess_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.result_guarantee_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryLocalRefine.integral_spec_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMetricAnchor.produce_s238`, `OAI.MetricKMedianRecovery.Ellipsoid.boundedRationalDecide_correct_s238`, `OAI.MetricKMedianRecovery.Ellipsoid.finalFace_feasible_s238`, `OAI.MetricKMedianRecovery.Ellipsoid.iterate_contains_s238`, `OAI.MetricKMedianRecovery.Ellipsoid.selectFace_spec_s238`, `OAI.MetricKMedianRecovery.Ellipsoid.weakSolve_complete_diameters_s238`, `OAI.MetricKMedianRecovery.IntegralCandidates.separated_comparison_s238`, `OAI.MetricKMedianRecovery.LocalSearch.local_combined_cost_bound_s238`, `OAI.MetricKMedianRecovery.LocalSearch.local_five_approx_s238`, `OAI.MetricKMedianRecovery.LocalSearch.optimum_attained_exact_s238`, `OAI.MetricKMedianRecovery.LocalSearch.optimum_attained_s238`, `OAI.MetricKMedianRecovery.PhaseSurplusProducer.normal_cost_s238`, `OAI.MetricKMedianRecovery.Sensitivity.sensitive_optimum_s238` and `OAI.MetricKMedianRecovery.Surplus.protected_partition_cost_s238`; the proofs of `OAI.MetricKMedianRecovery.Anchoring.anchoring_s238`, `OAI.MetricKMedianRecovery.Anchoring.total_assignment_excess_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionFair.result_guarantee_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat.amplified_s238`, `OAI.MetricKMedianRecovery.Ellipsoid.finalFace_feasible_s238`, `OAI.MetricKMedianRecovery.Ellipsoid.iterate_contains_s238`, `OAI.MetricKMedianRecovery.Ellipsoid.selectFace_spec_s238`, `OAI.MetricKMedianRecovery.IntegralCandidates.separated_comparison_s238`, `OAI.MetricKMedianRecovery.LocalSearch.local_combined_cost_bound_s238`, `OAI.MetricKMedianRecovery.LocalSearch.local_five_approx_s238`, `OAI.MetricKMedianRecovery.LocalSearch.optimum_attained_exact_s238`, `OAI.MetricKMedianRecovery.LocalSearch.optimum_attained_s238`, `OAI.MetricKMedianRecovery.PhaseParameterTransfer.prefix_map_s238`, `OAI.MetricKMedianRecovery.PhaseSurplusProducer.normal_cost_s238`, `OAI.MetricKMedianRecovery.Sensitivity.sensitive_optimum_s238` and `OAI.MetricKMedianRecovery.Surplus.protected_partition_cost_s238`.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_KMedianRefinedRecovery
import Definitions.Def_Q238K000
import Definitions.Def_Q238K002
import Definitions.Def_Q238K003
import Definitions.Def_Q238K004
import Definitions.Def_Q238K005

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
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_Nearest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalOpenability
open RationalLinearFeasibility OpenabilityLinearization
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

noncomputable def paymentForm (loc : D → X) (d : X → D → ℚ) (F W : Finset X)
    (v z : ℚ) (i : X) : Form (Variables D F) := by
  classical
  exact Form.sum (fun j => if activeAt loc (1-3*(v:ℝ)) (z:ℝ) W j then
    if dist i (loc j) ≤ (v:ℝ)*(z:ℝ) then (bid F j).sub (Form.const ((1-3*v)*d i j))
    else Form.const (max (z-(1-3*v)*d i j) 0)
    else Form.const (max ((1-3*v)*nearest d W j-(1-3*v)*d i j) 0))

noncomputable def dualForm (loc : D → X) (d : X → D → ℚ) (F W : Finset X)
    (v z : ℚ) (f : F) (a j : D) : Form (Variables D F) := by
  classical
  exact if activeAt loc (1-3*(v:ℝ)) (z:ℝ) W j then
    (bid F j).sub (Form.const (d f j))
    else (bid F a).sub (Form.const (2*d f j+d f a))

noncomputable def system (loc : D → X) (d : X → D → ℚ) (F W : Finset X)
    (v z lam eta : ℚ) (i : X) : Kind D W F → Form (Variables D F) := by
  classical
  exact fun k => match k with
  | .lower j => if activeAt loc (1-3*(v:ℝ)) (z:ℝ) W j then (Form.const z).sub (bid F j) else Form.const 0
  | .upper j => if activeAt loc (1-3*(v:ℝ)) (z:ℝ) W j then (bid F j).sub (Form.const ((1+v^2)*z)) else Form.const 0
  | .cap j f => if activeAt loc (1-3*(v:ℝ)) (z:ℝ) W j then (bid F j).sub (Form.const ((1-3*v)*d f j)) else Form.const 0
  | .far j => if activeAt loc (1-3*(v:ℝ)) (z:ℝ) W j ∧ (v:ℝ)*(z:ℝ)<dist i (loc j) then (bid F j).sub (Form.const z) else Form.const 0
  | .payment => (Form.const (lam-(Fintype.card D:ℚ)*eta)).sub (paymentForm loc d F W v z i)
  | .slackZero f a j => if activeAt loc (1-3*(v:ℝ)) (z:ℝ) W a then (Form.const 0).sub (slack f a j) else Form.const 0
  | .slackTerm f a j => if activeAt loc (1-3*(v:ℝ)) (z:ℝ) W a then (dualForm loc d F W v z f a j).sub (slack f a j) else Form.const 0
  | .dual f a => if activeAt loc (1-3*(v:ℝ)) (z:ℝ) W a then (Form.sum (fun j => slack f a j)).sub (Form.const lam) else Form.const 0

end MetricKMedianRecovery.RationalOpenability

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

noncomputable def State.real {m d : ℕ} (s : State m d) : ExecutionState (Fin d) (Fin m) :=
  ⟨s.opened,(s.phase:ℝ),fun j => (s.budget[j]:ℝ)⟩

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

inductive Instruction (m d : ℕ) where
  | opening : Event m d → Instruction m d
  | advance : Instruction m d

end MetricKMedianRecovery.RationalPhase

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

noncomputable def effectiveBid (loc : D → X) (t z : ℝ) (W : Finset X)
    (tau : D → ℝ) (j : D) : ℝ := by
  classical
  exact if activeAt loc t z W j then tau j else t*nearestDistance (loc j) W

end ClippingTransfer
end MetricKMedianRecovery

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
open PhaseHistoryTransfer PhaseMergeCompletion HistoryPhaseBound
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
-- module Solutions.Q238_KM.KMedianRecovery_Machines_FirstSize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RadiusMenus

lemma first_menu_available (kappa q r : ℝ) (hk : 0 < kappa) (hq : 0 < q)
    (hr : 0 ≤ r) (hsmall : r ≤ 10*q) :
    1 ≤ upwardIndex kappa q r ∧ upwardIndex kappa q r ≤ firstSize kappa ∧
      r ≤ additiveRadius kappa q (upwardIndex kappa q r) ∧
      additiveRadius kappa q (upwardIndex kappa q r) ≤ (1+kappa)*r+kappa*q := by
  have hrq : r/(kappa*q) ≤ 10/kappa := by
    apply (div_le_div_iff₀ (mul_pos hk hq) hk).mpr
    nlinarith
  have hceil := Nat.ceil_mono hrq
  have hbound : upwardIndex kappa q r ≤ firstSize kappa := by
    unfold upwardIndex firstSize
    omega
  have hb := upward_radius_bounds kappa q r hk hq hr
  exact ⟨le_max_left _ _, hbound, hb.1, hb.2.trans (by nlinarith [mul_nonneg hk.le hr])⟩

lemma third_menu_available (kappa q r : ℝ) (m : ℕ) (hk : 0 < kappa)
    (hq : 0 < q) (hr : 0 < r) (hbudget : r/q ≤ (10/9 : ℝ)*m) :
    1 ≤ Nat.ceil (r/(kappa*q)) ∧ Nat.ceil (r/(kappa*q)) ≤ thirdSize kappa m ∧
      r ≤ additiveRadius kappa q (Nat.ceil (r/(kappa*q))) ∧
      additiveRadius kappa q (Nat.ceil (r/(kappa*q))) ≤ (1+kappa)*r+kappa*q := by
  have hj : 0 < Nat.ceil (r/(kappa*q)) := Nat.ceil_pos.mpr (div_pos hr (mul_pos hk hq))
  have he : r/(kappa*q) = (r/q)/kappa := by ring
  have hratio : r/(kappa*q) ≤ 2*m/kappa := by
    rw [he]
    apply div_le_div_of_nonneg_right _ hk.le
    nlinarith [Nat.cast_nonneg (α := ℝ) m]
  have hm := Nat.ceil_mono hratio
  have hidx : upwardIndex kappa q r = Nat.ceil (r/(kappa*q)) := max_eq_right hj
  have hu := upward_radius_bounds kappa q r hk hq hr.le
  rw [hidx] at hu
  refine ⟨hj, ?_, hu.1, hu.2.trans ?_⟩
  · dsimp [thirdSize]
    omega
  · nlinarith [mul_nonneg hk.le hr.le]

lemma geometricCap_spec (kappa : ℝ) (hk : 0 < kappa) :
    10 ≤ (1+kappa)^(geometricCap kappa hk) := Nat.find_spec (geometric_exists kappa hk)

lemma geometric_menu_available (kappa D r : ℝ) (hk : 0 < kappa)
    (hr : 0 < r) (hlow : r ≤ D) (hupp : D ≤ 10*r) :
    ∃ e ≤ geometricCap kappa hk,
      r ≤ D/(1+kappa)^e ∧ D/(1+kappa)^e ≤ (1+kappa)*r := by
  have hb : 1 < 1+kappa := by linarith
  have hratio : 1 ≤ D/r := (le_div_iff₀ hr).mpr (by simpa only [one_mul] using hlow)
  obtain ⟨e, he₀, he₁⟩ := exists_nat_pow_near hratio hb
  have hpow : 0 < (1+kappa)^e := pow_pos (by linarith) _
  have heE : e ≤ geometricCap kappa hk := by
    by_contra hh
    have hegt : geometricCap kappa hk < e := lt_of_not_ge hh
    have hn := pow_lt_pow_right₀ hb hegt
    have hcap := geometricCap_spec kappa hk
    have hratio' : D/r ≤ 10 := (div_le_iff₀ hr).mpr hupp
    linarith
  refine ⟨e, heE, ?_, ?_⟩
  · apply (le_div_iff₀ hpow).mpr
    have hh := (le_div_iff₀ hr).mp he₀
    nlinarith
  · apply (div_le_iff₀ hpow).mpr
    have hh := (div_lt_iff₀ hr).mp he₁
    rw [pow_succ] at hh
    nlinarith

noncomputable def menuConstant (kappa : ℝ) (hk : 0 < kappa) : ℝ :=
  min (1/(3*(firstSize kappa : ℝ)))
    (min (1/(3*((geometricCap kappa hk : ℝ)+1))) (1/3))

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

noncomputable def radius (D : Finset V) (hn : D.Nonempty)
    (P : ℝ) (m : ℕ) (w : V) : ℝ := D.inf' hn (candidate D P m w)

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
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_State2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Sampling

namespace State
variable {V : Type*}
def initial : State V := ⟨∅, []⟩
end State

variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V]

noncomputable def tagDistance (Δ : ℝ) (s : State V) (x : V) (t : Tag V) : ℝ :=
  match ofLex t with
  | .inl v => dist x v
  | .inr 0 => Δ
  | .inr (j+1) => match s.leaves[j]? with
    | some z => dist x z.1 + z.2
    | none => Δ

noncomputable def chosen (S : Finset V) (Δ : ℝ) (s : State V) (x : V) : Tag V :=
  Classical.choose (Finset.exists_min_image (tags S s)
    (fun t => toLex (tagDistance Δ s x t,t)) (tags_nonempty S s))

end MetricKMedianRecovery.Sampling

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Cluster
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Sampling
variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V]

namespace Comparison
variable {D S O : Finset V}
noncomputable def bad (C : Comparison D S O) : Finset V := O \ C.good
noncomputable def nonproxy (C : Comparison D S O) : Finset V := S \ C.good.image C.proxy

end Comparison
end MetricKMedianRecovery.Sampling

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_CoveredCenter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Sampling
open Completion
variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V]

def toVirtual (s : State V) (t : Tag V) : Virtual V s.leaves.length :=
  match ofLex t with
  | .inl v => .real v
  | .inr 0 => .permanent
  | .inr (j+1) => if h : j < s.leaves.length then .ball ⟨j,h⟩ else .permanent

noncomputable def completionAssignment (S : Finset V) (Δ : ℝ) (s : State V) (x : V) :=
  toVirtual s (chosen S Δ s x)

end MetricKMedianRecovery.Sampling

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_LabelRange
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.ColorLabel

noncomputable def labelMass (b : ℕ) (hb : 0 < b) (j : Fin b) : ℝ :=
  ∑ x : Fin (labelRange b), if label b hb x = j then 1/(labelRange b : ℝ) else 0

noncomputable def binaryDistinctMass (b : ℕ) (hb : 0 < b) : ℝ :=
  ∑ seed : Fin b → Fin (labelRange b),
    if Function.Injective (fun i => label b hb (seed i))
    then (1/(labelRange b : ℝ))^b else 0

end MetricKMedianRecovery.ColorLabel

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_ReferenceBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalSampling
open Sampling
open BitMachine BinarySamplingReference
variable {n l : ℕ}
def fromArrays (T : Finset (Fin n)) (v : Fin l→Fin n) (r : Fin l→ℚ) : State n :=
  ⟨T,List.ofFn (fun j=>(v j,r j))⟩
end MetricKMedianRecovery.RationalSampling

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_RawCount
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
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_VirtualCast
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalSampling
open Completion
variable {n : ℕ}
lemma State.real_length (s : State n) : s.real.leaves.length=s.leaves.length := List.length_map _
def State.center (s : State n) (i : Fin s.leaves.length) : Fin n := s.leaves[i.val].1
def State.radius (s : State n) (i : Fin s.leaves.length) : ℝ := (s.leaves[i.val].2:ℝ)
variable [PseudoMetricSpace (Fin n)]
noncomputable def State.assignment (S : Finset (Fin n)) (Δ : ℚ) (s : State n) : Fin n→Virtual (Fin n) s.leaves.length :=
  Virtual.cast s.real_length ∘ Sampling.completionAssignment S (Δ:ℝ) s.real
end MetricKMedianRecovery.RationalSampling

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
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_Metric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalMetricInput

def outputBits (I : RationalMetricInput) (S : Finset (Fin I.pointCount)) : List Bool :=
  List.ofFn (fun i : Fin I.pointCount => decide (i ∈ S))

end MetricKMedianRecovery.RationalMetricInput

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
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_SamplerDraw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalSampling
open BitMachine RationalHeight
variable {n : ℕ}
def State.Height (s : State n) (H : ℕ) : Prop := ∀ z∈s.leaves,RationalHeight.Height z.2 H
end MetricKMedianRecovery.RationalSampling

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


