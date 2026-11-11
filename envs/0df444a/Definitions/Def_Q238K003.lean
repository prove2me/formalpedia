-- Prove2me | Definitions.Def_Q238K003
-- name    : Q238K003
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T23:10:51.727578+00:00
-- url     : https://prove2.me/theorems/01a94751-c829-4696-abaa-054bc1885c0c
-- title:
--   Definitions bundle Q238K003 of the split of OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 126 declarations of OpenAI's Lean: 96 definitions, 11 inductive types or structures, 1 instance and 18 theorems. The definitions and types are `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchTape.colorCount`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchTape.labelCount`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchTape.split`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.Resources.capPoly`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.Tape.K`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.Tape.M`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.Tape.split`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.Tape.tensorPair`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.elemBits`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.omitted`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.runCapPoly`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionFill.elemBits`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupled.bound`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupled.boundPoly`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledLoop.capPoly`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledState.bankBound`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledState.bound`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledState.historyBound`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledState.labelBound`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDuplicateMatrix.duplicate`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDuplicateMatrix.forget`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDuplicateMatrix.twice`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDyadic.power`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalRounding.duplicateMetric`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalZero.key`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalZero.keys`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalZero.output`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalZero.pick`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInputParser.Metric.flat`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInputParser.Metric.mask`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInputParser.Stream.raw`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat.FiniteTape.layout`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInverseCDF.encodeOption`, `OAI.MetricKMedianRecovery.BitMachine.BinaryLabel.orderedSort`, `OAI.MetricKMedianRecovery.BitMachine.BinaryLocalSearch.capPoly`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMatch.capacityPoly`, `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseCount.dummy`, `OAI.MetricKMedianRecovery.BitMachine.BinaryPopulation.candidateQ`, `OAI.MetricKMedianRecovery.BitMachine.BinaryPopulation.distanceList`, `OAI.MetricKMedianRecovery.BitMachine.BinaryPopulation.radiusQ` and 67 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedianRecovery_Algorithms_GlobalCall`, `KMedianRecovery_Algorithms_GlobalRoundMetric`, `KMedianRecovery_Algorithms_GlobalZero`, `KMedianRecovery_Algorithms_IntegralPrecision`, `KMedianRecovery_Algorithms_IntegralRecoveryAmplified`, `KMedianRecovery_Branching_BlueDPValue`, `KMedianRecovery_Branching_BranchSeedLayout`, `KMedianRecovery_Branching_CategoricalOutput`, `KMedianRecovery_Branching_CategoricalRawPrep`, `KMedianRecovery_Branching_CategoricalResources`, `KMedianRecovery_Branching_CategoricalScore`, `KMedianRecovery_Branching_CategoricalSize`, `KMedianRecovery_Branching_CategoricalTable`, `KMedianRecovery_Branching_CopyGround`, `KMedianRecovery_Branching_PopulationBridge`, `KMedianRecovery_Branching_PopulationMachine`, `KMedianRecovery_Encoding_ColorLabelMachine`, `KMedianRecovery_Encoding_DuplicateMatrix`, `KMedianRecovery_Encoding_LabelOrder`, `KMedianRecovery_Encoding_LabelRange`, `KMedianRecovery_Encoding_PrecisionBits`, `KMedianRecovery_Encoding_RationalMenus`, `KMedianRecovery_Encoding_RationalStream`, `KMedianRecovery_Encoding_StateBits2`, `KMedianRecovery_Geometry_LeafDistances`, `KMedianRecovery_Geometry_LocalBest`, `KMedianRecovery_Geometry_Metric`, `KMedianRecovery_Geometry_MetricParser`, `KMedianRecovery_Geometry_Nearest`, `KMedianRecovery_Geometry_RoundingMatrix`, `KMedianRecovery_Machines_CorrectionSize`, `KMedianRecovery_Machines_DeleteFold`, `KMedianRecovery_Machines_FirstSize`, `KMedianRecovery_Machines_LoopMachine`, `KMedianRecovery_Machines_LoopSize`, `KMedianRecovery_Machines_MatchFold`, `KMedianRecovery_Machines_MatchSize`, `KMedianRecovery_Machines_RecoveryTape`, `KMedianRecovery_Machines_SliceFold`, `KMedianRecovery_Recovery_Basic`, `KMedianRecovery_Recovery_Cap`, `KMedianRecovery_Recovery_EnumeratedRow`, `KMedianRecovery_Recovery_FinImages`, `KMedianRecovery_Recovery_FinishPhase`, `KMedianRecovery_Recovery_FiniteCross`, `KMedianRecovery_Recovery_Form`, `KMedianRecovery_Recovery_FormTrans`, `KMedianRecovery_Recovery_InitialState`, `KMedianRecovery_Recovery_KindRows`, `KMedianRecovery_Recovery_LeafOrder`, `KMedianRecovery_Recovery_LengthSearch`, `KMedianRecovery_Recovery_MergeCross`, `KMedianRecovery_Recovery_MergeRefine`, `KMedianRecovery_Recovery_NearEligible`, `KMedianRecovery_Recovery_RawCount`, `KMedianRecovery_Recovery_RawUnary`, `KMedianRecovery_Recovery_State`, `KMedianRecovery_Recovery_StoredForms`, `KMedianRecovery_Sampling_InverseCDF`, `KMedianRecovery_Sampling_RealizedKernel`, `KMedianRecovery_Sampling_SamplerContext`, `KMedianRecovery_Sampling_SamplerParameters`, `KMedianRecovery_Sampling_SamplerResources`, `KMedianRecovery_Sampling_SeedTensor`, `KMedianRecovery_Sampling_TensorEquiv`, `KMedianRecovery_Strictness_StrictnessGap`.
--
--   **Imports.** It imports the published bundle `Def_KMedianRefinedRecovery`.
--
--   **Imported by** (directly, in this split): the bundles `Q238K011`, `Q238K012`, `Q238K013`, `Q238K014`, `Q238K015` and `Q238K016`.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_KMedianRefinedRecovery

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Form
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalLinearFeasibility

structure Form (V : Type*) where
  constant : ℚ
  coeff : V → ℚ

namespace Form
variable {V I : Type*} [Fintype V]

def eval (f : Form V) (x : V → ℚ) : ℚ := f.constant+∑ v, f.coeff v*x v
noncomputable def realEval (f : Form V) (x : V → ℝ) : ℝ :=
  (f.constant:ℝ)+∑ v, (f.coeff v:ℝ)*x v

def const (c : ℚ) : Form V := ⟨c,fun _ => 0⟩
def coord [DecidableEq V] (v : V) : Form V := ⟨0,fun u => if u=v then 1 else 0⟩
def sub (f g : Form V) : Form V := ⟨f.constant-g.constant,fun v => f.coeff v-g.coeff v⟩
def sum [Fintype I] (f : I → Form V) : Form V := ⟨∑ i, (f i).constant,fun v => ∑ i, (f i).coeff v⟩

@[simp] lemma eval_const (c : ℚ) (x : V → ℚ) : (const c).eval x = c := by simp [eval,const]
@[simp] lemma realEval_const (c : ℚ) (x : V → ℝ) : (const c).realEval x = (c:ℝ) := by simp [realEval,const]
@[simp] lemma eval_coord [DecidableEq V] (v : V) (x : V → ℚ) : (coord v).eval x = x v := by simp [eval,coord]
@[simp] lemma realEval_coord [DecidableEq V] (v : V) (x : V → ℝ) : (coord v).realEval x = x v := by simp [realEval,coord,apply_ite]
@[simp] lemma eval_sub (f g : Form V) (x : V → ℚ) : (f.sub g).eval x = f.eval x-g.eval x := by
  simp only [eval,sub,sub_mul,Finset.sum_sub_distrib]
  ring
@[simp] lemma realEval_sub (f g : Form V) (x : V → ℝ) : (f.sub g).realEval x = f.realEval x-g.realEval x := by
  simp only [realEval,sub,Rat.cast_sub,sub_mul,Finset.sum_sub_distrib]
  ring
@[simp] lemma eval_sum [Fintype I] (f : I → Form V) (x : V → ℚ) :
    (sum f).eval x = ∑ i, (f i).eval x := by
  simp only [eval,sum,Finset.sum_mul,Finset.sum_add_distrib]
  rw [Finset.sum_comm]
@[simp] lemma realEval_sum [Fintype I] (f : I → Form V) (x : V → ℝ) :
    (sum f).realEval x = ∑ i, (f i).realEval x := by
  simp only [realEval,sum,Rat.cast_sum,Finset.sum_mul,Finset.sum_add_distrib]
  rw [Finset.sum_comm]

end Form

end MetricKMedianRecovery.RationalLinearFeasibility

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
open RationalLinearFeasibility
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

def nearest (d : X → D → ℚ) (W : Finset X) (j : D) : ℚ :=
  if h : W.Nonempty then W.inf' h (fun f => d f j) else 0

inductive Kind (D W F : Type*) where
  | lower : D → Kind D W F
  | upper : D → Kind D W F
  | cap : D → W → Kind D W F
  | far : D → Kind D W F
  | payment : Kind D W F
  | slackZero : F → D → D → Kind D W F
  | slackTerm : F → D → D → Kind D W F
  | dual : F → D → Kind D W F
  deriving Fintype

abbrev Variables (D F : Type*) := D ⊕ (F × D × D)

noncomputable def bid (F : Type*) (j : D) : Form (Variables D F) := by
  classical
  exact Form.coord (.inl j)
noncomputable def slack {Facilities : Type*} (f : Facilities) (a j : D) :
    Form (Variables D Facilities) := by
  classical
  exact Form.coord (.inr (f,a,j))

@[simp] lemma bid_eval (F : Type*) [Fintype F] (j : D) (x : Variables D F → ℝ) :
    (bid F j).realEval x = x (.inl j) := by
  classical
  simp [bid]
@[simp] lemma slack_eval (F : Type*) [Fintype F] (f : F) (a j : D) (x : Variables D F → ℝ) :
    (slack f a j).realEval x = x (.inr (f,a,j)) := by
  classical
  simp [slack]

end MetricKMedianRecovery.RationalOpenability

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_EnumeratedRow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.EffectiveOpenability
open RationalLinearFeasibility RationalOpenability
variable {D X : Type*} [Fintype D] [DecidableEq D] [DecidableEq X]

def active (d : X → D → ℚ) (v z : ℚ) (W : Finset X) (j : D) : Prop :=
  ∀ f ∈ W, z < (1-3*v)*d f j
instance activeDecidable (d : X → D → ℚ) (v z : ℚ) (W : Finset X) (j : D) :
    Decidable (active d v z W j) := inferInstanceAs (Decidable (∀ f ∈ W, z < (1-3*v)*d f j))

def bid (F : Type*) [DecidableEq F] (j : D) : Form (Variables D F) := Form.coord (.inl j)

def payment (d : X → D → ℚ) (F W : Finset X) (v z : ℚ) (i : X) : Form (Variables D F) :=
  Form.sum (fun j => if active d v z W j then
    if d i j ≤ v*z then (bid F j).sub (Form.const ((1-3*v)*d i j))
    else Form.const (max (z-(1-3*v)*d i j) 0)
    else Form.const (max ((1-3*v)*nearest d W j-(1-3*v)*d i j) 0))

def dual (d : X → D → ℚ) (F W : Finset X) (v z : ℚ) (f : F) (a j : D) : Form (Variables D F) :=
  if active d v z W j then (bid F j).sub (Form.const (d f j))
  else (bid F a).sub (Form.const (2*d f j+d f a))

end MetricKMedianRecovery.EffectiveOpenability

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_KindRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.EffectiveOpenability

section
open RationalOpenability
variable {D W F : Type*}

def subtypeList {m : ℕ} (F : Finset (Fin m)) : List F :=
  List.ofFn (F.orderIsoOfFin rfl)

end

open RationalOpenability

end MetricKMedianRecovery.EffectiveOpenability

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_FormTrans
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Ellipsoid

open Matrix
open scoped Matrix
variable {V : Type*} [Fintype V] [DecidableEq V]

def gridDenominator (n T : ℕ) : ℕ := 16*n^3*3^(T+1)

end MetricKMedianRecovery.Ellipsoid

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_State
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Ellipsoid
open Matrix RationalLinearFeasibility
open scoped Matrix

structure State (n : ℕ) where
  shape : Matrix (Fin n) (Fin n) ℚ
  center : Fin n → ℚ

end MetricKMedianRecovery.Ellipsoid

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_InitialState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Ellipsoid
open Matrix RationalLinearFeasibility
open scoped Matrix

def initialState (n : ℕ) (R : ℚ) : State n := ⟨(R^2) • 1,0⟩

end MetricKMedianRecovery.Ellipsoid

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine

namespace RationalMin
def minimum (qs : List ℚ) : ℚ := qs.foldl min (qs.head?.getD 0)
end RationalMin
end MetricKMedianRecovery.BitMachine

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
open EffectiveOpenability

structure State (m d : ℕ) where
  opened : Finset (Fin m)
  phase : ℚ
  budget : Vector ℚ d

end MetricKMedianRecovery.RationalPhase

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
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

inductive Jump (X : Type*) where
  | add (i : X)
  | remove (C T A : List X) (i : X)
  | replace (C T : List X) (i : X)
  deriving DecidableEq

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
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

inductive Result (X : Type*) where
  | success (H : List X) (T : List (List X))
  | common (H : List X) (T U : List (List X))
  | sensitive (H G : List X) (T U : List (List X))

end MetricKMedianRecovery.CanonicalMergeCrossing

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
open CanonicalMergeRefinement
variable {X : Type*} [DecidableEq X] {d : ℕ}

inductive Plan (X : Type*) where
  | free (i f : X)
  | paid (C T : List X) (i : X)

end MetricKMedianRecovery.CanonicalLengthView

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_LengthSearch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CanonicalLengthSearch
open CanonicalMergeCrossing
variable {X : Type*} [DecidableEq X]

inductive Result (X : Type*) where
  | success (s : ℚ) (T : List (List X))
  | bracket (l u : ℚ) (T U : List (List X))

end MetricKMedianRecovery.CanonicalLengthSearch

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_LeafOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CanonicalCoupledMerge
open CanonicalMergeCrossing
variable {V : Type*} [DecidableEq V] {d : ℕ}

inductive Correction (V : Type*) where
  | identity
  | shorten (key : ℕ) (i : V) (l u : ℚ)

end MetricKMedianRecovery.CanonicalCoupledMerge

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_LabelOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryLabel

def orderedSort {α : Type*} [LinearOrder α] (s : Finset α) : List α := s.sort (·≤·)

end MetricKMedianRecovery.BitMachine.BinaryLabel

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_FinishPhase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryPhaseCount
open EffectiveOpenability RationalPhase
def dummy (_v : ℚ) : State 0 0 := ⟨∅,1,Vector.replicate 0 0⟩
end MetricKMedianRecovery.BitMachine.BinaryPhaseCount

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_RationalStream
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryInputParser.Stream
abbrev raw (rs : List ℚ) : List Bool := (rs.map RationalMetricInput.rationalBits).flatten
end MetricKMedianRecovery.BitMachine.BinaryInputParser.Stream

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_RawUnary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.RawUnary
def run (x : List Bool) : List Bool := List.replicate x.length true
end MetricKMedianRecovery.BitMachine.RawUnary

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_MetricParser
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryInputParser.Metric
attribute [local irreducible] RawUnary.run
def mask {n : ℕ} (S : Finset (Fin n)) : List Bool := List.ofFn (fun i=>decide (i∈S))
def flat (I : RationalMetricInput) : List ℚ := (List.ofFn (fun i=>List.ofFn (I.distance i))).flatten
end MetricKMedianRecovery.BitMachine.BinaryInputParser.Metric

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_FinImages
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryTaggedSets
variable {n : ℕ}
def left (i : Fin n) : Fin (n+n) := Fin.castLE (Nat.le_add_right n n) i
def right (i : Fin n) : Fin (n+n) := Fin.natAdd n i
end MetricKMedianRecovery.BitMachine.BinaryTaggedSets

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CopyGround
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Completion.CopyGround
variable {n a : ℕ}
def embed (H : Fin a→Finset (Fin n)) (e : (i : Fin a)×(H i)) : Fin (a*n) := finProdFinEquiv (e.1,e.2.val)
noncomputable def origin (H : Fin a→Finset (Fin n)) (hH : ∀ i,(H i).Nonempty) (i : Fin a) : Fin (a*n) :=
  embed H ⟨i,⟨(H i).min' (hH i),Finset.min'_mem _ _⟩⟩
end MetricKMedianRecovery.Completion.CopyGround

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

noncomputable def rawCount (p : A → ℝ) (b : ℕ) (a : A) : ℕ :=
  Nat.floor ((2:ℝ)^b * p a)

end MetricKMedianRecovery.Dyadic

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_PopulationMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryPopulation
def candidateQ (P : ℚ) (m : ℕ) (ds : List ℚ) (d : ℚ) : ℚ :=
  max d (P / ((m:ℚ)*(ds.filter (fun t=>decide (t≤d))).length))
def radiusQ (P : ℚ) (m : ℕ) (ds : List ℚ) : ℚ := RationalMin.minimum (ds.map (candidateQ P m ds))
end MetricKMedianRecovery.BitMachine.BinaryPopulation

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_PopulationBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryPopulation
variable {n : ℕ} [PseudoMetricSpace (Fin n)] (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
def distanceList (D : Finset (Fin n)) (w : Fin n) : List ℚ := (D.sort (·≤·)).map (δ w)
end MetricKMedianRecovery.BitMachine.BinaryPopulation

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

noncomputable def firstSize (kappa : ℝ) : ℕ := Nat.ceil (10/kappa)+1
noncomputable def thirdSize (kappa : ℝ) (m : ℕ) : ℕ := 1+Nat.ceil (2*m/kappa)

lemma geometric_exists (kappa : ℝ) (hk : 0 < kappa) : ∃ e : ℕ, 10 ≤ (1+kappa)^e := by
  obtain ⟨e, he⟩ := pow_unbounded_of_one_lt (10 : ℝ) (show 1 < 1+kappa by linarith)
  exact ⟨e, he.le⟩

noncomputable def geometricCap (kappa : ℝ) (hk : 0 < kappa) : ℕ :=
  Nat.find (geometric_exists kappa hk)

end MetricKMedianRecovery.RadiusMenus

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_LeafDistances
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Sampling
open RadiusMenus
variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V]

abbrev Entry (M E J : ℕ) := Fin M ⊕ (Fin (E+1) ⊕ Fin J)
abbrev Action (D : Finset V) (M E J : ℕ) := Unit ⊕ (D ⊕ (D × Entry M E J))

end MetricKMedianRecovery.Sampling

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_RationalMenus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalSampling
open Sampling BitMachine
variable {n : ℕ}
def menuWeight (M E J : ℕ) : Sampling.Entry M E J → ℚ
  | .inl _=>1/(3*M)
  | .inr (.inl _)=>1/(3*(E+1))
  | .inr (.inr j)=>(1/3)*((1/2:ℚ)^(j.val+1)/(1-(1/2:ℚ)^J))
end MetricKMedianRecovery.RationalSampling

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

noncomputable def labelRange (b : ℕ) : ℕ := 2 ^ Nat.clog 2 b

def label (b : ℕ) (hb : 0 < b) (x : Fin (labelRange b)) : Fin b :=
  ⟨x.val % b, Nat.mod_lt _ hb⟩

def color (x : Fin 4) : Fin 3 :=
  if x.val < 2 then 0 else if x.val = 2 then 1 else 2

end MetricKMedianRecovery.ColorLabel

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_SeedTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySeed
def Tensor : List ℕ→ℕ→Type
  | [],b =>Fin b→Bool
  | n::ns,b =>Fin n→Tensor ns b
def raw : {ds : List ℕ}→{b : ℕ}→Tensor ds b→List Bool
  | [],_,s=>List.ofFn s
  | _::_,_,s=>(List.ofFn (fun i=>raw (s i))).flatten
end MetricKMedianRecovery.BitMachine.BinarySeed

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_ColorLabelMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRationalPower
noncomputable def capPoly : Polynomial ℕ := 20*(Polynomial.X+1)^2
end MetricKMedianRecovery.BitMachine.BinaryRationalPower

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
variable {A : Type*}
def select (default : A) : List (A×ℕ) → ℕ → A
  | [],_=>default
  | (a,w)::ws,v=>if v<w then a else select default ws (v-w)
variable [Fintype A] [DecidableEq A]
noncomputable def list (p : A→ℝ) (b : ℕ) (as : List A) : List (A×ℕ) := as.map (fun a=>(a,rawCount p b a))
end MetricKMedianRecovery.Dyadic.Canonical

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_InverseCDF
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryInverseCDF
open Dyadic.Canonical

def encodeOption : Option ℕ→List Bool
  | none=>[]
  | some j=>true::j.bits
end MetricKMedianRecovery.BitMachine.BinaryInverseCDF

namespace MetricKMedianRecovery.BitMachine.BinaryDyadic
noncomputable def power (x : List Bool) : List Bool := List.replicate x.length false++[true]
end MetricKMedianRecovery.BitMachine.BinaryDyadic

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_NearEligible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Sampling
variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V]
namespace Comparison
variable {D S O : Finset V}
open RadiusMenus

open scoped Classical

noncomputable def mainKappa : ℝ := 1/1000000
lemma mainKappa_pos : 0 < mainKappa := by norm_num [mainKappa]

end Comparison
end MetricKMedianRecovery.Sampling

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_RealizedKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalSampling
open Sampling BitMachine
variable {n : ℕ}
def entries (M E J : ℕ) : List (Entry M E J) :=
  (List.ofFn (fun i : Fin M=>Sum.inl i))++
    (List.ofFn (fun i : Fin (E+1)=>Sum.inr (Sum.inl i)))++
    (List.ofFn (fun i : Fin J=>Sum.inr (Sum.inr i)))

def clients (D : Finset (Fin n)) : List D := D.attach.sort (·≤·)
def actions (D : Finset (Fin n)) (M E J : ℕ) : List (Action D M E J) :=
  Sum.inl () :: ((clients D).map (fun w=>Sum.inr (Sum.inl w))++
    ((clients D).product (entries M E J)).map (fun z=>Sum.inr (Sum.inr z)))
end MetricKMedianRecovery.RationalSampling

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CategoricalTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCategorical
variable {E : Type*} {a T : ℕ}
def omitted (r : Fin a→Fin T→Option E) (skip : ℕ) : Fin a→Fin T→Option E :=
  fun j t=>if j.val=skip then none else r j t
end MetricKMedianRecovery.BitMachine.BinaryCategorical

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CategoricalScore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCategorical
variable {q a T L : ℕ}
def elemBits {q : ℕ} (e : Fin q) : List Bool := e.val.bits
end MetricKMedianRecovery.BitMachine.BinaryCategorical

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CategoricalResources
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Categorical.Explicit
lemma pow_size_bound (n : ℕ) : 2^n.size ≤ 2*(n+1) := by
  by_cases hn : n=0
  · subst n; norm_num
  · have hp : 0<n.size := Nat.size_pos.mpr (Nat.pos_of_ne_zero hn)
    have hh:=Nat.lt_size.mp (show n.size-1<n.size by omega)
    have he : n.size=n.size-1+1 := by omega
    rw [he,pow_succ]
    omega
end MetricKMedianRecovery.Categorical.Explicit

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CategoricalSize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCategorical
variable {q a T L : ℕ}
noncomputable def runCapPoly : Polynomial ℕ := 100*(Polynomial.X+1)^4
end MetricKMedianRecovery.BitMachine.BinaryCategorical

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_TensorEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySeed
def count : List ℕ→ℕ→ℕ
  | [],b=>b
  | n::ns,b=>n*count ns b
def tensorEquiv : (ds : List ℕ)→(b : ℕ)→(Fin (count ds b)→Bool)≃Tensor ds b
  | [],_=>Equiv.refl _
  | n::ns,b=> ((Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl Bool)).trans
    (Equiv.curry (Fin n) (Fin (count ns b)) Bool)).trans
      (Equiv.arrowCongr (Equiv.refl (Fin n)) (tensorEquiv ns b))
end MetricKMedianRecovery.BitMachine.BinarySeed

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CategoricalOutput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCategorical.Tape
open BinarySeed
variable (q a b L : ℕ)
abbrev M : ℕ := count [2^b,q,L,a] b
abbrev K : ℕ := count [a] b

def split : (Fin (M q a b L+K a b)→Bool)≃
    (Fin (M q a b L)→Bool)×(Fin (K a b)→Bool) :=
  (Equiv.arrowCongr finSumFinEquiv.symm (Equiv.refl Bool)).trans
    (Equiv.sumArrowEquivProdArrow _ _ _)
def tensorPair : (Fin (M q a b L+K a b)→Bool)≃Tensor [2^b,q,L,a] b × Tensor [a] b :=
  (split q a b L).trans (Equiv.prodCongr (tensorEquiv _ b) (tensorEquiv _ b))
end MetricKMedianRecovery.BitMachine.BinaryCategorical.Tape

namespace MetricKMedianRecovery.BitMachine.BinaryCategorical.Resources
open Categorical.Explicit

attribute [local irreducible] RawUnary.run
noncomputable def capPoly : Polynomial ℕ := 4096000000000*(Polynomial.X+2)^5
end MetricKMedianRecovery.BitMachine.BinaryCategorical.Resources

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CategoricalRawPrep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCompletionFill
variable {q a : ℕ}
def elemBits (e : Fin q) := e.val.bits
end MetricKMedianRecovery.BitMachine.BinaryCompletionFill

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BlueDPValue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BlueDP
variable {A L : Type*}
lemma list_min_inf [DecidableEq L] (xs : List L) (f : L→WithTop ℝ) :
    ((xs.map f).foldr min ⊤)=xs.toFinset.inf f := by
  induction xs with
  | nil=>simp
  | cons x xs ih=>simp [ih]

variable [LinearOrder L]
def enumBlocks (U : Finset L) : List (Finset L) :=
  (((U.sort (·≤·)).sublists).map List.toFinset).filter (·≠∅)
lemma range_succ_set (c : ℕ) : ((List.range c).map (·+1)).toFinset=Finset.Icc 1 c := by
  ext i
  simp only [List.mem_toFinset,List.mem_map,List.mem_range,Finset.mem_Icc]
  constructor
  · rintro ⟨j,hj,rfl⟩;omega
  · intro h;exact ⟨i-1,by omega,by omega⟩
end MetricKMedianRecovery.BlueDP

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BranchSeedLayout
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBranchTape
open BinarySeed
abbrev colorCount (n : ℕ) := n*2
abbrev labelCount (n b : ℕ) := n*Nat.clog 2 b
def split (a b : ℕ) : (Fin (a+b)→Bool)≃(Fin a→Bool)×(Fin b→Bool) :=
  (Equiv.arrowCongr finSumFinEquiv.symm (Equiv.refl Bool)).trans (Equiv.sumArrowEquivProdArrow _ _ _)
end MetricKMedianRecovery.BitMachine.BinaryBranchTape

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Strictness_StrictnessGap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery

noncomputable def strictnessGap (T : ℝ) : ℝ :=
  (1 / (200 * (T + 2))) ^ 2 / 100

end MetricKMedianRecovery

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_PrecisionBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RadiusMenus

def precisionBits (n d M E J : ℕ) : ℕ := n+d+M+E+J+5

end MetricKMedianRecovery.RadiusMenus

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_IntegralPrecision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Sampling.Comparison
open MetricKMedianRecovery RadiusMenus
variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V]

noncomputable local instance instDecidableEqAction_2_rf73f4b_1 (D : Finset V) (M E J : ℕ) : DecidableEq (Action D M E J) := Classical.decEq _
noncomputable def integralPrecision (D : Finset V) (Δ : ℝ) (m : ℕ) : ℕ :=
  precisionBits D.card (Nat.ceil Δ) (firstSize mainKappa)
    (geometricCap mainKappa mainKappa_pos) (thirdSize mainKappa m)

end MetricKMedianRecovery.Sampling.Comparison

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Cap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Rounding
variable {V : Type*} [PseudoMetricSpace V] [DecidableEq V]

noncomputable def cap (n : ℕ) (eps : ℝ) : ℕ := ⌈20*(n:ℝ)^2/eps⌉₊+1

end MetricKMedianRecovery.Rounding

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

@[instance_reducible]
noncomputable def metric (I : RationalMetricInput) : PseudoMetricSpace (Fin I.pointCount) where
  dist x y := I.distance x y
  dist_self x := by exact_mod_cast I.distance_self x
  dist_comm x y := by exact_mod_cast I.distance_symm x y
  dist_triangle x y z := by exact_mod_cast I.distance_triangle x y z

end MetricKMedianRecovery.RationalMetricInput

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_SamplerParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySampler.Parameters
open Polynomial RadiusMenus Sampling Sampling.Comparison
noncomputable def M : ℕ := firstSize mainKappa
noncomputable def E : ℕ := geometricCap mainKappa mainKappa_pos
end MetricKMedianRecovery.BitMachine.BinarySampler.Parameters

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_SamplerResources
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySampler.Loop
variable {n : ℕ}
noncomputable def capPoly : Polynomial ℕ := 1000*(Polynomial.X+1)^5
end MetricKMedianRecovery.BitMachine.BinarySampler.Loop

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_RecoveryTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRecovery
open BinaryBranchTape
attribute [local irreducible] ColorLabel.label ColorLabel.color
  
def tapeSize (H : ℕ) : ℕ := 201326592000000015*(H+2)^12
end MetricKMedianRecovery.BitMachine.BinaryRecovery

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_IntegralRecoveryAmplified
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat.FiniteTape
open Sampling.Comparison
variable {n : ℕ}
def layout (t b : ℕ) : (Fin (t*b)→Bool)≃(Fin t→Fin b→Bool) :=
  BinarySeed.tensorEquiv [t] b
end MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat.FiniteTape

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_SliceFold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.WordList.Slices
noncomputable def capacityPoly : Polynomial ℕ :=
  let X : Polynomial ℕ:=Polynomial.X
  2*(X*(2*X+2)+X+X*(2*(2*(X*(2*X+2)+X+X)+6)+2))+6
end MetricKMedianRecovery.BitMachine.WordList.Slices

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_StateBits2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCoupledState
open WordList CanonicalCoupledMerge

def labelBound (m t h : ℕ) : ℕ := 6*t+2*m+3*h+8
def bankBound (m t : ℕ) : ℕ := t*(2*m+1)
def historyBound (m t h : ℕ) : ℕ := t*(2*(m+bankBound m t)*(2*labelBound m t h+2)+2)
def bound (m t h p : ℕ) : ℕ :=
  4*bankBound m t*(2*labelBound m t h+2)+8*historyBound m t h+12*p+40

end MetricKMedianRecovery.BitMachine.BinaryCoupledState

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_LocalBest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryLocalSearch
open WordList
noncomputable def capPoly : Polynomial ℕ := 10*(Polynomial.X+1)^2
end MetricKMedianRecovery.BitMachine.BinaryLocalSearch

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_CorrectionSize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCoupled
open WordList CanonicalCoupledMerge
variable {m d : ℕ} [PseudoMetricSpace (Fin m)]
def bound (m t h p : ℕ) : ℕ := BinaryCoupledState.bound m t h p+6*BinaryCoupledState.labelBound m t h+2
end MetricKMedianRecovery.BitMachine.BinaryCoupled

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
variable {X : Type*} [DecidableEq X]
structure Acc (X : Type*) where
  remaining : List X
  extras : List X
  vertices : List (List X)
  deriving DecidableEq

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
variable {X D : Type*} [DecidableEq X]
structure Acc (X : Type*) where
  front : List X
  rest : List X
  vertices : List (List X)
  deriving DecidableEq

end MetricKMedianRecovery.CanonicalMatch

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_MatchSize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryMatch
open WordList CanonicalMatch

noncomputable def capacityPoly : Polynomial ℕ :=
  let X : Polynomial ℕ:=Polynomial.X
  2*(2*X*(2*X+2)+X*(X+2)*(2*((X+1)*(2*X+2))+2))+6
end MetricKMedianRecovery.BitMachine.BinaryMatch

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_LoopMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCoupled
open BinaryCoupledState
noncomputable def boundPoly : Polynomial ℕ :=
  let X:=Polynomial.X
  let label:=6*X+2*X+3*(8*X+3)+8
  let bank:=X*(2*X+1)
  let history:=X*(2*(X+bank)*(2*label+2)+2)
  4*bank*(2*label+2)+8*history+12*X+40+6*label+2
end MetricKMedianRecovery.BitMachine.BinaryCoupled

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_LoopSize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCoupledLoop
open WordList CanonicalCoupledMerge

noncomputable def capPoly : Polynomial ℕ := 20*Polynomial.X+4*BinaryCoupled.boundPoly+100
end MetricKMedianRecovery.BitMachine.BinaryCoupledLoop

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_DuplicateMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryDuplicateMatrix
open WordList
variable {n : ℕ}
def forget : Fin (n+n)→Fin n := Fin.append id id
def duplicate (δ : Fin n→Fin n→ℚ) : Fin (n+n)→Fin (n+n)→ℚ :=
  fun i j=>δ (forget i) (forget j)
noncomputable def twice (xs : List Bool) : List Bool := xs++xs

end MetricKMedianRecovery.BitMachine.BinaryDuplicateMatrix

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_RoundingMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRoundingMatrix
open WordList
variable {n : ℕ}
def round (δ : Fin n→Fin n→ℚ) (u : ℚ) (cap : ℕ) (i j : Fin n) : ℚ :=
  if i=j then 0 else (min cap (max 1 ⌈δ i j/u⌉₊):ℕ)
end MetricKMedianRecovery.BitMachine.BinaryRoundingMatrix

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_GlobalCall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryGlobalZero
open WordList
variable {n : ℕ}
def keys (F : Finset (Fin n)) (row : Fin n→ℚ) : Finset (ℚ ×ₗ ℕ) :=
  F.image (fun f=>toLex (row f,f.val))
lemma keys_nonempty (F : Finset (Fin n)) (hF : F.Nonempty) (row : Fin n→ℚ) :
    (keys F row).Nonempty := hF.image _
noncomputable def key (F : Finset (Fin n)) (hF : F.Nonempty) (row : Fin n→ℚ) : ℚ ×ₗ ℕ :=
  (keys F row).min' (keys_nonempty F hF row)
lemma key_mem (F : Finset (Fin n)) (hF : F.Nonempty) (row : Fin n→ℚ) :
    ∃ f∈F,toLex (row f,f.val)=key F hF row :=
  Finset.mem_image.mp (Finset.min'_mem _ _)
lemma key_lt (F : Finset (Fin n)) (hF : F.Nonempty) (row : Fin n→ℚ) :
    (ofLex (key F hF row)).2<n := by
  obtain ⟨f,_,he⟩:=key_mem F hF row
  rw [←he]
  exact f.isLt
noncomputable def pick (F : Finset (Fin n)) (hF : F.Nonempty) (row : Fin n→ℚ) : Fin n :=
  ⟨(ofLex (key F hF row)).2,key_lt F hF row⟩
end MetricKMedianRecovery.BitMachine.BinaryGlobalZero

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_GlobalRoundMetric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryGlobalRounding
open BinaryDuplicateMatrix BinaryTaggedSets
variable {n : ℕ}
@[instance_reducible]
noncomputable def duplicateMetric (I : RationalMetricInput) : PseudoMetricSpace (Fin (I.pointCount+I.pointCount)) :=
  PseudoMetricSpace.induced forget I.metric
end MetricKMedianRecovery.BitMachine.BinaryGlobalRounding

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_GlobalZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryGlobalZero
open WordList
variable {n : ℕ}
noncomputable def output (δ : Fin n→Fin n→ℚ) (D F : Finset (Fin n)) (hF : F.Nonempty) : Finset (Fin n) :=
  D.image (fun p=>pick F hF (δ p))
end MetricKMedianRecovery.BitMachine.BinaryGlobalZero

end OAI
end


