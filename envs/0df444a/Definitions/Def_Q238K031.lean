-- Prove2me | Definitions.Def_Q238K031
-- name    : Q238K031
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T23:23:21.203875+00:00
-- url     : https://prove2.me/theorems/17efac81-2e44-4ce4-b04d-6d8831a1a0f2
-- title:
--   Definitions bundle Q238K031 of the split of OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 48 declarations of OpenAI's Lean: 46 definitions, 1 inductive type or structure and 1 theorem. The definitions and types are `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalZero.one`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalZero.rowRun`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalZero.run`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalZero.values`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInputParser.Rows.offset`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInputParser.Stream.step_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInputParser.denominator_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInputParser.nat_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInputParser.numerator_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInputParser.rational_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses.sizeWord`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMaskOutput.member`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMaskOutput.run`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMaskParser.run`, `OAI.MetricKMedianRecovery.BitMachine.BinaryNormalization.cap`, `OAI.MetricKMedianRecovery.BitMachine.BinaryNormalization.capArgument`, `OAI.MetricKMedianRecovery.BitMachine.BinaryNormalization.count`, `OAI.MetricKMedianRecovery.BitMachine.BinaryNormalization.mesh`, `OAI.MetricKMedianRecovery.BitMachine.BinaryNormalization.roundingInput`, `OAI.MetricKMedianRecovery.BitMachine.BinaryNormalization.run`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRecovery.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRoundingMatrix.colIndex_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRoundingMatrix.ctx_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRoundingMatrix.rowIndex_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinarySamplingState.keep`, `OAI.MetricKMedianRecovery.BitMachine.BinarySamplingState.remove`, `OAI.MetricKMedianRecovery.BitMachine.BinarySamplingState.retain`, `OAI.MetricKMedianRecovery.BitMachine.BinaryTaggedSets.shift`, `OAI.MetricKMedianRecovery.BitMachine.BinaryTaggedSets.unshift`, `OAI.MetricKMedianRecovery.BitMachine.UnaryParser.loop_computes`, `OAI.MetricKMedianRecovery.BitMachine.UnaryParser.next_computes`, `OAI.MetricKMedianRecovery.BitMachine.UnaryParser.run_computes`, `OAI.MetricKMedianRecovery.BitMachine.UnaryParser.step_computes`, `OAI.MetricKMedianRecovery.BitMachine.UnaryTake.dropWords_computes`, `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.Certified`, `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.Certified.coupled`, `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.Correction.error`, `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.Frame.Stopped`, `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.Frame.Valid`, `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.Frame.value` and 7 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedianRecovery_Algorithms_GlobalCall`, `KMedianRecovery_Algorithms_GlobalZero`, `KMedianRecovery_Algorithms_IntegralRecoveryGuesses`, `KMedianRecovery_Encoding_FinSets`, `KMedianRecovery_Encoding_MaskOutput`, `KMedianRecovery_Encoding_MatrixRows`, `KMedianRecovery_Encoding_RationalStream`, `KMedianRecovery_Encoding_UnaryParser`, `KMedianRecovery_Geometry_RoundingMatrix`, `KMedianRecovery_Machines_CoupledLoop`, `KMedianRecovery_Machines_LoopInvariant`, `KMedianRecovery_Machines_NormalizationMachine`, `KMedianRecovery_Recovery_CoupledInitial`, `KMedianRecovery_Recovery_CoupledResolve`, `KMedianRecovery_Recovery_FinImages`, `KMedianRecovery_Recovery_LeafOrder`, `KMedianRecovery_Recovery_PlanResult`, `KMedianRecovery_Recovery_RawSlices`, `KMedianRecovery_Recovery_RecoveryContext`, `KMedianRecovery_Sampling_SamplingStateMachine`.
--
--   **Imports.** It imports the published bundle `Def_KMedianRefinedRecovery`; the bundles `Q238K024`, `Q238K025`, `Q238K026` and `Q238K027` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q238K035` and `Q238K047`; the statements `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledLoop.pack_length_bound_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.a_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.banks_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalZero.run_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.recoveryContext_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryNormalization.run_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRecovery.atBranch_context_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRecovery.atBranch_source_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinarySamplingState.remove_pair_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryTaggedSets.unshift_encode_s238`, `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.leaf_certified_s238`, `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.resolve_correct_s238`, `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.start_certificate_s238`, `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.start_correct_s238`, `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.start_small_certificate_s238`, `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.step_correct_s238` and `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.transition_valid_s238`; the proofs of `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledLoop.pack_length_bound_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.a_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.banks_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalZero.run_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.recoveryContext_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryNormalization.run_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRecovery.atBranch_context_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRecovery.atBranch_source_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinarySamplingState.remove_pair_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryTaggedSets.unshift_encode_s238`, `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.leaf_certified_s238`, `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.resolve_correct_s238`, `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.start_certificate_s238`, `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.start_correct_s238`, `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.start_small_certificate_s238`, `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.step_correct_s238` and `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.transition_valid_s238`.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_KMedianRefinedRecovery
import Definitions.Def_Q238K024
import Definitions.Def_Q238K025
import Definitions.Def_Q238K026
import Definitions.Def_Q238K027

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_LeafOrder
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CanonicalCoupledMerge
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion PhaseMergeRefinement PhaseCountCrossing
  CanonicalMergeCrossing RationalLeaves PhaseMergeInvariant PhaseCoupledMerge
variable {V : Type*} [DecidableEq V] {d : ℕ}

def Correction.error : Correction V → ℚ
  | .identity => 0
  | .shorten _ _ l u => u-l

def State.a (F : Finset V) (s : State V) :=
  ((after (after ∅ s.mapPrefix) s.T)∩F.image original).card

variable [PseudoMetricSpace V]
attribute [local instance] RationalLeaves.metric

structure Certified (loc : Fin d → V) (F : Finset V) (v eta lo hi : ℝ)
    (q n k : ℕ) (s : State V) : Prop where
  before : Before (3*q) s.B
  before_map : Before (3*q) s.mapFree
  disjoint : Disjoint (F.image original) s.B
  low : lo≤(s.lam:ℝ)
  high : (s.lam':ℝ)≤hi
  price : (s.lam:ℝ)≤(s.lam':ℝ)
  eps_nonneg : (0:ℝ)≤ s.correction.error
  error : (s.lam':ℝ)-s.lam+(d:ℝ)*((1-3*v)*(s.correction.error:ℝ))≤(d:ℝ)*eta
  inj : Function.Injective s.correction.apply
  fixed : ∀ i∈F.image original,s.correction.apply i=i
  shrink : ∀ j,∀ x∈F.image original∪s.B,
    dist (original (loc j)) (s.correction.apply x)≤dist (original (loc j)) x
  loss : ∀ j,∀ x∈F.image original∪s.B,
    dist (original (loc j)) x≤dist (original (loc j)) (s.correction.apply x)+s.correction.error
  old_prefix : PrefixData (fun j=>original (loc j)) (F.image original) s.B v s.lam eta q s.P
  new_prefix : PrefixData (fun j=>original (loc j)) (F.image original) s.mapFree v s.lam' eta q s.mapPrefix
  sandwich : Sandwich k (s.a F) (s.b F)
  new_tail : Runs (fun j=>original (loc j)) (F.image original) s.mapFree (after ∅ s.mapPrefix) v s.lam' q n s.T
  old_tail : Runs (fun j=>original (loc j)) (F.image original) s.B (after ∅ s.P) v s.lam q n s.U

noncomputable def Certified.coupled {loc : Fin d → V} {F : Finset V} {v eta lo hi : ℝ}
    {q n k : ℕ} {s : State V} (h : Certified loc F v eta lo hi q n k s) :
    Coupled (fun j=>original (loc j)) (F.image original) v eta lo hi q n k where
  B := s.B
  P := s.P
  r := s.correction.apply
  lam := s.lam
  lam' := s.lam'
  eps := s.correction.error
  a := s.a F
  b := s.b F
  disjoint := h.disjoint
  low := h.low
  high := h.high
  price := h.price
  eps_nonneg := h.eps_nonneg
  error := by simpa only [Fintype.card_fin] using h.error
  inj := h.inj
  fixed := h.fixed
  shrink := h.shrink
  loss := h.loss
  old_prefix := h.old_prefix
  new_prefix := h.new_prefix
  sandwich := h.sandwich
  new_tail := h.new_tail.attains
  old_tail := h.old_tail.attains

end MetricKMedianRecovery.CanonicalCoupledMerge

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_CoupledResolve
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CanonicalCoupledMerge

section
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion PhaseMergeRefinement PhaseCountCrossing
  CanonicalMergeCrossing RationalLeaves PhaseMergeInvariant PhaseCoupledMerge CanonicalLengthView
variable {V : Type*} [LinearOrder V] {d : ℕ}

variable [PseudoMetricSpace V]
attribute [local instance] RationalLeaves.metric

def Outcome.Correct (loc : Fin d → V) (F : Finset V) (v eta lo hi : ℝ) (q n k : ℕ) : Outcome V → Prop
  | .inl o => o.Correct loc F v eta lo hi (q+(n+1)) k
  | .inr s => Certified loc F v eta lo hi (q+1) n k s

end

open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion PhaseMergeRefinement PhaseCountCrossing
  CanonicalMergeCrossing RationalLeaves PhaseMergeInvariant PhaseCoupledMerge
variable {V : Type*} [LinearOrder V] {d : ℕ}

def banks (F : Finset V) (B : Finset (Label V)) (q : ℕ) : Finset (Label V) :=
  PhaseMergePath.pool (F.image original) (PhaseMergePath.pool (F.image original) B (copy (3*q))) (copy (3*q+1))

def step (loc : Fin d → V) (distance : V → Fin d → ℚ) (F : Finset V)
    (v M : ℚ) (N precision q n k : ℕ) (s : State V) : Outcome V :=
  match s.T,s.U with
  | H::T,G::U =>
    let W := FiniteLabelContinuation.continuation (fun j=>original (loc j)) (rows distance)
      (F.image original) v s.lam' (q+1) n (after ∅ s.mapPrefix∪G.toFinset)
    let c := finalCount (F.image original) (after ∅ s.mapPrefix) G W
    if c=k then .inl (finish s.mapFree s.lam' (s.mapPrefix++[G]) W)
    else if Sandwich k (s.a F) c then
      resolve loc distance F v M N precision q n k (3*q+2) (banks F s.mapFree q)
        s.lam' s.mapPrefix
        (FiniteLabelCrossing.run (fun j=>original (loc j)) (rows distance) (F.image original)
          (after ∅ s.mapPrefix) v s.lam' q n k (copy (3*q)) (copy (3*q+1)) H G T W)
    else .inr (advanceState s G W U)
  | _,_ => .inl (finish s.B s.lam s.P [])

attribute [local instance] RationalLeaves.metric

end MetricKMedianRecovery.CanonicalCoupledMerge

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_MatrixRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryInputParser.Rows
open WordOperations WordList BinaryArithmetic
noncomputable def offset (x : List Bool) : List Bool :=
  (value (UnaryResources.lengthBits (extractPrefix (extractPrefix x)))*value (discardPrefix x)).bits
attribute [local irreducible] offset Drop.run
attribute [local irreducible] mapWith
end MetricKMedianRecovery.BitMachine.BinaryInputParser.Rows

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_RawSlices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.UnaryTake
open WordOperations
noncomputable def dropWords_computes : PolyComputes dropWords := by
  have hi := pack_computes true extractPrefix_computes discardPrefix_computes (const_computes [])
  have hh := (hi.comp loop_computes).comp data_computes
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  simp only [Function.comp_apply,rank,pack,List.head?_cons,ite_true, if_true,counter,List.tail_cons,
    extractPrefix_pairBits]
  change dropWords x=data (next^[(extractPrefix x).length+1]
    (pack true (extractPrefix x) (discardPrefix x) []))
  rw [loop_spec,data_pack]
  rfl
end MetricKMedianRecovery.BitMachine.UnaryTake

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_UnaryParser
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.UnaryParser
open WordOperations UnaryTake

noncomputable def step_computes : PolyComputes step := by
  have ht:=pack_computes true ((const_computes [true]).append counter_computes)
    (data_computes.comp tail_computes) (const_computes [])
  have hf:=pack_computes false counter_computes (data_computes.comp tail_computes) (const_computes [])
  unfold step
  simpa only [Function.comp_def,List.singleton_append] using
    (data_computes.comp head_computes).cond ht hf
noncomputable def next_computes : PolyComputes next := by
  have h:=head_computes.cond step_computes id_computes
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  simp only [next,While.next,id_eq]
  cases x with
  | nil=>rfl
  | cons b xs=>cases b <;> rfl
noncomputable def loop_computes : PolyComputes loop := by
  have h:=BoundedIteration.polynomialRun_computes next_computes Polynomial.X (7*Polynomial.X+3)
  have he (x : List Bool) : BoundedIteration.polynomialRun next Polynomial.X (7*Polynomial.X+3) x=loop x := by
    have ht:=BoundedIteration.polynomialRun_eq next Polynomial.X (7*Polynomial.X+3) x (by
      intro j _
      have hb:=(iterate_bounds x j).2
      obtain ⟨hc,hd,ho⟩:=projection_bounds x
      simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X]
      unfold mass at hb
      omega)
    simpa only [Polynomial.eval_X,loop] using ht
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  exact (he x).symm
noncomputable def run_computes : PolyComputes run :=
  ((pack_computes true (const_computes []) id_computes (const_computes [])).comp loop_computes).comp
    (counter_computes.pair data_computes)
end MetricKMedianRecovery.BitMachine.UnaryParser

namespace MetricKMedianRecovery.BitMachine.BinaryInputParser
open WordOperations
attribute [local irreducible] UnaryParser.run UnaryTake.takeWords UnaryTake.dropWords
noncomputable def nat_computes : PolyComputes nat :=
  UnaryParser.run_computes.comp (UnaryTake.takeWords_computes.pair UnaryTake.dropWords_computes)
attribute [local irreducible] nat
noncomputable def numerator_computes : PolyComputes numerator :=
  head_computes.append ((tail_computes.comp nat_computes).comp extractPrefix_computes)
noncomputable def denominator_computes : PolyComputes denominator :=
  ((tail_computes.comp nat_computes).comp discardPrefix_computes).comp nat_computes
attribute [local irreducible] numerator denominator
noncomputable def rational_computes : PolyComputes rational :=
  (numerator_computes.pair (denominator_computes.comp extractPrefix_computes)).pair
    (denominator_computes.comp discardPrefix_computes)
end MetricKMedianRecovery.BitMachine.BinaryInputParser

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
open WordOperations
attribute [local irreducible] rational
noncomputable def step_computes : PolyComputes step := by
  have hp:=extractPrefix_computes.comp rational_computes
  have hc:=WordList.cons_computes (hp.comp extractPrefix_computes) discardPrefix_computes
  have hh:=(extractPrefix_computes.comp isEmpty_computes).cond id_computes ((hp.comp discardPrefix_computes).pair hc)
  unfold step
  simpa only [Function.comp_def,decide_eq_true_eq,id_eq] using hh
end MetricKMedianRecovery.BitMachine.BinaryInputParser.Stream

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_FinSets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryMaskParser
open WordOperations WordList
noncomputable def run (x : List Bool) : List Bool :=
  BinaryNatSet.sort (filterWith member (pairBits (x,BinaryEllipsoidInitial.indices (RawUnary.run x))))
end MetricKMedianRecovery.BitMachine.BinaryMaskParser

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
open WordOperations WordList BinaryArithmetic
variable {n : ℕ}
noncomputable def shift : List Bool→List Bool := BinaryNatSet.sort ∘ mapWith plus
noncomputable def unshift : List Bool→List Bool := BinaryNatSet.sort ∘ mapWith minus
end MetricKMedianRecovery.BitMachine.BinaryTaggedSets

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_SamplingStateMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySamplingState
open WordOperations WordList BinaryArithmetic RationalSampling
open BinaryOpeningPayment (field field_encode)
variable {n : ℕ}
noncomputable def remove (x : List Bool) : List Bool := pairBits
  (BinaryNatSet.union (pairBits (extractPrefix (extractPrefix x),WordList.encode [discardPrefix x])),discardPrefix (extractPrefix x))
noncomputable def keep (x : List Bool) : Bool := decide
  (value (UnaryResources.lengthBits (Count.run (discardPrefix (discardPrefix x))))≤value (extractPrefix x) ∧
   value (UnaryResources.lengthBits (Count.run (extractPrefix (discardPrefix x))))≤value (extractPrefix x))
noncomputable def retain (x : List Bool) : List Bool := if keep x then WordList.encode [discardPrefix x] else []
end MetricKMedianRecovery.BitMachine.BinarySamplingState

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_RecoveryContext
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRecovery
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_encode)
def pack {n : ℕ} (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℚ)
    (s : RationalSampling.State n) (m : ℕ) (extra raw : List Bool) : List Bool :=
  encode [RationalMatrix.encode δ,BinaryFinSet.encode D,BinaryFinSet.encode F,BinaryFinSet.encode S,
    BinaryRational.encode Δ,BinarySamplingState.encode s,List.replicate n true,List.replicate m true,extra,raw]
attribute [local irreducible] BinaryEllipsoidInitial.indices
attribute [local irreducible] mapWith
attribute [local irreducible] src zeros qbits
end MetricKMedianRecovery.BitMachine.BinaryRecovery

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_IntegralRecoveryGuesses
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses
open WordOperations WordList
open BinaryOpeningPayment (field field_encode)
attribute [local irreducible] BinaryFinSet.encode Count.run src
attribute [local irreducible] mapWith
noncomputable def sizeWord (x : List Bool) : List Bool := UnaryResources.lengthBits (Count.run (src 4 x))
attribute [local irreducible] sizeWord
end MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_CoupledLoop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CanonicalCoupledMerge
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion PhaseMergeRefinement PhaseCountCrossing
  CanonicalMergeCrossing RationalLeaves PhaseMergeInvariant PhaseCoupledMerge
variable {V : Type*} [LinearOrder V] {d : ℕ}

def run (loc : Fin d → V) (distance : V → Fin d → ℚ) (F : Finset V)
    (v M : ℚ) (N precision k : ℕ) : ℕ → ℕ → State V → Output V
  | _q,0,s => finish s.B s.lam s.P []
  | q,n+1,s => match step loc distance F v M N precision q n k s with
    | .inl o => o
    | .inr t => run loc distance F v M N precision k (q+1) n t

attribute [local instance] RationalLeaves.metric

end MetricKMedianRecovery.CanonicalCoupledMerge

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_CoupledInitial
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CanonicalCoupledMerge
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion PhaseMergeRefinement PhaseCountCrossing
  CanonicalMergeCrossing RationalLeaves PhaseMergeInvariant PhaseCoupledMerge
variable {V : Type*} [LinearOrder V] {d : ℕ}

def start (loc : Fin d → V) (distance : V → Fin d → ℚ) (F : Finset V)
    (v lo M : ℚ) (N precision total k : ℕ) : StartOutput V :=
  let count := fun lam => initialCount loc distance F v lam total
  if count lo≤k then .small (finish ∅ lo [] (initialHistory loc distance F v lo total))
  else
    let high := 8*(d:ℚ)*M
    let I := PriceBisection.search count k (PriceBisection.iterations lo high precision) (lo,high)
    let U := initialHistory loc distance F v I.1 total
    let T := initialHistory loc distance F v I.2 total
    if count I.1=k then .normal (finish ∅ I.1 [] U)
    else if count I.2=k then .normal (finish ∅ I.2 [] T)
    else .normal (run loc distance F v M N precision k 0 total (initial I.1 I.2 T U))

attribute [local instance] RationalLeaves.metric

end MetricKMedianRecovery.CanonicalCoupledMerge

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_LoopInvariant
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CanonicalCoupledMerge
open RationalLeaves RationalHeight
variable {V : Type*} [LinearOrder V] {d : ℕ}

def transition (loc : Fin d→V) (distance : V→Fin d→ℚ) (F : Finset V)
    (v M : ℚ) (N precision k : ℕ) (f : Frame V) : Frame V :=
  match f.out,f.n with
  | .inr s,n+1=>⟨f.q+1,n,step loc distance F v M N precision f.q n k s⟩
  | _,_=>f

def Frame.value (loc : Fin d→V) (distance : V→Fin d→ℚ) (F : Finset V)
    (v M : ℚ) (N precision k : ℕ) (f : Frame V) : Output V :=
  match f.out with
  | .inl o=>o
  | .inr s=>run loc distance F v M N precision k f.q f.n s

def Frame.Stopped (f : Frame V) : Prop := match f.out with
  | .inl _=>True
  | .inr _=>f.n=0

variable [PseudoMetricSpace V]
attribute [local instance] RationalLeaves.metric

def Frame.Valid (loc : Fin d→V) (F : Finset V) (v eta lo hi : ℝ) (total k h p : ℕ) (f : Frame V) : Prop :=
  f.q+f.n=total ∧ match f.out with
  | .inl o=>o.Correct loc F v eta lo hi total k ∧ o.Resources F f.q h p
  | .inr s=>Certified loc F v eta lo hi f.q f.n k s ∧ s.Resources F f.q h p ∧ s.correction.Keys f.q

end MetricKMedianRecovery.CanonicalCoupledMerge

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_PlanResult
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryPlanResult
open WordOperations WordList BinaryArithmetic RationalLeaves CanonicalCoupledMerge CanonicalLengthView
open BinaryOpeningPayment (field field_encode)
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)

lemma leafInput_pack {m d : ℕ} (distance : Fin m→Fin d→ℚ) (loc : Fin d→Label (Fin m))
    (F Q B : Finset (Label (Fin m))) (v z lam : ℚ) (n q key : ℕ) (b : ℚ) (k N : ℕ)
    (H : List (Label (Fin m))) (T U P : List (List (Label (Fin m)))) (J : Plan (Label (Fin m)))
    (R : CanonicalLengthSearch.Result (Label (Fin m))) :
    leafInput (pack (BinarySensitive.pack (BinaryFiniteContext.pack distance loc F Q v z lam) n q key b k N H T U J) B P R)=
      match R with
      | .success s W=>BinaryCoupled.leafPack B P lam key J.root (J.common H) s s W []
      | .bracket l u A Z=>BinaryCoupled.leafPack B P lam key J.root (J.common H) l u A Z := by
  have hc:=(BinarySensitive.views_pack (BinaryFiniteContext.pack distance loc F Q v z lam) n q key b k N H T U J).1
  have hr:=(BinarySensitive.views_pack (BinaryFiniteContext.pack distance loc F Q v z lam) n q key b k N H T U J).2.2.2
  simp only [BinarySensitive.jf,Function.comp_apply] at hr
  unfold leafInput common
  simp only [pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Function.comp_apply]
  rw [hc]
  simp only [root,sf,Function.comp_apply,field_encode,List.getElem?_cons_zero,Option.getD_some]
  rw [hr]
  cases R <;> simp only [price,sf,rf,rightHeight,success,Function.comp_apply,BinarySensitive.pack,BinaryFiniteContext.pack,
    BinaryLengthSearch.resultBits,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
    value_bits,decide_true,one_ne_zero,decide_false,ite_true, if_true,Bool.false_eq_true,ite_false, if_false,BinaryCoupled.leafPack]
  all_goals rfl
end MetricKMedianRecovery.BitMachine.BinaryPlanResult

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
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_encode)
variable {n : ℕ}
noncomputable def ctx_computes : PolyComputes ctx := extractPrefix_computes.comp extractPrefix_computes
noncomputable def rowIndex_computes : PolyComputes rowIndex := extractPrefix_computes.comp discardPrefix_computes
noncomputable def colIndex_computes : PolyComputes colIndex := discardPrefix_computes
end MetricKMedianRecovery.BitMachine.BinaryRoundingMatrix

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_NormalizationMachine
attribute [-instance] _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryNormalization
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_encode)
open IntegralAssembly (gammaRat)
noncomputable def count (x : List Bool) : List Bool := UnaryResources.lengthBits (field 2 x)
noncomputable def mesh (x : List Bool) : List Bool := BinaryRational.encode
  ((gammaRat/16)*BinaryRational.decode (field 3 x)/(value (count x):ℚ))
noncomputable def capArgument (x : List Bool) : List Bool := BinaryRational.encode
  (20*(value (count x):ℚ)*(value (count x):ℚ)/(gammaRat/16))
noncomputable def cap (x : List Bool) : List Bool :=
  (⌈BinaryRational.decode (capArgument x)⌉₊+1).bits
noncomputable def roundingInput (x : List Bool) : List Bool :=
  encode [BinaryDuplicateMatrix.run (field 0 x),BinaryDuplicateMatrix.twice (field 1 x),mesh x,cap x]
noncomputable def run : List Bool→List Bool := BinaryRoundingMatrix.run ∘ roundingInput
end MetricKMedianRecovery.BitMachine.BinaryNormalization

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
open WordOperations WordList
open BinaryRationalSort (entryBits)
variable {n : ℕ}
noncomputable def rowRun (x : List Bool) : List Bool :=
  discardPrefix (BinaryRationalMinKey.run (mapWith BinarySamplingReference.original x))
end MetricKMedianRecovery.BitMachine.BinaryGlobalZero

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
open WordOperations WordList LocalSearch
open BinaryOpeningPayment (field field_encode)
variable {n : ℕ}
noncomputable def one (x : List Bool) : List Bool :=
  rowRun (pairBits (BinaryMetricArrays.row x,field 2 (extractPrefix x)))
noncomputable def values (x : List Bool) : List Bool := mapWith one (pairBits (x,field 1 x))
noncomputable def run : List Bool→List Bool := BinaryNatSet.sort ∘ values
end MetricKMedianRecovery.BitMachine.BinaryGlobalZero

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_MaskOutput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryMaskOutput
open WordOperations WordList
variable {n : ℕ}
noncomputable def member (x : List Bool) : List Bool :=
  [BinaryNatSet.contains (pairBits (discardPrefix x,extractPrefix x))]
noncomputable def run (x : List Bool) : List Bool :=
  Flatten.run (mapWith member (pairBits (discardPrefix x,BinaryEllipsoidInitial.indices (extractPrefix x))))
end MetricKMedianRecovery.BitMachine.BinaryMaskOutput

end OAI
end


