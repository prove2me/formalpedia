-- Prove2me | Definitions.Def_QEC_Coding_FiberBundle_PartitionedChecksProbability
-- name    : QEC_Coding_FiberBundle_PartitionedChecksProbability
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T08:17:45.883195+00:00
-- url     : https://prove2.me/theorems/3b1a037c-25f2-4d80-93a1-07d937b577b8
-- title:
--   Partitioned Checks Probability
-- statement:
--   Definitions and structural lemmas for Partitioned Checks Probability, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphSpectrumProbability
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Rank
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_ExpansionProbability
import Mathlib.Probability.Independence.Integration
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_supportWord_hammingSupport

set_option autoImplicit false
namespace QEC.Coding.FiberBundle.RandomPartition
open scoped BigOperators
open MeasureTheory
abbrev LocalSample := Bool → Bool
abbrev RowSample (r : Nat) :=
  Fin (4 * r) → LocalSample
abbrev Sample (r : Nat) :=
  Fin (3 * r) → RowSample r
noncomputable def localCoordinatePMF
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (side : Bool) : PMF Bool :=
  if side then
    PMF.bernoulli (1 / 2 : NNReal) (by norm_num)
  else
    PMF.bernoulli
      (RandomBase.incidenceProbability (4 * r) Delta)
      (RandomBase.incidenceProbability_le_one hDelta)
noncomputable def localDistribution
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r) :
    PMF LocalSample :=
  RandomBase.independentProduct
    (localCoordinatePMF r Delta hDelta)
noncomputable def rowDistribution
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r) :
    PMF (RowSample r) :=
  RandomBase.independentProduct fun _ =>
    localDistribution r Delta hDelta
noncomputable def distribution
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r) :
    PMF (Sample r) :=
  RandomBase.independentProduct fun _ =>
    rowDistribution r Delta hDelta
def baseSample
    {r : Nat} (sample : Sample r) :
    RandomBase.Sample r :=
  fun edge => sample edge.1 edge.2 false
def isTail
    {r : Nat} (sample : Sample r)
    (a : Fin (3 * r)) (b : Fin (4 * r)) : Bool :=
  sample a b true
def twistSample
    {r typeCount ell : Nat}
    (sample : Sample r)
    (typeShifts : Fin typeCount → Fin (ell - 1)) :
    RandomTwist.Sample r typeCount ell
  | Sum.inl edge => isTail sample edge.1 edge.2
  | Sum.inr τ => typeShifts τ
noncomputable def fullyGoodBaseFailureBound
    (r Delta : Nat) : ENNReal :=
  (ENNReal.ofReal
      ((14 * r : Real) * Real.exp (-(Delta : Real) / 40000)) +
    ((1 + ENNReal.ofReal
      (Real.exp (-(Delta : Real) / 2))) ^ (3 * r) - 1 +
      (2 : ENNReal) ^ (3 * r) *
        (ENNReal.ofReal ((4 : Real) / 7)) ^ (4 * r)) +
    ((1 + ENNReal.ofReal
      (Real.exp (-(3 : Real) * Delta / 28))) ^ (4 * r) - 1 +
      ((3 : ENNReal) ^ ((4 * r) / 5) *
        ((4 : ENNReal) / 3) ^ (4 * r)) *
        (ENNReal.ofReal ((172 : Real) / 343)) ^ (3 * r))) +
  ((1 + ENNReal.ofReal
    (Real.exp (-(Delta : Real) / 1000))) ^ (3 * r) - 1)
noncomputable def localPairContribution
    {r : Nat}
    (y z : Word (ZMod 2) (Fin (4 * r)))
    (b : Fin (4 * r))
    (localSample : LocalSample) : ZMod 2 :=
  if localSample false then
    if localSample true then y b else z b
  else
    0
noncomputable def rowPairSyndrome
    {r : Nat}
    (row : RowSample r)
    (y z : Word (ZMod 2) (Fin (4 * r))) : ZMod 2 :=
  ∑ b : Fin (4 * r), localPairContribution y z b (row b)
noncomputable def localPairSign
    {r : Nat}
    (y z : Word (ZMod 2) (Fin (4 * r)))
    (b : Fin (4 * r))
    (localSample : LocalSample) : Real :=
  RandomBase.paritySign
    (localPairContribution y z b localSample)
def localIncidenceReal (localSample : LocalSample) : Real :=
  cond (localSample false) 1 0
noncomputable def localSelectedPairSign
    {r : Nat}
    (y z : Word (ZMod 2) (Fin (4 * r)))
    (b : Fin (4 * r))
    (localSample : LocalSample) : Real :=
  if localSample true then
    RandomBase.paritySign (y b)
  else
    RandomBase.paritySign (z b)
noncomputable def rowViolationIndicator
    {r : Nat}
    (y z : Word (ZMod 2) (Fin (4 * r)))
    (row : RowSample r) : Real :=
  if rowPairSyndrome row y z ≠ 0 then 1 else 0
noncomputable def pairOverlapCount
    {r : Nat}
    (y z : Word (ZMod 2) (Fin (4 * r))) : Nat :=
  (Finset.univ.filter fun b => y b ≠ 0 ∧ z b ≠ 0).card
noncomputable def sampleRowViolationIndicator
    {r : Nat}
    (y z : Word (ZMod 2) (Fin (4 * r)))
    (a : Fin (3 * r))
    (sample : Sample r) : Real :=
  rowViolationIndicator y z (sample a)
noncomputable def centeredSampleRowViolationIndicator
    {r : Nat}
    (Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (y z : Word (ZMod 2) (Fin (4 * r)))
    (a : Fin (3 * r))
    (sample : Sample r) : Real :=
  sampleRowViolationIndicator y z a sample -
    (rowDistribution r Delta hDelta).toMeasure.real
      {row | rowPairSyndrome row y z ≠ 0}
noncomputable def typeRows
    (r typeCount : Nat) [NeZero typeCount]
    (τ : Fin typeCount) : Finset (Fin (3 * r)) :=
  Finset.univ.filter fun a => RandomTwist.checkType typeCount a = τ
noncomputable def groupedTypeViolationCount
    {r typeCount : Nat} [NeZero typeCount]
    (sample : Sample r)
    (τ : Fin typeCount)
    (y z : Word (ZMod 2) (Fin (4 * r))) : Nat :=
  ((typeRows r typeCount τ).filter fun a =>
    rowPairSyndrome (sample a) y z ≠ 0).card
noncomputable def binaryWordFinsetEquiv (r : Nat) :
    Word (ZMod 2) (Fin (4 * r)) ≃ Finset (Fin (4 * r)) where
  toFun := hammingSupport
  invFun := RandomBase.supportWord
  left_inv := RandomBase.supportWord_hammingSupport
  right_inv := RandomBase.hammingSupport_supportWord
abbrev NonzeroWordPair (r : Nat) :=
  {pair :
      Word (ZMod 2) (Fin (4 * r)) ×
        Word (ZMod 2) (Fin (4 * r)) //
    pair ≠ (0, 0)}
noncomputable instance instFintypeNonzeroWordPair (r : Nat) :
    Fintype (NonzeroWordPair r) := by
  classical
  exact Subtype.fintype _
abbrev LightFailureIndex (r typeCount : Nat) :=
  Fin typeCount × NonzeroWordPair r
noncomputable def groupedLightBadAt
    (r Delta typeCount : Nat) [NeZero typeCount]
    (index : LightFailureIndex r typeCount) :
    Set (Sample r) :=
  if
      Delta * HammingWeight index.2.1.1 ≤ 4 * (4 * r) ∧
      Delta * HammingWeight index.2.1.2 ≤ 4 * (4 * r)
    then
      {sample |
        100 * typeCount *
            groupedTypeViolationCount sample index.1
              index.2.1.1 index.2.1.2 <
          Delta *
            (HammingWeight index.2.1.1 +
              HammingWeight index.2.1.2)}
    else ∅
def HasGroupedHHO20LightChecks
    {r typeCount : Nat} [NeZero typeCount]
    (Delta : Nat) (sample : Sample r) : Prop :=
  ∀ (τ : Fin typeCount)
      (y z : Word (ZMod 2) (Fin (4 * r))),
    Delta * HammingWeight y ≤ 4 * (4 * r) →
    Delta * HammingWeight z ≤ 4 * (4 * r) →
      Delta * (HammingWeight y + HammingWeight z) ≤
        100 * typeCount * groupedTypeViolationCount sample τ y z
noncomputable def rowEitherViolationIndicator
    {r : Nat}
    (x outWord inWord : Word (ZMod 2) (Fin (4 * r)))
    (row : RowSample r) : Real :=
  if
      rowPairSyndrome row x outWord ≠ 0 ∨
      rowPairSyndrome row inWord x ≠ 0
    then 1
    else 0
noncomputable def selectedTypeRows
    (r typeCount : Nat) [NeZero typeCount]
    (types : Finset (Fin typeCount)) :
    Finset (Fin (3 * r)) :=
  Finset.univ.filter fun a =>
    RandomTwist.checkType typeCount a ∈ types
noncomputable def sampleRowEitherViolationIndicator
    {r typeCount : Nat} [NeZero typeCount]
    (x : Word (ZMod 2) (Fin (4 * r)))
    (outWord inWord :
      Fin typeCount → Word (ZMod 2) (Fin (4 * r)))
    (a : Fin (3 * r))
    (sample : Sample r) : Real :=
  rowEitherViolationIndicator x
    (outWord (RandomTwist.checkType typeCount a))
    (inWord (RandomTwist.checkType typeCount a))
    (sample a)
noncomputable def centeredSampleRowEitherViolationIndicator
    {r typeCount : Nat} [NeZero typeCount]
    (Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (x : Word (ZMod 2) (Fin (4 * r)))
    (outWord inWord :
      Fin typeCount → Word (ZMod 2) (Fin (4 * r)))
    (a : Fin (3 * r))
    (sample : Sample r) : Real :=
  sampleRowEitherViolationIndicator x outWord inWord a sample -
    ∫ sample',
      sampleRowEitherViolationIndicator
        x outWord inWord a sample' ∂
        (distribution r Delta hDelta).toMeasure
abbrev HHO20LightNeighborWord (r Delta : Nat) :=
  {w : Word (ZMod 2) (Fin (4 * r)) //
    Delta * HammingWeight w ≤ 2 * (4 * r)}
abbrev HeavyFailureIndex (r Delta typeCount : Nat) :=
  Word (ZMod 2) (Fin (4 * r)) ×
    Finset (Fin typeCount) ×
      (Fin typeCount → HHO20LightNeighborWord r Delta) ×
        (Fin typeCount → HHO20LightNeighborWord r Delta)
def groupedHeavyBadAt
    (r Delta typeCount ell : Nat) [NeZero typeCount]
    (typeShifts : Fin typeCount → Fin (ell - 1))
    (index : HeavyFailureIndex r Delta typeCount) :
    Set (Sample r) :=
  if
      4 * (4 * r) ≤ Delta * HammingWeight index.1 ∧
      98 * typeCount ≤ 100 * index.2.1.card
    then
      {sample |
        ¬4 * r ≤
          100 *
            TwistGraph.heavyIncidentViolationCount
              (baseSample sample) (twistSample sample typeShifts)
              index.1 index.2.1
              (fun τ => (index.2.2.1 τ).1)
              (fun τ => (index.2.2.2 τ).1)}
    else ∅
def HasGroupedHHO20PartitionedChecks
    {r typeCount ell : Nat} [NeZero typeCount]
    (Delta : Nat) (typeShifts : Fin typeCount → Fin (ell - 1))
    (sample : Sample r) : Prop :=
  HasGroupedHHO20LightChecks
      (r := r) (typeCount := typeCount) Delta sample ∧
    TwistGraph.HasHHO20HeavyChecks Delta
      (baseSample sample) (twistSample sample typeShifts)
def HasGroupedHHO20ConstructionBase
    {r typeCount ell : Nat} [NeZero typeCount]
    (Delta : Nat) (typeShifts : Fin typeCount → Fin (ell - 1))
    (sample : Sample r) : Prop :=
  RandomBase.IsFullyGood
      (Delta := Delta) (baseSample sample) ∧
    HasGroupedHHO20PartitionedChecks
      Delta typeShifts sample
end QEC.Coding.FiberBundle.RandomPartition


