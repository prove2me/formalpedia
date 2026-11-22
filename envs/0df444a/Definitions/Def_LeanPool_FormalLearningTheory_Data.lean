-- Prove2me | Definitions.Def_LeanPool_FormalLearningTheory_Data
-- name    : LeanPool_FormalLearningTheory_Data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T05:31:52.823022+00:00
-- url     : https://prove2.me/theorems/e3be5a0b-2430-4d50-b425-14ff883f92c1
-- title:
--   Data
-- statement:
--   Definitions and structural lemmas for Data, from Dhruv Gupta; LeanPool contributors's pinned Formal Learning Theory Kernel development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Data.lean

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
set_option autoImplicit true
@[expose] public section
@[expose] public section
universe u v
abbrev TimeStep := ℕ
structure DataStream (X : Type u) (Y : Type v) where
  /-- The stream of examples at each time step -/
  observe : TimeStep → X × Y
structure TextPresentation (X : Type u) (c : X → Bool) extends DataStream X Bool where
  /-- Every element in the stream is a positive example -/
  positive : ∀ t, (observe t).2 = true
  /-- Every element in the stream satisfies c -/
  correct : ∀ t, c (observe t).1 = true
  /-- Every positive element eventually appears -/
  exhaustive : ∀ x, c x = true → ∃ t, (observe t).1 = x
structure InformantPresentation (X : Type u) (c : X → Bool) extends DataStream X Bool where
  /-- Labels are correct: the stream tells the truth about membership -/
  correct : ∀ t, (observe t).2 = c (observe t).1
  /-- Every element of X eventually appears -/
  exhaustive : ∀ x : X, ∃ t, (observe t).1 = x
structure NoisyDataStream (X : Type u) (Y : Type v) extends DataStream X Y where
  /-- The true labels (unobserved by learner) -/
  trueLabel : TimeStep → Y
  /-- Noise rate: probability of corruption at each step -/
  noiseRate : ℝ
  /-- Noise rate is bounded -/
  noiseRate_pos : 0 ≤ noiseRate
  noiseRate_lt : noiseRate < 1 / 2
structure IIDSample (X : Type u) (Y : Type v) [MeasurableSpace X] [MeasurableSpace Y] where
  /-- The underlying distribution over labeled examples -/
  distribution : MeasureTheory.Measure (X × Y)
  /-- The distribution is a probability measure -/
  isProbability : MeasureTheory.IsProbabilityMeasure distribution
  /-- Sample size -/
  sampleSize : ℕ
  /-- The sample itself: a function from index to labeled example -/
  sample : Fin sampleSize → X × Y
class MeasurableBoolSpace (X : Type u) [MeasurableSpace X] : Prop where
  all_bool_measurable : ∀ f : X → Bool, Measurable f
instance (priority := 50) MeasurableHypotheses.ofMeasurableBoolSpace
    {X : Type u} [MeasurableSpace X] [h : MeasurableBoolSpace X]
    (C : ConceptClass X Bool) : MeasurableHypotheses X C where
  mem_measurable := fun c _ => h.all_bool_measurable c
noncomputable def IIDSample.marginalX {X : Type u} {Y : Type v}
    [MeasurableSpace X] [MeasurableSpace Y]
    (S : IIDSample X Y) : MeasureTheory.Measure X :=
  S.distribution.map Prod.fst
structure MembershipOracle (X : Type u) (Y : Type v) where
  /-- The oracle's response function -/
  query : X → Y
  /-- The target concept the oracle answers about -/
  target : Concept X Y
  /-- Oracle is truthful -/
  truthful : ∀ x, query x = target x
structure EquivalenceOracle (X : Type u) (Y : Type v) where
  /-- The target concept -/
  target : Concept X Y
  /-- Query: given hypothesis, either confirm or give counterexample -/
  query : Concept X Y → Option X
  /-- If query returns none, hypothesis equals target -/
  correct_none : ∀ h, query h = none → h = target
  /-- If query returns some x, it's a genuine counterexample -/
  correct_some : ∀ h x, query h = some x → h x ≠ target x
def Counterexample (X : Type u) (Y : Type v) (h c : Concept X Y) := { x : X // h x ≠ c x }
def Advice (A : Type*) := A


