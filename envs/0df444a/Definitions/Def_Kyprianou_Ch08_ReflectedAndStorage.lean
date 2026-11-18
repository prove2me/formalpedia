-- Prove2me | Definitions.Def_Kyprianou_Ch08_ReflectedAndStorage
-- name    : Kyprianou_Ch08_ReflectedAndStorage
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-17T07:15:50.693902+00:00
-- url     : https://prove2.me/theorems/837bfb69-ca15-40c7-be96-87fff1a100cd
-- title:
--   Kyprianou Chapter 8: ReflectedAndStorage
-- statement:
--   Supremum and infimum reflected Levy processes, first exit, full reflected q-potential measure and almost-sure double Skorokhod capped storage with version independence.
-- source:
--   Kyprianou (2006), first edition, Chapter 8, original physical pages 219-246; source SHA-256 3696f4b3373cabcd968e300994fdd70a04df97b57a16837ad672bac5a1c269bf.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_PassageAndPotentials
open MeasureTheory Set
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch08

/-- Local boundedness of each original sample path, needed before
the real-valued interval suprema/infima have their intended meaning.
Cadlag Levy paths imply this; it is a proof obligation for a.s. paths. -/
def HasLocallyBoundedPaths {Ω : Type*}
    (X : ℝ≥0 → Ω → ℝ) : Prop :=
  ∀ (ω : Ω) (t : ℝ≥0),
    BddAbove {y : ℝ | ∃ u : ℝ≥0, u ≤ t ∧ y = X u ω} ∧
    BddBelow {y : ℝ | ∃ u : ℝ≥0, u ≤ t ∧ y = X u ω}

/-- The source process is only required to have locally bounded
paths P-almost surely. A globally cadlag modification and a choice of
such a representative are separate obligations, not implicit data. -/
def HasLocallyBoundedPathsAlmostSure {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℝ≥0 → Ω → ℝ) : Prop :=
  ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
    BddAbove {y : ℝ | ∃ u : ℝ≥0, u ≤ t ∧ y = X u ω} ∧
    BddBelow {y : ℝ | ∃ u : ℝ≥0, u ≤ t ∧ y = X u ω}

/-- Running sup on [0,t]. For arbitrary paths this needs bounded-above
proof; finite values follow from cadlag on compact intervals. -/
noncomputable def runningSup {Ω : Type*} (X : ℝ≥0 → Ω → ℝ)
    (t : ℝ≥0) (ω : Ω) : ℝ :=
  sSup {y : ℝ | ∃ u : ℝ≥0, u ≤ t ∧ y = X u ω}

/-- Running inf on [0,t], with the analogous bounded-below caveat. -/
noncomputable def runningInf {Ω : Type*} (X : ℝ≥0 → Ω → ℝ)
    (t : ℝ≥0) (ω : Ω) : ℝ :=
  sInf {y : ℝ | ∃ u : ℝ≥0, u ≤ t ∧ y = X u ω}

/-- Reflection at the supremum: Y^x_t = (x vee Xbar_t)-X_t.
This is a drawdown process, not the infimum reflection. -/
noncomputable def reflectAtSup {Ω : Type*}
    (X : ℝ≥0 → Ω → ℝ) (x : ℝ)
    (t : ℝ≥0) (ω : Ω) : ℝ :=
  max x (runningSup X t ω) - X t ω

/-- Reflection at the infimum: Z^x_t = X_t-(Xunder_t wedge -x). -/
noncomputable def reflectAtInf {Ω : Type*}
    (X : ℝ≥0 → Ω → ℝ) (x : ℝ)
    (t : ℝ≥0) (ω : Ω) : ℝ :=
  X t ω - min (runningInf X t ω) (-x)

/-- The strict first exit of the supremum-reflected process. -/
noncomputable def reflectedSupExit {Ω : Type*}
    (X : ℝ≥0 → Ω → ℝ) (x a : ℝ) (ω : Ω) : WithTop ℝ≥0 :=
  tauPlus (reflectAtSup X x) a ω

/-- The strict first exit of the infimum-reflected process. -/
noncomputable def reflectedInfExit {Ω : Type*}
    (X : ℝ≥0 → Ω → ℝ) (x a : ℝ) (ω : Ω) : WithTop ℝ≥0 :=
  tauPlus (reflectAtInf X x) a ω

/-- A double Skorokhod reflection on a COMMON measurable full-measure
set of locally bounded/cadlag source paths. Exceptional null paths do
not require finite real regulators, and all balance/contact requirements
are restricted to the same event. This structure asserts no Laplace
identity or first-emptying transform. -/
structure CappedStorage {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (input : ℝ≥0 → Ω → ℝ)
    (initial capacity : ℝ) where
  nonnegativeInitial : 0 ≤ initial
  initialWithinCapacity : initial ≤ capacity
  good : Set Ω
  goodMeasurable : MeasurableSet good
  goodAlmostSure : ∀ᵐ ω ∂P, ω ∈ good
  goodCadlag : ∀ ω ∈ good,
    (∀ t : ℝ≥0, ContinuousWithinAt
      (fun u : ℝ≥0 => input u ω) (Set.Ici t) t) ∧
    (∀ t : ℝ≥0, 0 < t → ∃ left : ℝ,
      Filter.Tendsto (fun u : ℝ≥0 => input u ω)
        (nhdsWithin t (Set.Iio t)) (nhds left))
  workload : ℝ≥0 → Ω → ℝ
  lowerRegulator : ℝ≥0 → Ω → ℝ
  upperRegulator : ℝ≥0 → Ω → ℝ
  workloadMeasurable : ∀ t, Measurable (workload t)
  lowerMeasurable : ∀ t, Measurable (lowerRegulator t)
  upperMeasurable : ∀ t, Measurable (upperRegulator t)
  lowerInitiallyZero : ∀ ω ∈ good, lowerRegulator 0 ω = 0
  upperInitiallyZero : ∀ ω ∈ good, upperRegulator 0 ω = 0
  balance : ∀ t ω, ω ∈ good →
    workload t ω = initial + input t ω +
      lowerRegulator t ω - upperRegulator t ω
  range : ∀ t ω, ω ∈ good →
    0 ≤ workload t ω ∧ workload t ω ≤ capacity
  lowerMonotone : ∀ ω ∈ good, ∀ s t, s ≤ t →
    lowerRegulator s ω ≤ lowerRegulator t ω
  upperMonotone : ∀ ω ∈ good, ∀ s t, s ≤ t →
    upperRegulator s ω ≤ upperRegulator t ω
  lowerContact : ∀ ω ∈ good, ∀ s t, s ≤ t →
    (∀ u, s ≤ u → u ≤ t → 0 < workload u ω) →
    lowerRegulator s ω = lowerRegulator t ω
  upperContact : ∀ ω ∈ good, ∀ s t, s ≤ t →
    (∀ u, s ≤ u → u ≤ t → workload u ω < capacity) →
    upperRegulator s ω = upperRegulator t ω

/-- Existence with uniqueness of the workload/regulators modulo one
probability-one event; equality is across all times simultaneously.
The null-path choice does not affect the source first-passage law. -/
def HasUniqueCappedStorage {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ)
    (initial capacity : ℝ) : Prop :=
  ∃ S : CappedStorage P X initial capacity,
    ∀ T : CappedStorage P X initial capacity,
      ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        S.workload t ω = T.workload t ω ∧
        S.lowerRegulator t ω = T.lowerRegulator t ω ∧
        S.upperRegulator t ω = T.upperRegulator t ω

/-- First emptying of a selected full-measure reflected solution,
starting at positive time and using the weak zero-level hit. -/
noncomputable def cappedEmptyingTime {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω}
    {X : ℝ≥0 → Ω → ℝ} {x c : ℝ}
    (S : CappedStorage P X x c) (ω : Ω) : WithTop ℝ≥0 :=
  tauWeakBelow S.workload 0 ω

/-- Source scale-function candidate for the complete reflected resolvent.
The density is taken after cancellation at positive discount. The real
quotients are only interpreted as a measure formula when the derivative at
the upper endpoint is nonzero; no zero-over-zero value is assigned. -/
noncomputable def supremumReflectedScaleResolvent
    (W : ℝ → ℝ → ℝ) (q x a : ℝ) : Measure ℝ :=
  let V := W q
  let da := derivWithin V (Set.Ici a) a
  (ENNReal.ofReal (V (a - x) * V 0 / da)) •
    (Measure.dirac (0 : ℝ)) +
  (volume.restrict (Set.Ioo 0 a)).withDensity
    (fun y : ℝ =>
      ENNReal.ofReal
        (V (a - x) * derivWithin V (Set.Ici y) y / da -
          V (y - x)))

/-- q-potential measure for the supremum-reflected process killed at
its first strict upcrossing of a. No density or atom formula is postulated. -/
def IsSupremumReflectedPotential {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ)
    (q x a : ℝ) (U : Measure ℝ) : Prop :=
  0 ≤ q ∧ 0 ≤ x ∧ x ≤ a ∧ 0 < a ∧
  ∀ A : Set ℝ, MeasurableSet A →
    U A = ∫⁻ t : ℝ≥0,
      ENNReal.ofReal (Real.exp (-q * (t : ℝ))) *
        P {ω | (t : WithTop ℝ≥0) <
          reflectedSupExit X x a ω ∧
          reflectAtSup X x t ω ∈ A} ∂positiveTimeLebesgue

/-- q-potential measure for the infimum-reflected process killed at a. -/
def IsInfimumReflectedPotential {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ)
    (q x a : ℝ) (U : Measure ℝ) : Prop :=
  0 ≤ q ∧ 0 ≤ x ∧ x ≤ a ∧ 0 < a ∧
  ∀ A : Set ℝ, MeasurableSet A →
    U A = ∫⁻ t : ℝ≥0,
      ENNReal.ofReal (Real.exp (-q * (t : ℝ))) *
        P {ω | (t : WithTop ℝ≥0) <
          reflectedInfExit X x a ω ∧
          reflectAtInf X x t ω ∈ A} ∂positiveTimeLebesgue

end Kyprianou.Ch08


