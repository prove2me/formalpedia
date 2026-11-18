-- Prove2me | Definitions.Def_Kyprianou_Ch08_PassageAndPotentials
-- name    : Kyprianou_Ch08_PassageAndPotentials
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-17T07:14:57.939623+00:00
-- url     : https://prove2.me/theorems/fa8bbe69-08bf-4331-8202-7cff587da4c1
-- title:
--   Kyprianou Chapter 8: PassageAndPotentials
-- statement:
--   Strict upward and downward passage, equality hitting, last entrance times, infinity-aware discount and killed or unrestricted potential kernels.
-- source:
--   Kyprianou (2006), first edition, Chapter 8, original physical pages 219-246; source SHA-256 3696f4b3373cabcd968e300994fdd70a04df97b57a16837ad672bac5a1c269bf.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_ProcessAndExponent
open MeasureTheory Set
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch08

/-- Strict first passage t>0 above a; infinity if the set is empty.
WithTop is essential: a plain NNReal infimum cannot represent infinity. -/
noncomputable def tauPlus {Ω : Type*} (X : ℝ≥0 → Ω → ℝ)
    (a : ℝ) (ω : Ω) : WithTop ℝ≥0 :=
  sInf {t : WithTop ℝ≥0 | ∃ u : ℝ≥0,
    0 < u ∧ (u : WithTop ℝ≥0) = t ∧ a < X u ω}

/-- Strict first passage t>0 below a. -/
noncomputable def tauMinus {Ω : Type*} (X : ℝ≥0 → Ω → ℝ)
    (a : ℝ) (ω : Ω) : WithTop ℝ≥0 :=
  sInf {t : WithTop ℝ≥0 | ∃ u : ℝ≥0,
    0 < u ∧ (u : WithTop ℝ≥0) = t ∧ X u ω < a}

/-- Weak entry above a at strictly positive time, distinguished
from the strict >a convention of tauPlus. -/
noncomputable def tauWeakAbove {Ω : Type*} (X : ℝ≥0 → Ω → ℝ)
    (a : ℝ) (ω : Ω) : WithTop ℝ≥0 :=
  sInf {t : WithTop ℝ≥0 | ∃ u : ℝ≥0,
    0 < u ∧ (u : WithTop ℝ≥0) = t ∧ a ≤ X u ω}

/-- Weak entry below a, needed to distinguish the strict convention. -/
noncomputable def tauWeakBelow {Ω : Type*} (X : ℝ≥0 → Ω → ℝ)
    (a : ℝ) (ω : Ω) : WithTop ℝ≥0 :=
  sInf {t : WithTop ℝ≥0 | ∃ u : ℝ≥0,
    0 < u ∧ (u : WithTop ℝ≥0) = t ∧ X u ω ≤ a}

/-- First hit of -x (equality, not downcrossing). -/
noncomputable def hitNegative {Ω : Type*} (X : ℝ≥0 → Ω → ℝ)
    (x : ℝ) (ω : Ω) : WithTop ℝ≥0 :=
  sInf {t : WithTop ℝ≥0 | ∃ u : ℝ≥0,
    0 < u ∧ (u : WithTop ℝ≥0) = t ∧ X u ω = -x}

/-- Last entrance into (-infinity,0), Exercise 8.10: sup of
strictly positive t with X_t<0, with sup(empty)=0; infinity if
the negative visits are unbounded. Finiteness needs X_t→+infinity. -/
noncomputable def lastNegativeVisit {Ω : Type*}
    (X : ℝ≥0 → Ω → ℝ) (ω : Ω) : WithTop ℝ≥0 :=
  sSup {t : WithTop ℝ≥0 | ∃ u : ℝ≥0,
    0 < u ∧ (u : WithTop ℝ≥0) = t ∧ X u ω < 0}

/-- Discounted first-passage payoff, zero at infinite passage even at q=0. -/
noncomputable def discountedAt (q : ℝ) (τ : WithTop ℝ≥0) : ℝ :=
  match τ with
  | ⊤ => 0
  | (t : ℝ≥0) => Real.exp (-q * (t : ℝ))

/-- The left limit is a distinct path observable; existence/cadlag
must be proved from the actual Levy process before using at τ. -/
def IsLeftLimit {Ω : Type*} (X : ℝ≥0 → Ω → ℝ)
    (t : ℝ≥0) (ω : Ω) (v : ℝ) : Prop :=
  0 < t ∧
  Filter.Tendsto (fun s : ℝ≥0 => X s ω)
    (nhdsWithin t (Set.Iio t)) (nhds v)

/-- Adaptation of a WithTop-valued passage time to a filtration.
For a right-continuous completed natural filtration, this is the
measurability requirement that later results must establish. -/
def IsStoppingTime {Ω : Type*} (m : MeasurableSpace Ω)
    (ℱ : Filtration ℝ≥0 m) (τ : Ω → WithTop ℝ≥0) : Prop :=
  ∀ t : ℝ≥0, @MeasurableSet Ω (ℱ t) {ω | τ ω ≤ (t : WithTop ℝ≥0)}

/-- Post-passage path value exists only for finite passage time. -/
noncomputable def postPassageValue {Ω : Type*}
    (X : ℝ≥0 → Ω → ℝ) (τ : WithTop ℝ≥0) (ω : Ω) : Option ℝ :=
  match τ with
  | ⊤ => none
  | (t : ℝ≥0) => some (X t ω)

/-- Overshoot at finite passage; None when the passage time is
infinite. At downward passage, the sign must be interpreted separately. -/
noncomputable def passageOvershoot {Ω : Type*}
    (X : ℝ≥0 → Ω → ℝ) (a : ℝ)
    (τ : WithTop ℝ≥0) (ω : Ω) : Option ℝ :=
  (postPassageValue X τ ω).map (fun v => v - a)

/-- Left-value predicate at finite passage, different from X_tau. -/
def IsPrePassageValue {Ω : Type*}
    (X : ℝ≥0 → Ω → ℝ)
    (τ : WithTop ℝ≥0) (ω : Ω) (v : ℝ) : Prop :=
  ∃ t : ℝ≥0, (t : WithTop ℝ≥0) = τ ∧
    IsLeftLimit X t ω v

/-- Lebesgue measure on nonnegative clock time, pushed forward from
nonnegative real time; this is the clock in the q-resolvent integral. -/
noncomputable def positiveTimeLebesgue : Measure ℝ≥0 :=
  Measure.map Real.toNNReal
    (volume.restrict (Set.Ici (0 : ℝ)))

/-- A q-resolvent on real state space, defined through its measure identity.
Kernels and their measurability are obligations, not density axioms. -/
def IsResolvent {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ)
    (q : ℝ) (U : Measure ℝ) : Prop :=
  0 ≤ q ∧
  ∀ A : Set ℝ, MeasurableSet A →
    U A = ∫⁻ t : ℝ≥0,
      ENNReal.ofReal (Real.exp (-q * (t : ℝ))) *
        P {ω | X t ω ∈ A} ∂positiveTimeLebesgue

/-- Killed interval (0,a): lifetime is tau_0^- ∧ tau_a^+. -/
def IsIntervalKilledResolvent {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ)
    (q a : ℝ) (U : Measure ℝ) : Prop :=
  0 ≤ q ∧ 0 < a ∧
  ∀ A : Set ℝ, MeasurableSet A →
    U A = ∫⁻ t : ℝ≥0,
      ENNReal.ofReal (Real.exp (-q * (t : ℝ))) *
        P {ω | (t : WithTop ℝ≥0) <
          min (tauMinus X 0 ω) (tauPlus X a ω) ∧ X t ω ∈ A} ∂positiveTimeLebesgue

/-- Killed on the half-line at first strict downcrossing. -/
def IsHalflineKilledResolvent {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ)
    (q : ℝ) (U : Measure ℝ) : Prop :=
  0 ≤ q ∧
  ∀ A : Set ℝ, MeasurableSet A →
    U A = ∫⁻ t : ℝ≥0,
      ENNReal.ofReal (Real.exp (-q * (t : ℝ))) *
        P {ω | (t : WithTop ℝ≥0) < tauMinus X 0 ω ∧ X t ω ∈ A} ∂positiveTimeLebesgue

/-- Genuine measurable-state kernel with the full x-coordinate
resolvent law. The Kernel type forces the x to measure map to be measurable. -/
def IsResolventKernel {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ)
    (q : ℝ) (K : ProbabilityTheory.Kernel ℝ ℝ) : Prop :=
  ∀ x : ℝ, IsResolvent P (fun t ω => x + X t ω) q (K x)

end Kyprianou.Ch08


