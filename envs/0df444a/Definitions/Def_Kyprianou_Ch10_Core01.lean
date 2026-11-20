-- Prove2me | Definitions.Def_Kyprianou_Ch10_Core01
-- name    : Kyprianou_Ch10_Core01
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T15:37:00.262034+00:00
-- url     : https://prove2.me/theorems/40b43402-f41e-47a3-a46c-46932f349e6d
-- title:
--   Kyprianou Ch10 original model source, bounded segment 1/7
-- statement:
--   Dependency-closed original Chapter 10 Lean source, ordered segment 1 of 7; immutable source lines 24 to 479. Historical original declaration names and proof bodies preserved; no theorem is being asserted Proved.

import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Process.Filtration
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Data.EReal.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Martingale.Basic

open Filter Set ProbabilityTheory

open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch10

abbrev Time := ℝ≥0
abbrev Mass := ℝ≥0∞

/-- Population path and original-law family, with defining initial conditions. -/
structure CSBPRaw (Ω : Type*) [MeasurableSpace Ω] where
  process : Time → Ω → Mass
  law : Time → Measure Ω
  probability : ∀ x : Time, IsProbabilityMeasure (law x)
  measurable_coordinate : ∀ t : Time, Measurable (process t)
  starts_at : ∀ x : Time, (law x) {ω | process 0 ω = (x : Mass)} = 1

/-- One-time transition law of the mass at time t from mass x. -/
noncomputable def transition {Ω : Type*} [MeasurableSpace Ω]
    (Y : CSBPRaw Ω) (t : Time) (x : Time) : Measure Mass :=
  (Y.law x).map (Y.process t)

/-- Source defining branching property for independent initial populations. -/
def HasBranching {Ω : Type*} [MeasurableSpace Ω]
    (Y : CSBPRaw Ω) : Prop :=
  ∀ (t : Time) (x y : Time),
    transition Y t (x + y) =
      ((Y.law x).prod (Y.law y)).map
        (fun z : Ω × Ω => Y.process t z.1 + Y.process t z.2)

/-- Unique absorbing boundary law used only for the infinite *state*
of the transition kernel. The source original laws have finite initial mass. -/
noncomputable def extendedTransition {Ω : Type*} [MeasurableSpace Ω]
    (Y : CSBPRaw Ω) (t : Time) (m : Mass) : Measure Mass :=
  if m = ⊤ then Measure.dirac (⊤ : Mass)
  else transition Y t m.toNNReal

/-- Boundary extension is a canonical absorbing law, not arbitrary source data. -/
theorem extendedTransition_top {Ω : Type*} [MeasurableSpace Ω]
    (Y : CSBPRaw Ω) (t : Time) :
    extendedTransition Y t (⊤ : Mass) = Measure.dirac (⊤ : Mass) := by
  simp [extendedTransition]

/-- The canonical infinite-state extension agrees with the original
finite-initial-mass transition laws at every finite state. -/
theorem extendedTransition_finite {Ω : Type*} [MeasurableSpace Ω]
    (Y : CSBPRaw Ω) (t x : Time) :
    extendedTransition Y t (x : Mass) = transition Y t x := by
  simp [extendedTransition]

/-- Source Markov transition-semigroup law at one-time marginals. -/
def HasChapmanKolmogorov {Ω : Type*} [MeasurableSpace Ω]
    (Y : CSBPRaw Ω) : Prop :=
  ∀ (s t x : Time),
    transition Y (s + t) x = (transition Y s x).bind (extendedTransition Y t)

/-- Continuous extension from positive Laplace parameters at infinity:
the zero-parameter value is 0 for an infinite population, not 1. -/
noncomputable def expNegMass (theta : Time) (m : Mass) : Mass :=
  if m = ⊤ then 0
  else ENNReal.ofReal (Real.exp (-((theta : ℝ) * m.toReal)))


/-- The extended-state kernel at zero detects finite population mass. -/
theorem expNegMass_zero_finite (x : Time) :
    expNegMass 0 (x : Mass) = 1 := by
  simp [expNegMass]

/-- Infinite mass, whether caused by explosion or the absorbed killed state,
contributes zero to the positive-parameter limit and its extension at zero. -/
theorem expNegMass_zero_infinity :
    expNegMass 0 (⊤ : Mass) = 0 := by
  simp [expNegMass]

theorem expNegMass_positive_infinity (theta : Time) :
    expNegMass theta (⊤ : Mass) = 0 := by
  simp [expNegMass]

/-- Laplace functional of the original law at initial mass x. -/
noncomputable def laplace {Ω : Type*} [MeasurableSpace Ω]
    (Y : CSBPRaw Ω) (x : Time) (t theta : Time) : Mass :=
  ∫⁻ ω, expNegMass theta (Y.process t ω) ∂ Y.law x

/-- The defining exponential-affine Laplace identity for a CSBP cumulant. -/
def HasCumulant {Ω : Type*} [MeasurableSpace Ω]
    (Y : CSBPRaw Ω) (u : Time → Time → Time) : Prop :=
  ∀ (x t theta : Time),
    laplace Y x t theta = expNegMass (u t theta) (x : Mass)

end Kyprianou.Ch10

open MeasureTheory Set
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch10.Mechanism

/-- Source Lévy–Khintchine parameters, including optional independent killing.
Jump integrability is the genuine Lévy-measure second-order condition. -/
structure Parameters where
  killing : ℝ≥0
  drift : ℝ
  gaussianVariance : ℝ≥0
  jumps : Measure ℝ≥0
  no_zero_atom : jumps {0} = 0
  second_order_integrable :
    (∫⁻ z : ℝ≥0, min (1 : ℝ≥0∞) ((z : ℝ≥0∞) ^ (2 : ℕ)) ∂ jumps) < ⊤

/-- The compensated small-positive-jump integrand. -/
noncomputable def jumpIntegrand (theta z : ℝ≥0) : ℝ :=
  Real.exp (-(theta : ℝ) * (z : ℝ)) - 1 +
    (if z < 1 then (theta : ℝ) * (z : ℝ) else 0)

/-- Actual signed branching mechanism, with the Lévy integral over positive
jump heights and the no-killing case obtained by setting killing = 0. -/
noncomputable def psi (T : Parameters) (theta : ℝ≥0) : ℝ :=
  -(T.killing : ℝ) - T.drift * (theta : ℝ) +
    (T.gaussianVariance : ℝ) * (theta : ℝ) ^ (2 : ℕ) / 2 +
    ∫ z : ℝ≥0, jumpIntegrand theta z ∂ T.jumps

/-- A killed pure-drift limiting cumulant u(t,theta)=theta+q*t.
For q>0 and t>0 this is strictly positive at theta=0. -/
def pureKillingCumulant (q : ℝ≥0) (t : ℝ) (theta : ℝ≥0) : ℝ :=
  (theta : ℝ) + (q : ℝ) * t

theorem pureKillingCumulant_zero (q : ℝ≥0) (t : ℝ) :
    pureKillingCumulant q t 0 = (q : ℝ) * t := by
  simp [pureKillingCumulant]

/-- Positive killing is compatible with a strictly positive cumulant
at zero: the pure-killing solution has u(t,0)=q*t>0 when q,t>0. -/
theorem pureKillingCumulant_zero_positive (q : ℝ≥0) (t : ℝ)
    (hq : 0 < q) (ht : 0 < t) :
    0 < pureKillingCumulant q t 0 := by
  have hqr : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  simpa [pureKillingCumulant] using (mul_pos hqr ht)

/-- Right-sided source cumulant ODE, including the t=0 boundary.
The ODE is a target predicate, not a field of Parameters. -/
def HasCumulantODE (u : ℝ → ℝ≥0 → ℝ)
    (T : Parameters) : Prop :=
  (∀ theta : ℝ≥0, u 0 theta = (theta : ℝ)) ∧
  (∀ (t : ℝ), 0 ≤ t →
    ∀ (theta : ℝ≥0), 0 ≤ u t theta ∧
      HasDerivWithinAt (fun s : ℝ => u s theta)
        (-(psi T (Real.toNNReal (u t theta)))) (Ici (0 : ℝ)) t)

end Kyprianou.Ch10.Mechanism

open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch10

/-- Original branching mechanism on nonnegative arguments. -/
abbrev Mechanism := ℝ≥0 → ℝ

/-- An extended right-hand derivative at zero, allowing negative infinity.
The value of the quotient at zero is ignored by the positive one-sided filter. -/
def HasRightSlope (psi : Mechanism) (slope : EReal) : Prop :=
  Tendsto
    (fun theta : ℝ≥0 => ((psi theta - psi 0) / (theta : ℝ) : EReal))
    (nhdsWithin (0 : ℝ≥0) (Ioi 0)) (nhds slope)

/-- Complete Definition 10.4(i), defined by the sign of psi'(0+). -/
def SubcriticalMechanism (psi : Mechanism) : Prop :=
  ∃ slope : EReal, HasRightSlope psi slope ∧ 0 < slope

/-- Complete Definition 10.4(ii), including the one-sided derivative. -/
def CriticalMechanism (psi : Mechanism) : Prop :=
  ∃ slope : EReal, HasRightSlope psi slope ∧ slope = 0

/-- Complete Definition 10.4(iii), including infinite negative slope. -/
def SupercriticalMechanism (psi : Mechanism) : Prop :=
  ∃ slope : EReal, HasRightSlope psi slope ∧ slope < 0

end Kyprianou.Ch10

open MeasureTheory Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch10.Clock

abbrev Time := ℝ≥0
abbrev ExtendedTime := ℝ≥0∞

/-- Integrated real Lebesgue time up to a nonnegative endpoint, using an
extended nonnegative integrand to retain infinite occupation accurately. -/
noncomputable def occupation {Ω : Type*}
    (Y : Time → Ω → ExtendedTime) (ω : Ω) (t : Time) : ExtendedTime :=
  ∫⁻ s in Icc (0 : ℝ) (t : ℝ), Y (Real.toNNReal s) ω ∂ (volume : Measure ℝ)

/-- Reciprocal of a strictly positive height, with infinity at zero. -/
noncomputable def positiveReciprocal (height : ℝ) : ExtendedTime :=
  if 0 < height then ENNReal.ofReal height⁻¹ else ⊤

/-- Extended reciprocal Lamperti clock before first strict down-crossing. -/
noncomputable def reciprocal {Ω : Type*}
    (X : Time → Ω → ℝ) (ω : Ω) (t : Time) : ExtendedTime :=
  ∫⁻ s in Icc (0 : ℝ) (t : ℝ),
    positiveReciprocal (X (Real.toNNReal s) ω) ∂ (volume : Measure ℝ)

/-- Right generalised inverse; the empty event has infinite inverse time. -/
noncomputable def inverse (A : Time → ExtendedTime)
    (u : ExtendedTime) : ExtendedTime :=
  sInf {t : ExtendedTime | t ≠ ⊤ ∧ u < A t.toNNReal}

end Kyprianou.Ch10.Clock

open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch10.Killing

abbrev Time := ℝ≥0
abbrev Lifetime := ℝ≥0∞
abbrev Mass := ℝ≥0∞

/-- Cemetery has a distinct value None; Some 0 means extinction and
Some infinity means explosion. This preserves all three source events. -/
abbrev KilledMass := Option Mass

/-- Kill at or after the extended lifetime, respecting infinity as never
killed at any finite physical time. -/
noncomputable def atLifetime {Ω A : Type*} (Y : Time → Ω → A)
    (life : Ω → Lifetime) (t : Time) (ω : Ω) : Option A :=
  if (t : Lifetime) < life ω then some (Y t ω) else none

/-- Lifetime of the first among physical down-crossing and independent kill. -/
noncomputable def firstLifetime {Ω : Type*} (strictNegative independentKill : Ω → Lifetime)
    (ω : Ω) : Lifetime :=
  min (strictNegative ω) (independentKill ω)

/-- Exact exponential survival condition, with rate zero corresponding
to almost sure survival at every finite time. -/
def HasExponentialKilling {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (ζ : Ω → Lifetime) (q : Time) : Prop :=
  ∀ t : Time,
    μ {ω | (t : Lifetime) < ζ ω} =
      ENNReal.ofReal (Real.exp (-((q : ℝ) * (t : ℝ))))

end Kyprianou.Ch10.Killing

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch10.Levy

abbrev Time := ℝ≥0
abbrev Lifetime := ℝ≥0∞

/-- Measurable real Lévy path data with a spectrally positive jump condition.
Stationary independent increments are separate model obligations. -/
structure PositiveJumpPaths (Ω : Type*) [MeasurableSpace Ω] where
  path : Time → Ω → ℝ
  leftLimit : Time → Ω → ℝ
  law : ℝ → Measure Ω
  probability : ∀ x : ℝ, IsProbabilityMeasure (law x)
  coordinate_measurable : ∀ t : Time, Measurable (path t)
  initial : ∀ x : ℝ, (law x) {ω | path 0 ω = x} = 1
  left_limit_correct : ∀ (ω : Ω) (t : Time), 0 < t →
    Tendsto (fun s : Time => path s ω) (nhdsWithin t (Iio t)) (nhds (leftLimit t ω))
  no_negative_jump : ∀ (ω : Ω) (t : Time), 0 < t →
    leftLimit t ω ≤ path t ω

/-- First strict entry into the negative half-line, with infinity if absent. -/
noncomputable def firstStrictNegative {Ω : Type*}
    (X : Time → Ω → ℝ) (ω : Ω) : Lifetime :=
  sInf {t : Lifetime | t ≠ ⊤ ∧ X t.toNNReal ω < 0}

/-- First hit of zero; this differs from strict first passage below zero. -/
noncomputable def firstHitZero {Ω : Type*}
    (X : Time → Ω → ℝ) (ω : Ω) : Lifetime :=
  sInf {t : Lifetime | t ≠ ⊤ ∧ X t.toNNReal ω = 0}

end Kyprianou.Ch10.Levy

namespace Kyprianou.Ch10.Levy

/-- Lévy law: right-continuous paths and stationary increments which are
independent of the entire natural history, for each initial state. -/
def HasLevyLaw {Ω : Type*} [MeasurableSpace Ω]
    (X : PositiveJumpPaths Ω) : Prop :=
  (∀ (ω : Ω) (t : Time),
    Tendsto (fun s : Time => X.path s ω)
      (nhdsWithin t (Ici t)) (nhds (X.path t ω))) ∧
  (∀ (x : ℝ) (s t : Time),
    (X.law x).map (fun ω => X.path (s + t) ω - X.path s ω) =
      (X.law 0).map (fun ω => X.path t ω)) ∧
  (∀ (x : ℝ) (s t : Time),
    Indep
      (MeasurableSpace.comap
        (fun ω : Ω => fun r : {r : Time // r ≤ s} => X.path r.1 ω)
        inferInstance)
      (MeasurableSpace.comap
        (fun ω : Ω => X.path (s + t) ω - X.path s ω)
        inferInstance)
      (X.law x))

end Kyprianou.Ch10.Levy

namespace Kyprianou.Ch10

/-- The original path history through s, including all coordinates up to s. -/
def naturalPast {Ω : Type*} [MeasurableSpace Ω]
    (Y : CSBPRaw Ω) (s : Time) : MeasurableSpace Ω :=
  MeasurableSpace.comap
    (fun ω : Ω => fun t : {t : Time // t ≤ s} => Y.process t.1 ω)
    inferInstance

/-- Actual finite-dimensional conditional Markov property, tested against
every event in the full original natural history, not only one-time laws. -/
def HasPathMarkov {Ω : Type*} [MeasurableSpace Ω]
    (Y : CSBPRaw Ω) : Prop :=
  ∀ (s t : Time) (x : Time) (A : Set Ω) (B : Set Mass),
    @MeasurableSet Ω (naturalPast Y s) A →
    MeasurableSet B →
    Y.law x (A ∩ {ω | Y.process (s + t) ω ∈ B}) =
      ∫⁻ ω in A, extendedTransition Y t (Y.process s ω) B ∂ Y.law x

/-- Right-continuous paths with existing left limits at every positive
physical time; this is a path property, not an assumed Lamperti theorem. -/
def HasCadlagPaths {Ω : Type*} [MeasurableSpace Ω]
    (Y : CSBPRaw Ω) : Prop :=
  ∀ x : Time, ∀ᵐ ω ∂ Y.law x,
    (∀ t : Time,
      Tendsto (fun s : Time => Y.process s ω)
        (nhdsWithin t (Set.Ici t)) (nhds (Y.process t ω))) ∧
    (∀ t : Time, 0 < t →
      ∃ l : Mass,
        Tendsto (fun s : Time => Y.process s ω)
          (nhdsWithin t (Set.Iio t)) (nhds l))

/-- Complete Theorem 10.1 proposal: from the defining branching and
conditional Markov properties, construct the true Laplace cumulant, its
time ODE and a killed Lévy–Khintchine branching mechanism. The theorem
is an unproved Prop; no result is assumed as a model field. -/
def theorem10_1_source_type {Ω : Type*} [MeasurableSpace Ω]
    (Y : CSBPRaw Ω) : Prop :=
  HasBranching Y →
  HasPathMarkov Y →
  HasCadlagPaths Y →
  ∃ (u : ℝ → Time → ℝ) (T : Mechanism.Parameters),
    Mechanism.HasCumulantODE u T ∧
      ∀ (x t theta : Time),
        laplace Y x t theta =
          expNegMass (Real.toNNReal (u (t : ℝ) theta)) (x : Mass)

end Kyprianou.Ch10

namespace Kyprianou.Ch10

/-- Genuine conservativeness: no path of infinite mass at a finite time,
for every finite nonnegative initial population under its original law. -/
def ConservativePopulation {Ω : Type*} [MeasurableSpace Ω]
    (Y : CSBPRaw Ω) : Prop :=
  ∀ (x t : Time),
    Y.law x {ω | Y.process t ω ≠ ⊤} = 1

/-- Proper reciprocal of |psi|, interpreted as infinity at its zeros,
rather than Lean's total division by zero. -/
noncomputable def reciprocalAbsMechanism
    (T : Mechanism.Parameters) (theta : Time) : Mass :=
  if Mechanism.psi T theta = 0 then ⊤
  else ENNReal.ofReal (1 / |Mechanism.psi T theta|)

/-- Source Grey divergence at zero, requiring divergence on every
sufficiently small positive interval and excluding far-away roots. -/
def GreyNearZeroDivergence (T : Mechanism.Parameters) : Prop :=
  ∀ delta : Time, 0 < delta →
    (∫⁻ s in Set.Ioc (0 : ℝ) (delta : ℝ),
      reciprocalAbsMechanism T (Real.toNNReal s) ∂ (volume : Measure ℝ)) = ⊤

/-- Extended first moment of jumps of size at least one. -/
def FiniteLargeJumpFirstMoment (T : Mechanism.Parameters) : Prop :=
  (∫⁻ z in Set.Ici (1 : Time), (z : Mass) ∂ T.jumps) < ⊤

/-- The source's assumption that T describes the given CSBP Laplace
cumulant. This is an explicitly named prior-Theorem-10.1 obligation. -/
def HasIdentifiedMechanism {Ω : Type*} [MeasurableSpace Ω]
    (Y : CSBPRaw Ω) (T : Mechanism.Parameters) : Prop :=
  ∃ u : ℝ → Time → ℝ,
    Mechanism.HasCumulantODE u T ∧
      ∀ (x t theta : Time),
        laplace Y x t theta =
          expNegMass (Real.toNNReal (u (t : ℝ) theta)) (x : Mass)

/-- Theorem 10.3: exact extended Grey criterion, necessary absence of
killing, sufficiency of a finite right-hand slope, and the equivalent
large-jump finite-first-moment criterion. All are proof obligations. -/
def theorem10_3_source_type {Ω : Type*} [MeasurableSpace Ω]
    (Y : CSBPRaw Ω) (T : Mechanism.Parameters) : Prop :=
  HasBranching Y →
  HasPathMarkov Y →
  HasCadlagPaths Y →
  HasIdentifiedMechanism Y T →
    (ConservativePopulation Y ↔ GreyNearZeroDivergence T) ∧
    (ConservativePopulation Y → T.killing = 0) ∧
    ((T.killing = 0 ∧
       ∃ slope : ℝ,
         HasRightSlope (Mechanism.psi T) (slope : EReal)) →
       ConservativePopulation Y) ∧
    ((T.killing = 0 ∧ FiniteLargeJumpFirstMoment T) →
       ConservativePopulation Y) ∧
    ((∃ slope : ℝ,
        HasRightSlope (Mechanism.psi T) (slope : EReal)) ↔
       FiniteLargeJumpFirstMoment T)

end Kyprianou.Ch10

namespace Kyprianou.Ch10

/-- Forward Lamperti physical path, preserving external killing as infinite
CSBP mass and downward passage as extinction at zero. -/
noncomputable def lampertiForward {Ω : Type*} [MeasurableSpace Ω]
    (X : Levy.PositiveJumpPaths Ω) (kill : Ω → Mass)
    (ω : Ω) (t : Time) : Mass :=
  let theta := Clock.inverse (Clock.reciprocal X.path ω) (t : Mass)
  let tau := Levy.firstStrictNegative X.path ω
  if kill ω ≠ ⊤ ∧ kill ω ≤ theta then ⊤
  else if tau ≠ ⊤ ∧ tau ≤ theta then 0
  else if theta = ⊤ then ⊤
  else ENNReal.ofReal (X.path theta.toNNReal ω)

/-- Reverse Lamperti physical path; None marks the killed/cemetery state. -/
noncomputable def lampertiReverse {Ω : Type*} [MeasurableSpace Ω]
    (Y : CSBPRaw Ω) (ω : Ω) (t : Time) : Option ℝ :=
  let phi := Clock.inverse (Clock.occupation Y.process ω) (t : Mass)
  if phi = ⊤ then none
  else
    let m := Y.process phi.toNNReal ω
    if m = ⊤ then none else some m.toReal

/-- Defining independence of external exponential killing from the full
Lévy path. -/
def IndependentKilling {Ω : Type*} [MeasurableSpace Ω]
    (X : Levy.PositiveJumpPaths Ω) (kill : Ω → Mass) : Prop :=
  ∀ (x : ℝ),
    Indep
      (MeasurableSpace.comap kill inferInstance)
      (MeasurableSpace.comap
        (fun ω : Ω => fun t : Time => X.path t ω) inferInstance)
      (X.law x)

/-- The killed Lévy Laplace exponent convention of Theorem 10.2. -/
def HasKilledLaplaceExponent {Ω : Type*} [MeasurableSpace Ω]
    (X : Levy.PositiveJumpPaths Ω) (kill : Ω → Mass)
    (T : Mechanism.Parameters) : Prop :=
  ∀ (x : ℝ) (t theta : Time),
    (∫⁻ ω, (if (t : Mass) < kill ω then
      ENNReal.ofReal (Real.exp (-((theta : ℝ) *
        (X.path t ω - x)))) else (0 : Mass)) ∂ X.law x) =
      ENNReal.ofReal (Real.exp ((t : ℝ) * Mechanism.psi T theta))

/-- Missing height is coded as (0,1), present height r as (r,0). -/
def encodeKilled : Option ℝ → ℝ × ℝ
  | none => (0,1)
  | some r => (r,0)

end Kyprianou.Ch10


