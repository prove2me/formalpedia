-- Prove2me | Definitions.Def_Kyprianou_Ch10_Core02
-- name    : Kyprianou_Ch10_Core02
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T15:37:21.209413+00:00
-- url     : https://prove2.me/theorems/8f657bd2-88b4-43bf-b63a-6f44bd592be4
-- title:
--   Kyprianou Ch10 original model source, bounded segment 2/7
-- statement:
--   Dependency-closed original Chapter 10 Lean source, ordered segment 2 of 7; immutable source lines 480 to 952. Historical original declaration names and proof bodies preserved; no theorem is being asserted Proved.

import Definitions.Def_Kyprianou_Ch10_Core01
open Filter Set ProbabilityTheory MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false
namespace Kyprianou.Ch10
/-- Both path-law Lamperti directions in the complete source Theorem 10.2.
The two existential constructions and their full path-law equalities remain
proof obligations; no converse is discarded. -/
def theorem10_2_source_type {Ω : Type*} [MeasurableSpace Ω]
    (X : Levy.PositiveJumpPaths Ω)
    (kill : Ω → Mass) (T : Mechanism.Parameters) : Prop :=
  Levy.HasLevyLaw X →
  IndependentKilling X kill →
  (∀ (x : Time), 0 < x →
    Killing.HasExponentialKilling (X.law (x : ℝ)) kill T.killing) →
  HasKilledLaplaceExponent X kill T →
    (∃ (ΩY : Type) (mY : MeasurableSpace ΩY),
      letI : MeasurableSpace ΩY := mY
      ∃ Y : CSBPRaw ΩY,
        HasBranching Y ∧ HasPathMarkov Y ∧ HasCadlagPaths Y ∧
        HasIdentifiedMechanism Y T ∧
        Measurable (fun ω : Ω => fun t : Time =>
          lampertiForward X kill ω t) ∧
        Measurable (fun ω : ΩY => fun t : Time =>
          Y.process t ω) ∧
        (∀ x : Time, 0 < x →
          (X.law (x : ℝ)).map
            (fun ω : Ω => fun t : Time => lampertiForward X kill ω t) =
          (Y.law x).map
            (fun ω : ΩY => fun t : Time => Y.process t ω))) ∧
    (∀ (ΩY : Type) (mY : MeasurableSpace ΩY),
      letI : MeasurableSpace ΩY := mY
      ∀ (Y : CSBPRaw ΩY),
        HasBranching Y → HasPathMarkov Y → HasCadlagPaths Y →
        HasIdentifiedMechanism Y T →
        ∃ (ΩX : Type) (mX : MeasurableSpace ΩX),
          letI : MeasurableSpace ΩX := mX
          ∃ X2 : Levy.PositiveJumpPaths ΩX,
            Levy.HasLevyLaw X2 ∧
            ∃ kill2 : ΩX → Mass,
              IndependentKilling X2 kill2 ∧
              HasKilledLaplaceExponent X2 kill2 T ∧
              Measurable (fun ω : ΩY => fun t : Time =>
                encodeKilled (lampertiReverse Y ω t)) ∧
              Measurable (fun ω : ΩX => fun t : Time =>
                encodeKilled (Killing.atLifetime X2.path
                  (Killing.firstLifetime
                    (Levy.firstStrictNegative X2.path) kill2) t ω)) ∧
              (∀ x : Time, 0 < x →
                Killing.HasExponentialKilling
                  (X2.law (x : ℝ)) kill2 T.killing) ∧
              (∀ x : Time, 0 < x →
                (Y.law x).map
                  (fun ω : ΩY => fun t : Time => encodeKilled (lampertiReverse Y ω t)) =
                (X2.law (x : ℝ)).map
                  (fun ω : ΩX => fun t : Time =>
                    encodeKilled (Killing.atLifetime X2.path
                      (Killing.firstLifetime
                        (Levy.firstStrictNegative X2.path) kill2) t ω))))

end Kyprianou.Ch10

open MeasureTheory Set
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch10.Conditioning

abbrev Time := ℝ≥0

/-- A candidate change of path law. A candidate is allowed to be defective.
Neither probability of the tilted law nor a Radon-Nikodym theorem is assumed. -/
structure CandidateLaw (Ω : Type*) [MeasurableSpace Ω] where
  original : Measure Ω
  tilted : Measure Ω
  original_probability : IsProbabilityMeasure original
  filtration : Time → MeasurableSpace Ω
  filtration_increases : Monotone filtration

/-- Source finite-time Radon-Nikodym assertion, stated independently of
the data structure so it remains a proof obligation. -/
def HasFiniteTimeDensity {Ω : Type*} [MeasurableSpace Ω]
    (C : CandidateLaw Ω) (D : Time → Ω → ℝ≥0∞) : Prop :=
  ∀ (t : Time) (A : Set Ω),
    @MeasurableSet Ω (C.filtration t) A →
    C.tilted A =
      ∫⁻ ω in A, D t ω ∂ C.original

/-- Candidate has total mass one; this must be proved for Theorem 10.12. -/
def HasConditionedProbability {Ω : Type*} [MeasurableSpace Ω]
    (C : CandidateLaw Ω) : Prop :=
  C.tilted Set.univ = 1

/-- Conditioned-law Laplace functional retains the same zero-parameter
convention for killed/exploded mass as the original law. -/
noncomputable def conditionedLaplace {Ω : Type*} [MeasurableSpace Ω]
    (C : CandidateLaw Ω) (state : Time → Ω → ℝ≥0∞)
    (t theta : Time) : ℝ≥0∞ :=
  ∫⁻ ω, Kyprianou.Ch10.expNegMass theta (state t ω) ∂ C.tilted

end Kyprianou.Ch10.Conditioning

open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch10.Immigration

/-- Drift and Lévy measure of the immigration subordinator. -/
structure Parameters where
  drift : ℝ≥0
  jumps : Measure ℝ≥0
  no_zero_atom : jumps {0} = 0
  first_order_integrable :
    (∫⁻ z : ℝ≥0, min (1 : ℝ≥0∞) (z : ℝ≥0∞) ∂ jumps) < ⊤

/-- Nonnegative immigration jump contribution at Laplace parameter theta. -/
noncomputable def kernel (theta z : ℝ≥0) : ℝ≥0∞ :=
  ENNReal.ofReal (1 - Real.exp (-((theta : ℝ) * (z : ℝ))))

/-- Complete subordinator immigration mechanism
phi(theta)=d theta+integral(1-exp(-theta*z)) nu(dz). -/
noncomputable def phi (B : Parameters) (theta : ℝ≥0) : ℝ≥0∞ :=
  (B.drift : ℝ≥0∞) * (theta : ℝ≥0∞) +
    ∫⁻ z : ℝ≥0, kernel theta z ∂ B.jumps

/-- A CBI path-law candidate with initial mass, before its immigration
Laplace-semigroup identity has been established. -/
structure CBIRaw (Ω : Type*) [MeasurableSpace Ω] where
  state : ℝ≥0 → Ω → ℝ≥0∞
  original : ℝ≥0 → Measure Ω
  original_probability : ∀ x : ℝ≥0, IsProbabilityMeasure (original x)
  coordinate_measurable : ∀ t : ℝ≥0, Measurable (state t)
  starts_at : ∀ x : ℝ≥0, original x {ω | state 0 ω = (x : ℝ≥0∞)} = 1

end Kyprianou.Ch10.Immigration

open MeasureTheory Set
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch10.Progeny

abbrev Time := ℝ≥0
abbrev Mass := ℝ≥0∞

/-- Total population-time integral up to infinity. This is extended-valued,
so the source's infinite progeny is not reset to zero by nonintegrability. -/
noncomputable def total {Ω : Type*}
    (Y : Time → Ω → Mass) (ω : Ω) : Mass :=
  ∫⁻ s in Ici (0 : ℝ), Y (Real.toNNReal s) ω ∂ (volume : Measure ℝ)

/-- Source cumulative q-scale function convention Z^(q)(x)=1+q∫_0^xW^(q). -/
noncomputable def Z (q : Time) (W : Time → Mass) (x : Time) : Mass :=
  1 + (q : Mass) *
    (∫⁻ s in Icc (0 : ℝ) (x : ℝ),
      W (Real.toNNReal s) ∂ (volume : Measure ℝ))

/-- Rightmost nonnegative root, extended to infinity when none is bounded. -/
noncomputable def rightmostRoot (psi : Time → ℝ) : Mass :=
  sSup ((fun q : Time => (q : Mass)) '' {q : Time | psi q = 0})

/-- Branching right inverse Φ. At q=0 the source uses the largest
nonnegative root, including a possibly unbounded set of roots. Positive
q uses the right-side first exceedance, with ENNReal.top for an empty set.
The bridge between the two at q↓0 needs convexity/source hypotheses. -/
noncomputable def rightInverse (psi : Time → ℝ) (q : Time) : Mass :=
  if q = 0 then rightmostRoot psi else
    sInf ((fun theta : Time => (theta : Mass)) ''
      {theta : Time | (q : ℝ) ≤ psi theta})

theorem rightInverse_zero (psi : Time → ℝ) :
    rightInverse psi 0 = rightmostRoot psi := by
  simp [rightInverse]

theorem rightInverse_positive (psi : Time → ℝ) (q : Time) (hq : q ≠ 0) :
    rightInverse psi q =
      sInf ((fun theta : Time => (theta : Mass)) ''
        {theta : Time | (q : ℝ) ≤ psi theta}) := by
  simp [rightInverse, hq]

/-- A genuine spectrally positive quadratic non-killed branching mechanism. -/
def quadraticMechanism (θ : Time) : ℝ := (θ : ℝ)^2 - (θ : ℝ)

theorem quadratic_zero_at_zero : quadraticMechanism 0 = 0 := by
  norm_num [quadraticMechanism]

theorem quadratic_zero_at_one : quadraticMechanism 1 = 0 := by
  norm_num [quadraticMechanism]

theorem quadratic_negative_at_half :
    quadraticMechanism (1/2 : Time) < 0 := by
  norm_num [quadraticMechanism]

theorem quadratic_largest_zero (θ : Time)
    (h : quadraticMechanism θ = 0) : θ ≤ 1 := by
  have ht : 0 ≤ (θ : ℝ) := θ.property
  have hmul : (θ : ℝ) * ((θ : ℝ) - 1) = 0 := by
    dsimp [quadraticMechanism] at h
    nlinarith [h]
  rcases mul_eq_zero.mp hmul with h0 | h1
  · exact_mod_cast (show (θ : ℝ) ≤ 1 by linarith)
  · exact_mod_cast (show (θ : ℝ) ≤ 1 by linarith)

theorem quadratic_rightmostRoot_eq_one :
    rightmostRoot quadraticMechanism = (1 : Mass) := by
  apply le_antisymm
  · apply sSup_le
    intro z hz
    rcases hz with ⟨θ, hθ, rfl⟩
    change (θ : Mass) ≤ (1 : Mass)
    exact ENNReal.coe_le_coe.mpr (quadratic_largest_zero θ hθ)
  · apply le_sSup
    exact ⟨(1 : Time), quadratic_zero_at_one, rfl⟩

theorem quadratic_rightInverse_zero_eq_one :
    rightInverse quadraticMechanism 0 = (1 : Mass) := by
  rw [rightInverse_zero, quadratic_rightmostRoot_eq_one]

end Kyprianou.Ch10.Progeny

open MeasureTheory Set
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch10.Immigration

/-- Accurate extended exponential: exp(-infinity)=0. -/
noncomputable def expNegExtended (v : ℝ≥0∞) : ℝ≥0∞ :=
  if v = ⊤ then 0
  else ENNReal.ofReal (Real.exp (-v.toReal))

/-- Complete defining Laplace-functional property of a CBI process, including
the source's immigration integral over true time and the initial population.
This is a meaningful model predicate and is not assumed in a CSBP theorem. -/
def HasCBILaplace {Ω : Type*} [MeasurableSpace Ω]
    (B : CBIRaw Ω) (I : Parameters)
    (u : ℝ≥0 → ℝ≥0 → ℝ≥0) : Prop :=
  ∀ (x t theta : ℝ≥0),
    (∫⁻ ω, Kyprianou.Ch10.expNegMass theta (B.state t ω) ∂ B.original x) =
      Kyprianou.Ch10.expNegMass (u t theta) (x : ℝ≥0∞) *
        expNegExtended
          (∫⁻ s in Set.Icc (0 : ℝ) (t : ℝ),
            phi I (u (t - Real.toNNReal s) theta) ∂
              (volume : Measure ℝ))

end Kyprianou.Ch10.Immigration

namespace Kyprianou.Ch10

/-- The martingale clause of Theorem 10.12 is under the ORIGINAL law P_x.
Finite paths must be proved in the theorem's conservativeness assumptions;
the toReal conversion is valid a.s. only after that obligation. -/
def OriginalLawMartingaleClause {Ω : Type*} [MeasurableSpace Ω]
    (Y : CSBPRaw Ω)
    (F : Filtration Time (inferInstance : MeasurableSpace Ω))
    (rho : ℝ) (x : Time) : Prop :=
  letI : IsProbabilityMeasure (Y.law x) := Y.probability x
  Martingale (fun (t : Time) (ω : Ω) =>
        Real.exp (rho * (t : ℝ)) * (Y.process t ω).toReal)
      F (Y.law x)

end Kyprianou.Ch10


open MeasureTheory Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch10.StageD

abbrev Time := Kyprianou.Ch10.Time
abbrev Mass := Kyprianou.Ch10.Mass

/-- First positive time at which the population is zero, infinite if absent. -/
noncomputable def extinction {Ω : Type*} [MeasurableSpace Ω]
    (Y : CSBPRaw Ω) (ω : Ω) : Mass :=
  sInf {t : Mass | t ≠ ⊤ ∧ 0 < t ∧ Y.process t.toNNReal ω = 0}

/-- Strict first upcrossing, including a never-crossed infinite lifetime. -/
noncomputable def upcross {Ω : Type*} [MeasurableSpace Ω]
    (Y : CSBPRaw Ω) (a : Time) (ω : Ω) : Mass :=
  sInf {t : Mass | t ≠ ⊤ ∧ 0 < t ∧ (a : Mass) < Y.process t.toNNReal ω}

/-- Population time until an extended stopping time, with infinity respected. -/
noncomputable def progenyUntil {Ω : Type*} [MeasurableSpace Ω]
    (Y : CSBPRaw Ω) (ω : Ω) (stop : Mass) : Mass :=
  if stop = ⊤ then Progeny.total Y.process ω
  else ∫⁻ s in Set.Iio stop.toReal, Y.process (Real.toNNReal s) ω ∂
    (volume : Measure ℝ)

/-- The probability of finite-time absorption at zero. -/
noncomputable def extinctionProbability {Ω : Type*} [MeasurableSpace Ω]
    (Y : CSBPRaw Ω) (x : Time) : Mass :=
  Y.law x {ω | extinction Y ω < ⊤}

/-- Extended nonnegative version of the Grey integral above a positive level. -/
noncomputable def inversePositiveMechanism
    (T : Mechanism.Parameters) (theta : Time) : Mass :=
  if Mechanism.psi T theta ≤ 0 then ⊤
  else ENNReal.ofReal (1 / Mechanism.psi T theta)

/-- Source's improper integral over the infinite positive tail of psi. -/
def GreyAtInfinity (T : Mechanism.Parameters) : Prop :=
  ∃ a : Time, 0 < a ∧
    (∫⁻ s in Set.Ici (a : ℝ),
      inversePositiveMechanism T (Real.toNNReal s) ∂
        (volume : Measure ℝ)) < ⊤

/-- Formally records a strictly negative limiting mechanism at infinity.
The equivalence with the book's extended psi(infinity) is an open bridge. -/
def EventuallyNegative (T : Mechanism.Parameters) : Prop :=
  ∃ lim : EReal, lim < 0 ∧
    Tendsto (fun θ : Time => (Mechanism.psi T θ : EReal)) atTop (nhds lim)

/-- Formally records an eventually increasing-to-infinity mechanism. -/
def MechanismGrows (T : Mechanism.Parameters) : Prop :=
  Tendsto (fun θ : Time => Mechanism.psi T θ) atTop atTop

/-- Theorem 10.5, both source regimes with no intrinsic killing. -/
def theorem10_5_source_type {Ω : Type*} [MeasurableSpace Ω]
    (Y : CSBPRaw Ω) (T : Mechanism.Parameters) : Prop :=
  HasBranching Y → HasPathMarkov Y → HasCadlagPaths Y →
  HasIdentifiedMechanism Y T → T.killing = 0 →
  ((EventuallyNegative T →
      ∀ x : Time, 0 < x → extinctionProbability Y x = 0) ∧
   (MechanismGrows T →
     ((∃ x : Time, 0 < x ∧ 0 < extinctionProbability Y x) ↔ GreyAtInfinity T) ∧
     (GreyAtInfinity T →
       (∀ x : Time, 0 < x → 0 < extinctionProbability Y x) ∧
       (∀ x : Time, 0 < x →
         extinctionProbability Y x =
           Immigration.expNegExtended ((Progeny.rightmostRoot (Mechanism.psi T)) * (x : Mass))))))

/-- Corollary 10.6, strictly subunit extinction iff supercriticality. -/
def corollary10_6_source_type {Ω : Type*} [MeasurableSpace Ω]
    (Y : CSBPRaw Ω) (T : Mechanism.Parameters) : Prop :=
  HasIdentifiedMechanism Y T → T.killing = 0 →
  MechanismGrows T → GreyAtInfinity T →
  ((∃ x : Time, 0 < x ∧ extinctionProbability Y x < 1) ↔
      SupercriticalMechanism (Mechanism.psi T)) ∧
  (SupercriticalMechanism (Mechanism.psi T) →
      ∀ x : Time, 0 < x → extinctionProbability Y x < 1)

/-- Scale function, determined by its positive Laplace transform. -/
def IsScaleFunction (T : Mechanism.Parameters)
    (q : Time) (W : Time → ℝ) : Prop :=
  (∀ x : Time, 0 ≤ W x) ∧
  (∀ θ : Time, (q : ℝ) < Mechanism.psi T θ →
    (∫⁻ z in Set.Ioi (0 : ℝ),
      ENNReal.ofReal (Real.exp (-((θ : ℝ) * z))) *
      ENNReal.ofReal (W (Real.toNNReal z)) ∂
      (volume : Measure ℝ)) =
      ENNReal.ofReal (1 / (Mechanism.psi T θ - (q : ℝ))))

/-- Real q-scale companion Z^(q)(x) = 1 + q integral_0^x W^(q). -/
noncomputable def scaleZ (q : Time) (W : Time → ℝ) (x : Time) : ℝ :=
  1 + (q : ℝ) * ∫ s in Set.Icc (0 : ℝ) (x : ℝ),
    W (Real.toNNReal s) ∂ (volume : Measure ℝ)

/-- Source-compatible right-continuous Laplace transform at q=0.
For infinite progeny, its positive-q limit is 0. For finite progeny
it is 1; ENNReal's total product 0*top cannot encode that limit. -/
noncomputable def extendedProgenyLaplace (q : Time) (a : Mass) : Mass :=
  if q = 0 then (if a = ⊤ then 0 else 1)
  else Immigration.expNegExtended ((q : Mass) * a)

theorem extendedProgenyLaplace_zero_top :
    extendedProgenyLaplace 0 ⊤ = 0 := by
  simp [extendedProgenyLaplace]

theorem extendedProgenyLaplace_zero_finite (a : Mass) (ha : a ≠ ⊤) :
    extendedProgenyLaplace 0 a = 1 := by
  simp [extendedProgenyLaplace, ha]

theorem extendedProgenyLaplace_positive (q : Time) (hq : q ≠ 0) (a : Mass) :
    extendedProgenyLaplace q a =
      Immigration.expNegExtended ((q : Mass) * a) := by
  simp [extendedProgenyLaplace, hq]

/-- Exactly the stopped-progeny kernel, including the q=0 boundary. -/
noncomputable def discountedUntil {Ω : Type*} [MeasurableSpace Ω]
    (Y : CSBPRaw Ω) (q : Time) (ω : Ω) (tau : Mass) : Mass :=
  extendedProgenyLaplace q (progenyUntil Y ω tau)

theorem discountedUntil_zero_infinite {Ω : Type*} [MeasurableSpace Ω]
    (Y : CSBPRaw Ω) (ω : Ω) (τ : Mass)
    (h : progenyUntil Y ω τ = ⊤) :
    discountedUntil Y 0 ω τ = 0 := by
  simp [discountedUntil, h, extendedProgenyLaplace]

theorem discountedUntil_zero_finite {Ω : Type*} [MeasurableSpace Ω]
    (Y : CSBPRaw Ω) (ω : Ω) (τ : Mass)
    (h : progenyUntil Y ω τ ≠ ⊤) :
    discountedUntil Y 0 ω τ = 1 := by
  simp [discountedUntil, h, extendedProgenyLaplace]

/-- Theorem 10.7: both stopped total-progeny transforms, with distinct
intrinsic killing and transform parameters. -/
def theorem10_7_source_type {Ω : Type*} [MeasurableSpace Ω]
    (Y : CSBPRaw Ω) (T : Mechanism.Parameters) : Prop :=
  HasIdentifiedMechanism Y T → T.killing = 0 → MechanismGrows T →
  ∀ (x a q : Time), 0 < x → x ≤ a →
    ∀ (W : Time → ℝ), IsScaleFunction T q W → 0 < W a →
      ((∫⁻ ω in {ω | upcross Y a ω < extinction Y ω},
         discountedUntil Y q ω (upcross Y a ω) ∂ Y.law x).toReal =
          scaleZ q W (a - x) -
            W (a - x) * scaleZ q W a / W a) ∧
      ((∫⁻ ω in {ω | extinction Y ω < upcross Y a ω},
         discountedUntil Y q ω (extinction Y ω) ∂ Y.law x).toReal =
          W (a - x) / W a)

/-- Whole-path supremum, retaining a possible explosion at infinity. -/
noncomputable def populationSup {Ω : Type*} [MeasurableSpace Ω]
    (Y : CSBPRaw Ω) (ω : Ω) : Mass :=
  sSup (Set.range (fun t : Time => Y.process t ω))

/-- Corollary 10.8: distribution of bounded supremum, the global finite
supremum probability and its non-supercritical classification. -/
def corollary10_8_source_type {Ω : Type*} [MeasurableSpace Ω]
    (Y : CSBPRaw Ω) (T : Mechanism.Parameters) : Prop :=
  HasIdentifiedMechanism Y T → T.killing = 0 → MechanismGrows T →
  (∀ (x a : Time), 0 < x → x ≤ a →
    ∀ W : Time → ℝ, IsScaleFunction T 0 W → 0 < W a →
      (Y.law x {ω | populationSup Y ω ≤ (a : Mass)}).toReal =
        W (a - x) / W a) ∧
  (∀ x : Time, 0 < x →
    Y.law x {ω | populationSup Y ω < ⊤} =
      Immigration.expNegExtended ((Progeny.rightmostRoot (Mechanism.psi T)) * (x : Mass))) ∧
  ((∀ x : Time, 0 < x → Y.law x {ω | populationSup Y ω < ⊤} = 1) ↔
    ¬ SupercriticalMechanism (Mechanism.psi T))

/-- Corollary 10.9: total progeny transform for every q >= 0, including 0. -/
def corollary10_9_source_type {Ω : Type*} [MeasurableSpace Ω]
    (Y : CSBPRaw Ω) (T : Mechanism.Parameters) : Prop :=
  HasIdentifiedMechanism Y T → T.killing = 0 → MechanismGrows T →
  ∀ (x q : Time), 0 < x →
    (∫⁻ ω, discountedUntil Y q ω (extinction Y ω) ∂ Y.law x) =
      Immigration.expNegExtended ((Progeny.rightInverse (Mechanism.psi T) q) * (x : Mass))

end Kyprianou.Ch10.StageD



open MeasureTheory Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch10.StageDConditioning

abbrev Time := Kyprianou.Ch10.Time
abbrev Mass := Kyprianou.Ch10.Mass

/-- Event probability conditioned on a positive-mass survival event. -/
noncomputable def conditional {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω)
    (A B : Set Ω) : Mass := μ (A ∩ B) / μ B

/-- A spectrally positive Levy path remains alive strictly before passage. -/
def levyAlive {Ω : Type*} [MeasurableSpace Ω]
    (X : Levy.PositiveJumpPaths Ω) (t : Time) : Set Ω :=
  {ω | (t : Mass) < Levy.firstStrictNegative X.path ω}

/-- Finite-time Doob h-transform density, under the UNCONDITIONED law. -/
noncomputable def levyDensity {Ω : Type*} [MeasurableSpace Ω]
    (X : Levy.PositiveJumpPaths Ω) (x t : Time) (ω : Ω) : Mass :=
  if (t : Mass) < Levy.firstStrictNegative X.path ω then
    ENNReal.ofReal (X.path t ω / (x : ℝ))
  else 0

/-- Explicit conditional event for an independent exponential time e_q. -/
def levyConditionEvent {Ω : Type*} [MeasurableSpace Ω]
    (X : Levy.PositiveJumpPaths Ω) (kill : Ω → Mass)
    (t : Time) : Set Ω :=
  {ω | (t : Mass) < kill ω ∧
    Levy.firstStrictNegative X.path ω > kill ω}

end Kyprianou.Ch10.StageDConditioning


