-- Prove2me | Definitions.Def_Kyprianou_Ch10_Core03
-- name    : Kyprianou_Ch10_Core03
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T15:37:48.909997+00:00
-- url     : https://prove2.me/theorems/58e9ad58-a4c5-446d-8f9f-47708623a1c6
-- title:
--   Kyprianou Ch10 original model source, bounded segment 3/7
-- statement:
--   Source-faithful Chapter 10 supporting definitions, including the survival-conditioned probability law identified by its natural finite-time filtration and Radon-Nikodym density; bounded segment 3 of 7.

import Definitions.Def_Kyprianou_Ch10_Core02
open Filter Set ProbabilityTheory MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false
namespace Kyprianou.Ch10.StageDConditioning
/-- Theorem 10.10: q-down-to-zero survival conditioning and the h-density
are separate conclusions for every finite-time natural-history event. -/
def theorem10_10_source_type {Ω : Type*} [MeasurableSpace Ω]
    (X : Levy.PositiveJumpPaths Ω) (T : Mechanism.Parameters) : Prop :=
  Levy.HasLevyLaw X →
  HasKilledLaplaceExponent X (fun _ : Ω => (⊤ : Mass)) T →
  T.killing = 0 →
  (∃ slope : EReal,
     HasRightSlope (Mechanism.psi T) slope ∧ 0 ≤ slope) →
  ∀ x : Time, 0 < x →
    ∃ C : Conditioning.CandidateLaw Ω,
      C.original = X.law (x : ℝ) ∧
      (∀ t : Time, C.filtration t =
        MeasurableSpace.comap
          (fun ω : Ω => fun s : {s : Time // s ≤ t} => X.path s.1 ω)
          inferInstance) ∧
      (∀ (t : Time) (A : Set Ω),
        0 < t → @MeasurableSet Ω (C.filtration t) A →
          C.tilted A = ∫⁻ ω in A, levyDensity X x t ω ∂ X.law (x : ℝ)) ∧
      (∀ (t : Time) (A : Set Ω) (kill : Time → Ω → Mass),
        0 < t → @MeasurableSet Ω (C.filtration t) A →
        (∀ q : Time, 0 < q →
          Killing.HasExponentialKilling (X.law (x : ℝ)) (kill q) q ∧
          IndependentKilling X (kill q)) →
        Tendsto
          (fun q : Time =>
            conditional (X.law (x : ℝ)) A (levyConditionEvent X (kill q) t))
          (nhdsWithin (0 : Time) (Set.Ioi 0)) (nhds (C.tilted A)))

/-- Lemma 10.11: total conditioned mass, with critical versus
strictly subcritical parameter regimes. -/
def lemma10_11_source_type {Ω : Type*} [MeasurableSpace Ω]
    (X : Levy.PositiveJumpPaths Ω) (T : Mechanism.Parameters) : Prop :=
  Levy.HasLevyLaw X →
  HasKilledLaplaceExponent X (fun _ : Ω => (⊤ : Mass)) T →
  T.killing = 0 →
  (∃ slope : EReal,
    HasRightSlope (Mechanism.psi T) slope ∧ 0 ≤ slope) →
  ∀ x : Time, 0 < x →
    ∀ C : Conditioning.CandidateLaw Ω,
      C.original = X.law (x : ℝ) →
      (∀ (t : Time) (A : Set Ω),
        0 < t → @MeasurableSet Ω (C.filtration t) A →
          C.tilted A = ∫⁻ ω in A, levyDensity X x t ω ∂ X.law (x : ℝ)) →
      ((C.tilted Set.univ = 1 ↔
          CriticalMechanism (Mechanism.psi T)) ∧
       (SubcriticalMechanism (Mechanism.psi T) →
          C.tilted Set.univ < 1))

/-- Density of a positive-mass CSBP conditioned to survive, with the
normalisation e^(rho t) Y_t/x on the original probability space. -/
noncomputable def populationDensity {Ω : Type*} [MeasurableSpace Ω]
    (Y : CSBPRaw Ω) (rho : ℝ) (x t : Time) (ω : Ω) : Mass :=
  ENNReal.ofReal
    (Real.exp (rho * (t : ℝ)) * (Y.process t ω).toReal / (x : ℝ))

/-- Source law P_x^up: its finite-time restriction is the canonical
    size-biased survival-conditioned path measure, on the natural past. -/
def IsPopulationConditioning {Ω : Type*} [MeasurableSpace Ω]
    (Y : CSBPRaw Ω) (rho : ℝ) (x : Time)
    (C : Conditioning.CandidateLaw Ω) : Prop :=
  C.original = Y.law x ∧
  (∀ t : Time, C.filtration t = naturalPast Y t) ∧
  ∀ (t : Time) (A : Set Ω), 0 < t →
    @MeasurableSet Ω (C.filtration t) A →
    C.tilted A =
      ∫⁻ ω in A, populationDensity Y rho x t ω ∂ Y.law x

/-- First zero hitting time, including infinite-time survival. -/
noncomputable def extinction {Ω : Type*} [MeasurableSpace Ω]
    (Y : CSBPRaw Ω) (ω : Ω) : Mass :=
  sInf {t : Mass | t ≠ ⊤ ∧ 0 < t ∧ Y.process t.toNNReal ω = 0}

/-- Full Theorem 10.12: limit, actual probability, density, no extinction,
and the original-law martingale in one target. -/
def theorem10_12_source_type {Ω : Type*} [MeasurableSpace Ω]
    (Y : CSBPRaw Ω) (T : Mechanism.Parameters) (rho : ℝ) : Prop :=
  HasBranching Y → HasPathMarkov Y → HasCadlagPaths Y →
  HasIdentifiedMechanism Y T → T.killing = 0 →
  Mechanism.psi T 0 = 0 →
  HasRightSlope (Mechanism.psi T) (rho : EReal) → 0 ≤ rho →
  Tendsto (fun theta : Time => Mechanism.psi T theta) atTop atTop →
  (∃ a : Time, 0 < a ∧
    (∫⁻ theta in Set.Ici (a : ℝ),
      (if 0 < Mechanism.psi T (Real.toNNReal theta) then
        ENNReal.ofReal (1 / Mechanism.psi T (Real.toNNReal theta))
       else (⊤ : Mass)) ∂ (volume : Measure ℝ)) < ⊤) →
  ∀ x : Time, 0 < x →
    ∃ C : Conditioning.CandidateLaw Ω,
      C.original = Y.law x ∧
      (∀ t : Time, C.filtration t = naturalPast Y t) ∧
      Conditioning.HasConditionedProbability C ∧
      (∀ (t : Time) (A : Set Ω),
        @MeasurableSet Ω (C.filtration t) A →
          C.tilted A =
            ∫⁻ ω in A, populationDensity Y rho x t ω ∂ Y.law x) ∧
      (∀ (t : Time) (A : Set Ω),
        @MeasurableSet Ω (C.filtration t) A →
          Tendsto
            (fun s : Time =>
              conditional (Y.law x) A
                {ω | (t : Mass) + (s : Mass) < extinction Y ω})
            atTop (nhds (C.tilted A))) ∧
      C.tilted {ω | extinction Y ω < ⊤} = 0 ∧
      ∃ F : Filtration Time (inferInstance : MeasurableSpace Ω),
        (∀ t : Time, F t = naturalPast Y t) ∧
        OriginalLawMartingaleClause Y F rho x

/-- Immigration Levy-Khintchine integrand under the size-biased jump law. -/
noncomputable def sizeBiasedImmigration
    (T : Mechanism.Parameters) (theta : Time) : Mass :=
  (T.gaussianVariance : Mass) * (theta : Mass) +
    (∫⁻ z : Time,
      Immigration.kernel theta z * (z : Mass) ∂ T.jumps)

/-- Lemma 10.13: the conditioned CSBP is a CBI law with the
immigration mechanism psi'(theta) - psi'(0+). -/
def lemma10_13_source_type {Ω : Type*} [MeasurableSpace Ω]
    (Y : CSBPRaw Ω) (T : Mechanism.Parameters) (rho : ℝ) : Prop :=
  HasBranching Y → HasPathMarkov Y → HasCadlagPaths Y →
  HasIdentifiedMechanism Y T → T.killing = 0 →
  HasRightSlope (Mechanism.psi T) (rho : EReal) → 0 ≤ rho →
  ∀ x : Time, 0 < x →
    ∃ (C : Conditioning.CandidateLaw Ω)
      (I : Immigration.Parameters) (B : Immigration.CBIRaw Ω)
      (u : Time → Time → Time),
      IsPopulationConditioning Y rho x C ∧
      C.tilted Set.univ = 1 ∧
      B.state = Y.process ∧
      B.original x = C.tilted ∧
      (∀ θ : Time, Immigration.phi I θ = sizeBiasedImmigration T θ) ∧
      (∀ θ : Time, 0 < θ →
        Immigration.phi I θ =
          ENNReal.ofReal
            (deriv (fun r : ℝ => Mechanism.psi T (Real.toNNReal r))
              (θ : ℝ) - rho)) ∧
      Immigration.HasCBILaplace B I u

/-- Lemma 10.14(i) and (ii), retaining spectrally POSITIVE paths in the
approved correction to the printed jump direction, with both clocks. -/
def lemma10_14_source_type {ΩX ΩY : Type*}
    [MeasurableSpace ΩX] [MeasurableSpace ΩY]
    (X : Levy.PositiveJumpPaths ΩX) (Y : CSBPRaw ΩY)
    (T : Mechanism.Parameters)
    (XC : Time → Conditioning.CandidateLaw ΩX)
    (YC : Time → Conditioning.CandidateLaw ΩY) : Prop :=
  Levy.HasLevyLaw X →
  HasKilledLaplaceExponent X (fun _ : ΩX => (⊤ : Mass)) T →
  HasBranching Y → HasPathMarkov Y →
  HasCadlagPaths Y → HasIdentifiedMechanism Y T →
  CriticalMechanism (Mechanism.psi T) → T.killing = 0 →
  (∃ a : Time, 0 < a ∧
    (∫⁻ s in Set.Ici (a : ℝ),
      (if 0 < Mechanism.psi T (Real.toNNReal s) then
        ENNReal.ofReal (1 / Mechanism.psi T (Real.toNNReal s))
       else (⊤ : Mass)) ∂ (volume : Measure ℝ)) < ⊤) →
  (∀ x : Time, 0 < x →
    (XC x).original = X.law (x : ℝ) ∧
    (YC x).original = Y.law x ∧
    Conditioning.HasConditionedProbability (XC x) ∧
    Conditioning.HasConditionedProbability (YC x) ∧
    (∀ (t : Time) (A : Set ΩX), 0 < t →
      @MeasurableSet ΩX ((XC x).filtration t) A →
      (XC x).tilted A =
        ∫⁻ ω in A, levyDensity X x t ω ∂ X.law (x : ℝ)) ∧
    (∀ (t : Time) (A : Set ΩY), 0 < t →
      @MeasurableSet ΩY ((YC x).filtration t) A →
      (YC x).tilted A =
        ∫⁻ ω in A, populationDensity Y 0 x t ω ∂ Y.law x)) →
  (∀ x : Time, 0 < x →
    (XC x).tilted.map
      (fun ω : ΩX => fun t : Time =>
        ENNReal.ofReal
          (X.path (Clock.inverse (Clock.reciprocal X.path ω) (t : Mass)).toNNReal ω)) =
    (YC x).tilted.map (fun ω : ΩY => fun t : Time => Y.process t ω)) ∧
  (∀ x : Time, 0 < x →
    (YC x).tilted.map
      (fun ω : ΩY => fun t : Time =>
        encodeKilled (lampertiReverse Y ω t)) =
    (XC x).tilted.map
      (fun ω : ΩX => fun t : Time =>
        encodeKilled (Killing.atLifetime X.path
          (Levy.firstStrictNegative X.path) t ω)))

end Kyprianou.Ch10.StageDConditioning



open MeasureTheory Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch10.StageDExercises

abbrev Time := Kyprianou.Ch10.Time
abbrev Mass := Kyprianou.Ch10.Mass

/-- Exponential jump kernel, correcting the printed positive exponent. -/
noncomputable def jumpKernel (theta z : Time) : Mass :=
  ENNReal.ofReal (1 - Real.exp (-((theta : ℝ) * (z : ℝ))))

/-- Exercise 10.1: persistence at positive initial mass, followed by
eventual exponential decay with positive random amplitude. -/
def exercise10_1_source_type {Ω : Type*} [MeasurableSpace Ω]
    (Y : CSBPRaw Ω) (T : Mechanism.Parameters)
    (c rate : Time) (F : Measure Time) : Prop :=
  HasBranching Y → HasPathMarkov Y → HasCadlagPaths Y →
  HasIdentifiedMechanism Y T → 0 < c → 0 < rate →
  IsProbabilityMeasure F → F {0} = 0 →
  SubcriticalMechanism (Mechanism.psi T) →
  (∀ θ : Time,
    Mechanism.psi T θ =
      (c : ℝ) * (θ : ℝ) -
        (rate : ℝ) * (∫ z : Time,
          (1 - Real.exp (-((θ : ℝ) * (z : ℝ)))) ∂ F)) →
  ∀ x : Time, 0 < x →
    (Y.law x {ω | ∀ t : Time, 0 < Y.process t ω} = 1) ∧
    (∃ (amplitude : Ω → Mass) (threshold : Ω → Mass),
      Measurable amplitude ∧ Measurable threshold ∧
      Y.law x {ω | 0 < amplitude ω ∧ amplitude ω < ⊤ ∧ threshold ω < ⊤ ∧
        ∀ t : Time, threshold ω ≤ (t : Mass) →
          Y.process t ω =
            ENNReal.ofReal (Real.exp (-((c : ℝ) * (t : ℝ)))) *
              amplitude ω} = 1)

/-- Maximum positive displacement before the killing time. -/
noncomputable def runningSup {Ω : Type*} [MeasurableSpace Ω]
    (X : Levy.PositiveJumpPaths Ω) (x : Time)
    (kill : Ω → Mass) (ω : Ω) : Mass :=
  sSup ((fun t : Time => (Real.toNNReal (X.path t ω - (x : ℝ)) : Mass)) ''
    {t : Time | (t : Mass) < kill ω})

/-- First strict upward passage of a Levy path. -/
noncomputable def firstAbove {Ω : Type*} [MeasurableSpace Ω]
    (X : Levy.PositiveJumpPaths Ω) (z : ℝ) (ω : Ω) : Mass :=
  sInf {t : Mass | t ≠ ⊤ ∧ 0 < t ∧ z < X.path t.toNNReal ω}

/-- First strict downward passage of a Levy path. -/
noncomputable def firstBelow {Ω : Type*} [MeasurableSpace Ω]
    (X : Levy.PositiveJumpPaths Ω) (y : ℝ) (ω : Ω) : Mass :=
  sInf {t : Mass | t ≠ ⊤ ∧ 0 < t ∧ X.path t.toNNReal ω < y}

/-- The finite-time conditioned Doob density from Theorem 10.10. -/
def IsLevyConditioning {Ω : Type*} [MeasurableSpace Ω]
    (X : Levy.PositiveJumpPaths Ω) (x : Time)
    (C : Conditioning.CandidateLaw Ω) : Prop :=
  C.original = X.law (x : ℝ) ∧
  (∀ t : Time, C.filtration t = MeasurableSpace.comap
    (fun ω : Ω => fun s : {s : Time // s ≤ t} => X.path s.1 ω) inferInstance) ∧
  ∀ (t : Time) (A : Set Ω), 0 < t →
    @MeasurableSet Ω (C.filtration t) A →
    C.tilted A = ∫⁻ ω in A,
      (if (t : Mass) < Levy.firstStrictNegative X.path ω then
        ENNReal.ofReal (X.path t ω / (x : ℝ)) else 0) ∂ X.law (x : ℝ)

/-- Actual zero-scale function condition through its defining Laplace
transform, rather than an arbitrary unverified W. -/
def IsZeroScaleFunction (T : Mechanism.Parameters)
    (W : Time → ℝ) : Prop :=
  (∀ y : Time, 0 ≤ W y) ∧
  (∀ theta : Time, 0 < Mechanism.psi T theta →
    (∫⁻ y in Set.Ioi (0 : ℝ),
      ENNReal.ofReal (Real.exp (-((theta : ℝ) * y))) *
      ENNReal.ofReal (W (Real.toNNReal y)) ∂
        (volume : Measure ℝ)) =
      ENNReal.ofReal (1 / Mechanism.psi T theta))

/-- Exercise 10.2, with all three independent source parts.
The Wiener-Hopf supremum and q-resolvent retain their actual integrals. -/
def exercise10_2_source_type {Ω : Type*} [MeasurableSpace Ω]
    (X : Levy.PositiveJumpPaths Ω) (T : Mechanism.Parameters) : Prop :=
  Levy.HasLevyLaw X →
  HasKilledLaplaceExponent X (fun _ : Ω => (⊤ : Mass)) T →
  T.killing = 0 →
  (∃ slope : EReal,
    HasRightSlope (Mechanism.psi T) slope ∧ 0 ≤ slope) →
  (∀ (x q : Time), 0 < x → 0 < q →
    ∀ (C : Conditioning.CandidateLaw Ω) (kill : Ω → Mass)
      (f : Time → Time),
      IsLevyConditioning X x C →
      Killing.HasExponentialKilling (X.law (x : ℝ)) kill q →
      IndependentKilling X kill →
      Continuous f → HasCompactSupport f →
        (∫⁻ t in Set.Ici (0 : ℝ),
          ENNReal.ofReal (Real.exp (-((q : ℝ) * t))) *
          (∫⁻ ω, (f (Real.toNNReal (X.path (Real.toNNReal t) ω)) : Mass) ∂ C.tilted) ∂
            (volume : Measure ℝ)) =
        ENNReal.ofReal
          ((Progeny.rightInverse (Mechanism.psi T) q).toReal /
            ((q : ℝ) * (x : ℝ))) *
        (∫⁻ y in Set.Ioc (0 : ℝ) (x : ℝ),
          ENNReal.ofReal
            (Real.exp (-((Progeny.rightInverse (Mechanism.psi T) q).toReal * y))) *
          (∫⁻ z : Mass,
            (f (Real.toNNReal ((x : ℝ) + z.toReal - y)) : Mass) *
            ENNReal.ofReal ((x : ℝ) + z.toReal - y) ∂
            (X.law (x : ℝ)).map (runningSup X x kill)) ∂
              (volume : Measure ℝ))) ∧
  (∀ x : Time, 0 < x →
    ∀ (C : Conditioning.CandidateLaw Ω) (W : Time → ℝ),
      IsLevyConditioning X x C →
      IsZeroScaleFunction T W →
      ∀ B : Set ℝ, MeasurableSet B →
        (∫⁻ t in Set.Ici (0 : ℝ),
          C.tilted {ω | X.path (Real.toNNReal t) ω ∈ B} ∂
            (volume : Measure ℝ)) =
        (∫⁻ y in B ∩ Set.Ici (0 : ℝ),
          ENNReal.ofReal ((y / (x : ℝ)) *
            (W (Real.toNNReal y) -
              (if y < (x : ℝ) then 0 else W (Real.toNNReal (y - (x : ℝ)))))) ∂
            (volume : Measure ℝ))) ∧
  (CriticalMechanism (Mechanism.psi T) →
    ∀ (x : Time), 0 < x →
      ∀ (C : Conditioning.CandidateLaw Ω) (W : Time → ℝ),
        IsLevyConditioning X x C →
        IsZeroScaleFunction T W →
        (∀ (y z : ℝ), 0 ≤ y → y < (x : ℝ) → (x : ℝ) < z →
          C.tilted {ω | firstAbove X z ω < firstBelow X y ω} =
            ENNReal.ofReal (1 -
              (y / (x : ℝ)) *
                (W (Real.toNNReal ((x : ℝ) - y)) /
                  W (Real.toNNReal (z - y))))) ∧
        C.tilted {ω | Tendsto (fun t : Time => X.path t ω) atTop atTop} = 1)

/-- Original-law x-log-x jump moment at sizes larger than one. -/
def FiniteXLogX (T : Mechanism.Parameters) : Prop :=
  (∫⁻ z in Set.Ioi (1 : Time),
    (z : Mass) * ENNReal.ofReal (Real.log (z : ℝ)) ∂ T.jumps) < ⊤

/-- Positive-parameter quotient in the conditioned CSBP Laplace identity. -/
noncomputable def conditionedQuotient
    (T : Mechanism.Parameters) (rho : ℝ)
    (u : Time → Time → Time) (x t theta : Time) : Mass :=
  ENNReal.ofReal
    (Real.exp (-((x : ℝ) * (u t theta : ℝ)) + rho * (t : ℝ)) *
      Mechanism.psi T (u t theta) / Mechanism.psi T theta)

/-- Source-corrected theta=0 boundary is separate from positive theta. -/
def exercise10_3_source_type {Ω : Type*} [MeasurableSpace Ω]
    (Y : CSBPRaw Ω) (T : Mechanism.Parameters) (rho : ℝ) : Prop :=
  HasBranching Y → HasPathMarkov Y → HasCadlagPaths Y →
  ConservativePopulation Y → HasIdentifiedMechanism Y T →
  HasRightSlope (Mechanism.psi T) (rho : EReal) →
  0 ≤ rho → T.killing = 0 →
  Tendsto
    (fun θ : Time =>
      deriv (fun r : ℝ => Mechanism.psi T (Real.toNNReal r)) (θ : ℝ))
    atTop atTop →
  (∃ a : Time, 0 < a ∧
    (∫⁻ s in Set.Ici (a : ℝ),
      (if 0 < Mechanism.psi T (Real.toNNReal s) then
        ENNReal.ofReal (1 / Mechanism.psi T (Real.toNNReal s))
       else (⊤ : Mass)) ∂ (volume : Measure ℝ)) < ⊤) →
  (∀ (x : Time), 0 < x →
    ∀ (C : Conditioning.CandidateLaw Ω) (u : Time → Time → Time),
      Kyprianou.Ch10.StageDConditioning.IsPopulationConditioning Y rho x C →
      Conditioning.HasConditionedProbability C →
      HasCumulant Y u →
      (∀ (t θ : Time), 0 < t → 0 < θ →
        Conditioning.conditionedLaplace C Y.process t θ =
          conditionedQuotient T rho u x t θ) ∧
      (∀ t : Time, 0 < t →
        Conditioning.conditionedLaplace C Y.process t 0 = 1)) ∧
  (rho = 0 →
    ∀ x : Time, 0 < x →
      ∀ C : Conditioning.CandidateLaw Ω,
        Kyprianou.Ch10.StageDConditioning.IsPopulationConditioning Y rho x C →
          C.tilted {ω | Tendsto (fun t : Time => Y.process t ω) atTop (nhds ⊤)} = 1) ∧
  (0 < rho →
    ((∀ θ : Time, 0 < θ →
       let I : ℝ :=
         ∫ s in Set.Ioc (0 : ℝ) (θ : ℝ),
           (Mechanism.psi T (Real.toNNReal s) - rho * s) / (s ^ 2) ∂
             (volume : Measure ℝ)
       0 ≤ I ∧
       I = (T.gaussianVariance : ℝ) * (θ : ℝ) / 2 +
         ∫ z : Time, (z : ℝ) *
           (∫ lambda in Set.Ioc (0 : ℝ) ((θ : ℝ) * (z : ℝ)),
             (Real.exp (-lambda) - 1 + lambda) / (lambda ^ 2) ∂
               (volume : Measure ℝ)) ∂ T.jumps) ∧
     (FiniteXLogX T ↔
       ∃ epsilon : Time, 0 < epsilon ∧
         (∫⁻ s in Set.Ioc (0 : ℝ) (epsilon : ℝ),
           ENNReal.ofReal
             (1 / (rho * s) -
               1 / Mechanism.psi T (Real.toNNReal s)) ∂
                 (volume : Measure ℝ)) < ⊤))) ∧
  (0 < rho →
    ∀ x : Time, 0 < x →
      ∀ C : Conditioning.CandidateLaw Ω,
        Kyprianou.Ch10.StageDConditioning.IsPopulationConditioning Y rho x C →
        ((¬ FiniteXLogX T →
           ∀ b : Time, Tendsto
             (fun t : Time => C.tilted {ω | Y.process t ω ≤ (b : Mass)})
             atTop (nhds 0)) ∧
         (FiniteXLogX T →
           ∃ ν : Measure Mass,
             IsProbabilityMeasure ν ∧ ν {⊤} = 0 ∧
             (∀ θ : Time, 0 < θ →
               Tendsto
                 (fun t : Time =>
                   Conditioning.conditionedLaplace C Y.process t θ)
                 atTop (nhds (∫⁻ m : Mass, expNegMass θ m ∂ ν)) ∧
               (∫⁻ m : Mass, expNegMass θ m ∂ ν) =
                 ENNReal.ofReal
                   (((rho * (θ : ℝ)) / Mechanism.psi T θ) *
                     Real.exp (-rho *
                       ∫ s in Set.Ioc (0 : ℝ) (θ : ℝ),
                         (1 / (rho * s) -
                           1 / Mechanism.psi T (Real.toNNReal s)) ∂
                           (volume : Measure ℝ)))) ∧
             (∀ f : Mass → ℝ,
               Continuous f →
               (∃ K : ℝ, ∀ m : Mass, |f m| ≤ K) →
               Tendsto
                 (fun t : Time =>
                   ∫ ω, f (Y.process t ω) ∂ C.tilted)
                 atTop
                 (nhds (∫ m : Mass, f m ∂ ν))))))

end Kyprianou.Ch10.StageDExercises



open Filter Set MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch10.StageDPathwise

abbrev Time := Kyprianou.Ch10.Time
abbrev Mass := Kyprianou.Ch10.Mass

/-- A cemetery code distinguishes death, extinction, and every live height. -/
theorem cemeteryCode_injective : Function.Injective encodeKilled := by
  intro a b h
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some v =>
      have h2 := congrArg Prod.snd h
      simp [encodeKilled] at h2
  | some u =>
    cases b with
    | none =>
      have h2 := congrArg Prod.snd h
      simp [encodeKilled] at h2
    | some v =>
      have h2 : u = v := by
        have h3 := congrArg Prod.fst h
        simpa [encodeKilled] using h3
      cases h2
      rfl

/-- Cemetery coding injects full physical paths, not merely marginals. -/
theorem cemeteryFullPath_injective :
    Function.Injective
      (fun p : Time → Option ℝ => fun t : Time => encodeKilled (p t)) := by
  intro p q h
  funext t
  apply cemeteryCode_injective
  exact congrFun h t

/-- The right generalised inverse cannot cross an infinite clock level. -/
theorem inverseClock_infinity
    (A : Time → Mass) : Clock.inverse A ⊤ = ⊤ := by
  simp [Clock.inverse]

/-- A genuinely infinite lifetime leaves every finite-time value alive. -/
theorem lifetimeInfinity_alive {Ω α : Type*}
    (Y : Time → Ω → α) (life : Ω → Mass)
    (ω : Ω) (t : Time) (h : life ω = ⊤) :
    Killing.atLifetime Y life t ω = some (Y t ω) := by
  simp [Killing.atLifetime, h]

/-- The forward Lamperti construction identifies the actual coupled path.
The full-path almost-sure equality remains a conclusion, not a provider. -/
def theorem10_2_forward_pathwise {Ω : Type*} [MeasurableSpace Ω]
    (X : Levy.PositiveJumpPaths Ω) (kill : Ω → Mass)
    (T : Mechanism.Parameters) : Prop :=
  Levy.HasLevyLaw X →
  IndependentKilling X kill →
  HasKilledLaplaceExponent X kill T →
  (∀ x : Time, 0 < x →
    Killing.HasExponentialKilling (X.law (x : ℝ)) kill T.killing) →
  ∃ Y : CSBPRaw Ω,
    HasBranching Y ∧ HasPathMarkov Y ∧ HasCadlagPaths Y ∧
    HasIdentifiedMechanism Y T ∧
    (∀ x : Time, 0 < x → Y.law x = X.law (x : ℝ)) ∧
    (∀ x : Time, 0 < x →
      (∀ᵐ ω ∂ X.law (x : ℝ),
        ∀ t : Time, Y.process t ω = lampertiForward X kill ω t))

end Kyprianou.Ch10.StageDPathwise


