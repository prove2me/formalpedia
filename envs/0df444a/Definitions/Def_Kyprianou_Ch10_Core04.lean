-- Prove2me | Definitions.Def_Kyprianou_Ch10_Core04
-- name    : Kyprianou_Ch10_Core04
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T15:38:18.633266+00:00
-- url     : https://prove2.me/theorems/30bbc0a3-8c22-43a2-9f3c-309e254f6424
-- title:
--   Kyprianou Ch10 original model source, bounded segment 4/7
-- statement:
--   Source-faithful Chapter 10 supporting definitions and Exercise 10.3 part statements with the specified survival-conditioned probability law; bounded segment 4 of 7.

import Definitions.Def_Kyprianou_Ch10_Core03
open Filter Set ProbabilityTheory MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false
namespace Kyprianou.Ch10.StageDPathwise
/-- Source-level path regularity is required only almost surely for each P_x.
Replacing it by all-ω cadlag would exclude otherwise valid laws. -/
def HasAlmostSureCadlag {Ω : Type*} [MeasurableSpace Ω]
    (Y : CSBPRaw Ω) : Prop :=
  (∀ x : Time, ∀ᵐ ω ∂ Y.law x, ∀ t : Time,
    Tendsto (fun s : Time => Y.process s ω)
      (nhdsWithin t (Set.Ici t)) (nhds (Y.process t ω))) ∧
  (∀ x : Time, ∀ᵐ ω ∂ Y.law x, ∀ t : Time, 0 < t →
    ∃ l : Mass, Tendsto (fun s : Time => Y.process s ω)
      (nhdsWithin t (Set.Iio t)) (nhds l))

/-- Reverse Lamperti exists on an enlarged measurable probability space.
The map lift copies the entire Y law under EACH positive initial mass.
Independent killing need only exist on the enlarged space. Every pathwise
identity is asserted almost surely under the coupled law, not for all ω.
The remaining measurable-copy and cemetery-clock bridges are explicit goals. -/
def theorem10_2_reverse_extended (T : Mechanism.Parameters) : Prop :=
  ∀ (Ω : Type) (m : MeasurableSpace Ω),
    letI : MeasurableSpace Ω := m
    ∀ Y : CSBPRaw Ω,
      HasBranching Y → HasPathMarkov Y → HasAlmostSureCadlag Y →
      HasIdentifiedMechanism Y T →
      ∃ (Ω' : Type) (m' : MeasurableSpace Ω'),
        letI : MeasurableSpace Ω' := m'
        ∃ (lift : Ω' → Ω) (X : Levy.PositiveJumpPaths Ω')
          (kill : Ω' → Mass),
          Measurable lift ∧
          Levy.HasLevyLaw X ∧ IndependentKilling X kill ∧
          HasKilledLaplaceExponent X kill T ∧
          (∀ x : Time, 0 < x →
            Killing.HasExponentialKilling
              (X.law (x : ℝ)) kill T.killing) ∧
          (∀ x : Time, 0 < x →
            (X.law (x : ℝ)).map lift = Y.law x) ∧
          (∀ x : Time, 0 < x →
            (∀ᵐ ω ∂ X.law (x : ℝ), ∀ t : Time,
              Killing.atLifetime X.path
                (Killing.firstLifetime
                  (Levy.firstStrictNegative X.path) kill) t ω =
                lampertiReverse Y (lift ω) t))

/-- Retains the same fixed-Ω source statement as a visibly unproved,
strictly stronger auxiliary obligation; it is not the book certificate. -/
def theorem10_2_reverse_same_space_is_stronger (T : Mechanism.Parameters) : Prop :=
  ∀ (Ω : Type) (m : MeasurableSpace Ω),
    letI : MeasurableSpace Ω := m
    ∀ Y : CSBPRaw Ω,
      HasBranching Y → HasPathMarkov Y → HasCadlagPaths Y →
      HasIdentifiedMechanism Y T →
      ∃ (X : Levy.PositiveJumpPaths Ω) (kill : Ω → Mass),
        Levy.HasLevyLaw X ∧ IndependentKilling X kill ∧
        HasKilledLaplaceExponent X kill T ∧
        (∀ x : Time, 0 < x →
          Killing.HasExponentialKilling
            (X.law (x : ℝ)) kill T.killing) ∧
        (∀ x : Time, 0 < x →
          X.law (x : ℝ) = Y.law x)

/-- Two-way Lamperti certificate: original input X is a source model,
reverse direction constructs a coupled extension of arbitrary source Y. -/
def theorem10_2_complete_extended {Ω : Type*} [MeasurableSpace Ω]
    (X : Levy.PositiveJumpPaths Ω) (kill : Ω → Mass)
    (T : Mechanism.Parameters) : Prop :=
  theorem10_2_forward_pathwise X kill T ∧
  theorem10_2_reverse_extended T

/-- Explicit original-source two-way Lamperti statement obligations. -/
def theorem10_2_complete_pathwise {Ω : Type*} [MeasurableSpace Ω]
    (X : Levy.PositiveJumpPaths Ω) (kill : Ω → Mass)
    (T : Mechanism.Parameters) : Prop :=
  theorem10_2_complete_extended X kill T

end Kyprianou.Ch10.StageDPathwise

namespace Kyprianou.Ch10.StageDExercises

def exercise10_1_part_i {Ω : Type*} [MeasurableSpace Ω]
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

    (Y.law x {ω | ∀ t : Time, 0 < Y.process t ω} = 1)

theorem exercise10_1_source_type_implies_i {Ω : Type*} [MeasurableSpace Ω]
    (Y : CSBPRaw Ω) (T : Mechanism.Parameters)
    (c rate : Time) (F : Measure Time)
    (h : exercise10_1_source_type Y T c rate F) :
    exercise10_1_part_i Y T c rate F := by
  intro h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 x hx
  exact (h h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 x hx).1

def exercise10_1_part_ii {Ω : Type*} [MeasurableSpace Ω]
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

    (∃ (amplitude : Ω → Mass) (threshold : Ω → Mass),
      Measurable amplitude ∧ Measurable threshold ∧
      Y.law x {ω | 0 < amplitude ω ∧ amplitude ω < ⊤ ∧ threshold ω < ⊤ ∧
        ∀ t : Time, threshold ω ≤ (t : Mass) →
          Y.process t ω =
            ENNReal.ofReal (Real.exp (-((c : ℝ) * (t : ℝ)))) *
              amplitude ω} = 1)

theorem exercise10_1_source_type_implies_ii {Ω : Type*} [MeasurableSpace Ω]
    (Y : CSBPRaw Ω) (T : Mechanism.Parameters)
    (c rate : Time) (F : Measure Time)
    (h : exercise10_1_source_type Y T c rate F) :
    exercise10_1_part_ii Y T c rate F := by
  intro h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 x hx
  exact (h h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 x hx).2

def exercise10_2_part_i {Ω : Type*} [MeasurableSpace Ω]
    (X : Levy.PositiveJumpPaths Ω) (T : Mechanism.Parameters) : Prop :=
  Levy.HasLevyLaw X →
  HasKilledLaplaceExponent X (fun _ : Ω => (⊤ : Mass)) T →
  T.killing = 0 →
  (∃ slope : EReal,
    HasRightSlope (Mechanism.psi T) slope ∧ 0 ≤ slope) →


    (∀ (x q : Time), 0 < x → 0 < q →    ∀ (C : Conditioning.CandidateLaw Ω) (kill : Ω → Mass)
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
              (volume : Measure ℝ)))

theorem exercise10_2_source_type_implies_i {Ω : Type*} [MeasurableSpace Ω]
    (X : Levy.PositiveJumpPaths Ω) (T : Mechanism.Parameters)
    (h : exercise10_2_source_type X T) :
    exercise10_2_part_i X T := by
  intro h0 h1 h2 h3
  exact (h h0 h1 h2 h3).1

def exercise10_2_part_ii {Ω : Type*} [MeasurableSpace Ω]
    (X : Levy.PositiveJumpPaths Ω) (T : Mechanism.Parameters) : Prop :=
  Levy.HasLevyLaw X →
  HasKilledLaplaceExponent X (fun _ : Ω => (⊤ : Mass)) T →
  T.killing = 0 →
  (∃ slope : EReal,
    HasRightSlope (Mechanism.psi T) slope ∧ 0 ≤ slope) →


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
            (volume : Measure ℝ)))

theorem exercise10_2_source_type_implies_ii {Ω : Type*} [MeasurableSpace Ω]
    (X : Levy.PositiveJumpPaths Ω) (T : Mechanism.Parameters)
    (h : exercise10_2_source_type X T) :
    exercise10_2_part_ii X T := by
  intro h0 h1 h2 h3
  exact (h h0 h1 h2 h3).2.1

def exercise10_2_part_iii {Ω : Type*} [MeasurableSpace Ω]
    (X : Levy.PositiveJumpPaths Ω) (T : Mechanism.Parameters) : Prop :=
  Levy.HasLevyLaw X →
  HasKilledLaplaceExponent X (fun _ : Ω => (⊤ : Mass)) T →
  T.killing = 0 →
  (∃ slope : EReal,
    HasRightSlope (Mechanism.psi T) slope ∧ 0 ≤ slope) →


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

theorem exercise10_2_source_type_implies_iii {Ω : Type*} [MeasurableSpace Ω]
    (X : Levy.PositiveJumpPaths Ω) (T : Mechanism.Parameters)
    (h : exercise10_2_source_type X T) :
    exercise10_2_part_iii X T := by
  intro h0 h1 h2 h3
  exact (h h0 h1 h2 h3).2.2

def exercise10_3_part_i {Ω : Type*} [MeasurableSpace Ω]
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


    (∀ (x : Time), 0 < x →    ∀ (C : Conditioning.CandidateLaw Ω) (u : Time → Time → Time),
      Kyprianou.Ch10.StageDConditioning.IsPopulationConditioning Y rho x C →
      Conditioning.HasConditionedProbability C →
      HasCumulant Y u →
      (∀ (t θ : Time), 0 < t → 0 < θ →
        Conditioning.conditionedLaplace C Y.process t θ =
          conditionedQuotient T rho u x t θ) ∧
      (∀ t : Time, 0 < t →
        Conditioning.conditionedLaplace C Y.process t 0 = 1))

theorem exercise10_3_source_type_implies_i {Ω : Type*} [MeasurableSpace Ω]
    (Y : CSBPRaw Ω) (T : Mechanism.Parameters) (rho : ℝ)
    (h : exercise10_3_source_type Y T rho) :
    exercise10_3_part_i Y T rho := by
  intro h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
  exact (h h0 h1 h2 h3 h4 h5 h6 h7 h8 h9).1

def exercise10_3_part_ii {Ω : Type*} [MeasurableSpace Ω]
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


    (rho = 0 →
    ∀ x : Time, 0 < x →
      ∀ C : Conditioning.CandidateLaw Ω,
        Kyprianou.Ch10.StageDConditioning.IsPopulationConditioning Y rho x C →
          C.tilted {ω | Tendsto (fun t : Time => Y.process t ω) atTop (nhds ⊤)} = 1)

theorem exercise10_3_source_type_implies_ii {Ω : Type*} [MeasurableSpace Ω]
    (Y : CSBPRaw Ω) (T : Mechanism.Parameters) (rho : ℝ)
    (h : exercise10_3_source_type Y T rho) :
    exercise10_3_part_ii Y T rho := by
  intro h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
  exact (h h0 h1 h2 h3 h4 h5 h6 h7 h8 h9).2.1

def exercise10_3_part_iii {Ω : Type*} [MeasurableSpace Ω]
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
                 (volume : Measure ℝ)) < ⊤)))

theorem exercise10_3_source_type_implies_iii {Ω : Type*} [MeasurableSpace Ω]
    (Y : CSBPRaw Ω) (T : Mechanism.Parameters) (rho : ℝ)
    (h : exercise10_3_source_type Y T rho) :
    exercise10_3_part_iii Y T rho := by
  intro h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
  exact (h h0 h1 h2 h3 h4 h5 h6 h7 h8 h9).2.2.1

def exercise10_3_part_iv {Ω : Type*} [MeasurableSpace Ω]
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

theorem exercise10_3_source_type_implies_iv {Ω : Type*} [MeasurableSpace Ω]
    (Y : CSBPRaw Ω) (T : Mechanism.Parameters) (rho : ℝ)
    (h : exercise10_3_source_type Y T rho) :
    exercise10_3_part_iv Y T rho := by
  intro h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
  exact (h h0 h1 h2 h3 h4 h5 h6 h7 h8 h9).2.2.2

end Kyprianou.Ch10.StageDExercises

open MeasureTheory Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch10.StageD1Certificates

abbrev Time := Kyprianou.Ch10.Time
abbrev Mass := Kyprianou.Ch10.Mass

/-- Each certificate quantifies over genuine raw stochastic process models;
no theorem is added as a field of a model or assumed as an axiom. -/
def certTheorem10_1 : Prop :=
  ∀ (Ω : Type) (m : MeasurableSpace Ω),
    letI : MeasurableSpace Ω := m
    ∀ (Y : CSBPRaw Ω),
      Kyprianou.Ch10.theorem10_1_source_type Y

def certTheorem10_2 : Prop :=
  ∀ (Ω : Type) (m : MeasurableSpace Ω),
    letI : MeasurableSpace Ω := m
    ∀ (X : Levy.PositiveJumpPaths Ω) (kill : Ω → Mass) (T : Mechanism.Parameters),
      Kyprianou.Ch10.StageDPathwise.theorem10_2_complete_extended X kill T

def certTheorem10_3 : Prop :=
  ∀ (Ω : Type) (m : MeasurableSpace Ω),
    letI : MeasurableSpace Ω := m
    ∀ (Y : CSBPRaw Ω) (T : Mechanism.Parameters),
      Kyprianou.Ch10.theorem10_3_source_type Y T

def certTheorem10_5 : Prop :=
  ∀ (Ω : Type) (m : MeasurableSpace Ω),
    letI : MeasurableSpace Ω := m
    ∀ (Y : CSBPRaw Ω) (T : Mechanism.Parameters),
      Kyprianou.Ch10.StageD.theorem10_5_source_type Y T

def certCorollary10_6 : Prop :=
  ∀ (Ω : Type) (m : MeasurableSpace Ω),
    letI : MeasurableSpace Ω := m
    ∀ (Y : CSBPRaw Ω) (T : Mechanism.Parameters),
      Kyprianou.Ch10.StageD.corollary10_6_source_type Y T

def certTheorem10_7 : Prop :=
  ∀ (Ω : Type) (m : MeasurableSpace Ω),
    letI : MeasurableSpace Ω := m
    ∀ (Y : CSBPRaw Ω) (T : Mechanism.Parameters),
      Kyprianou.Ch10.StageD.theorem10_7_source_type Y T

def certCorollary10_8 : Prop :=
  ∀ (Ω : Type) (m : MeasurableSpace Ω),
    letI : MeasurableSpace Ω := m
    ∀ (Y : CSBPRaw Ω) (T : Mechanism.Parameters),
      Kyprianou.Ch10.StageD.corollary10_8_source_type Y T

def certCorollary10_9 : Prop :=
  ∀ (Ω : Type) (m : MeasurableSpace Ω),
    letI : MeasurableSpace Ω := m
    ∀ (Y : CSBPRaw Ω) (T : Mechanism.Parameters),
      Kyprianou.Ch10.StageD.corollary10_9_source_type Y T

def certTheorem10_10 : Prop :=
  ∀ (Ω : Type) (m : MeasurableSpace Ω),
    letI : MeasurableSpace Ω := m
    ∀ (X : Levy.PositiveJumpPaths Ω) (T : Mechanism.Parameters),
      Kyprianou.Ch10.StageDConditioning.theorem10_10_source_type X T

def certLemma10_11 : Prop :=
  ∀ (Ω : Type) (m : MeasurableSpace Ω),
    letI : MeasurableSpace Ω := m
    ∀ (X : Levy.PositiveJumpPaths Ω) (T : Mechanism.Parameters),
      Kyprianou.Ch10.StageDConditioning.lemma10_11_source_type X T

def certTheorem10_12 : Prop :=
  ∀ (Ω : Type) (m : MeasurableSpace Ω),
    letI : MeasurableSpace Ω := m
    ∀ (Y : CSBPRaw Ω) (T : Mechanism.Parameters) (rho : ℝ),
      Kyprianou.Ch10.StageDConditioning.theorem10_12_source_type Y T rho

def certLemma10_13 : Prop :=
  ∀ (Ω : Type) (m : MeasurableSpace Ω),
    letI : MeasurableSpace Ω := m
    ∀ (Y : CSBPRaw Ω) (T : Mechanism.Parameters) (rho : ℝ),
      Kyprianou.Ch10.StageDConditioning.lemma10_13_source_type Y T rho

def certLemma10_14 : Prop :=
  ∀ (ΩX : Type) (mX : MeasurableSpace ΩX),
    letI : MeasurableSpace ΩX := mX
    ∀ (ΩY : Type) (mY : MeasurableSpace ΩY),
      letI : MeasurableSpace ΩY := mY
      ∀ (X : Levy.PositiveJumpPaths ΩX) (Y : CSBPRaw ΩY)
        (T : Mechanism.Parameters)
        (XC : Time → Conditioning.CandidateLaw ΩX)
        (YC : Time → Conditioning.CandidateLaw ΩY),
      Kyprianou.Ch10.StageDConditioning.lemma10_14_source_type X Y T XC YC

end Kyprianou.Ch10.StageD1Certificates


