-- Prove2me | Definitions.Def_Kyprianou_Ch05_ChapterCertificateGroupD
-- name    : Kyprianou_Ch05_ChapterCertificateGroupD
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-15T09:41:36.512891+00:00
-- url     : https://prove2.me/theorems/49619324-c3af-467c-8336-9509744e8da5
-- title:
--   Chapter 5 exact theorem certificates, group D
-- statement:
--   Source-equivalent universally quantified propositions for exercise_5_1, exercise_5_2, exercise_5_3, exercise_5_4. These contain no assumed proofs and are the formal cumulative mission certificates.
-- source:
--   Kyprianou (2006), first edition, Chapter 5, pp. 111-138; exact statements from independently registered item specifications.

import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch03_IsSubordinator
import Definitions.Def_Kyprianou_Ch05_BivariateKilledSubordinator
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_RegularVariation
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_RiskConditionalPassage
import Definitions.Def_Kyprianou_Ch05_WeakPassageObservables
import Mathlib
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch05

/-- Exact quantified source type of Kyprianou.Ch05.exercise51ProveTheorem57. -/
noncomputable def certificate_exercise_5_1 : Prop :=
  ∀ {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Y Yleft : NNReal → Omega → Real)
    (death : Omega → WithTop NNReal)
    (d : Real) (Pi : Measure Real) (Phi : Real → Real)
    (hKilled : IsKilledSubordinator P Y death 0)
    (hTriplet : IsKilledLaplaceTriplet 0 d Pi Phi)
    (hLaplaceLaw : ∀ (t : NNReal) (theta : Real), 0 ≤ theta →
      (∫ omega, Real.exp (-theta * Y t omega) ∂P) =
        Real.exp (-(t : Real) * Phi theta))
    (hLeft : IsLeftLimitVersion P Y Yleft)
    (U : Real → Measure Real)
    (hPotential : IsKilledPotentialFamily P Y death U)
    (hFiniteMean : Integrable (Y (1 : NNReal)) P)
    (hPositiveMean : 0 < ∫ omega, Y 1 omega ∂P)
    (hNonLattice : NonLatticeMeasure (U 0)),
    let mu : Real := ∫ omega, Y 1 omega ∂P;
      ((∀ f : Real × Real → Real, IsBoundedContinuousTest f →
         Tendsto
           (fun x : Real => passageTestExpectation P Y Yleft death x f)
           atTop
           (nhds
             (d / mu * f (0,0) +
               (1 / mu) *
                 (∫ y in Set.Ici (0 : Real),
                    ∫ z in Set.Ioi y, f (z-y,y) ∂Pi ∂volume)))) ∧
       (Tendsto (fun x : Real => creepingProbability P Y death x)
         atTop (nhds (d / mu))))

/-- Exact quantified source type of Kyprianou.Ch05.exercise52SpectrallyPositiveRiskJointLaw. -/
noncomputable def certificate_exercise_5_2 : Prop :=
    ∀ {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Y X Xleft : NNReal → Omega → Real)
    (triplet : ProbabilityTheory.LevyKhintchineTriple)
    (hLevy : ProbabilityTheory.IsLevyProcess Y P)
    (hLK : ∀ (t : NNReal) (xi : Real),
      charFun (P.map (Y t)) xi =
        Complex.exp (((t : Real) : Complex) *
          Kyprianou.Ch01.levyTripleExponent triplet xi))
    (hBV : triplet.gaussianVariance = 0 ∧
       (∫⁻ z in Set.Ioo (-1 : Real) 1,
         ENNReal.ofReal |z| ∂triplet.levyMeasure) < ⊤)
    (hPositiveJumps : triplet.levyMeasure (Set.Iio 0) = 0)
    (hDownwardDrift : ∀ᵐ omega : Omega ∂P,
      Tendsto (fun t : NNReal => Y t omega) atTop atBot)
    (m : Real)
    (hM : m =
       ∫ z in Set.Ioi (0 : Real),
         (triplet.levyMeasure (Set.Ioi z)).toReal ∂volume)
    (hMPositive : 0 < m)
    (F : Measure Real)
    (hJumpLaw : F = ascendingRecordJumpDistribution
      triplet.levyMeasure m)
    (deathX : Omega → WithTop NNReal)
    (hX : IsKilledSubordinator P X deathX 0)
    (hXCompoundPoisson : ∀ (t : NNReal) (theta : Real),
        0 ≤ theta →
          (∫ omega, Real.exp (-theta*X t omega) ∂P) =
            Real.exp (-(t : Real) *
              (∫ z in Set.Ioi 0,
                (1-Real.exp (-theta*z)) ∂F)))
    (hLeftX : IsLeftLimitVersion P X Xleft),
  let hFiniteSecondMoment : Prop := IntegrableOn
       (fun z : Real => z * (triplet.levyMeasure (Set.Ioi z)).toReal)
       (Set.Ioi 0) volume;
    -- (i) Conditional equality of the entire joint passage law,
   -- with no assumed target equality between the two processes.
   -- Source-implied positive risk passage and almost-sure comparison passage.
   ((∀ x : Real, 0 < x →
      0 < (P {omega : Omega |
        PassageFinite Y (fun _ => (⊤ : WithTop NNReal)) x omega}).toReal ∧
      (P {omega : Omega | PassageFinite X deathX x omega}).toReal = 1) ∧
    -- (i) Source-exact conditional risk law equals unconditioned comparison law.
    (∀ x : Real, 0 < x →
      ∀ A B : Set Real, MeasurableSet A → MeasurableSet B →
        conditionalRunningSupremumPair P Y
          (fun _ => (⊤ : WithTop NNReal)) x A B =
        (P {omega : Omega |
          PassageFinite X deathX x omega ∧
          passageOvershoot X deathX x omega ∈ A ∧
          passageUndershoot X Xleft deathX x omega ∈ B}).toReal) ∧
    -- (ii) The full finite-mean limiting joint overshoot and undershoot.
    (hFiniteSecondMoment → ∀ u y : Real, 0 < u → 0 < y →
      Tendsto
        (fun x : Real =>
          conditionalRunningSupremumPair P Y
            (fun _ => (⊤ : WithTop NNReal)) x
            (Set.Ioi u) (Set.Ioi y))
        atTop
        (nhds
          ((∫ z in Set.Ioi (u+y),
              (F (Set.Ioi z)).toReal ∂volume) /
                (∫ z : Real, z ∂F)))) ∧
    -- (iii) Historical minimum reserve, based on the running maximum of Y,
    -- distinguished from the current pre-ruin reserve.
    (hFiniteSecondMoment → ∀ deficit wealth : Real, 0 < deficit → 0 < wealth →
      Tendsto
        (fun capital : Real =>
          (P {omega : Omega |
             PassageFinite Y (fun _ => (⊤ : WithTop NNReal)) capital omega ∧
             deficit <
               Y (passageFiniteTime Y
                   (fun _ => (⊤ : WithTop NNReal)) capital omega) omega -
                 capital ∧
             wealth <
               capital - runningSupremumBefore Y (passageFiniteTime Y
                 (fun _ => (⊤ : WithTop NNReal)) capital omega) omega}).toReal /
          (P {omega : Omega |
             PassageFinite Y
               (fun _ => (⊤ : WithTop NNReal)) capital omega}).toReal)
        atTop
        (nhds
           ((∫ z in Set.Ioi (deficit+wealth),
               (F (Set.Ioi z)).toReal ∂volume) /
               (∫ z : Real, z ∂F)))))

/-- Exact quantified source type of Kyprianou.Ch05.exercise53SizeBiasedUniformRepresentation. -/
noncomputable def certificate_exercise_5_3 : Prop :=
  ∀ {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Y Yleft : NNReal → Omega → Real)
    (death : Omega → WithTop NNReal)
    (d : Real) (Pi : Measure Real) (Phi : Real → Real)
    (hKilled : IsKilledSubordinator P Y death 0)
    (hTriplet : IsKilledLaplaceTriplet 0 d Pi Phi)
    (hLaplaceLaw : ∀ (t : NNReal) (theta : Real), 0 ≤ theta →
      (∫ omega, Real.exp (-theta * Y t omega) ∂P) =
        Real.exp (-(t : Real) * Phi theta))
    (hLeft : IsLeftLimitVersion P Y Yleft)
    (hMean : Integrable (Y (1 : NNReal)) P)
    (hPositiveMean : 0 < ∫ omega, Y 1 omega ∂P)
    (U : Real → Measure Real)
    (hPotential : IsKilledPotentialFamily P Y death U)
    (hNonLattice : NonLatticeMeasure (U 0))
    (V W Z Uunif : Omega → Real)
    (hMeasurableV : Measurable V)
    (hMeasurableW : Measurable W)
    (hMeasurableZ : Measurable Z)
    (hMeasurableU : Measurable Uunif)
    (hLimitPair : ∀ f : Real × Real → Real,
       IsBoundedContinuousTest f →
         Tendsto
           (fun x : Real => passageTestExpectation P Y Yleft death x f)
           atTop (nhds (∫ omega, f (V omega,W omega) ∂P)))
    (hLimitJump : ∀ g : Real → Real, Continuous g →
       (∃ M : Real, 0 ≤ M ∧ ∀ z : Real, |g z| ≤ M) →
         Tendsto
           (fun x : Real =>
             passageTestExpectation P Y Yleft death x
               (fun pair : Real × Real => g (pair.1+pair.2)))
           atTop (nhds (∫ omega, g (Z omega) ∂P)))
    (hUniform : Measure.map Uunif P =
       (volume : Measure Real).restrict (Set.Icc (0 : Real) 1))
    (hIndependent : ∀ (A : Set Real) (B : Set (Real × Real × Real)),
       MeasurableSet A → MeasurableSet B →
         P {omega : Omega |
           Uunif omega ∈ A ∧
           (V omega,W omega,Z omega) ∈ B} =
         P {omega : Omega | Uunif omega ∈ A} *
         P {omega : Omega | (V omega,W omega,Z omega) ∈ B}),
    Measure.map (fun omega : Omega => (V omega,W omega)) P =
        Measure.map
          (fun omega : Omega =>
            ((1-Uunif omega)*Z omega,Uunif omega*Z omega)) P

/-- Exact quantified source type of Kyprianou.Ch05.exercise54CorrelatedBivariateQuadrupleLaw. -/
noncomputable def certificate_exercise_5_4 : Prop :=
  ∀ {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X Y Xleft Yleft : NNReal → Omega → Real)
    (death : Omega → WithTop NNReal)
    (eta dX dY : Real)
    (Pi U : Measure (Real × Real))
    (hBivariate : IsKilledBivariateSubordinator P X Y death eta dX dY Pi)
    (hPotential : IsBivariateKilledPotential P X Y death U)
    (hLeftX : IsLeftLimitVersion P X Xleft)
    (hLeftY : IsLeftLimitVersion P Y Yleft),
    ∀ x : Real, 0 < x →
        ∀ T S B A : Set Real,
          MeasurableSet T → MeasurableSet S →
          MeasurableSet B → MeasurableSet A →
          T ⊆ Set.Ici (0 : Real) → S ⊆ Set.Ici (0 : Real) →
          B ⊆ Set.Icc (0 : Real) x → A ⊆ Set.Ioi (0 : Real) →
          P {omega : Omega |
            PassageFinite Y death x omega ∧
            (X (passageFiniteTime Y death x omega) omega -
              Xleft (passageFiniteTime Y death x omega) omega) ∈ T ∧
            Xleft (passageFiniteTime Y death x omega) omega ∈ S ∧
            (x - Yleft (passageFiniteTime Y death x omega) omega) ∈ B ∧
            (Y (passageFiniteTime Y death x omega) omega-x) ∈ A} =
           bivariateQuadrupleKernel U Pi x T S B A

end Kyprianou.Ch05


