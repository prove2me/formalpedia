-- Prove2me | Definitions.Def_Kyprianou_Ch05_ChapterCertificateGroupB
-- name    : Kyprianou_Ch05_ChapterCertificateGroupB
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-15T09:31:37.190509+00:00
-- url     : https://prove2.me/theorems/6d6e7a47-fdbe-411b-a7ac-ad5944fa28b5
-- title:
--   Chapter 5 exact theorem certificates, group B
-- statement:
--   Source-equivalent universally quantified propositions for 5_6, 5_7, 5_8, 5_9, 5_10, 5_11. These contain no assumed proofs and are the formal cumulative mission certificates.
-- source:
--   Kyprianou (2006), first edition, Chapter 5, pp. 111-138; exact statements from independently registered item specifications.

import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_RegularVariation
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_WeakPassageObservables
import Mathlib
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch05

/-- Exact quantified source type of Kyprianou.Ch05.killedJointPassageKernel. -/
noncomputable def certificate_5_6 : Prop :=
  ∀ {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Y Yleft : NNReal → Omega → Real)
    (death : Omega → WithTop NNReal)
    (eta d : Real) (Pi : Measure Real) (Phi : Real → Real)
    (hKilled : IsKilledSubordinator P Y death eta)
    (hTriplet : IsKilledLaplaceTriplet eta d Pi Phi)
    (hLaplaceLaw : ∀ (t : NNReal) (theta : Real), 0 ≤ theta →
      (∫ omega, Real.exp (-theta * Y t omega) ∂P) =
        Real.exp (-(t : Real) * (Phi theta - eta)))
    (hLeft : IsLeftLimitVersion P Y Yleft)
    (U : Real → Measure Real)
    (hPotential : IsKilledPotentialFamily P Y death U),
    ∀ (x : Real), 0 < x →
        ∀ (A B : Set Real), MeasurableSet A → MeasurableSet B →
          A ⊆ Set.Ioi (0 : Real) → B ⊆ Set.Icc (0 : Real) x →
            positiveJointPassageLaw P Y Yleft death x A B =
              jumpPotentialKernel (U 0) Pi x A B

/-- Exact quantified source type of Kyprianou.Ch05.finiteMeanPassageJointWeakLimit. -/
noncomputable def certificate_5_7 : Prop :=
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

/-- Exact quantified source type of Kyprianou.Ch05.noLandingByJumpInfiniteActivity. -/
noncomputable def certificate_5_8 : Prop :=
  ∀ {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Y Yleft : NNReal → Omega → Real)
    (death : Omega → WithTop NNReal)
    (eta d : Real) (Pi : Measure Real) (Phi : Real → Real)
    (hKilled : IsKilledSubordinator P Y death eta)
    (hTriplet : IsKilledLaplaceTriplet eta d Pi Phi)
    (hLaplaceLaw : ∀ (t : NNReal) (theta : Real), 0 ≤ theta →
      (∫ omega, Real.exp (-theta * Y t omega) ∂P) =
        Real.exp (-(t : Real) * (Phi theta - eta)))
    (hLeft : IsLeftLimitVersion P Y Yleft)
    (hInfinite : Pi (Set.Ioi (0 : Real)) = ⊤),
    ∀ x : Real, 0 < x →
        P {omega : Omega |
          PassageFinite Y death x omega ∧
          passageOvershoot Y death x omega = 0 ∧
          0 < passageUndershoot Y Yleft death x omega} = 0

/-- Exact quantified source type of Kyprianou.Ch05.creepingEquivalenceDensity. -/
noncomputable def certificate_5_9 : Prop :=
  ∀ {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Y Yleft : NNReal → Omega → Real)
    (death : Omega → WithTop NNReal)
    (eta d : Real) (Pi : Measure Real) (Phi : Real → Real)
    (hKilled : IsKilledSubordinator P Y death eta)
    (hTriplet : IsKilledLaplaceTriplet eta d Pi Phi)
    (hLaplaceLaw : ∀ (t : NNReal) (theta : Real), 0 ≤ theta →
      (∫ omega, Real.exp (-theta * Y t omega) ∂P) =
        Real.exp (-(t : Real) * (Phi theta - eta)))
    (hLeft : IsLeftLimitVersion P Y Yleft)
    (hInfinite : Pi (Set.Ioi (0 : Real)) = ⊤)
    (U : Real → Measure Real)
    (hPotential : IsKilledPotentialFamily P Y death U),
    ((d = 0 →
         ∀ x : Real, 0 < x → creepingProbability P Y death x = 0) ∧
       (0 < d →
         ∃ u : Real → Real,
           ContinuousOn u (Set.Ioi (0 : Real)) ∧
           (∀ x : Real, 0 < x → 0 < u x) ∧
           ((U 0).restrict (Set.Ioi (0 : Real)) =
             ((volume : Measure Real).restrict (Set.Ioi (0 : Real))).withDensity
               (fun x : Real => ENNReal.ofReal (u x))) ∧
           (∀ x : Real, 0 < x →
             creepingProbability P Y death x = d * u x)))

/-- Exact quantified source type of Kyprianou.Ch05.creepingProbabilityBounds. -/
noncomputable def certificate_5_10 : Prop :=
  ∀ {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Y Yleft : NNReal → Omega → Real)
    (death : Omega → WithTop NNReal)
    (eta d : Real) (Pi : Measure Real) (Phi : Real → Real)
    (hKilled : IsKilledSubordinator P Y death eta)
    (hTriplet : IsKilledLaplaceTriplet eta d Pi Phi)
    (hLaplaceLaw : ∀ (t : NNReal) (theta : Real), 0 ≤ theta →
      (∫ omega, Real.exp (-theta * Y t omega) ∂P) =
        Real.exp (-(t : Real) * (Phi theta - eta)))
    (hLeft : IsLeftLimitVersion P Y Yleft)
    (hInfinite : Pi (Set.Ioi (0 : Real)) = ⊤),
    let p := creepingProbability P Y death;
      (((∃ x : Real, 0 < x ∧ 0 < p x) →
         Tendsto
           (fun epsilon : Real =>
             sSup (p '' Set.Ioo (0 : Real) epsilon))
           (nhdsWithin (0 : Real) (Set.Ioi 0)) (nhds 1)) ∧
       (∀ x : Real, 0 < x → 3 / 4 < p x →
         ∀ y : Real, 0 < y → y ≤ x →
           1 / 2 + Real.sqrt (p x - 3 / 4) ≤ p y))

/-- Exact quantified source type of Kyprianou.Ch05.creepingProbabilityContinuous. -/
noncomputable def certificate_5_11 : Prop :=
  ∀ {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Y Yleft : NNReal → Omega → Real)
    (death : Omega → WithTop NNReal)
    (eta d : Real) (Pi : Measure Real) (Phi : Real → Real)
    (hKilled : IsKilledSubordinator P Y death eta)
    (hTriplet : IsKilledLaplaceTriplet eta d Pi Phi)
    (hLaplaceLaw : ∀ (t : NNReal) (theta : Real), 0 ≤ theta →
      (∫ omega, Real.exp (-theta * Y t omega) ∂P) =
        Real.exp (-(t : Real) * (Phi theta - eta)))
    (hLeft : IsLeftLimitVersion P Y Yleft)
    (hInfinite : Pi (Set.Ioi (0 : Real)) = ⊤),
    let p := creepingProbability P Y death;
      ((∃ x : Real, 0 < x ∧ 0 < p x) →
         (Tendsto p (nhdsWithin (0 : Real) (Set.Ioi 0)) (nhds 1)) ∧
         ContinuousOn p (Set.Ici (0 : Real)) ∧
         (∀ x : Real, 0 ≤ x → 0 < p x))

end Kyprianou.Ch05


