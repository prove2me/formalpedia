-- Prove2me | Definitions.Def_Kyprianou_Ch05_ChapterCertificateGroupA
-- name    : Kyprianou_Ch05_ChapterCertificateGroupA
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-15T09:32:15.332971+00:00
-- url     : https://prove2.me/theorems/8654e1c8-4379-460b-9ab9-f764a7b260cc
-- title:
--   Chapter 5 exact theorem certificates, group A
-- statement:
--   Source-equivalent universally quantified propositions for 5_1, 5_2, 5_3, 5_4, 5_5. These contain no assumed proofs and are the formal cumulative mission certificates.
-- source:
--   Kyprianou (2006), first edition, Chapter 5, pp. 111-138; exact statements from independently registered item specifications.

import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Definitions.Def_Kyprianou_Ch03_IsSubordinator
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_RenewalEpochProcess
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Mathlib
import Mathlib.MeasureTheory.Group.Convolution
open MeasureTheory Filter
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch05

/-- Exact quantified source type of Kyprianou.Ch05.classicalRenewalTheorem. -/
noncomputable def certificate_5_1 : Prop :=
  ∀ (F : Measure Real) [IsProbabilityMeasure F]
    (hSupport : F (Set.Iio (0 : Real)) = 0)
    (hFiniteMean : Integrable (fun x : Real => x) F)
    (hPositiveMean : 0 < ∫ x : Real, x ∂F),
    let mu := ∫ x : Real, x ∂F;
        let V := renewalMeasure F;
        ((NonLatticeMeasure F →
          ∀ y : Real, 0 < y →
            Tendsto
              (fun x : Real => (V (Set.Ioc x (x + y))).toReal)
              atTop (nhds (y / mu))) ∧
         (NonLatticeMeasure F →
          ∀ h : Real → Real, DirectlyRiemannIntegrable h →
            Tendsto
              (fun x : Real =>
                ∫ z in Set.Icc (0 : Real) x, h (x - z) ∂V)
              atTop
              (nhds ((∫ z in Set.Ici (0 : Real), h z ∂volume) / mu))) ∧
         (Tendsto
           (fun x : Real => (V (Set.Icc (0 : Real) x)).toReal / x)
           atTop (nhds (1 / mu))))

/-- Exact quantified source type of Kyprianou.Ch05.potentialRenewalIdentity. -/
noncomputable def certificate_5_2 : Prop :=
  ∀ {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Y : NNReal → Omega → Real)
    (death : Omega → WithTop NNReal)
    (hKilled : IsKilledSubordinator P Y death 0)
    (U : Real → Measure Real)
    (hPotential : IsKilledPotentialFamily P Y death U),
    renewalMeasure (U 1) = Measure.dirac (0 : Real) + U 0

/-- Exact quantified source type of Kyprianou.Ch05.subordinatorPotentialRenewalLimits. -/
noncomputable def certificate_5_3 : Prop :=
  ∀ {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Y : NNReal → Omega → Real)
    (death : Omega → WithTop NNReal)
    (hKilled : IsKilledSubordinator P Y death 0)
    (U : Real → Measure Real)
    (hPotential : IsKilledPotentialFamily P Y death U)
    (hFiniteMean : Integrable (Y (1 : NNReal)) P)
    (hPositiveMean : 0 < ∫ omega, Y 1 omega ∂P),
    let mu : Real := ∫ omega, Y 1 omega ∂P;
      ((NonLatticeMeasure (U 0) →
        ∀ y : Real, 0 < y →
          Tendsto
            (fun x : Real =>
              ((U 0) (Set.Ioc x (x + y))).toReal)
            atTop (nhds (y / mu))) ∧
       (Tendsto
         (fun x : Real =>
           ((U 0) (Set.Icc (0 : Real) x)).toReal / x)
         atTop (nhds (1 / mu))))

/-- Exact quantified source type of Kyprianou.Ch05.killedSubordinatorPotentialLattice. -/
noncomputable def certificate_5_4 : Prop :=
  ∀ {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Y : NNReal → Omega → Real)
    (death : Omega → WithTop NNReal)
    (eta d : Real) (Pi : Measure Real) (Phi : Real → Real)
    (hKilled : IsKilledSubordinator P Y death eta)
    (hTriplet : IsKilledLaplaceTriplet eta d Pi Phi)
    (hLaplaceLaw : ∀ (t : NNReal) (theta : Real), 0 ≤ theta →
      (∫ omega, Real.exp (-theta * Y t omega) ∂P) =
        Real.exp (-(t : Real) * (Phi theta - eta)))
    (U : Real → Measure Real)
    (hPotential : IsKilledPotentialFamily P Y death U),
    ((Pi (Set.Ioi (0 : Real)) = ⊤ →
        ∀ q : Real, 0 ≤ q →
          ∀ x : Real, (U q) {x} = 0) ∧
       (Pi (Set.Ioi (0 : Real)) < ⊤ →
         NonLatticeMeasure Pi →
         ∀ q : Real, 0 ≤ q → NonLatticeMeasure (U q)) ∧
       (Pi (Set.Ioi (0 : Real)) < ⊤ →
         d = 0 →
         ∀ q : Real, 0 ≤ q →
           ∀ h : Real, 0 < h →
             (Pi {z : Real | ∀ n : Int, z ≠ (n : Real) * h} = 0 ↔
              ((U q).restrict (Set.Ioi (0 : Real)))
                {z : Real | ∀ n : Int, z ≠ (n : Real) * h} = 0)))

/-- Exact quantified source type of Kyprianou.Ch05.renewalJointOvershootUndershoot. -/
noncomputable def certificate_5_5 : Prop :=
  ∀ {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Z : Nat → Omega → Real) (F : Measure Real)
    (hRenewal : IsRenewalEpochProcess P Z F)
,
    ((∀ (x : Real), 0 < x →
          ∀ (A B : Set Real), MeasurableSet A → MeasurableSet B →
            A ⊆ Set.Ioi (0 : Real) →
            B ⊆ Set.Ioc (0 : Real) x →
              P {omega : Omega |
                0 < renewalOvershoot Z x omega ∧
                renewalOvershoot Z x omega ∈ A ∧
                renewalUndershoot Z x omega ∈ B} =
              renewalJointKernel (renewalMeasure F) F x A B) ∧
       ((Integrable (fun z : Real => z) F) →

          NonLatticeMeasure F →
            ∀ (u y : Real), 0 < u → 0 < y →
              Tendsto
                (fun x : Real =>
                  (P {omega : Omega |
                    u < renewalOvershoot Z x omega ∧
                    y < renewalUndershoot Z x omega}).toReal)
                atTop
                (nhds
                  ((∫ z in Set.Ioi (u+y),
                     (F (Set.Ioi z)).toReal ∂volume) /
                    (∫ z : Real, z ∂F)))))

end Kyprianou.Ch05


