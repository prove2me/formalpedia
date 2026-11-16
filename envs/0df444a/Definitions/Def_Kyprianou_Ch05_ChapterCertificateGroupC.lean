-- Prove2me | Definitions.Def_Kyprianou_Ch05_ChapterCertificateGroupC
-- name    : Kyprianou_Ch05_ChapterCertificateGroupC
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-15T09:30:05.431692+00:00
-- url     : https://prove2.me/theorems/4c1d6ca1-6453-41ec-bc36-ba2c764eadc8
-- title:
--   Chapter 5 exact theorem certificates, group C
-- statement:
--   Source-equivalent universally quantified propositions for 5_13, 5_14, 5_15, 5_16, 5_17. These contain no assumed proofs and are the formal cumulative mission certificates.
-- source:
--   Kyprianou (2006), first edition, Chapter 5, pp. 111-138; exact statements from independently registered item specifications.

import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_MonotoneDensity
import Definitions.Def_Kyprianou_Ch05_RegularVariation
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_WeakPassageObservables
import Mathlib
open MeasureTheory Filter
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch05

/-- Exact quantified source type of Kyprianou.Ch05.karamataTauberianInfinity. -/
noncomputable def certificate_5_13 : Prop :=
  ∀ (U : Measure Real) (L : Real → Real) (rho : Real)
    (hL : SlowlyVaryingAtInfinity L)
    (hRho : 0 ≤ rho)
    (hSupport : U (Set.Iio (0 : Real)) = 0),
    (Tendsto
           (fun theta : Real =>
             (positiveLaplace U theta).toReal /
               (theta ^ (-rho) * L (1 / theta)))
           (nhdsWithin (0 : Real) (Set.Ioi 0)) (nhds 1)) ↔
        (Tendsto
           (fun x : Real =>
             (cumulativePotential U x).toReal /
               (x ^ rho * L x / Real.Gamma (1 + rho)))
           atTop (nhds 1))

/-- Exact quantified source type of Kyprianou.Ch05.karamataMonotoneDensityInfinity. -/
noncomputable def certificate_5_14 : Prop :=
  ∀ (U : Measure Real) (u L : Real → Real) (rho : Real)
    (hL : SlowlyVaryingAtInfinity L)
    (hRho : 0 < rho)
    (hDensity : U =
      ((volume : Measure Real).restrict (Set.Ici 0)).withDensity
        (fun x : Real => ENNReal.ofReal (u x)))
    (hNonnegative : ∀ x : Real, 0 ≤ x → 0 ≤ u x)
    (hEventuallyMonotone : UltimatelyMonotone u),
    (Tendsto
           (fun theta : Real =>
             (positiveLaplace U theta).toReal /
               (theta ^ (-rho) * L (1 / theta)))
           (nhdsWithin (0 : Real) (Set.Ioi 0)) (nhds 1)) ↔
        (Tendsto
           (fun x : Real =>
             u x / (x ^ (rho - 1) * L x / Real.Gamma rho))
           atTop (nhds 1))

/-- Exact quantified source type of Kyprianou.Ch05.karamataTauberianZero. -/
noncomputable def certificate_5_15 : Prop :=
  ∀ (U : Measure Real) (L : Real → Real) (rho : Real)
    (hL : SlowlyVaryingAtZero L)
    (hRho : 0 ≤ rho)
    (hSupport : U (Set.Iio (0 : Real)) = 0),
    ((Tendsto
            (fun theta : Real =>
              (positiveLaplace U theta).toReal /
                (theta ^ (-rho) * L (1 / theta)))
            atTop (nhds 1)) ↔
         (Tendsto
            (fun x : Real =>
              (cumulativePotential U x).toReal /
                (x ^ rho * L x / Real.Gamma (1 + rho)))
            (nhdsWithin (0 : Real) (Set.Ioi 0)) (nhds 1))) ∧
        (0 < rho →
          ∀ (u : Real → Real),
            U = ((volume : Measure Real).restrict (Set.Ici 0)).withDensity
              (fun x : Real => ENNReal.ofReal (u x)) →
            (∀ x : Real, 0 ≤ x → 0 ≤ u x) →
            UltimatelyMonotoneAtZero u →
            ((Tendsto
               (fun theta : Real =>
                 (positiveLaplace U theta).toReal /
                   (theta ^ (-rho) * L (1 / theta)))
               atTop (nhds 1)) ↔
             (Tendsto
               (fun x : Real =>
                 u x / (x ^ (rho - 1) * L x / Real.Gamma rho))
               (nhdsWithin (0 : Real) (Set.Ioi 0)) (nhds 1))))

/-- Exact quantified source type of Kyprianou.Ch05.dynkinLampertiJointWeakLimit. -/
noncomputable def certificate_5_16 : Prop :=
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
    (alpha : Real) (hAlpha : 0 < alpha ∧ alpha < 1)
    (hRV : RegularlyVaryingAtZero Phi alpha ∨
            RegularlyVaryingAtInfinity Phi alpha),
    ((RegularlyVaryingAtZero Phi alpha →
         ∀ f : Real × Real → Real, IsBoundedContinuousTest f →
           Tendsto
             (fun x : Real => scaledPassageTestExpectation P Y Yleft death x f)
             atTop (nhds (dynkinLampertiTestIntegral alpha f))) ∧
       (RegularlyVaryingAtInfinity Phi alpha →
         ∀ f : Real × Real → Real, IsBoundedContinuousTest f →
           Tendsto
             (fun x : Real => scaledPassageTestExpectation P Y Yleft death x f)
             (nhdsWithin (0 : Real) (Set.Ioi 0))
             (nhds (dynkinLampertiTestIntegral alpha f))))

/-- Exact quantified source type of Kyprianou.Ch05.regularVariationPotentialAndTailLimits. -/
noncomputable def certificate_5_17 : Prop :=
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
    (alpha : Real) (hAlpha : 0 ≤ alpha ∧ alpha ≤ 1)
    (hRV : RegularlyVaryingAtZero Phi alpha ∨
            RegularlyVaryingAtInfinity Phi alpha),
    ((RegularlyVaryingAtZero Phi alpha →
         ((∀ lambda : Real, 0 < lambda →
            Tendsto
              (fun x : Real =>
                ((U 0) (Set.Icc (0 : Real) (lambda * x))).toReal *
                  Phi (1 / x))
              atTop
              (nhds (lambda ^ alpha / Real.Gamma (1+alpha)))) ∧
          (alpha < 1 →
            ∀ lambda : Real, 0 < lambda →
              Tendsto
                (fun x : Real =>
                  (Pi (Set.Ioi (lambda*x))).toReal / Phi (1 / x))
                atTop
                (nhds (lambda ^ (-alpha) / Real.Gamma (1-alpha)))))) ∧
       (RegularlyVaryingAtInfinity Phi alpha →
         ((∀ lambda : Real, 0 < lambda →
            Tendsto
              (fun x : Real =>
                ((U 0) (Set.Icc (0 : Real) (lambda * x))).toReal *
                  Phi (1 / x))
              (nhdsWithin (0 : Real) (Set.Ioi 0))
              (nhds (lambda ^ alpha / Real.Gamma (1+alpha)))) ∧
          (alpha < 1 →
            ∀ lambda : Real, 0 < lambda →
              Tendsto
                (fun x : Real =>
                  (Pi (Set.Ioi (lambda*x))).toReal / Phi (1 / x))
                (nhdsWithin (0 : Real) (Set.Ioi 0))
                (nhds (lambda ^ (-alpha) / Real.Gamma (1-alpha)))))))

end Kyprianou.Ch05


