-- Prove2me | Definitions.Def_Kyprianou_Ch05_ChapterCertificateGroupE
-- name    : Kyprianou_Ch05_ChapterCertificateGroupE
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-15T09:31:10.720436+00:00
-- url     : https://prove2.me/theorems/80335fa7-ede9-433e-9584-4cc5e7185c2e
-- title:
--   Chapter 5 exact theorem certificates, group E
-- statement:
--   Source-equivalent universally quantified propositions for exercise_5_5, exercise_5_6, exercise_5_7, exercise_5_8, exercise_5_9. These contain no assumed proofs and are the formal cumulative mission certificates.
-- source:
--   Kyprianou (2006), first edition, Chapter 5, pp. 111-138; exact statements from independently registered item specifications.

import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch03_IsSubordinator
import Definitions.Def_Kyprianou_Ch05_ExponentialPassageMoments
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_RegularVariation
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_TailRatioClassL
import Definitions.Def_Kyprianou_Ch05_WeakPassageObservables
import Mathlib
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch05

/-- Exact quantified source type of Kyprianou.Ch05.exercise55ExponentialPassageAllParts. -/
noncomputable def certificate_exercise_5_5 : Prop :=
  ∀ {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Y Yleft : NNReal → Omega → Real)
    (death : Omega → WithTop NNReal)
    (d : Real) (Pi : Measure Real) (Phi : Real → Real)
    (U : Real → Measure Real)
    (hKilled : IsKilledSubordinator P Y death 0)
    (hTriplet : IsKilledLaplaceTriplet 0 d Pi Phi)
    (hLaplaceLaw : ∀ (t : NNReal) (theta : Real), 0 ≤ theta →
      (∫ omega, Real.exp (-theta * Y t omega) ∂P) =
        Real.exp (-(t : Real) * Phi theta))
    (hPotential : IsKilledPotentialFamily P Y death U)
    (hLeft : IsLeftLimitVersion P Y Yleft),
      -- (i) Finite-positive prefactor: a finite ordinary integral
  -- gives the strong-Markov identity. The zero-prefactor case is
  -- stated separately, avoiding the undefined 0 times infinity.
  ((∀ alpha beta x : Real, 0 ≤ alpha → 0 ≤ beta → 0 < x →
      ((0 < alpha + Phi beta →
        IntegrableOn (fun z : Real => Real.exp (-beta*z))
          (Set.Ioi x) (U alpha) ∧
        exponentialFirstPassageMoment P Y death alpha beta x =
          (alpha + Phi beta) *
            ∫ z in Set.Ioi x, Real.exp (-beta*z) ∂(U alpha)) ∧
       (alpha + Phi beta = 0 →
         (beta = 0 →
            exponentialFirstPassageMoment P Y death alpha beta x =
              (P {omega : Omega | PassageFinite Y death x omega}).toReal) ∧
         (0 < beta →
            exponentialFirstPassageMoment P Y death alpha beta x = 0)))) ∧
   -- (ii) The q>beta transform is valid with positive denominator.
   -- The identically zero subordinator has zero passage transform.
   (∀ alpha beta q : Real, 0 ≤ alpha → 0 ≤ beta → beta < q →
      ((0 < alpha + Phi q →
        (∫ x in Set.Ioi (0 : Real),
           Real.exp (-q*x) *
             exponentialOvershootMoment P Y death alpha beta x ∂volume) =
          (1 - (alpha + Phi beta) / (alpha + Phi q)) / (q-beta)) ∧
       (alpha + Phi q = 0 →
        (∫ x in Set.Ioi (0 : Real),
           Real.exp (-q*x) *
             exponentialOvershootMoment P Y death alpha beta x ∂volume) = 0))) ∧
-- (iii) Exact creeping identity, including d=0 and the
       -- continuous strictly positive density when d>0.
       ((d = 0 →
          ∀ alpha x : Real, 0 ≤ alpha → 0 < x →
            exponentialCreepingMoment P Y death alpha x = 0) ∧
        (0 < d →
          ∀ alpha : Real, 0 ≤ alpha →
            ∃ ualpha : Real → Real,
              ContinuousOn ualpha (Set.Ioi (0 : Real)) ∧
              (∀ x : Real, 0 < x → 0 < ualpha x) ∧
              ((U alpha).restrict (Set.Ioi (0 : Real)) =
                ((volume : Measure Real).restrict (Set.Ioi (0 : Real))).withDensity
                   (fun x : Real => ENNReal.ofReal (ualpha x))) ∧
              (∀ x : Real, 0 < x →
                exponentialCreepingMoment P Y death alpha x =
                  d * ualpha x) ∧
              -- (iv) For the same density version, u^(alpha)(0+)=1/d.
              Tendsto ualpha
                (nhdsWithin (0 : Real) (Set.Ioi 0)) (nhds (1 / d)))))

/-- Exact quantified source type of Kyprianou.Ch05.exercise56StableSubordinatorAllParts. -/
noncomputable def certificate_exercise_5_6 : Prop :=
  ∀ {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Y Yleft : NNReal → Omega → Real)
    (death : Omega → WithTop NNReal)
    (d : Real) (Pi : Measure Real) (Phi : Real → Real)
    (U : Real → Measure Real)
    (alpha : Real) (hAlpha : 0 < alpha ∧ alpha < 1)
    (hKilled : IsKilledSubordinator P Y death 0)
    (hTriplet : IsKilledLaplaceTriplet 0 d Pi Phi)
    (hLaplaceLaw : ∀ (t : NNReal) (theta : Real), 0 ≤ theta →
      (∫ omega, Real.exp (-theta * Y t omega) ∂P) =
        Real.exp (-(t : Real) * Phi theta))
    (hStablePhi : ∀ theta : Real, 0 ≤ theta → Phi theta = theta ^ alpha)
    (hPotential : IsKilledPotentialFamily P Y death U)
    (hLeft : IsLeftLimitVersion P Y Yleft),
    -- (i) The Lévy measure has the exact positive stable density.
      ((Pi =
          ((volume : Measure Real).restrict (Set.Ioi 0)).withDensity
            (fun z : Real =>
              ENNReal.ofReal (z ^ (-1-alpha) / (-Real.Gamma (-alpha))))) ∧
       -- (ii) The undiscounted potential density is x^(alpha-1)/Gamma(alpha).
       ((U 0) =
          ((volume : Measure Real).restrict (Set.Ioi 0)).withDensity
            (fun z : Real =>
              ENNReal.ofReal (z ^ (alpha-1) / Real.Gamma alpha))) ∧
       -- (iii) The full joint density, and its exact scale invariance.
       ((∀ x : Real, 0 < x →
          ∀ (A B : Set Real), MeasurableSet A → MeasurableSet B →
            A ⊆ Set.Ioi 0 → B ⊆ Set.Ioc 0 x →
              positiveJointPassageLaw P Y Yleft death x A B =
                ∫⁻ u in A,
                  (∫⁻ y in B,
                    ENNReal.ofReal
                      ((alpha * Real.sin (Real.pi*alpha) / Real.pi) *
                        (x-y) ^ (alpha-1) * (y+u) ^ (-1-alpha))
                      ∂volume) ∂volume) ∧
         (∀ x : Real, 0 < x →
           P {omega : Omega | PassageFinite Y death x omega} = 1) ∧
         (∀ x y : Real, 0 < x → 0 < y →
           Measure.map
             (fun omega : Omega =>
               (passageOvershoot Y death x omega / x,
                passageUndershoot Y Yleft death x omega / x)) P =
           Measure.map
             (fun omega : Omega =>
               (passageOvershoot Y death y omega / y,
                passageUndershoot Y Yleft death y omega / y)) P)) ∧
       -- (iv) Stable paths cannot creep.
       (∀ x : Real, 0 < x → creepingProbability P Y death x = 0))

/-- Exact quantified source type of Kyprianou.Ch05.exercise57TransformsAndConverseAllParts. -/
noncomputable def certificate_exercise_5_7 : Prop :=
  ∀ {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Y Yleft : NNReal → Omega → Real)
    (death : Omega → WithTop NNReal)
    (d : Real) (Pi : Measure Real) (Phi : Real → Real)
    (U : Real → Measure Real)
    (hKilled : IsKilledSubordinator P Y death 0)
    (hTriplet : IsKilledLaplaceTriplet 0 d Pi Phi)
    (hLaplaceLaw : ∀ (t : NNReal) (theta : Real), 0 ≤ theta →
      (∫ omega, Real.exp (-theta * Y t omega) ∂P) =
        Real.exp (-(t : Real) * Phi theta))
    (hPotential : IsKilledPotentialFamily P Y death U)
    (hLeft : IsLeftLimitVersion P Y Yleft),
    -- (i) Jump-only integrated joint transform, q>gamma.
      ((∀ beta gamma q : Real, 0 ≤ beta → 0 ≤ gamma → gamma < q →
        (∫ x in Set.Ioi (0 : Real),
           Real.exp (-q*x) *
             jointFirstPassageMoment P Y Yleft death beta gamma x true ∂volume) =
          ((Phi q - Phi gamma) / (Phi (q+beta)) / (q-gamma)) -
            d / Phi (q+beta)) ∧
       -- (ii) Full transform includes creeping and scales t>0.
       (∀ beta gamma q t : Real,
          0 ≤ beta → 0 ≤ gamma → gamma < q → 0 < t →
          (∫ x in Set.Ioi (0 : Real),
            Real.exp (-q*x) *
              jointFirstPassageMoment P Y Yleft death (beta/t) (gamma/t) (t*x)
              false ∂volume) =
            (Phi (q/t) - Phi (gamma/t)) /
              ((q-gamma) * Phi ((q+beta)/t))) ∧
       -- (iii) For alpha=1, levels become asymptotically continuous:
       -- pre-crossing fraction->1 and overshoot fraction->0.
       (∀ atZero : Bool,
          (if atZero then RegularlyVaryingAtZero Phi 1
           else RegularlyVaryingAtInfinity Phi 1) →
          ∀ epsilon : Real, 0 < epsilon →
            Tendsto
              (fun x : Real =>
                (P {omega : Omega |
                  PassageFinite Y death x omega ∧
                  (|Yleft (passageFiniteTime Y death x omega) omega / x - 1| >
                     epsilon ∨
                   passageOvershoot Y death x omega / x > epsilon)}).toReal)
              (if atZero then atTop else nhdsWithin (0 : Real) (Set.Ioi 0))
              (nhds 0)) ∧
       -- alpha=0: pre-crossing fraction vanishes and overshoot/x escapes,
       -- so there is no tight, nondegenerate R^2 limiting law.
       (∀ atZero : Bool,
          (if atZero then RegularlyVaryingAtZero Phi 0
           else RegularlyVaryingAtInfinity Phi 0) →
          (∀ epsilon : Real, 0 < epsilon →
            Tendsto
              (fun x : Real =>
                (P {omega : Omega |
                  PassageFinite Y death x omega ∧
                  Yleft (passageFiniteTime Y death x omega) omega / x >
                    epsilon}).toReal)
              (if atZero then atTop else nhdsWithin (0 : Real) (Set.Ioi 0))
              (nhds 0)) ∧
          (∀ M : Real, 0 < M →
            Tendsto
              (fun x : Real =>
                (P {omega : Omega |
                  PassageFinite Y death x omega ∧
                  passageOvershoot Y death x omega / x ≤ M}).toReal)
              (if atZero then atTop else nhdsWithin (0 : Real) (Set.Ioi 0))
              (nhds 0))) ∧
       -- (iv) Nondegenerate weak limits imply Phi is regularly varying
       -- at the opposite endpoint with a strictly interior index.
       (∀ atZero : Bool,
         ∀ mu : Measure (Real × Real), IsProbabilityMeasure mu →
           (∀ f : Real × Real → Real, IsBoundedContinuousTest f →
             Tendsto
               (fun x : Real =>
                 ∫ omega in {omega : Omega | PassageFinite Y death x omega},
                   f (Yleft (passageFiniteTime Y death x omega) omega / x,
                      passageOvershoot Y death x omega / x) ∂P)
               (if atZero then atTop else nhdsWithin (0 : Real) (Set.Ioi 0))
               (nhds (∫ z : Real × Real, f z ∂mu))) →
           -- General necessity, including possible degenerate weak limits.
           (∃ alpha : Real,
              0 ≤ alpha ∧ alpha ≤ 1 ∧
              (if atZero then RegularlyVaryingAtZero Phi alpha
               else RegularlyVaryingAtInfinity Phi alpha)) ∧
           -- A non-Dirac limit forces a strictly interior index.
           ((¬∃ z : Real × Real, mu = Measure.dirac z) →
             ∃ alpha : Real,
               0 < alpha ∧ alpha < 1 ∧
               (if atZero then RegularlyVaryingAtZero Phi alpha
                else RegularlyVaryingAtInfinity Phi alpha)))) ∧
      -- Sufficiency in the printed 'if and only if': an interior index gives
      -- a non-Dirac probability weak limit of the scaled passage pair.
      (∀ atZero : Bool, ∀ alpha : Real,
         0 < alpha → alpha < 1 →
         (if atZero then RegularlyVaryingAtZero Phi alpha
          else RegularlyVaryingAtInfinity Phi alpha) →
         ∃ mu : Measure (Real × Real),
           IsProbabilityMeasure mu ∧
           (¬∃ z : Real × Real, mu = Measure.dirac z) ∧
           (∀ f : Real × Real → Real, IsBoundedContinuousTest f →
             Tendsto
               (fun x : Real =>
                 ∫ omega in {omega : Omega | PassageFinite Y death x omega},
                   f (Yleft (passageFiniteTime Y death x omega) omega / x,
                      passageOvershoot Y death x omega / x) ∂P)
               (if atZero then atTop else nhdsWithin (0 : Real) (Set.Ioi 0))
               (nhds (∫ z : Real × Real, f z ∂mu))))

/-- Exact quantified source type of Kyprianou.Ch05.exercise58KilledTailRatioAllParts. -/
noncomputable def certificate_exercise_5_8 : Prop :=
  ∀ {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Y : NNReal → Omega → Real)
    (death : Omega → WithTop NNReal)
    (eta d alpha : Real) (Pi : Measure Real)
    (Phi : Real → Real) (U : Real → Measure Real)
    (hEta : 0 < eta)
    (hKilled : IsKilledSubordinator P Y death eta)
    (hTriplet : IsKilledLaplaceTriplet eta d Pi Phi)
    (hLaplaceLaw : ∀ (t : NNReal) (theta : Real), 0 ≤ theta →
      (∫ omega, Real.exp (-theta * Y t omega) ∂P) =
         Real.exp (-(t : Real) * (Phi theta-eta)))
    (hPotential : IsKilledPotentialFamily P Y death U)
    (hClassL : IsTailRatioClassL (U 0) alpha)
    (hExtMoment : IntegrableOn
      (fun z : Real => Real.exp (alpha*z)-1) (Set.Ioi 0) Pi)
    (hExtendedPhi : Phi (-alpha) = eta-d*alpha +
      ∫ z in Set.Ioi (0 : Real),
         (1-Real.exp (alpha*z)) ∂Pi),
    -- (i) Crossing probability is eta times the potential tail.
      ((∀ x : Real, 0 ≤ x →
        (P {omega : Omega | PassageFinite Y death x omega}).toReal =
           eta*(U 0 (Set.Ioi x)).toReal) ∧
       -- (ii) Finite-level conditional overshoot Laplace transform.
       (∀ beta x : Real, 0 ≤ beta → 0 ≤ x →
         conditionalOvershootTransform P Y death beta x =
           Phi beta / (eta * (U 0 (Set.Ioi x)).toReal) *
             (∫ z in Set.Ioi x, Real.exp (-beta*(z-x)) ∂(U 0))) ∧
       -- (iii) The class-L limit. beta=alpha=0 is an exact removable
       -- boundary case, whose value must be one.
       (∀ beta : Real, 0 ≤ beta →
         Tendsto
           (fun x : Real => conditionalOvershootTransform P Y death beta x)
           atTop
           (nhds (if beta = 0 then 1
              else (Phi beta / eta) * (alpha / (alpha+beta))))) ∧
       -- (iv) For alpha>0 the limit is a genuine probability measure:
       -- its atom at zero and its positive-overshoot Laplace transform
       -- are both required, with no missing creeping contribution.
       (0 < alpha →
         ∃ G : Measure Real, IsProbabilityMeasure G ∧
           G (Set.Iio (0 : Real)) = 0 ∧
           G {0} = ENNReal.ofReal (d*alpha/eta) ∧
           (∀ u : Real, 0 ≤ u →
             (G (Set.Ioi u)).toReal =
               limitingKilledOvershootTail eta alpha Phi Pi u) ∧
           (∀ beta : Real, 0 ≤ beta →
             ∫ z in Set.Ioi (0 : Real),
               Real.exp (-beta*z) ∂G =
               (alpha*Phi beta / (eta*(alpha+beta))) -
                  d*alpha/eta) ∧
           -- (v) Weak tail limit and exact creeping atom.
           (∀ u : Real, 0 ≤ u →
             Tendsto
               (fun x : Real =>
                 (P {omega : Omega |
                   PassageFinite Y death x omega ∧
                   u < passageOvershoot Y death x omega}).toReal /
                     (P {omega : Omega |
                       PassageFinite Y death x omega}).toReal)
               atTop (nhds ((G (Set.Ioi u)).toReal))) ∧
           Tendsto
             (fun x : Real =>
               (P {omega : Omega |
                 PassageFinite Y death x omega ∧
                 passageOvershoot Y death x omega = 0}).toReal /
                 (P {omega : Omega |
                     PassageFinite Y death x omega}).toReal)
             atTop (nhds (d*alpha/eta))) ∧
       -- At alpha=0, finite-level conditional laws escape to infinity.
       -- The printed generic probability limit needs a point at infinity.
       (alpha = 0 →
         (∀ u : Real, 0 ≤ u →
           Tendsto
             (fun x : Real =>
               (P {omega : Omega |
                 PassageFinite Y death x omega ∧
                 u < passageOvershoot Y death x omega}).toReal /
                 (P {omega : Omega |
                   PassageFinite Y death x omega}).toReal)
             atTop (nhds 1)) ∧
          Tendsto
            (fun x : Real =>
              (P {omega : Omega |
                PassageFinite Y death x omega ∧
                passageOvershoot Y death x omega = 0}).toReal /
                 (P {omega : Omega |
                    PassageFinite Y death x omega}).toReal)
            atTop (nhds 0)))

/-- Exact quantified source type of Kyprianou.Ch05.exercise59ZeroDriftPolarPoints. -/
noncomputable def certificate_exercise_5_9 : Prop :=
  ∀ {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → Real)
    (hLevy : ProbabilityTheory.IsLevyProcess X P)
    (triplet : ProbabilityTheory.LevyKhintchineTriple)
    (hTriplet : ∀ (t : NNReal) (xi : Real),
      charFun (P.map (X t)) xi =
        Complex.exp (((t : Real) : Complex) *
          Kyprianou.Ch01.levyTripleExponent triplet xi))
    (hBV : triplet.gaussianVariance = 0 ∧
       (∫⁻ z in Set.Ioo (-1 : Real) 1,
         ENNReal.ofReal |z| ∂triplet.levyMeasure) < ⊤)
    (hZeroDrift : triplet.drift -
       (∫ z in Set.Ioo (-1 : Real) 1, z ∂triplet.levyMeasure) = 0)
    (hNotCompoundPoisson : triplet.levyMeasure Set.univ = ⊤),
    (∀ x : Real,
        P {omega : Omega |
          ∃ t : NNReal, 0 < t ∧ X t omega = x} = 0) ∧
      ∃ Xplus Xminus : NNReal → Omega → Real,
        Kyprianou.Ch03.IsSubordinator P Xplus ∧
        Kyprianou.Ch03.IsSubordinator P Xminus ∧
        (∀ᵐ omega : Omega ∂P, ∀ t : NNReal,
           X t omega = Xplus t omega - Xminus t omega) ∧
        Indep
          (MeasurableSpace.comap
            (fun omega : Omega => fun t : NNReal => Xplus t omega) inferInstance)
          (MeasurableSpace.comap
            (fun omega : Omega => fun t : NNReal => Xminus t omega) inferInstance)
          P

end Kyprianou.Ch05


