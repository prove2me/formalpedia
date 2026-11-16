-- Prove2me | Definitions.Def_Kyprianou_Ch04_ChapterCertificationV2
-- name    : Kyprianou_Ch04_ChapterCertificationV2
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-15T10:18:17.524676+00:00
-- url     : https://prove2.me/theorems/514cee88-2e69-45c2-b40a-32ccb9f95540
-- title:
--   Corrected exact-type certification of all twelve chapter results
-- statement:
--   Each of the twelve Prop-valued certificates reproduces the complete binder telescope and conclusion of its corresponding numbered theorem. No individual certificate presumes its own theorem's conclusion. The source hashes in certificate_source_map.json are authoritative for regenerating changed certificates.
-- source:
--   Kyprianou (2006), first edition, Chapter 4, pp. 87-109.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_Kyprianou_Ch04_StochasticIntegralUCPV2
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
import Mathlib.MeasureTheory.Group.Convolution
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
open MeasureTheory Filter ProbabilityTheory LevyStochCalc.Poisson AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false
namespace Kyprianou.Ch04

noncomputable def certificate_4_1_v2 : Prop :=
  ∀ {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hBV : L.BoundedVariation)
    (hd : 0 < L.drift)
    (w : Real) (hw : 0 ≤ w),
    let supX : NNReal → Omega → Real := fun t omega =>
          sSup ((fun s : NNReal => L.X s omega) '' Set.Iic t)
        let W : NNReal → Omega → Real := fun t omega =>
          max w (supX t omega) - L.X t omega
        let totalIdle : Omega → ENNReal := fun omega =>
          ∫⁻ t in Set.Ici (0 : Real),
            (if W (Real.toNNReal t) omega = 0 then (1 : ENNReal) else 0) ∂volume
        let rho : ENNReal :=
          (∫⁻ y : Real, ENNReal.ofReal (-y) ∂L.ν) /
            ENNReal.ofReal L.drift
        (rho > 1 →
          ∃ phi : Real,
            0 < phi ∧ L.ψ phi = 0 ∧
            (∀ theta : Real, 0 ≤ theta → L.ψ theta = 0 → theta ≤ phi) ∧
            (P {omega : Omega | totalIdle omega = 0}).toReal =
              1 - Real.exp (-phi * w) ∧
            (∀ x : Real, 0 ≤ x →
              (P {omega : Omega |
                0 < totalIdle omega ∧
                totalIdle omega ≤ ENNReal.ofReal x}).toReal =
                  Real.exp (-phi * w) *
                    (1 - Real.exp (-phi * L.drift * x)))) ∧
        (rho ≤ 1 →
          (P {omega : Omega | totalIdle omega = ⊤}).toReal = 1)

noncomputable def certificate_4_2_v2 : Prop :=
  ∀ {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → Real)
    (hLevy : ProbabilityTheory.IsLevyProcess X P)
    (triplet : ProbabilityTheory.LevyKhintchineTriple)
    (hTriplet : forall (t : NNReal) (xi : Real),
      charFun (P.map (X t)) xi =
        Complex.exp (((t : Real) : Complex) *
          Kyprianou.Ch01.levyTripleExponent triplet xi))
    (hBV : triplet.gaussianVariance = 0 ∧
      (∫⁻ y in Set.Ioo (-1 : Real) 1,
        ENNReal.ofReal |y| ∂triplet.levyMeasure) < ⊤)
    (Xleft : NNReal → Omega → Real)
    (hLeft : ∀ᵐ omega : Omega ∂P, forall t : NNReal,
      0 < t →
        Tendsto (fun s : NNReal => X s omega)
          (nhdsWithin t (Set.Iio t))
          (nhds (Xleft t omega)))
    (f : Real × Real → Real)
    (hf : ContDiffOn Real 1 f
      (Set.prod (Set.Ici (0 : Real)) Set.univ)),
    ∀ᵐ omega : Omega ∂P, forall t : NNReal,
          f ((t : Real), X t omega) =
            f (0, X 0 omega) +
            (∫ s in Set.Icc (0 : Real) (t : Real),
              fderiv Real f (s, X (Real.toNNReal s) omega)
                (1, 0) ∂volume) +
            (triplet.drift -
              ∫ y in Set.Ioo (-1 : Real) 1, y ∂triplet.levyMeasure) *
              (∫ s in Set.Icc (0 : Real) (t : Real),
                fderiv Real f (s, X (Real.toNNReal s) omega)
                  (0, 1) ∂volume) +
            (∫ z in Set.prod (Set.Icc (0 : Real) (t : Real))
                (Set.univ : Set Real),
              (f (z.1, Xleft (Real.toNNReal z.1) omega + z.2) -
               f (z.1, Xleft (Real.toNNReal z.1) omega))
              ∂(pathJumpMeasure X Xleft omega))

noncomputable def certificate_4_3_v2 : Prop :=
  ∀ {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal -> Omega -> Real)
    (hLevy : ProbabilityTheory.IsLevyProcess X P)
    (triplet : ProbabilityTheory.LevyKhintchineTriple)
    (hTriplet : forall (t : NNReal) (xi : Real),
      charFun (P.map (X t)) xi =
        Complex.exp (((t : Real) : Complex) *
          Kyprianou.Ch01.levyTripleExponent triplet xi))
    (Xleft : NNReal -> Omega -> Real)
    (hLeft : ∀ᵐ omega : Omega ∂P,
      forall t : NNReal, 0 < t ->
        Tendsto (fun s : NNReal => X s omega)
          (nhdsWithin t (Set.Iio t))
          (nhds (Xleft t omega)))
    (f : Real × Real -> Real)
    (hfJointC1 : ContDiffOn Real 1 f
      (Set.prod (Set.Ici (0 : Real)) Set.univ))
    (hfSpaceC2 : forall s : NNReal,
      ContDiff Real 2 (fun x : Real => f ((s : Real), x)))
    (hfSpaceSecondContinuous :
      ContinuousOn
        (fun z : Real × Real =>
          iteratedDeriv 2 (fun x : Real => f (z.1, x)) z.2)
        (Set.prod (Set.Ici (0 : Real)) Set.univ)),
    ∃ (stochasticIntegral : NNReal -> Omega -> Real),
          IsStochasticIntegralInProbabilityV2 P X
            (fun s omega =>
              fderiv Real f ((s : Real), Xleft s omega) (0, 1))
            stochasticIntegral ∧
          (∀ᵐ omega : Omega ∂P, forall t : NNReal,
          f ((t : Real), X t omega) =
            f (0, X 0 omega) +
            (∫ s in Set.Icc (0 : Real) (t : Real),
              fderiv Real f ((s : Real), X (Real.toNNReal s) omega)
                (1, 0) ∂volume) +
            stochasticIntegral t omega +
            ((triplet.gaussianVariance : Real) / 2) *
              (∫ s in Set.Icc (0 : Real) (t : Real),
                iteratedDeriv 2
                  (fun x : Real => f ((s : Real), x))
                  (X (Real.toNNReal s) omega) ∂volume) +
            (∫ z in Set.prod (Set.Icc (0 : Real) (t : Real))
                (Set.univ : Set Real),
              (f (z.1, Xleft (Real.toNNReal z.1) omega + z.2) -
               f (z.1, Xleft (Real.toNNReal z.1) omega) -
               z.2 * fderiv Real f
                 (z.1, Xleft (Real.toNNReal z.1) omega) (0, 1))
              ∂(pathJumpMeasure X Xleft omega)))

noncomputable def certificate_4_4_v2 : Prop :=
  ∀ {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (levyMeasure : Measure Real) [SigmaFinite levyMeasure]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (N : PoissonRandomMeasure.{0,0,0} P levyMeasure)
    (hFuture : IsFutureIndependentPoissonMeasure P levyMeasure F N)
    (phi : Real -> Real -> Omega -> Real)
    (hPhi : IsAdmissiblePoissonKernel P F phi),
    forall t : NNReal,
          (∫⁻ omega,
            (∫⁻ z in Set.prod (Set.Icc (0 : Real) (t : Real)) Set.univ,
              ENNReal.ofReal (phi z.1 z.2 omega) ∂(N.N omega)) ∂P) =
          (∫⁻ omega,
            (∫⁻ s in Set.Icc (0 : Real) (t : Real),
              (∫⁻ x, ENNReal.ofReal (phi s x omega) ∂levyMeasure)
              ∂volume) ∂P)

noncomputable def certificate_4_5_v2 : Prop :=
  ∀ {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (levyMeasure : Measure Real) [SigmaFinite levyMeasure]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (N : PoissonRandomMeasure.{0,0,0} P levyMeasure)
    (hFuture : IsFutureIndependentPoissonMeasure P levyMeasure F N)
    (phi : Real -> Real -> Omega -> Real)
    (hPhi : IsAdmissiblePoissonKernel P F phi),
    forall u t : NNReal, u <= t ->
          forall A : Set Omega, MeasurableSet[F u] A ->
          (∫⁻ omega in A,
            (∫⁻ z in Set.prod (Set.Ioc (u : Real) (t : Real)) Set.univ,
              ENNReal.ofReal (phi z.1 z.2 omega) ∂(N.N omega)) ∂P) =
          (∫⁻ omega in A,
            (∫⁻ s in Set.Ioc (u : Real) (t : Real),
              (∫⁻ x, ENNReal.ofReal (phi s x omega) ∂levyMeasure)
              ∂volume) ∂P)

noncomputable def certificate_4_6_v2 : Prop :=
  ∀ {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (levyMeasure : Measure Real) [SigmaFinite levyMeasure]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (N : PoissonRandomMeasure.{0,0,0} P levyMeasure)
    (hFuture : IsFutureIndependentPoissonMeasure P levyMeasure F N)
    (phi : Real -> Real -> Omega -> Real)
    (hPhi : IsAdmissiblePoissonKernel P F phi)
    (hFinite : forall t : NNReal,
      (∫⁻ omega,
        (∫⁻ s in Set.Icc (0 : Real) (t : Real),
          (∫⁻ x, ENNReal.ofReal (phi s x omega) ∂levyMeasure)
          ∂volume) ∂P) < ⊤),
    MeasureTheory.Martingale
          (fun (t : NNReal) omega =>
            (∫ z in Set.prod (Set.Icc (0 : Real) (t : Real)) Set.univ,
              phi z.1 z.2 omega ∂(N.N omega)) -
            (∫ s in Set.Icc (0 : Real) (t : Real),
              (∫ x, phi s x omega ∂levyMeasure) ∂volume))
          F P

noncomputable def certificate_4_7_v2 : Prop :=
  ∀ {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hBV : L.BoundedVariation)
    (hd : 0 < L.drift),
    ∀ alpha : Real, 0 ≤ alpha →
          let supX : NNReal → Omega → Real := fun t omega =>
            sSup ((fun s : NNReal => L.X s omega) '' Set.Iic t)
          MeasureTheory.Martingale
            (fun (t : NNReal) omega =>
              L.ψ alpha *
                (∫ s in Set.Icc (0 : Real) (t : Real),
                  Real.exp (-alpha * (supX (Real.toNNReal s) omega - L.X (Real.toNNReal s) omega))
                    ∂volume) +
              1 - Real.exp (-alpha * (supX t omega - L.X t omega)) -
                alpha * supX t omega) F P

noncomputable def certificate_4_8_v2 : Prop :=
  ∀ {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hNotNegativeSubordinator :
      ¬ (∀ᵐ omega : Omega ∂P,
        Antitone (fun t : NNReal => L.X t omega)))
    (q : Real) (hq : 0 < q)
    (expTime : Omega → NNReal)
    (heMeasurable : Measurable expTime)
    (heLaw : ∀ t : NNReal,
      (P {omega : Omega | t < expTime omega}).toReal =
        Real.exp (-q * (t : Real)))
    (heIndep :
      Indep
        (MeasurableSpace.comap expTime inferInstance)
        (MeasurableSpace.comap
          (fun omega : Omega => fun t : NNReal => L.X t omega)
          inferInstance) P),
    ∃ phi : Real,
          0 < phi ∧ L.ψ phi = q ∧
          (∀ theta : Real, 0 ≤ theta → L.ψ theta = q → theta ≤ phi) ∧
          (∀ beta : Real, 0 ≤ beta →
            (if beta = phi then
              (∫ omega, Real.exp (-beta *
                (sSup ((fun s : NNReal => L.X s omega) ''
                    Set.Iic (expTime omega)) - L.X (expTime omega) omega)) ∂P) =
                q / (phi * deriv L.ψ phi)
             else
              (∫ omega, Real.exp (-beta *
                (sSup ((fun s : NNReal => L.X s omega) ''
                    Set.Iic (expTime omega)) - L.X (expTime omega) omega)) ∂P) =
                (q / phi) * ((beta - phi) / (L.ψ beta - q))))

noncomputable def certificate_4_9_v2 : Prop :=
  ∀ {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hNotNegativeSubordinator :
      ¬ (∀ᵐ omega : Omega ∂P,
        Antitone (fun t : NNReal => L.X t omega))),
    let nonnegativeSlope : Real :=
          max 0 (sInf ((fun theta : Real => L.ψ theta / theta) '' Set.Ioi 0))
        let meanNonpositive : Prop :=
          forall epsilon : Real, 0 < epsilon ->
            exists theta : Real, 0 < theta ∧ L.ψ theta < epsilon * theta
        (∀ beta : Real, 0 < beta →
          Tendsto
            (fun t : NNReal =>
              ∫ omega, Real.exp (-beta *
                (sSup ((fun s : NNReal => L.X s omega) '' Set.Iic t) - L.X t omega)) ∂P)
            atTop (nhds (nonnegativeSlope * beta / L.ψ beta))) ∧
        (meanNonpositive ↔
          (P {omega : Omega |
            ¬ BddBelow (Set.range
              (fun t : NNReal => L.X t omega))}).toReal = 1) ∧
        (¬ meanNonpositive →
          (P {omega : Omega |
            BddBelow (Set.range
              (fun t : NNReal => L.X t omega))}).toReal = 1)

noncomputable def certificate_4_10_v2 : Prop :=
  ∀ {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hBV : L.BoundedVariation)
    (hd : 0 < L.drift),
    let rho : ENNReal :=
          (∫⁻ y : Real, ENNReal.ofReal (-y) ∂L.ν) /
            ENNReal.ofReal L.drift
        let eta : Measure Real :=
          ((volume : Measure Real).restrict (Set.Ioi 0)).withDensity
            (fun x : Real =>
              L.ν (Set.Iio (-x)) /
                (ENNReal.ofReal L.drift * rho))
        let convPow : Nat → Measure Real :=
          Nat.rec (Measure.dirac (0 : Real))
            (fun _ mu => mu.conv eta)
        (0 < rho → rho < 1 →
          ∃ mu : Measure Real,
            IsProbabilityMeasure mu ∧
            IsProbabilityMeasure eta ∧
            mu {0} = 1 - rho ∧
            (∀ B : Set Real, MeasurableSet B →
              mu B =
                ∑' n : Nat,
                  ((1 - rho) * rho ^ n) * (convPow n B)) ∧
            (∀ w : Real, 0 ≤ w →
              let supX : NNReal → Omega → Real := fun t omega =>
                sSup ((fun s : NNReal => L.X s omega) '' Set.Iic t)
              let W : NNReal → Omega → Real := fun t omega =>
                max w (supX t omega) - L.X t omega
              ∀ f : BoundedContinuousFunction Real Real,
                Tendsto
                  (fun t : NNReal =>
                    ∫ omega, f (W t omega) ∂P)
                  atTop
                  (nhds (∫ x : Real, f x ∂mu)))) ∧
        (rho = 0 →
          ∀ w : Real, 0 ≤ w →
            let supX : NNReal → Omega → Real := fun t omega =>
              sSup ((fun s : NNReal => L.X s omega) '' Set.Iic t)
            let W : NNReal → Omega → Real := fun t omega =>
              max w (supX t omega) - L.X t omega
            ∀ f : BoundedContinuousFunction Real Real,
              Tendsto
                (fun t : NNReal =>
                  ∫ omega, f (W t omega) ∂P)
                atTop (nhds (f 0))) ∧
        (1 ≤ rho →
          ¬ ∃ mu : Measure Real,
            IsProbabilityMeasure mu ∧
            mu (Set.Ici (0 : Real)) = 1 ∧
            (∀ (t : NNReal) (f : BoundedContinuousFunction Real Real),
              (∫ w in Set.Ici (0 : Real),
                (∫ omega,
                  f (max w
                    (sSup ((fun s : NNReal => L.X s omega) '' Set.Iic t)) -
                    L.X t omega) ∂P) ∂mu) =
              ∫ w, f w ∂mu)) ∧
        (1 < rho →
          ∀ w : Real, 0 ≤ w →
            let supX : NNReal → Omega → Real := fun t omega =>
              sSup ((fun s : NNReal => L.X s omega) '' Set.Iic t)
            let W : NNReal → Omega → Real := fun t omega =>
              max w (supX t omega) - L.X t omega
            ∀ᵐ omega : Omega ∂P,
              Tendsto (fun t : NNReal => W t omega) atTop atTop)

noncomputable def certificate_4_11_v2 : Prop :=
  ∀ {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hBV : L.BoundedVariation),
    (∀ᵐ omega : Omega ∂P,
          Tendsto (fun t : NNReal => L.X t omega / (t : Real))
            (nhdsWithin (0 : NNReal) (Set.Ioi 0))
            (nhds L.drift))

noncomputable def certificate_4_12_v2 : Prop :=
  ∀ {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hBV : L.BoundedVariation)
    (hd : 0 < L.drift)
    (hMeanPositive :
      0 < derivWithin L.ψ (Set.Ici (0 : Real)) 0),
    let tau : Omega → WithTop NNReal := fun omega =>
          Kyprianou.Ch03.firstHittingTime L.X (Set.Iio 0) omega
        let rho : Real :=
          (L.drift - derivWithin L.ψ (Set.Ici (0 : Real)) 0) /
            L.drift
        (P {omega : Omega | tau omega ≠ ⊤}).toReal = rho ∧
        (∀ (finiteTime : Omega → NNReal),
          (∀ omega : Omega, tau omega ≠ ⊤ →
            tau omega = (finiteTime omega : WithTop NNReal)) →
          ∀ x : Real, 0 ≤ x →
            let ruinAndDeficit : Set Omega :=
              {omega : Omega |
                tau omega ≠ ⊤ ∧
                  -(L.X (finiteTime omega) omega) ≤ x}
            let integratedTail : Real :=
              ∫ y in Set.Icc (0 : Real) x,
                (L.ν (Set.Iio (-y))).toReal ∂volume
            (P ruinAndDeficit).toReal =
              (1 / L.drift) * integratedTail ∧
            (0 < rho →
              (P ruinAndDeficit).toReal / rho =
                (1 / (L.drift * rho)) * integratedTail))
end Kyprianou.Ch04


