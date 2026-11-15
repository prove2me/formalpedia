-- Prove2me | Definitions.Def_Kyprianou_Ch03_ChapterCertification
-- name    : Kyprianou_Ch03_ChapterCertification
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-14T16:43:48.865702+00:00
-- url     : https://prove2.me/theorems/29762f19-278d-4295-acc4-296b0f2b8669
-- title:
--   Full quantified Chapter 3 certificates for all thirteen results
-- statement:
--   Thirteen full quantified certificate propositions extracted from the exact binders and conclusions of the standalone source theorem items. They correspond to results 3.1-3.6 and 3.8-3.14, preserving all hypotheses.
-- source:
--   Kyprianou (2006), Chapter 3, named theorems pp. 67-82.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Definitions.Def_Kyprianou_Ch03_EsscherDensity
import Definitions.Def_Kyprianou_Ch03_IsSubmultiplicative
import Definitions.Def_Kyprianou_Ch03_IsSubordinator
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LevyExtrema_SBA_runSup
import Mathlib
open MeasureTheory ProbabilityTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch03

/-- Full theorem obligation from Kyprianou.Ch03.strongMarkovAtExtendedStoppingTime. -/
noncomputable def certificate_3_1 : Prop :=
  forall {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (X : NNReal -> Omega -> Real)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hNatural : IsCompletedNaturalFiltration P X F)
    (tau : Omega -> WithTop NNReal)
    (hTau : IsStoppingTime F tau)
    (finiteTime : Omega -> NNReal)
    (hFiniteTime : forall omega, tau omega != ⊤ ->
      tau omega = (finiteTime omega : WithTop NNReal)),
    forall A : Set Omega,
      (forall s : NNReal,
        MeasurableSet[F s]
          (Set.inter A {omega : Omega | tau omega <= (s : WithTop NNReal)})) ->
      Measure.map
        (fun omega : Omega =>
          (Set.indicator A (fun _ : Omega => (1 : Real)) omega,
           fun u : NNReal =>
             X (finiteTime omega + u) omega - X (finiteTime omega) omega))
        (P.restrict {omega : Omega | tau omega != ⊤}) =
      (Measure.map
        (Set.indicator A (fun _ : Omega => (1 : Real)))
        (P.restrict {omega : Omega | tau omega != ⊤})).prod
        (Measure.map (fun omega : Omega => fun u : NNReal => X u omega) P)

/-- Full theorem obligation from Kyprianou.Ch03.quasiLeftContinuousAlongStoppingTimes. -/
noncomputable def certificate_3_2 : Prop :=
  forall {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (X : NNReal -> Omega -> Real)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hNatural : IsCompletedNaturalFiltration P X F)
    (T : Omega -> WithTop NNReal)
    (Tn : Nat -> Omega -> WithTop NNReal)
    (timeT : Omega -> NNReal) (timeTn : Nat -> Omega -> NNReal)
    (hTimeT : forall omega, T omega != ⊤ ->
      T omega = (timeT omega : WithTop NNReal))
    (hTimeTn : forall n omega, Tn n omega != ⊤ ->
      Tn n omega = (timeTn n omega : WithTop NNReal))
    (hT : IsStoppingTime F T)
    (hTn : forall n, IsStoppingTime F (Tn n))
    (hIncreasing : ∀ᵐ omega : Omega ∂ P,
      Monotone (fun n => Tn n omega))
    (hLimit : ∀ᵐ omega : Omega ∂ P,
      Tendsto (fun n => Tn n omega) atTop (nhds (T omega))),
    (∀ᵐ omega : Omega ∂ P, T omega != ⊤ ->
      Tendsto (fun n => X (timeTn n omega) omega)
        atTop (nhds (X (timeT omega) omega))) ∧
    (∀ᵐ omega : Omega ∂ P, T omega != ⊤ ->
      (forall n, Tn n omega < T omega) ->
      Function.leftLim (fun s : NNReal => X s omega) (timeT omega) =
        X (timeT omega) omega)

/-- Full theorem obligation from Kyprianou.Ch03.entranceAndHittingAreStoppingTimes. -/
noncomputable def certificate_3_3 : Prop :=
  forall {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (X : NNReal -> Omega -> Real)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hNatural : IsCompletedNaturalFiltration P X F)
    (B : Set Real) (hB : IsOpen B ∨ IsClosed B)
    (entranceTime hittingTime : Omega -> NNReal)
    (hEntranceTime : forall omega,
      firstEntranceTime X B omega != ⊤ ->
        firstEntranceTime X B omega = (entranceTime omega : WithTop NNReal))
    (hHittingTime : forall omega,
      firstHittingTime X B omega != ⊤ ->
        firstHittingTime X B omega = (hittingTime omega : WithTop NNReal)),
    IsStoppingTime F (firstEntranceTime X B) ∧
    IsStoppingTime F (firstHittingTime X B) ∧
    (∀ᵐ omega : Omega ∂ P,
      (firstEntranceTime X B omega != ⊤ ->
        X (entranceTime omega) omega ∈ closure B) ∧
      (firstHittingTime X B omega != ⊤ ->
        X (hittingTime omega) omega ∈ closure B))

/-- Full theorem obligation from Kyprianou.Ch03.timeReversalDuality. -/
noncomputable def certificate_3_4 : Prop :=
  forall {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal -> Omega -> Real)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (t : NNReal) (ht : 0 < t),
    Measure.map
      (fun omega : Omega =>
        fun s : {s : NNReal // s <= t} =>
          (if (s : NNReal) = t then X 0 omega
           else Function.leftLim (fun r : NNReal => X r omega) (t - (s : NNReal))) -
             X t omega) P =
    Measure.map
      (fun omega : Omega =>
        fun s : {s : NNReal // s <= t} =>
          -(X (s : NNReal) omega)) P

/-- Full theorem obligation from Kyprianou.Ch03.supremumInfimumDuality. -/
noncomputable def certificate_3_5 : Prop :=
  forall {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal -> Omega -> Real)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (t : NNReal) (ht : 0 < t),
    Measure.map
      (fun omega : Omega =>
        let supremum := LevyExtrema.SBA.runSup (fun s => X s omega) t
        (supremum, supremum - X t omega)) P =
    Measure.map
      (fun omega : Omega =>
        let infimum := sInf ((fun s : NNReal => X s omega) '' Set.Icc 0 t)
        (X t omega - infimum, -infimum)) P

/-- Full theorem obligation from Kyprianou.Ch03.exponentialMomentsIffLargeJumpIntegral. -/
noncomputable def certificate_3_6 : Prop :=
  forall {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal -> Omega -> Real)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (T : ProbabilityTheory.LevyKhintchineTriple)
    (hLK : forall (t : NNReal) (xi : Real),
      charFun (P.map (X t)) xi =
        Complex.exp ((((t : Real) : Complex)) *
          Kyprianou.Ch01.levyTripleExponent T xi))
    (beta : Real),
    (forall (t : NNReal),
      Integrable (fun omega => Real.exp (beta * X t omega)) P) <->
      IntegrableOn (fun x : Real => Real.exp (beta * x))
        {x : Real | 1 <= abs x} T.levyMeasure

/-- Full theorem obligation from Kyprianou.Ch03.submultiplicativeMomentsIffLargeJumpIntegral. -/
noncomputable def certificate_3_8 : Prop :=
  forall {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal -> Omega -> Real)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (T : ProbabilityTheory.LevyKhintchineTriple)
    (hLK : forall (t : NNReal) (xi : Real),
      charFun (P.map (X t)) xi =
        Complex.exp ((((t : Real) : Complex)) *
          Kyprianou.Ch01.levyTripleExponent T xi))
    (g : Real -> Real)
    (hg : Kyprianou.Ch03.IsSubmultiplicative g)
    (hg_meas : Measurable g)
    (hg_bounded : forall R : Real, 0 <= R ->
      exists M : Real, forall x : Real, abs x <= R -> g x <= M),
    (IntegrableOn g {x : Real | 1 <= abs x} T.levyMeasure) <->
    (forall (t : NNReal), 0 < t ->
      Integrable (fun omega => g (X t omega)) P)

/-- Full theorem obligation from Kyprianou.Ch03.esscherChangeOfMeasurePreservesLevyAndTriplet. -/
noncomputable def certificate_3_9 : Prop :=
  forall {Omega : Type} [MeasurableSpace Omega]
    (P Q : Measure Omega) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (X : NNReal -> Omega -> Real)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hNatural : IsCompletedNaturalFiltration P X F)
    (T : ProbabilityTheory.LevyKhintchineTriple)
    (hLK : forall (t : NNReal) (xi : Real),
      charFun (P.map (X t)) xi =
        Complex.exp ((((t : Real) : Complex)) *
          Kyprianou.Ch01.levyTripleExponent T xi))
    (beta : Real)
    (hBeta : IntegrableOn
      (fun x : Real => Real.exp (beta * x))
      {x : Real | 1 <= abs x} T.levyMeasure)
    (hEsscher : forall (t : NNReal) (A : Set Omega),
      MeasurableSet[F t] A ->
      Q A =
        ENNReal.ofReal
          (∫ omega, Set.indicator A
            (fun omega : Omega =>
              esscherDensity X beta
                (Real.log
                  (∫ eta, Real.exp (beta * X 1 eta) ∂P))
                t omega) omega ∂P)),
    exists (Tbeta : ProbabilityTheory.LevyKhintchineTriple),
      Tbeta.drift =
        T.drift + beta * (T.gaussianVariance : Real) +
          ∫ x in {x : Real | abs x < 1},
            (Real.exp (beta * x) - 1) * x ∂T.levyMeasure ∧
      Tbeta.gaussianVariance = T.gaussianVariance ∧
      Tbeta.levyMeasure =
        T.levyMeasure.withDensity
          (fun x : Real => ENNReal.ofReal (Real.exp (beta * x))) ∧
      ProbabilityTheory.IsLevyProcess X Q ∧
      (forall (t : NNReal) (xi : Real),
        charFun (Q.map (X t)) xi =
          Complex.exp ((((t : Real) : Complex)) *
            Kyprianou.Ch01.levyTripleExponent Tbeta xi)) ∧
      (forall theta : Real,
        Integrable (fun omega => Real.exp ((theta + beta) * X 1 omega)) P ->
        Real.log (∫ omega, Real.exp (theta * X 1 omega) ∂Q) =
          Real.log
            (∫ omega, Real.exp ((theta + beta) * X 1 omega) ∂P) -
          Real.log (∫ omega, Real.exp (beta * X 1 omega) ∂P))

/-- Full theorem obligation from Kyprianou.Ch03.esscherOfSpectrallyNegativeLevy. -/
noncomputable def certificate_3_10 : Prop :=
  forall {Omega : Type} [MeasurableSpace Omega]
    (P Q : Measure Omega) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hNatural : IsCompletedNaturalFiltration P L.X F)
    (beta : Real) (hBeta : 0 <= beta)
    (hEsscher : forall (t : NNReal) (A : Set Omega),
      MeasurableSet[F t] A ->
      Q A =
        ENNReal.ofReal
          (∫ omega, Set.indicator A
            (fun omega : Omega =>
              esscherDensity L.X beta (L.ψ beta) t omega)
            omega ∂P)),
    exists (Lbeta : AvramDividend.Classical.SpectrallyNegativeLevy Q F),
      Lbeta.X = L.X ∧
      Lbeta.σ = L.σ ∧
      Lbeta.ν = L.ν.withDensity
        (fun x : Real => ENNReal.ofReal (Real.exp (beta * x))) ∧
      Lbeta.c = L.c + beta * L.σ ^ 2 +
        (∫ x in {x : Real | abs x < 1},
          (Real.exp (beta * x) - 1) * x ∂L.ν) ∧
      forall theta : Real, -beta <= theta ->
        Lbeta.ψ theta = L.ψ (theta + beta) - L.ψ beta

/-- Full theorem obligation from Kyprianou.Ch03.esscherDensityAtExtendedStoppingTime. -/
noncomputable def certificate_3_11 : Prop :=
  forall {Omega : Type} [MeasurableSpace Omega]
    (P Q : Measure Omega) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (X : NNReal -> Omega -> Real)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hNatural : IsCompletedNaturalFiltration P X F)
    (T : ProbabilityTheory.LevyKhintchineTriple)
    (hLK : forall (t : NNReal) (xi : Real),
      charFun (P.map (X t)) xi =
        Complex.exp ((((t : Real) : Complex)) *
          Kyprianou.Ch01.levyTripleExponent T xi))
    (beta : Real)
    (hBeta : IntegrableOn
      (fun x : Real => Real.exp (beta * x))
      {x : Real | 1 <= abs x} T.levyMeasure)
    (hEsscher : forall (t : NNReal) (A : Set Omega),
      MeasurableSet[F t] A ->
      Q A =
        ENNReal.ofReal
          (∫ omega, Set.indicator A
            (fun omega : Omega =>
              esscherDensity X beta
                (Real.log
                  (∫ eta, Real.exp (beta * X 1 eta) ∂P))
                t omega) omega ∂P))
    (tau : Omega -> WithTop NNReal)
    (hStopping : IsStoppingTime F tau)
    (tauFinite : Omega -> NNReal)
    (hTauFinite : forall omega, tau omega != ⊤ ->
      tau omega = (tauFinite omega : WithTop NNReal)),
    forall (A : Set Omega),
      (forall t : NNReal,
        MeasurableSet[F t]
          (Set.inter A {omega : Omega |
            tau omega <= (t : WithTop NNReal)})) ->
      Q (Set.inter A {omega : Omega | tau omega != ⊤}) =
        ENNReal.ofReal
          (∫ omega,
            Set.indicator
              (Set.inter A {eta : Omega | tau eta != ⊤})
              (fun eta : Omega =>
                esscherDensity X beta
                  (Real.log
                    (∫ z, Real.exp (beta * X 1 z) ∂P))
                  (tauFinite eta) eta)
              omega ∂P)

/-- Full theorem obligation from Kyprianou.Ch03.upwardFirstPassageLaplaceTransform. -/
noncomputable def certificate_3_12 : Prop :=
  forall {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hNotDecreasing : ¬ (∀ᵐ omega : Omega ∂ P,
      Antitone (fun t : NNReal => L.X t omega))),
    forall (q : Real), 0 <= q ->
      exists phi : Real,
        0 <= phi ∧ L.ψ phi = q ∧
        (forall theta : Real, 0 <= theta ->
          L.ψ theta = q -> theta <= phi) ∧
        (forall (x : Real), 0 <= x ->
          forall (finiteTime : Omega -> NNReal),
            (forall omega,
              firstHittingTime L.X (Set.Ioi x) omega != ⊤ ->
                firstHittingTime L.X (Set.Ioi x) omega =
                  (finiteTime omega : WithTop NNReal)) ->
            (∫ omega,
              if firstHittingTime L.X (Set.Ioi x) omega = ⊤
              then (0 : Real)
              else Real.exp (-q * (finiteTime omega : Real)) ∂P) =
              Real.exp (-phi * x))

/-- Full theorem obligation from Kyprianou.Ch03.upwardPassageProbabilityAndDrift. -/
noncomputable def certificate_3_13 : Prop :=
  forall {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hNotDecreasing : ¬ (∀ᵐ omega : Omega ∂ P,
      Antitone (fun t : NNReal => L.X t omega))),
    exists phi : Real,
      0 <= phi ∧ L.ψ phi = 0 ∧
      (forall theta : Real, 0 <= theta ->
        L.ψ theta = 0 -> theta <= phi) ∧
      (forall x : Real, 0 <= x ->
        forall finiteTime : Omega -> NNReal,
          (forall omega,
            firstHittingTime L.X (Set.Ioi x) omega != ⊤ ->
              firstHittingTime L.X (Set.Ioi x) omega =
                (finiteTime omega : WithTop NNReal)) ->
          (P {omega : Omega |
            firstHittingTime L.X (Set.Ioi x) omega != ⊤}).toReal =
              Real.exp (-phi * x)) ∧
      (forall x : Real, 0 < x ->
        ((P {omega : Omega |
          firstHittingTime L.X (Set.Ioi x) omega != ⊤}).toReal = 1
          <-> phi = 0)) ∧
      ((phi = 0) <-> (forall theta : Real, 0 <= theta ->
        0 <= L.ψ theta)) ∧
      (Integrable (L.X 1) P ->
        ((phi = 0) <-> 0 <= (∫ omega, L.X 1 omega ∂P)))

/-- Full theorem obligation from Kyprianou.Ch03.upwardPassageIsKilledSubordinator. -/
noncomputable def certificate_3_14 : Prop :=
  forall {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hNotDecreasing : ¬ (∀ᵐ omega : Omega ∂ P,
      Antitone (fun t : NNReal => L.X t omega))),
    exists phi : Real,
      0 <= phi ∧ L.ψ phi = 0 ∧
      (forall theta : Real, 0 <= theta ->
        L.ψ theta = 0 -> theta <= phi) ∧
      exists (Omega2 : Type) (m2 : MeasurableSpace Omega2),
        letI : MeasurableSpace Omega2 := m2
        exists (Q : Measure Omega2) (hQ : IsProbabilityMeasure Q),
          letI : IsProbabilityMeasure Q := hQ
          exists (S : NNReal -> Omega2 -> Real)
                 (zeta : Omega2 -> WithTop NNReal),
            IsSubordinator Q S ∧
            Indep
              (MeasurableSpace.comap zeta
                (inferInstance : MeasurableSpace (WithTop NNReal)))
              (MeasurableSpace.comap
                (fun omega : Omega2 => fun x : NNReal => S x omega)
                (inferInstance : MeasurableSpace (NNReal -> Real)))
              Q ∧
            (forall x : NNReal,
              (Q {omega : Omega2 |
                (x : WithTop NNReal) < zeta omega}).toReal =
                  Real.exp (-phi * (x : Real))) ∧
            (phi = 0 ->
              (Q {omega : Omega2 | zeta omega = ⊤}).toReal = 1) ∧
            (0 < phi ->
              (Q {omega : Omega2 | zeta omega != ⊤}).toReal = 1) ∧
            Measure.map
              (fun omega : Omega =>
                fun x : NNReal =>
                  firstHittingTime L.X (Set.Ioi (x : Real)) omega) P =
            Measure.map
              (fun omega : Omega2 =>
                fun x : NNReal =>
                  if (x : WithTop NNReal) < zeta omega
                  then (Real.toNNReal (S x omega) : WithTop NNReal)
                  else ⊤) Q

end Kyprianou.Ch03


