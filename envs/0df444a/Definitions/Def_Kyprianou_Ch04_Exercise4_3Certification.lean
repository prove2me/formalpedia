-- Prove2me | Definitions.Def_Kyprianou_Ch04_Exercise4_3Certification
-- name    : Kyprianou_Ch04_Exercise4_3Certification
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-14T22:33:26.058885+00:00
-- url     : https://prove2.me/theorems/4dfae364-eda6-4edb-bd1c-c2e5c1d6703b
-- title:
--   Kyprianou Chapter 4 Exercise 4.3 full completion certificate
-- statement:
--   The conjunction of all 4 textbook subparts of Exercise 4.3, each proposition reproduced from its source-matched Lean theorem telescope. No proposition is replaced by True or assumed proved.
-- source:
--   Kyprianou (2006), Chapter 4 Exercise 4.3, pp.105-109.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter ProbabilityTheory LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04

noncomputable def certificate_ex4_3_i : Prop :=
  ∀ {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (X : NNReal -> Omega -> Real)
    (hLevy : ProbabilityTheory.IsLevyProcess X P)
    (hAdapted : ∀ t : NNReal,
      Measurable[(F t)] (fun omega : Omega => X t omega))
    (triplet : ProbabilityTheory.LevyKhintchineTriple)
    (hTriplet : ∀ (t : NNReal) (theta : Real),
      charFun (P.map (X t)) theta =
        Complex.exp (((t : Real) : Complex) *
          Kyprianou.Ch01.levyTripleExponent triplet theta))
    (hBV : triplet.gaussianVariance = 0 ∧
      (∫⁻ x in Set.Ioo (-1 : Real) 1,
        ENNReal.ofReal |x| ∂triplet.levyMeasure) < ⊤)
    (hNonLattice : triplet.levyMeasure Set.univ < ⊤ ->
      ¬ ∃ a : Real, 0 < a ∧
        triplet.levyMeasure
          {x : Real | ∃ k : Int, x = (k : Real) * a} =
        triplet.levyMeasure Set.univ)
    (f : Real -> Real) (hf : ContDiff Real 1 f)
    (lambda : Real) (hlambda : 0 ≤ lambda)
    (hEigen : MeasureTheory.Martingale
      (fun (t : NNReal) (omega : Omega) => Real.exp (-lambda * (t : Real)) * f (X t omega)) F P)
    (hIntegrable : ∀ y : Real,
      Integrable (fun x : Real => f (y + x) - f y)
        triplet.levyMeasure),
    ∀ n : Nat,
          let tau : Omega -> WithTop NNReal := fun omega =>
            sInf {v : WithTop NNReal |
              ∃ t : NNReal, v = ↑t ∧
                n < |∫ x : Real,
                   (f (X t omega + x) - f (X t omega))
                   ∂triplet.levyMeasure|}
          ∀ t : NNReal,
            MeasurableSet[(F t)]
              {omega : Omega | tau omega ≤ (t : WithTop NNReal)}

noncomputable def certificate_ex4_3_ii : Prop :=
  ∀ {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (X : NNReal -> Omega -> Real)
    (hLevy : ProbabilityTheory.IsLevyProcess X P)
    (hAdapted : ∀ t : NNReal,
      Measurable[(F t)] (fun omega : Omega => X t omega))
    (triplet : ProbabilityTheory.LevyKhintchineTriple)
    [SigmaFinite triplet.levyMeasure]
    (hTriplet : ∀ (t : NNReal) (theta : Real),
      charFun (P.map (X t)) theta =
        Complex.exp (((t : Real) : Complex) *
          Kyprianou.Ch01.levyTripleExponent triplet theta))
    (hBV : triplet.gaussianVariance = 0 ∧
      (∫⁻ x in Set.Ioo (-1 : Real) 1,
        ENNReal.ofReal |x| ∂triplet.levyMeasure) < ⊤)
    (hNonLattice : triplet.levyMeasure Set.univ < ⊤ ->
      ¬ ∃ a : Real, 0 < a ∧
        triplet.levyMeasure
          {x : Real | ∃ k : Int, x = (k : Real) * a} =
        triplet.levyMeasure Set.univ)
    (f : Real -> Real) (hf : ContDiff Real 1 f)
    (lambda : Real) (hlambda : 0 ≤ lambda)
    (hEigen : MeasureTheory.Martingale
      (fun (t : NNReal) (omega : Omega) => Real.exp (-lambda * (t : Real)) * f (X t omega)) F P)
    (hIntegrable : ∀ y : Real,
      Integrable (fun x : Real => f (y + x) - f y)
        triplet.levyMeasure),
    ∀ (Xleft : NNReal -> Omega -> Real)
          (hLeft : ∀ᵐ omega : Omega ∂P, ∀ t : NNReal, 0 < t →
            Tendsto (fun s : NNReal => X s omega)
              (nhdsWithin t (Set.Iio t)) (nhds (Xleft t omega)))
          (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0,0,0}
            P triplet.levyMeasure)
          (hJumpLaw : ∀ᵐ omega : Omega ∂P,
            N.N omega = Kyprianou.Ch04.pathJumpMeasure X Xleft omega),
          let M : NNReal -> Omega -> Real := fun t omega =>
            (∫ z in Set.prod (Set.Icc (0 : Real) (t : Real)) Set.univ,
              Real.exp (-lambda * z.1) *
                (f (Xleft (Real.toNNReal z.1) omega + z.2) -
                 f (Xleft (Real.toNNReal z.1) omega))
              ∂(N.N omega)) -
            (∫ s in Set.Icc (0 : Real) (t : Real),
              Real.exp (-lambda * s) *
                (∫ x : Real,
                  (f (X (Real.toNNReal s) omega + x) -
                   f (X (Real.toNNReal s) omega))
                  ∂triplet.levyMeasure) ∂volume)
          ∃ stop : Nat -> Omega -> NNReal -> NNReal,
            (∀ (n : Nat) (omega : Omega) (t : NNReal),
              let tau : WithTop NNReal :=
                sInf {v : WithTop NNReal |
                  ∃ s : NNReal, v = ↑s ∧
                    n < |∫ x : Real,
                      (f (X s omega + x) - f (X s omega))
                      ∂triplet.levyMeasure|}
              (stop n omega t : WithTop NNReal) =
                min (t : WithTop NNReal) tau) ∧
            ∀ n : Nat,
              MeasureTheory.Martingale
                (fun t omega => M (stop n omega t) omega) F P

noncomputable def certificate_ex4_3_iii : Prop :=
  ∀ {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (X : NNReal -> Omega -> Real)
    (hLevy : ProbabilityTheory.IsLevyProcess X P)
    (hAdapted : ∀ t : NNReal,
      Measurable[(F t)] (fun omega : Omega => X t omega))
    (triplet : ProbabilityTheory.LevyKhintchineTriple)
    (hTriplet : ∀ (t : NNReal) (theta : Real),
      charFun (P.map (X t)) theta =
        Complex.exp (((t : Real) : Complex) *
          Kyprianou.Ch01.levyTripleExponent triplet theta))
    (hBV : triplet.gaussianVariance = 0 ∧
      (∫⁻ x in Set.Ioo (-1 : Real) 1,
        ENNReal.ofReal |x| ∂triplet.levyMeasure) < ⊤)
    (hNonLattice : triplet.levyMeasure Set.univ < ⊤ ->
      ¬ ∃ a : Real, 0 < a ∧
        triplet.levyMeasure
          {x : Real | ∃ k : Int, x = (k : Real) * a} =
        triplet.levyMeasure Set.univ)
    (f : Real -> Real) (hf : ContDiff Real 1 f)
    (lambda : Real) (hlambda : 0 ≤ lambda)
    (hEigen : MeasureTheory.Martingale
      (fun (t : NNReal) (omega : Omega) => Real.exp (-lambda * (t : Real)) * f (X t omega)) F P)
    (hIntegrable : ∀ y : Real,
      Integrable (fun x : Real => f (y + x) - f y)
        triplet.levyMeasure),
    (∀ s : NNReal, 0 < s →
          ∀ a b : Real, a < b →
            0 < (P.map (X s)) (Set.Ioo a b)) →
        let drift : Real :=
          triplet.drift -
            ∫ x in Set.Ioo (-1 : Real) 1, x ∂triplet.levyMeasure
        ∀ y : Real,
          drift * deriv f y +
            (∫ x : Real, (f (y + x) - f y)
              ∂triplet.levyMeasure) = lambda * f y

noncomputable def certificate_ex4_3_iv : Prop :=
  ∀ {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (X : NNReal -> Omega -> Real)
    (hLevy : ProbabilityTheory.IsLevyProcess X P)
    (hAdapted : ∀ t : NNReal,
      Measurable[(F t)] (fun omega : Omega => X t omega))
    (triplet : ProbabilityTheory.LevyKhintchineTriple)
    (hTriplet : ∀ (t : NNReal) (theta : Real),
      charFun (P.map (X t)) theta =
        Complex.exp (((t : Real) : Complex) *
          Kyprianou.Ch01.levyTripleExponent triplet theta))
    (hBV : triplet.gaussianVariance = 0 ∧
      (∫⁻ x in Set.Ioo (-1 : Real) 1,
        ENNReal.ofReal |x| ∂triplet.levyMeasure) < ⊤)
    (hNonLattice : triplet.levyMeasure Set.univ < ⊤ ->
      ¬ ∃ a : Real, 0 < a ∧
        triplet.levyMeasure
          {x : Real | ∃ k : Int, x = (k : Real) * a} =
        triplet.levyMeasure Set.univ)
    (f : Real -> Real) (hf : ContDiff Real 1 f)
    (lambda : Real) (hlambda : 0 ≤ lambda)
    (hEigen : MeasureTheory.Martingale
      (fun (t : NNReal) (omega : Omega) => Real.exp (-lambda * (t : Real)) * f (X t omega)) F P)
    (hIntegrable : ∀ y : Real,
      Integrable (fun x : Real => f (y + x) - f y)
        triplet.levyMeasure),
    ∀ beta : Real,
          (∀ y : Real, f y = Real.exp (beta * y)) →
          (∫⁻ x in {x : Real | 1 < |x|},
            ENNReal.ofReal (Real.exp (beta * x))
              ∂triplet.levyMeasure) < ⊤ →
          let physicalDrift : Real :=
            triplet.drift -
              ∫ x in Set.Ioo (-1 : Real) 1,
                x ∂triplet.levyMeasure
          lambda = physicalDrift * beta +
            ∫ x : Real,
              (Real.exp (beta * x) - 1) ∂triplet.levyMeasure

/-- All textbook subparts of Exercise 4.3 are required, with none silently omitted. -/
noncomputable def certificate_exercise_4_3 : Prop :=
    certificate_ex4_3_i ∧
    certificate_ex4_3_ii ∧
    certificate_ex4_3_iii ∧
    certificate_ex4_3_iv

end Kyprianou.Ch04


