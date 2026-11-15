-- Prove2me | Definitions.Def_Kyprianou_Ch04_Exercise4_9Certification
-- name    : Kyprianou_Ch04_Exercise4_9Certification
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-14T22:36:05.35005+00:00
-- url     : https://prove2.me/theorems/4c78100c-54b5-4c80-8ff5-79db71a678d2
-- title:
--   Kyprianou Chapter 4 Exercise 4.9 full completion certificate
-- statement:
--   The conjunction of all 3 textbook subparts of Exercise 4.9, each proposition reproduced from its source-matched Lean theorem telescope. No proposition is replaced by True or assumed proved.
-- source:
--   Kyprianou (2006), Chapter 4 Exercise 4.9, pp.105-109.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Mathlib.MeasureTheory.Group.Convolution
open MeasureTheory ProbabilityTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04

noncomputable def certificate_ex4_9_i : Prop :=
  ∀ {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal -> Omega -> Real)
    (hLevy : ProbabilityTheory.IsLevyProcess X P)
    (triplet : ProbabilityTheory.LevyKhintchineTriple)
    (hTriplet : forall (t : NNReal) (xi : Real),
      charFun (P.map (X t)) xi =
        Complex.exp (((t : Real) : Complex) *
          Kyprianou.Ch01.levyTripleExponent triplet xi))
    (hBV : triplet.gaussianVariance = 0 ∧
      (∫⁻ y in Set.Ioo (-1 : Real) 1,
        ENNReal.ofReal |y| ∂triplet.levyMeasure) < ⊤)
    (drift : Real)
    (hDrift : drift =
       triplet.drift -
         ∫ y in Set.Ioo (-1 : Real) 1, y ∂triplet.levyMeasure)
    (hd : 0 < drift)
    (hNotSubordinator :
      ¬ (∀ᵐ omega : Omega ∂P, Monotone (fun t : NNReal => X t omega))),
    ∀ᵐ omega : Omega ∂P,
          Tendsto (fun t : NNReal => X t omega / (t : Real))
            (nhdsWithin (0 : NNReal) (Set.Ioi 0))
            (nhds drift)

noncomputable def certificate_ex4_9_ii : Prop :=
  ∀ {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal -> Omega -> Real)
    (hLevy : ProbabilityTheory.IsLevyProcess X P)
    (triplet : ProbabilityTheory.LevyKhintchineTriple)
    (hTriplet : forall (t : NNReal) (xi : Real),
      charFun (P.map (X t)) xi =
        Complex.exp (((t : Real) : Complex) *
          Kyprianou.Ch01.levyTripleExponent triplet xi))
    (hBV : triplet.gaussianVariance = 0 ∧
      (∫⁻ y in Set.Ioo (-1 : Real) 1,
        ENNReal.ofReal |y| ∂triplet.levyMeasure) < ⊤)
    (drift : Real)
    (hDrift : drift =
       triplet.drift -
         ∫ y in Set.Ioo (-1 : Real) 1, y ∂triplet.levyMeasure)
    (hd : 0 < drift)
    (hNotSubordinator :
      ¬ (∀ᵐ omega : Omega ∂P, Monotone (fun t : NNReal => X t omega))),
    let tau : Omega -> WithTop NNReal := fun omega =>
          sInf {u : WithTop NNReal |
            ∃ t : NNReal, u = ↑t ∧ 0 < t ∧ X t omega < 0};
        0 < P {omega : Omega | 0 < tau omega}

noncomputable def certificate_ex4_9_iii : Prop :=
  ∀ {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal -> Omega -> Real)
    (hLevy : ProbabilityTheory.IsLevyProcess X P)
    (triplet : ProbabilityTheory.LevyKhintchineTriple)
    (hTriplet : ∀ (t : NNReal) (theta : Real),
      charFun (P.map (X t)) theta =
        Complex.exp (((t : Real) : Complex) *
          Kyprianou.Ch01.levyTripleExponent triplet theta))
    (hBV : triplet.gaussianVariance = 0 ∧
      (∫⁻ y in Set.Ioo (-1 : Real) 1,
        ENNReal.ofReal |y| ∂triplet.levyMeasure) < ⊤)
    (drift : Real)
    (hDrift : drift = triplet.drift -
      ∫ y in Set.Ioo (-1 : Real) 1, y ∂triplet.levyMeasure)
    (hd : 0 < drift)
    (hNotSubordinator :
      ¬ (∀ᵐ omega : Omega ∂P, Monotone (fun t : NNReal => X t omega)))
    (hTendsInfinity : ∀ᵐ omega : Omega ∂P,
      Tendsto (fun t : NNReal => X t omega) atTop atTop),
    let tau : Real -> Omega -> WithTop NNReal := fun initial omega =>
          sInf {v : WithTop NNReal |
            ∃ t : NNReal, v = ↑t ∧ 0 < t ∧
              initial + X t omega < 0}
        let rho : Real := (P {omega : Omega | tau 0 omega ≠ ⊤}).toReal
        0 < rho ∧ rho < 1 ∧
        ∃ finiteTime : Omega -> NNReal,
          Measurable finiteTime ∧
          (∀ omega : Omega, tau 0 omega ≠ ⊤ →
            tau 0 omega = (finiteTime omega : WithTop NNReal)) ∧
          ∃ eta : Measure Real,
            IsProbabilityMeasure eta ∧
            (∀ B : Set Real, MeasurableSet B →
              (eta B).toReal =
                (P {omega : Omega | tau 0 omega ≠ ⊤ ∧
                    -(X (finiteTime omega) omega) ∈ B}).toReal / rho) ∧
            let convPow : Nat -> Measure Real :=
              Nat.rec (Measure.dirac (0 : Real))
                (fun _ mu => mu.conv eta)
            ∀ x : Real, 0 ≤ x →
              (P {omega : Omega | tau x omega = ⊤}).toReal =
                (1 - rho) *
                  ∑' k : Nat, rho ^ k * (convPow k (Set.Iic x)).toReal

/-- All textbook subparts of Exercise 4.9 are required, with none silently omitted. -/
noncomputable def certificate_exercise_4_9 : Prop :=
    certificate_ex4_9_i ∧
    certificate_ex4_9_ii ∧
    certificate_ex4_9_iii

end Kyprianou.Ch04


