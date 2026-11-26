-- Prove2me | Definitions.Def_Kyprianou_Ch04_Exercise4_9CertificationV3
-- name    : Kyprianou_Ch04_Exercise4_9CertificationV3
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-26T12:29:18.903462+00:00
-- url     : https://prove2.me/theorems/75636ca8-c8c5-4227-9b7c-40cb27610e0e
-- title:
--   Exercise 4.9: almost-sure hitting-time representative
-- statement:
--   Retains all original exercise conclusions and hypotheses. Corrects only the auxiliary measurable finite hitting-clock representative, which agrees almost surely on finite passage paths. Parts (i) and (ii) unchanged; original conditional deficit law and geometric convolution identity retained.
-- source:
--   Kyprianou (2006), Chapter 4 Exercise 4.9, pp.105-109.

import Definitions.Def_Kyprianou_Ch04_Exercise4_9Certification
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false
namespace Kyprianou.Ch04

noncomputable def certificate_ex4_9_iii_v3 : Prop :=
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
          (∀ᵐ omega : Omega ∂P, tau 0 omega ≠ ⊤ →
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

 /-- Source-faithful Exercise 4.9: measurable hitting-clock version agrees almost surely. -/
noncomputable def certificate_exercise_4_9_v3 : Prop :=
  certificate_ex4_9_i ∧ certificate_ex4_9_ii ∧ certificate_ex4_9_iii_v3
end Kyprianou.Ch04


