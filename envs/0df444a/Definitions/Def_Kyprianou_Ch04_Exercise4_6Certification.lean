-- Prove2me | Definitions.Def_Kyprianou_Ch04_Exercise4_6Certification
-- name    : Kyprianou_Ch04_Exercise4_6Certification
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-14T22:34:55.966641+00:00
-- url     : https://prove2.me/theorems/19f4f3ae-eaad-4a2a-87cf-0689f7e7a246
-- title:
--   Kyprianou Chapter 4 Exercise 4.6 full completion certificate
-- statement:
--   The conjunction of all 3 textbook subparts of Exercise 4.6, each proposition reproduced from its source-matched Lean theorem telescope. No proposition is replaced by True or assumed proved.
-- source:
--   Kyprianou (2006), Chapter 4 Exercise 4.6, pp.105-109.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04

noncomputable def certificate_ex4_6_i : Prop :=
  ∀ {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (G : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P G)
    (hBV : L.BoundedVariation)
    (hDrift : L.drift = 1)
    (lambda : Real) (hlambda : 0 < lambda)
    (service : Measure Real) [IsProbabilityMeasure service]
    (hServicePositive : service (Set.Ioi (0 : Real)) = 1)
    (hInputLaw : L.ν =
      ENNReal.ofReal lambda •
        (service.map (fun x : Real => -x)))
    (J : Omega -> Real)
    (hJLaw : P.map J = service)
    (hJPositive : ∀ᵐ omega : Omega ∂P, 0 < J omega)
    (hIndependent :
      Indep
        (MeasurableSpace.comap J inferInstance)
        (MeasurableSpace.comap
          (fun omega : Omega => fun t : NNReal => L.X t omega)
          inferInstance) P),
    let B : Omega -> WithTop NNReal := fun omega =>
          sInf {v : WithTop NNReal |
            ∃ t : NNReal, v = ↑t ∧ 0 < t ∧ J omega ≤ L.X t omega}
        ∀ beta : Real, 0 ≤ beta →
          ∃ phi : Real,
            0 ≤ phi ∧
            phi - lambda *
              (∫ y : Real,
                (1 - Real.exp (-phi * y)) ∂service) = beta ∧
            (∀ theta : Real, 0 ≤ theta →
              theta - lambda *
                (∫ y : Real,
                  (1 - Real.exp (-theta * y)) ∂service) = beta →
              theta ≤ phi) ∧
            (if beta = 0 then
              (P {omega : Omega | B omega ≠ ⊤}).toReal
            else
              beta * (∫ t in Set.Ici (0 : Real),
                Real.exp (-beta * t) *
                  (P {omega : Omega |
                    B omega ≤ ((Real.toNNReal t) : WithTop NNReal)}).toReal
                ∂volume)) =
              ∫ y : Real, Real.exp (-phi * y) ∂service

noncomputable def certificate_ex4_6_ii : Prop :=
  ∀ {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (G : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P G)
    (hBV : L.BoundedVariation)
    (hDrift : L.drift = 1)
    (lambda : Real) (hlambda : 0 < lambda)
    (service : Measure Real) [IsProbabilityMeasure service]
    (hServicePositive : service (Set.Ioi (0 : Real)) = 1)
    (hInputLaw : L.ν =
      ENNReal.ofReal lambda •
        (service.map (fun x : Real => -x)))
    (Wleft : NNReal -> Omega -> Real)
    (hWLeft : ∀ᵐ omega : Omega ∂P, ∀ t : NNReal, 0 < t →
      Tendsto
        (fun s : NNReal =>
          sSup ((fun u : NNReal => L.X u omega) '' Set.Iic s) -
          L.X s omega)
        (nhdsWithin t (Set.Iio t)) (nhds (Wleft t omega)))
    (rho : Real)
    (hRho : rho =
      lambda * (∫ y : Real, y ∂service))
    (hSupercritical : 1 < rho),
    let supX : NNReal -> Omega -> Real := fun t omega =>
          sSup ((fun s : NNReal => L.X s omega) '' Set.Iic t)
        let W : NNReal -> Omega -> Real := fun t omega =>
          supX t omega - L.X t omega
        let busyStarts : Omega -> Set NNReal := fun omega =>
          {t : NNReal | 0 < t ∧ Wleft t omega = 0 ∧ 0 < W t omega}
        (∀ᵐ omega : Omega ∂P, (busyStarts omega).Finite) ∧
        ∃ phi : Real,
          0 < phi ∧ L.ψ phi = 0 ∧
          (∀ theta : Real, 0 ≤ theta → L.ψ theta = 0 → theta ≤ phi) ∧
          let p : Real :=
            1 - ∫ y : Real, Real.exp (-phi * y) ∂service
          0 < p ∧ p < 1 ∧
          (∀ k : Nat,
            (P {omega : Omega | (busyStarts omega).ncard = k + 1}).toReal =
              p * (1 - p) ^ k) ∧
          ∀ x : Real, 0 ≤ x →
            (P {omega : Omega |
              (∫⁻ t in Set.Ici (0 : Real),
                if W (Real.toNNReal t) omega = 0
                then (1 : ENNReal) else 0 ∂volume)
                ≤ ENNReal.ofReal x}).toReal =
              1 - Real.exp (-phi * x)

noncomputable def certificate_ex4_6_iii : Prop :=
  ∀ {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hBV : L.BoundedVariation)
    (lambda mu : Real) (hlambda : 0 < lambda)
    (hmu : lambda < mu)
    (hd : L.drift = 1)
    (hServiceLaw :
      L.ν =
        ((volume : Measure Real).restrict (Set.Iio 0)).withDensity
          (fun y : Real =>
            ENNReal.ofReal (lambda * mu * Real.exp (mu * y)))),
    ∃ stationary : Measure Real,
          IsProbabilityMeasure stationary ∧
          stationary =
            ENNReal.ofReal (1 - lambda / mu) •
              ((Measure.dirac (0 : Real)) +
                ((volume : Measure Real).restrict (Set.Ioi 0)).withDensity
                  (fun x : Real =>
                    ENNReal.ofReal (lambda * Real.exp (-(mu - lambda) * x)))) ∧
          (∀ f : BoundedContinuousFunction Real Real,
            let supX : NNReal -> Omega -> Real := fun t omega =>
              sSup ((fun s : NNReal => L.X s omega) '' Set.Iic t)
            let W : NNReal -> Omega -> Real := fun t omega =>
              supX t omega - L.X t omega
            Tendsto
              (fun t : NNReal => ∫ omega, f (W t omega) ∂P)
              atTop (nhds (∫ x : Real, f x ∂stationary)))

/-- All textbook subparts of Exercise 4.6 are required, with none silently omitted. -/
noncomputable def certificate_exercise_4_6 : Prop :=
    certificate_ex4_6_i ∧
    certificate_ex4_6_ii ∧
    certificate_ex4_6_iii

end Kyprianou.Ch04


