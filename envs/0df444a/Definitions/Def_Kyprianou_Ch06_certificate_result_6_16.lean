-- Prove2me | Definitions.Def_Kyprianou_Ch06_certificate_result_6_16
-- name    : Kyprianou_Ch06_certificate_result_6_16
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-15T22:22:18.257639+00:00
-- url     : https://prove2.me/theorems/1bdbcbae-d993-46e5-80ab-bbafa51dee86
-- title:
--   Full quantified certificate for result:6.16
-- statement:
--   Exact fully quantified source theorem/exercise as a Prop, generated from the authoritative live theorem telescope and target with no conclusion weakening.
-- source:
--   Kyprianou (2006), Theorem 6.16(i)–(iv), printed pp. 158–159; physical PDF p. 84; proof pp. 161–167.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_IndexedExcursion
import Definitions.Def_Kyprianou_Ch06_AdmissibleLocalTime
import Definitions.Def_Kyprianou_Ch06_RealLevyLawAndRegularityIntegrals
import Definitions.Def_Kyprianou_Ch06_RunningMaximumAndContact
import Definitions.Def_Kyprianou_Ch06_AdmissibleWienerHopfFactor
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch06

/-- Closed, full quantified source proposition from wienerHopfFactorisationAllFourParts. -/
def certificate_result_6_16 : Prop :=
  ∀ {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → Real)
    (F : NNReal → MeasurableSpace Omega)
    (Lup Ldown : NNReal → Omega → NNReal)
    (e : Omega → NNReal) (p : Real)
    (psi : Real → Complex)
    (kappa kappaHat : Complex → Complex → Complex)
    (hp : 0 < p)
    (hX : IsRealLevyProcess P X)
    (hNonCompound : ¬ IsCompoundPoissonProcess P X)
    (hLup : IsAdmissibleLocalTimeAtMaximum P F X Lup)
    (hLdown :
      IsAdmissibleLocalTimeAtMaximum P F
        (fun t omega => -X t omega) Ldown)
    (hExp : ∀ t : NNReal,
      P {omega | t < e omega} =
        ENNReal.ofReal (Real.exp (-p * (t : Real))))
    (hExpIndependent : ∀ (m : Nat) (times : Fin m → NNReal)
      (A : Fin m → Set Real) (B : Set NNReal),
      (∀ i, MeasurableSet (A i)) → MeasurableSet B →
      P {omega | e omega ∈ B ∧
        (∀ i : Fin m, X (times i) omega ∈ A i)} =
        P {omega | e omega ∈ B} *
        P {omega | ∀ i : Fin m, X (times i) omega ∈ A i})
    (hPsi : ∀ (t : NNReal) (theta : Real),
      (∫ omega,
        Complex.exp (Complex.I *
          (↑(theta * X t omega) : Complex)) ∂P) =
        Complex.exp (-(↑(t : Real) : Complex) * psi theta))
    (hKappa : ∀ (alpha beta : Complex),
      0 ≤ alpha.re → 0 ≤ beta.re → ∀ t : NNReal,
      (∫ omega,
        let tau := inverseLocalTime Lup t omega
        if tau = ⊤ then (0 : Complex)
        else Complex.exp (
          -alpha * (↑((tau.untopD 0 : NNReal) : Real) : Complex) -
          beta * (↑(runningMaximum X (tau.untopD 0) omega) : Complex))
          ∂P) =
        Complex.exp (-(↑(t : Real) : Complex) * kappa alpha beta))
    (hKappaHat : ∀ (alpha beta : Complex),
      0 ≤ alpha.re → 0 ≤ beta.re → ∀ t : NNReal,
      (∫ omega,
        let tau := inverseLocalTime Ldown t omega
        if tau = ⊤ then (0 : Complex)
        else Complex.exp (
          -alpha * (↑((tau.untopD 0 : NNReal) : Real) : Complex) -
          beta * (↑(runningMaximum (fun s w => -X s w)
            (tau.untopD 0) omega) : Complex))
          ∂P) =
        Complex.exp (-(↑(t : Real) : Complex) * kappaHat alpha beta))
    (hKappaHolomorphic : ∀ alpha : Complex, 0 < alpha.re →
      DifferentiableOn Complex (fun beta => kappa alpha beta)
        {beta : Complex | 0 < beta.re})
    (hKappaHatHolomorphic : ∀ alpha : Complex, 0 < alpha.re →
      DifferentiableOn Complex (fun beta => kappaHat alpha beta)
        {beta : Complex | 0 < beta.re})
    (hKappaContinuous : ContinuousOn
      (fun ab : Complex × Complex => kappa ab.1 ab.2)
      {ab | 0 ≤ ab.1.re ∧ 0 ≤ ab.2.re})
    (hKappaHatContinuous : ContinuousOn
      (fun ab : Complex × Complex => kappaHat ab.1 ab.2)
      {ab | 0 ≤ ab.1.re ∧ 0 ≤ ab.2.re}),
    let G : Omega → NNReal := fun omega =>
      lastEpochAtRunningMaximum X (e omega) omega
    let high : Omega → Real := fun omega =>
      runningMaximum X (e omega) omega
    let positivePair : Omega → NNReal × Real := fun omega =>
      (G omega, high omega)
    let negativePair : Omega → NNReal × Real := fun omega =>
      (e omega - G omega, X (e omega) omega - high omega)
    let muPlus : Measure (NNReal × Real) :=
      Measure.map positivePair P
    let muMinus : Measure (NNReal × Real) :=
      Measure.map negativePair P
    -- (i) Spatial support, infinite divisibility, and independence
    (IsAdmissibleWienerHopfFactor true muPlus ∧
     IsAdmissibleWienerHopfFactor false muMinus ∧
     (∀ A B : Set (NNReal × Real),
       MeasurableSet A → MeasurableSet B →
       P {omega | positivePair omega ∈ A ∧
         negativePair omega ∈ B} =
         P {omega | positivePair omega ∈ A} *
         P {omega | negativePair omega ∈ B}) ∧
     (∀ (vartheta theta : Real),
       (∫ omega,
         Complex.exp (Complex.I *
           (↑(vartheta * (G omega : Real) +
             theta * high omega) : Complex)) ∂P) *
       (∫ omega,
         Complex.exp (Complex.I *
           (↑(vartheta * (e omega - G omega : NNReal) +
             theta * (X (e omega) omega - high omega)) : Complex)) ∂P) =
         (↑p : Complex) /
           ((↑p : Complex) -
             Complex.I * (↑vartheta : Complex) + psi theta))) ∧
    -- (ii) Analytically continued ascending and descending ladder factors
    ((∀ alpha beta : Complex, 0 ≤ alpha.re → 0 ≤ beta.re →
       kappa ((↑p : Complex) + alpha) beta ≠ 0 ∧
       kappaHat ((↑p : Complex) + alpha) beta ≠ 0 ∧
       (∫ omega,
         Complex.exp (-alpha * (↑(G omega : Real) : Complex) -
           beta * (↑(high omega) : Complex)) ∂P) =
         kappa (↑p : Complex) 0 /
           kappa ((↑p : Complex) + alpha) beta ∧
       (∫ omega,
         Complex.exp (-alpha *
           (↑((e omega - G omega : NNReal) : Real) : Complex) +
           beta * (↑(X (e omega) omega - high omega) : Complex))
           ∂P) =
         kappaHat (↑p : Complex) 0 /
           kappaHat ((↑p : Complex) + alpha) beta)) ∧
    -- (iii) Both complete spatially signed Frullani formulae
    (∃ kPos kNeg : Real, 0 < kPos ∧ 0 < kNeg ∧
       (∀ alpha beta : Real, 0 < alpha → 0 ≤ beta →
         kappa (↑alpha : Complex) (↑beta : Complex) =
           (↑kPos : Complex) * Complex.exp (
             ∫ t in Set.Ioi (0 : Real),
               ∫ omega,
                 if 0 < X t.toNNReal omega then
                   (Complex.exp (↑(-t) : Complex) -
                     Complex.exp (
                       -((↑alpha : Complex) * (↑t : Complex)) -
                       ((↑beta : Complex) *
                         (↑(X t.toNNReal omega) : Complex)))) /
                     (↑t : Complex)
                 else (0 : Complex) ∂P ∂volume) ∧
       (∀ alpha beta : Real, 0 < alpha → 0 ≤ beta →
         kappaHat (↑alpha : Complex) (↑beta : Complex) =
           (↑kNeg : Complex) * Complex.exp (
             ∫ t in Set.Ioi (0 : Real),
               ∫ omega,
                 if X t.toNNReal omega < 0 then
                   (Complex.exp (↑(-t) : Complex) -
                     Complex.exp (
                       -((↑alpha : Complex) * (↑t : Complex)) +
                       ((↑beta : Complex) *
                         (↑(X t.toNNReal omega) : Complex)))) /
                     (↑t : Complex)
                 else (0 : Complex) ∂P ∂volume)))) ∧
    -- (iv) Boundary characteristic exponent factorisation
    (∃ k : Real, 0 < k ∧
       ∀ theta : Real,
         (↑k : Complex) * psi theta =
           kappa 0 (-Complex.I * (↑theta : Complex)) *
             kappaHat 0 (Complex.I * (↑theta : Complex)))

end Kyprianou.Ch06


