-- Prove2me | Definitions.Def_Kyprianou_Ch06_certificate_exercise_6_2
-- name    : Kyprianou_Ch06_certificate_exercise_6_2
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-15T22:24:49.96563+00:00
-- url     : https://prove2.me/theorems/35a9e688-87be-42b9-afa6-7f667bf9075f
-- title:
--   Full quantified certificate for exercise:6.2
-- statement:
--   Exact fully quantified source theorem/exercise as a Prop, generated from the authoritative live theorem telescope and target with no conclusion weakening.
-- source:
--   Kyprianou (2006), Exercise 6.2(i)–(iii), printed p. 175; physical PDF p. 93.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_RegularityAtFirstEntrance
import Definitions.Def_Kyprianou_Ch06_RealLevyLawAndRegularityIntegrals
import Definitions.Def_Kyprianou_Ch06_LevyKhintchineTriple
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch06

/-- Closed, full quantified source proposition from spectrallyNegativeUnboundedVariationFirstPassage. -/
def certificate_exercise_6_2 : Prop :=
  ∀ {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → Real)
    (b : Real) (sigma2 : NNReal) (nu : Measure Real)
    (psi : NNReal → Real) (Phi : NNReal → NNReal)
    (kill drift : NNReal) (ladderJump : Measure NNReal)
    (e : Omega → NNReal) (q : Real)
    (hX : IsRealLevyProcess P X)
    (hTriplet : IsLevyKhintchineTriplet P X b sigma2 nu)
    (hNoPositiveJumps : nu (Set.Ioi 0) = 0)
    (hUnboundedVariation : ¬ (sigma2 = 0 ∧
      (∫⁻ y in {y : Real | |y| < 1},
        ENNReal.ofReal |y| ∂nu) < ⊤))
    (hLaplace : ∀ (t lambda : NNReal),
      (∫ omega,
        Real.exp ((lambda : Real) * X t omega) ∂P) =
          Real.exp ((t : Real) * psi lambda))
    (hRightInverse : ∀ a : NNReal,
      psi (Phi a) = (a : Real))
    (hLadderMeasure : ladderJump {0} = 0 ∧
      (∫⁻ y : NNReal, ENNReal.ofReal (min 1 (y : Real))
        ∂ladderJump) < ⊤)
    (hLadderExponent : ∀ a : NNReal,
      (Phi a : Real) = (kill : Real) +
        (drift : Real) * (a : Real) +
        (∫⁻ y : NNReal,
          ENNReal.ofReal
            (1 - Real.exp (-(a : Real) * (y : Real)))
          ∂ladderJump).toReal)
    (hPassageTransform : ∀ (a x : NNReal),
      (∫ omega,
        if firstEntranceTime X 0 (Set.Ioi (x : Real)) omega = ⊤
        then (0 : Real)
        else Real.exp (-(a : Real) *
          (↑((firstEntranceTime X 0
             (Set.Ioi (x : Real)) omega).untopD 0) : Real)) ∂P) =
        Real.exp (-(x : Real) * (Phi a : Real)))
    (hq : 0 < q)
    (hExp : ∀ t : NNReal,
      P {omega | t < e omega} =
        ENNReal.ofReal (Real.exp (-q * (t : Real))))
    (hIndependent : ∀ (k : Nat) (times : Fin k → NNReal)
      (A : Fin k → Set Real) (B : Set NNReal),
      (∀ i, MeasurableSet (A i)) → MeasurableSet B →
      P {omega | e omega ∈ B ∧
        (∀ i : Fin k, X (times i) omega ∈ A i)} =
        P {omega | e omega ∈ B} *
        P {omega | ∀ i : Fin k, X (times i) omega ∈ A i}),
    (drift = 0) ∧
    (∀ᵐ omega ∂P,
      Tendsto (fun x : NNReal =>
        (firstEntranceTime X 0 (Set.Ioi (x : Real))
          omega).untopD 0 / x)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) ∧
    (∀ᵐ omega ∂P,
      ∀ M : Real, ∀ delta : NNReal, 0 < delta →
        ∃ t : NNReal, 0 < t ∧ t < delta ∧
          M < X t omega / (t : Real)) ∧
    IsRegularFor P X 0 (Set.Ioi 0) ∧
    ladderJump (Set.Ioi 0) = ⊤ ∧
    Tendsto (fun theta : Real =>
      ∫ omega,
        Real.exp (theta *
          sInf ((fun s : NNReal => X s omega) ''
            Set.Icc 0 (e omega))) ∂P)
      atTop (nhds 0)

end Kyprianou.Ch06


