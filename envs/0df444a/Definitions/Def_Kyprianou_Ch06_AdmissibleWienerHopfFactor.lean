-- Prove2me | Definitions.Def_Kyprianou_Ch06_AdmissibleWienerHopfFactor
-- name    : Kyprianou_Ch06_AdmissibleWienerHopfFactor
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-15T22:10:46.669121+00:00
-- url     : https://prove2.me/theorems/55ae02eb-0b1c-4e4b-a76e-61894301d073
-- title:
--   Admissible infinitely divisible Wiener–Hopf probability factor
-- statement:
--   An admissible bivariate Wiener-Hopf factor is an infinitely divisible probability distribution on nonnegative time and real position, supported spatially on the appropriate nonnegative or nonpositive half-line and with spatial marginal support accumulating at zero. The final condition rules out artificial nonzero translations that would destroy uniqueness while preserving infinite divisibility.
-- source:
--   Kyprianou (2006), Theorem 6.16(i)–(iii) and Corollary 6.19, pp. 158–167, interpreted with admissible half-line factors; Döring et al. (2024) uniqueness analysis.

import Mathlib
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch06

/-- Admissible Wiener-Hopf probability factor for the non-compound-
Poisson case: infinite divisibility, half-line spatial support, and
spatial support accumulating at zero. The latter rules out artificial
opposing deterministic shifts of the factors. -/
def IsAdmissibleWienerHopfFactor
    (positive : Bool) (mu : Measure (NNReal × Real)) : Prop :=
  IsProbabilityMeasure mu ∧
  (mu {z | if positive then 0 ≤ z.2 else z.2 ≤ 0} = 1) ∧
  (∀ eps : Real, 0 < eps →
    0 < mu {z | |z.2| < eps}) ∧
  (∀ n : Nat, 0 < n →
    ∃ nu : Measure (NNReal × Real),
      IsProbabilityMeasure nu ∧
      ∀ (vartheta theta : Real),
        (∫ z : NNReal × Real,
          Complex.exp (Complex.I *
            (↑(vartheta * (z.1 : Real) + theta * z.2) : Complex)) ∂mu) =
          (∫ z : NNReal × Real,
            Complex.exp (Complex.I *
              (↑(vartheta * (z.1 : Real) + theta * z.2) : Complex)) ∂nu) ^ n)

end Kyprianou.Ch06


