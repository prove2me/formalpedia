-- Prove2me | Definitions.Def_Kyprianou_Ch06_LevyKhintchineTriple
-- name    : Kyprianou_Ch06_LevyKhintchineTriple
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-15T22:07:55.275633+00:00
-- url     : https://prove2.me/theorems/d84ee6e4-1860-477e-8787-a0b0dec15a17
-- title:
--   General real Lévy–Khintchine triplet and marginal law
-- statement:
--   Defines a real Lévy–Khintchine triplet with drift under small-jump truncation, Gaussian variance and a Lévy measure, constrained by the characteristic function of every marginal. Used to identify the bounded-variation drift and the Lévy-measure entrance test in Theorem 6.5.
-- source:
--   Kyprianou (2006), Chapter 2 equation (2.21) and Chapter 6 Theorem 6.5 printed pp. 142–143.

import Mathlib
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch06

/-- The characteristic Lévy-Khintchine triple of a real Lévy process:
general truncated drift b, Gaussian variance sigma2 and a Lévy measure nu.
This is an identity for every time marginal and Fourier variable. -/
def IsLevyKhintchineTriplet
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (X : NNReal → Omega → Real)
    (b : Real) (sigma2 : NNReal) (nu : Measure Real) : Prop :=
  nu {0} = 0 ∧
  (∫⁻ x : Real, ENNReal.ofReal (min 1 (x ^ 2)) ∂nu) < ⊤ ∧
  (∀ theta : Real,
    Integrable (fun x : Real =>
      Complex.exp (Complex.I * (↑(theta * x) : Complex)) - 1 -
      (if |x| < 1 then Complex.I * (↑(theta * x) : Complex) else 0)) nu) ∧
  (∀ (t : NNReal) (theta : Real),
    (∫ omega,
      Complex.exp (Complex.I * (↑(theta * X t omega) : Complex)) ∂P) =
    Complex.exp ((↑(t : Real) : Complex) *
      (Complex.I * (↑(b * theta) : Complex) -
        (↑(((sigma2 : Real) * theta ^ 2) / (2 : Real)) : Complex) +
        ∫ x : Real,
          (Complex.exp (Complex.I * (↑(theta * x) : Complex)) - 1 -
            (if |x| < 1
             then Complex.I * (↑(theta * x) : Complex) else 0)) ∂nu)))

end Kyprianou.Ch06


