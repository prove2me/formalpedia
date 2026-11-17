-- Prove2me | Definitions.Def_N25_GenusFourNumerator
-- name    : N25_GenusFourNumerator
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:00:15.818724+00:00
-- url     : https://prove2.me/theorems/e2725b6f-6dd0-483c-98eb-51b56c39b956
-- title:
--   Genus-four $L$-polynomials from point counts
-- statement:
--   Defines the first four Newton identities relating reciprocal-root power sums $s_1,…,s_4$ to coefficients $a_1,…,a_4$, rewrites them using the point counts $N_r=|C(F_{q^r})|$, and forms the reciprocal degree-eight numerator $L(T)=1+a_1T+…+a_4T^4+qa_3T^5+q^2a_2T^6+q^3a_1T^7+q^4T^8$. It also records the binary and ternary numerators determined by the supplied counts, for use in the good-reduction computation.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
/-! # Reciprocal numerators of genus-four curves

These definitions describe the integer-polynomial calculation from four point
counts. They do not assert a curve-zeta or Jacobian identification.
-/

noncomputable section

namespace N25

/-- The first four Newton identities, with reciprocal-root power sums. -/
def NewtonFourEquations (s₁ s₂ s₃ s₄ a₁ a₂ a₃ a₄ : ℤ) : Prop :=
  a₁ + s₁ = 0 ∧
  2 * a₂ + s₁ * a₁ + s₂ = 0 ∧
  3 * a₃ + s₁ * a₂ + s₂ * a₁ + s₃ = 0 ∧
  4 * a₄ + s₁ * a₃ + s₂ * a₂ + s₃ * a₁ + s₄ = 0

/-- Newton identities expressed directly through four point counts. -/
def CountNewtonFourEquations (q N₁ N₂ N₃ N₄ a₁ a₂ a₃ a₄ : ℤ) : Prop :=
  NewtonFourEquations (q + 1 - N₁) (q ^ 2 + 1 - N₂)
    (q ^ 3 + 1 - N₃) (q ^ 4 + 1 - N₄) a₁ a₂ a₃ a₄

/-- The reciprocal numerator with prescribed first four coefficients. -/
def genusFourNumerator (q a₁ a₂ a₃ a₄ : ℤ) : Polynomial ℤ :=
  1 + Polynomial.C a₁ * Polynomial.X ^ 1 +
    Polynomial.C a₂ * Polynomial.X ^ 2 +
    Polynomial.C a₃ * Polynomial.X ^ 3 +
    Polynomial.C a₄ * Polynomial.X ^ 4 +
    Polynomial.C (q * a₃) * Polynomial.X ^ 5 +
    Polynomial.C (q ^ 2 * a₂) * Polynomial.X ^ 6 +
    Polynomial.C (q ^ 3 * a₁) * Polynomial.X ^ 7 +
    Polynomial.C (q ^ 4) * Polynomial.X ^ 8

namespace Endgame

/-- The binary numerator determined by counts `5,5,20,29`. -/
def binaryLPolynomial25 : Polynomial ℤ :=
  1 + 2 * Polynomial.X + 2 * Polynomial.X ^ 2 +
    5 * Polynomial.X ^ 3 + 11 * Polynomial.X ^ 4 +
    10 * Polynomial.X ^ 5 + 8 * Polynomial.X ^ 6 +
    16 * Polynomial.X ^ 7 + 16 * Polynomial.X ^ 8

/-- The ternary numerator determined by counts `5,5,20,89`. -/
def ternaryLPolynomial25 : Polynomial ℤ :=
  1 + Polynomial.X - 2 * Polynomial.X ^ 2 - 5 * Polynomial.X ^ 3 +
    Polynomial.X ^ 4 - 15 * Polynomial.X ^ 5 - 18 * Polynomial.X ^ 6 +
    27 * Polynomial.X ^ 7 + 81 * Polynomial.X ^ 8

end Endgame
end N25


