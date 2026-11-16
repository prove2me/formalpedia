-- Prove2me | Definitions.Def_QiOPoQ_Supplement_PolyBounded2
-- name    : QiOPoQ_Supplement_PolyBounded2
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:04:59.486732+00:00
-- url     : https://prove2.me/theorems/72ef9be3-6a81-4b62-9381-4998bc7cbeb8
-- title:
--   Polynomially bounded and polynomial-time computable functions of two and three numbers
-- statement:
--   Helper notions for Section 6: a function of two or three numbers is polynomially bounded if a polynomial in the sum of its arguments bounds it, and polynomial-time computable if it is computed from the unary codes of its arguments in polynomial time, with unary output. They describe the functions $p_1,p_2,s,N$ of Assumptions 6.2 and 6.3. Polynomially bounded functions of $\lambda$ (widths and lengths) use the published one-variable notion QMAvsQCMAH.PolyBounded.
-- source:
--   Gheorghiu, Gupte, Havlíček, Liu, Verifiable Quantum Advantage and Computation via Quantum Circuit Obfuscation, arXiv:2609.40289 (sha256 fe2f9210…), §6.1, pp.31–32

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_QAlgorithms_ClassicalUnaryInput
import Definitions.Def_QAdvFew_PoQOracle_tup

set_option autoImplicit false

namespace QiOPoQ.Supplement

open QAlgorithms.Complexity QAdvFew.PoQOracle

/-- A function of two numbers bounded by a polynomial in their sum (Gheorghiu, Gupte, Havlíček,
Liu, arXiv:2609.40289, sha256 fe2f9210…, §6.1, pp.31–32: "nonnegative polynomially bounded and
polynomial-time computable functions p1, p2", "polynomially bounded functions s = s(λ, n)").
The one-variable notion ("polynomially bounded width n = n(λ)", "polynomially bounded lengths
N_A, N_B, N_R") is the published `QMAvsQCMAH.PolyBounded`. -/
def PolyBounded2 (f : ℕ → ℕ → ℕ) : Prop := ∃ p : Polynomial ℕ, ∀ a b, f a b ≤ p.eval (a + b)

/-- A function of three numbers bounded by a polynomial in their sum. -/
def PolyBounded3 (f : ℕ → ℕ → ℕ → ℕ) : Prop :=
  ∃ p : Polynomial ℕ, ∀ a b c, f a b c ≤ p.eval (a + b + c)

/-- A function of two numbers computable in polynomial time (inputs and output in unary,
§6.1: "polynomial-time computable functions p1, p2", "s = s(λ, n)"). -/
def PolyTime2 (f : ℕ → ℕ → ℕ) : Prop :=
  ∃ g : Str → Str, PolyTimeComputable g ∧ ∀ a b, g (tup [unary a, unary b]) = unary (f a b)

/-- A function of three numbers computable in polynomial time (inputs and output in unary,
§6.1: "N(λ, n, k)"). -/
def PolyTime3 (f : ℕ → ℕ → ℕ → ℕ) : Prop :=
  ∃ g : Str → Str, PolyTimeComputable g ∧
    ∀ a b c, g (tup [unary a, unary b, unary c]) = unary (f a b c)

end QiOPoQ.Supplement


