-- Prove2me | Definitions.Def_Polynomial_BinomialResidue
-- name    : Polynomial_BinomialResidue
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:00:12.300065+00:00
-- url     : https://prove2.me/theorems/8bc4d7cf-961e-43f0-8d76-33845571a0d7
-- title:
--   Modular evaluation of products of binomials
-- statement:
--   The file defines bounded modular arithmetic for evaluating factors $1-X^e$ at an integer base modulo a power of that base, iterating this operation over lists of exponent blocks, and computing modular powers without large intermediate numerals. It also defines the corresponding polynomial $$∏_{B}∏_{e∈B}(1-X^e)∈ℤ[X].$$ This is technical infrastructure for kernel-checked coefficient certificates.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
set_option autoImplicit false

namespace Polynomial

/-- Multiplication by a binomial, evaluated at an integer and reduced
modulo a power of that base. -/
def binomialResidue (base count value exponent : ℕ) : ℕ :=
  if exponent < count then
    let modulus := base ^ count
    let shifted := (value * base ^ exponent) % modulus
    if shifted ≤ value then value - shifted else value + modulus - shifted
  else value

/-- Evaluate a list of small blocks of binomials using modular arithmetic. -/
def binomialBlocksResidue (base count : ℕ) (blocks : List (List ℕ)) : ℕ :=
  blocks.foldl (fun value es => es.foldl (binomialResidue base count) value) 1

/-- Modular powers keep each intermediate integer within the kernel numeral bound. -/
def residuePower (value exponent modulus : ℕ) : ℕ :=
  (List.range exponent).foldl (fun z _ => z * value % modulus) 1

/-- The polynomial represented by the same blocks. -/
noncomputable def binomialBlocksPolynomial (blocks : List (List ℕ)) : ℤ[X] :=
  (blocks.map fun es => (es.map fun e => (1 - X ^ e : ℤ[X])).prod).prod

end Polynomial


