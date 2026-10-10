-- Prove2me | Definitions.Def_IntMul_CarryNormalization
-- name    : IntMul_CarryNormalization
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-10T08:51:49.286879+00:00
-- url     : https://prove2.me/theorems/4e7d7a0d-fde8-4c48-a791-ad47dc512148
-- title:
--   Exact low-to-high coefficient carry normalization and binary recovery
-- statement:
--   Defines one low-to-high carry pass on a finite natural coefficient array, retaining one output digit per input coefficient and an explicit final carry. Each step emits (coefficient+carry) modulo the base and updates the carry by division. Defines the product coefficient array of the binary digit polynomials, the output bit word, and carries after every prefix. This is a pure exact recovery algorithm; correctness and finite carry widths are theorem obligations, and physical implementation is separate.
-- source:
--   Original exact carry-recovery interface supporting fixed-tape HvdH multiplication in the campaign model. Written by Codex.

import Definitions.Def_IntMul_DigitConvolution
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Log

namespace IntMul.CarryNormalization

/-- One low-to-high carry pass. Each coefficient contributes one output digit;
the pair retains the final carry explicitly. -/
def scan (base : ℕ) : List ℕ → ℕ → List ℕ × ℕ
  | [], carry => ([],carry)
  | a::as, carry =>
      let rest := scan base as ((a+carry)/base)
      ((a+carry)%base::rest.1,rest.2)

def carryAt (base : ℕ) (as : List ℕ) (carry j : ℕ) : ℕ :=
  (scan base (as.take j) carry).2

/-- Full product coefficient array, retaining enough trailing positions for
exact zero final carry, even when either input has leading zeroes. -/
noncomputable def coefficients (B : ℕ) (x y : List Bool) : List ℕ :=
  (List.range (DigitConvolution.blockCount B x+DigitConvolution.blockCount B y)).map
    fun j => (DigitConvolution.polynomial B x*DigitConvolution.polynomial B y).coeff j

def bits (B : ℕ) (digits : List ℕ) : List Bool :=
  (digits.flatMap fun d => (bin B d).reverse).reverse

noncomputable def productWord (B : ℕ) (x y : List Bool) : List Bool :=
  bits B (scan (2^B) (coefficients B x y) 0).1

end IntMul.CarryNormalization


