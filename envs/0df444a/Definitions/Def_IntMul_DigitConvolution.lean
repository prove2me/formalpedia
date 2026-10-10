-- Prove2me | Definitions.Def_IntMul_DigitConvolution
-- name    : IntMul_DigitConvolution
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-10T08:41:16.013489+00:00
-- url     : https://prove2.me/theorems/f84bda8a-5e7c-43ac-b517-fccd39f028d5
-- title:
--   Exact binary block digits and integer convolution polynomial
-- statement:
--   For a campaign-model big-endian binary word x and block width B, defines its j-th least-significant binary block, its natural integer digit, its block count ceil(|x|/B), and its exact natural-coefficient digit polynomial. Short high blocks and leading zero blocks are retained; later blocks are empty. Evaluating at base 2^B, coefficient bounds, and convolution correctness are separate theorem obligations. This is a mathematical encoding, not a machine transition routine.
-- source:
--   Original exact digit encoding supporting the HvdH integer multiplication construction in the campaign MultitapeTM word model. Written by Codex.

import Definitions.Def_IntMul_MultitapeModel
import Definitions.Def_IntMul_BinaryAdder
import Mathlib.Algebra.Polynomial.Eval.Defs

namespace IntMul.DigitConvolution

/-- The j-th least-significant block of a campaign-model big-endian word.
The final block may be short; all later blocks are empty. -/
def chunk (B : ℕ) (x : List Bool) (j : ℕ) : List Bool :=
  ((x.reverse.drop (j*B)).take B).reverse

def digit (B : ℕ) (x : List Bool) (j : ℕ) : ℕ := val (chunk B x j)

/-- Number of possibly nonzero blocks, retaining leading zero blocks. -/
def blockCount (B : ℕ) (x : List Bool) : ℕ := (x.length+B-1)/B

/-- Exact integer digit polynomial with base 2^B, prior to carries. -/
noncomputable def polynomial (B : ℕ) (x : List Bool) : Polynomial ℕ :=
  ∑ j ∈ Finset.range (blockCount B x), Polynomial.monomial j (digit B x j)

end IntMul.DigitConvolution


