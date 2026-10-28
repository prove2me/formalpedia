-- Prove2me | Definitions.Def_D1Bound5_BennettBinomialIntegrality_Definitions
-- name    : D1Bound5_BennettBinomialIntegrality_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T01:32:28.364517+00:00
-- url     : https://prove2.me/theorems/12672041-3b2d-40e4-bf03-3f6b726581b6
-- title:
--   Bennett Binomial Integrality
-- statement:
--   The explicit integer obtained by clearing a half-binomial coefficient. The named objects in this bundle include `bennettScaledHalfInt`, `bennettScaledHalfShiftInt`.
-- source:
--   D1Bound5/BennettBinomialIntegrality.lean, lines 73-76, SHA-256 f95293967308ba92e9451def9a6f848adc0cc2ec40690f494052e3d6316f0262; D1Bound5/BennettBinomialIntegrality.lean, lines 86-90, SHA-256 f95293967308ba92e9451def9a6f848adc0cc2ec40690f494052e3d6316f0262. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.RingTheory.Binomial
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

section
open Finset

namespace D1Bound5

/-!
The integer denominator bounds used in the Bennett residue construction.
The rational half-binomial identity is proved from the actual Catalan and
central-binomial identities in mathlib, then transported to every
characteristic-zero field. No coefficient-integrality premise is assumed.
-/







/-- The explicit integer obtained by clearing a half-binomial coefficient. -/
def bennettScaledHalfInt : ℕ → ℤ
  | 0 => 1
  | n + 1 => (-1) ^ n * 2 * (catalan n : ℤ)



/-- Explicit integer numerator for the shifted half-binomial coefficient.
The finite convolution is Vandermonde with the required powers of four. -/
def bennettScaledHalfShiftInt (k h : ℕ) : ℤ :=
  ∑ uv ∈ Finset.antidiagonal h,
    (4 : ℤ) ^ uv.1 * (k.choose uv.1 : ℤ) * bennettScaledHalfInt uv.2













end D1Bound5
end


