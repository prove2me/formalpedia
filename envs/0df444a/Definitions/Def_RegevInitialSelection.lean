-- Prove2me | Definitions.Def_RegevInitialSelection
-- name    : RegevInitialSelection
-- status  : Definition
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-15T10:34:21.779891+00:00
-- url     : https://prove2.me/theorems/e69c3a40-4685-4c57-9e45-c98948eb5e65
-- title:
--   Binary initializer base and initial-to-terminal width selection
-- statement:
--   For binary-coded integer rows, rational target width $r$ and natural dimension $n$, these definitions compute the binary natural base
--
--   $$
--   b=n+2+\lceil r(n+2)\rceil_+,
--   $$
--
--   the rational initial width $W=b(1+\sum_{i,j}|B_{ij}|)$, and the first dyadic-crossing index and selected width from `RegevDyadicSchedule`. The output is the triple $(b,k,u)$. These are total functions, including on malformed row lists and nonpositive widths; the correctness theorem supplies the conditions under which they have the desired interpretation.
--
--   The initial-width expression matches the arithmetic expression of the local original-basis initializer. A separate parser and sampler composition is needed to identify actual platform inputs and the initialized output law.
--
--   On inputs with no satisfying scan index, the underlying dyadic scan uses its documented fallback index and capped exponent.
-- source:
--   Oded Regev, On Lattices, Learning with Errors, Random Linear Codes, and Cryptography, https://cims.nyu.edu/~regev/papers/qcrypto.pdf, Theorem 3.1 and Lemmas 3.2, 3.3 and 3.14. This is an explicit binary initializer-width interface for the fixed-family formalization, not a definition stated in the source.

import Definitions.Def_RegevDyadicSchedule

set_option autoImplicit false
namespace InfoLossLAR.WorstCase.NativeDyadicSchedule

abbrev InitialInput := (List (List ℤ) × ℚ) × ℕ

/-- Sum of absolute integer entries in one binary-coded row. -/
def initialRowMass (row : List ℤ) : ℚ := (row.map (fun value => (value.natAbs : ℚ))).sum

/-- The basis-entry envelope used by the native initializer. -/
def initialEntryMass (rows : List (List ℤ)) : ℚ := (rows.map initialRowMass).sum

/-- Binary natural base; no unary expansion of its value is required. -/
def initialBase (r : ℚ) (n : ℕ) : ℕ :=
  n+2 + ⌈r*((n+2 : ℕ) : ℚ)⌉₊

/-- The width used by the local original-basis initializer. -/
def initialWidth (rows : List (List ℤ)) (base : ℕ) : ℚ :=
  (base : ℚ)*(1+initialEntryMass rows)

def initialRequest (x : InitialInput) : Input :=
  ((initialWidth x.1.1 (initialBase x.1.2 x.2),x.1.2),x.2)

/-- Return the binary base, the first crossing index and selected width. -/
def initialSelection (x : InitialInput) : ℕ × (ℕ × ℚ) :=
  (initialBase x.1.2 x.2,
    (crossingIndex (initialRequest x),selectedWidth (initialRequest x)))

end InfoLossLAR.WorstCase.NativeDyadicSchedule


