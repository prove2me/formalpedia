-- Prove2me | Definitions.Def_SingleInteraction_ThresholdsValid
-- name    : SingleInteraction_ThresholdsValid
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:53:42.029577+00:00
-- url     : https://prove2.me/theorems/4d53066b-baf3-4323-bd87-4861c2b1f6e2
-- title:
--   Thresholds with polynomial precision and inverse-polynomial gap
-- statement:
--   For $n$ qubits and a polynomial exponent $c$, two thresholds $a,b$ are valid when they are binary rationals with positive denominators whose codes have at most $(n+1)^c$ bits, and
--
--   $$b-a\ \ge\ \frac{1}{(n+1)^c}.$$
--
--   This is the clause "two real numbers $a,b$ specified with $\mathrm{poly}(n)$ bits of precision such that $b-a\ge1/\mathrm{poly}(n)$" of the Hamiltonian problems.
--
--   **Formalization Note** One exponent $c$ bounds both the bit length and the inverse gap.
-- source:
--   Hecker, The Complexity of Single-Interaction Hamiltonians, arXiv:2609.39592 (held version, sha256 19ddc444…), Definition 31, pp.29–30; Definition 6, p.17

import Mathlib
import Definitions.Def_ContinuumCoulombHardness

open OAI.ContinuumCoulomb OAI.ContinuumCoulomb.BinaryEncoding

namespace SingleInteraction

/-- The threshold clause of a Hamiltonian promise problem on `n` qubits, for the polynomial exponent
`c` (Hecker, *The Complexity of Single-Interaction Hamiltonians*, arXiv:2609.39592 (held version, sha256 19ddc444…), Definition 31, pp.29–30: "two real numbers `a, b` specified with `poly(n)` bits of
precision such that `b − a ≥ 1/poly(n)`"; Definition 6, p.17, the same clause).

The thresholds are binary rationals `a = p/q`, `b = p'/q'` with positive denominators, whose codes have
at most `(n+1)^c` bits, and `b − a ≥ 1/(n+1)^c`.

**Formalization Note** "`poly(n)`" is the single exponent `c` (one polynomial `(n+1)^c` for the bit
length and the inverse gap); the paper's `poly(n)` for each is dominated by `(n+1)^c` for `c` large.
`(n+1)^c` avoids the degenerate `0^0` at `n = 0`. The thresholds are compared in `ℝ`. -/
def ThresholdsValid (n c : ℕ) (a b : BinaryRational) : Prop :=
  0 < a.denominator ∧ 0 < b.denominator ∧
    (binaryRationalCodec.encode a).length ≤ (n + 1) ^ c ∧
    (binaryRationalCodec.encode b).length ≤ (n + 1) ^ c ∧
    (((n : ℝ) + 1) ^ c)⁻¹ ≤ (b.value : ℝ) - (a.value : ℝ)

/-- Valid thresholds are strictly ordered. -/
theorem ThresholdsValid.lt {n c : ℕ} {a b : BinaryRational} (h : ThresholdsValid n c a b) :
    (a.value : ℝ) < (b.value : ℝ) := by
  have hpos : (0 : ℝ) < (((n : ℝ) + 1) ^ c)⁻¹ := by positivity
  linarith [h.2.2.2.2]

end SingleInteraction


