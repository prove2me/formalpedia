-- Prove2me | Definitions.Def_KTUnitary_Synth_fixedPoint
-- name    : KTUnitary_Synth_fixedPoint
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:23:44.037811+00:00
-- url     : https://prove2.me/theorems/58cfac41-604d-4d9d-9239-b54f0f3c584a
-- title:
--   Fixed-point binary decoding of a bit string
-- statement:
--   A string of the form $1^k\,0\,s\,m_0 m_1\cdots m_r$ denotes the dyadic rational
--   $$\mathrm{fp}(1^k 0 s m_0\cdots m_r)=(-1)^s\,\frac{\sum_{j=0}^r m_j 2^j}{2^k},$$
--   with $k$ fraction bits, a sign bit $s$ and the magnitude in little-endian binary. A string with no terminating $0$ after the leading ones, or with no sign bit, denotes $0$.
--
--   Every dyadic rational has such a code, of length comparable to its usual fixed-point representation. This is the decoding of the outputs $\phi$ of the approximation schemes (FPTEAS, FPSEAS, FPUSEAS) and of the numbers $\phi,\varepsilon$ in the promise problem $f\mathrm{Apx}$.
--
--   **Formalization Note** The paper fixes no concrete format ("encoded in fixed-point binary"); any standard choice gives the same polynomial bounds.
-- source:
--   Kretschmer, Tang, Unitary Complexity in Polynomial Space, arXiv:2610.03705 (revision of 2026-10-31), Definition 4.1, p. 14

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Complexity

open QAlgorithms.Complexity

namespace KTUnitary.Synth

/-- **Fixed-point binary decoding** (Kretschmer, Tang, *Unitary Complexity in Polynomial Space*, arXiv:2610.03705 (revision of 2026-10-31), Definition 4.1, p. 14: "where `ϕ` and `ε` are encoded
in fixed-point binary"). The string `1^k 0 s m₀ m₁ … m_r` denotes the dyadic rational
`(−1)^s · (m₀ + 2 m₁ + ⋯ + 2^r m_r) / 2^k`: `k` fraction bits, a sign bit `s`, and the magnitude
in little-endian binary. A string without the terminating `0` of the prefix, or without a sign
bit, denotes `0`.

**Formalization Note** The paper fixes no concrete format. Every dyadic rational has a code of
length `k + 2 + (number of magnitude bits)`, which is the length of the usual fixed-point
representation up to a constant factor, so time and space bounds polynomial in the code length
are the paper's bounds. -/
def fixedPoint (s : Str) : ℚ :=
  let k := (s.takeWhile id).length
  match s.drop (k + 1) with
  | [] => 0
  | sgn :: mag => (if sgn then -1 else 1) * (Nat.ofDigits 2 (mag.map Bool.toNat) : ℚ) / 2 ^ k

end KTUnitary.Synth


