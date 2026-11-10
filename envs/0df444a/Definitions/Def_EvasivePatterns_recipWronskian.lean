-- Prove2me | Definitions.Def_EvasivePatterns_recipWronskian
-- name    : EvasivePatterns_recipWronskian
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:26:15.65948+00:00
-- url     : https://prove2.me/theorems/29b6e9e2-2dec-4a6e-8c13-e3f00123d904
-- title:
--   Reciprocal Wronskian $W_Q=Q'Q^*-Q(Q^*)'$
-- statement:
--   For an integer polynomial $Q$ of degree $m$ let $Q^*(z) = z^m Q(z^{-1})$ be its reversal. The **reciprocal Wronskian** is
--   $$
--   W_Q(z) = Q'(z)\,Q^*(z) - Q(z)\,(Q^*)'(z),
--   $$
--   the numerator of $(Q/Q^*)'$. For $P = 01100$, $W_{Q_P}(z) = -z^8 + 4z^5 + 3z^4 + 4z^3 - 1$. The mission uses its **content** $\mathrm{cont}(W_Q)$, the positive gcd of the coefficients (with $\mathrm{cont}(0) = 0$).
--
--   **Formalization Note** $Q^*$ is Mathlib's `Polynomial.reverse`, which is exactly $z^{\deg Q} Q(z^{-1})$; the content is `Polynomial.content`.
-- source:
--   Faro, Marino, Pavone, A Complete Characterization of Eventually Evasive Binary Patterns, manuscript (Nov. 2026; sha256 e91deef3…), §5, display (8), p.7 (PDF p.8), lines 216–220

import Mathlib

namespace EvasivePatterns

/-- **The reciprocal Wronskian `W_Q = Q′ Q^* − Q (Q^*)′`** (display (8)), where
`Q^*(z) = z^m Q(z^{−1})` for an integer polynomial `Q` of degree `m`.

Source: S. Faro, F. P. Marino, A. Pavone, *A Complete Characterization of Eventually Evasive Binary
Patterns*, manuscript (Nov. 2026), §5, display (8), printed p. 7 (PDF p. 8), lines 216–217: "Let
Q^*(z) = z^m Q(z^{−1}) for an integer polynomial of degree m, and put
W_Q(z) = Q′(z)Q^*(z) − Q(z)(Q^*)′(z)."

**Formalization Note** `Q^*` is Mathlib's `Polynomial.reverse` (reflection at `natDegree Q`), which is
exactly `z^m Q(z^{−1})` with `m = deg Q`; `′` is `Polynomial.derivative`. The content
`cont(W_Q)` of the paper (positive gcd of the coefficients, `cont(0) = 0`) is Mathlib's
`Polynomial.content` on `ℤ[X]`. -/
noncomputable def recipWronskian (Q : Polynomial ℤ) : Polynomial ℤ :=
  Polynomial.derivative Q * Q.reverse - Q * Polynomial.derivative Q.reverse

end EvasivePatterns


