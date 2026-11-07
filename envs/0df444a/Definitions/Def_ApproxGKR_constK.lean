-- Prove2me | Definitions.Def_ApproxGKR_constK
-- name    : ApproxGKR_constK
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:27:04.823246+00:00
-- url     : https://prove2.me/theorems/3c12e4f4-cd4f-4b9c-9e00-4805602daf67
-- title:
--   The constants $R,U,W,C^*,K$ of (C.7)
-- statement:
--   From $h$, $m=\max_i m_i$ and the bounds $B_V,B_W$ the protocol uses
--   $$R=h^mB_V,\quad U=R+1,\quad W=2B_W,\quad C^*=h^{3m}W(2R+R^2)+1,\quad K=W(2+U+R).$$
--   $R$ bounds $\widetilde V_{i+1}$ on the unit torus and $U$ the claimed evaluations; $C^*$ bounds the coefficients of the round polynomials; $K$ controls how errors in the two claimed evaluations change the gate expression (eq. (C.9)). The verifier rejects coefficients of modulus greater than $C^*$ and claimed evaluations of modulus greater than $U$.
-- source:
--   Das, Gupta, Mondal, More, Delegating Computation with Approximate Arithmetic: Interactive Proofs for Wizards (manuscript, sha256 78b2a36b…), §C.1, eq. (C.7), p.32

import Mathlib

namespace ApproxGKR

/-- `R = h^m B_V` (eq. (C.7), p.32): bounds `Ṽ_{i+1}` on the unit torus.

Das, Gupta, Mondal, More, *Delegating Computation with Approximate Arithmetic* (manuscript,
sha256 78b2a36b…), §C.1, eq. (C.7), p.32. -/
noncomputable def constR (h m BV : ℕ) : ℝ := (h : ℝ) ^ m * BV

/-- `U = R + 1` (eq. (C.7)): the magnitude bound on claimed evaluations. -/
noncomputable def constU (h m BV : ℕ) : ℝ := constR h m BV + 1

/-- `W = 2B_W` (eq. (C.7)). -/
noncomputable def constW (BW : ℕ) : ℝ := 2 * BW

/-- `C* = h^{3m} W (2R + R²) + 1` (eq. (C.7)): the magnitude bound on round-polynomial
coefficients. -/
noncomputable def constCstar (h m BV BW : ℕ) : ℝ :=
  (h : ℝ) ^ (3 * m) * constW BW * (2 * constR h m BV + constR h m BV ^ 2) + 1

/-- `K = W(2 + U + R)` (eq. (C.7), p.32): "`K` bounds how much errors in the two evaluations of
`Ṽᵢ₊₁` can change `w⁺ᵢ(aᵢ + bᵢ) + w×ᵢ aᵢbᵢ`".

**Formalization Note** All five constants of (C.7) are real numbers computed from the natural
parameters `h`, `m = max_i m_i`, `B_V`, `B_W`. -/
noncomputable def constK (h m BV BW : ℕ) : ℝ :=
  constW BW * (2 + constU h m BV + constR h m BV)

end ApproxGKR


