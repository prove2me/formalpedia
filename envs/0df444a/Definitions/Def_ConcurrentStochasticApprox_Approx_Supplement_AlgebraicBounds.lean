-- Prove2me | Definitions.Def_ConcurrentStochasticApprox_Approx_Supplement_AlgebraicBounds
-- name    : ConcurrentStochasticApprox_Approx_Supplement_AlgebraicBounds
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T17:30:30.748772+00:00
-- url     : https://prove2.me/theorems/5ea933e7-f030-4b3a-8efe-2aaf067c4dc4
-- title:
--   Lemmas 8.3–8.4 — Exact coefficient and threshold exponents
-- statement:
--   For natural numbers $n,m,B_Q,B_{\mathrm{inp}}$, define the base-two ceiling-logarithm exponents
--   $$
--   B_{\mathrm{coef}}=\left\lceil\log_2\left(4nm^n(\lceil\log_2 n\rceil+n\lceil\log_2 m\rceil+B_Q+3)\right)\right\rceil,
--   $$
--   $$
--   B_\alpha=B_{\mathrm{coef}}+\left\lceil\log_2\left(m^n(B_{\mathrm{inp}}+3)\right)\right\rceil+1.
--   $$
--   The theorems use $n\ge1$ and $m=\max(|A|,|B|)\ge1$, so every logarithm argument is positive. The total natural-number definitions also assign values to zero arguments using Mathlib's ceiling logarithm convention. These two exponents are shared by the algebraicity and threshold-separation statements.
-- source:
--   Ali Asadi, Krishnendu Chatterjee, STOC 2027 submission #285 (October 2026), Lemmas 8.3–8.4, printed 36 (PDF 38)

import Mathlib

/-! Lemmas 8.3–8.4, printed p. 36 (PDF 38). Base-two ceiling logarithms,
with the same `Nat.clog 2` convention as the published Lemma 7.2.
-/

namespace ConcurrentStochasticApprox.Approx.Supplement

/-- Coefficient exponent with `m = max mA mB`. -/
def bCoef (n m BQ : ℕ) : ℕ :=
  Nat.clog 2 (4 * n * m ^ n * (Nat.clog 2 n + n * Nat.clog 2 m + BQ + 3))

/-- Threshold separation exponent. -/
def bAlpha (n m BQ Binp : ℕ) : ℕ :=
  bCoef n m BQ + Nat.clog 2 (m ^ n * (Binp + 3)) + 1

end ConcurrentStochasticApprox.Approx.Supplement


