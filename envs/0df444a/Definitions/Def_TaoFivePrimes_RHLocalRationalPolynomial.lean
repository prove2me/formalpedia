-- Prove2me | Definitions.Def_TaoFivePrimes_RHLocalRationalPolynomial
-- name    : TaoFivePrimes_RHLocalRationalPolynomial
-- status  : Definition
-- author  : @Johan Mercedes
-- created : 2026-10-27T20:22:53.750881+00:00
-- url     : https://prove2.me/theorems/948030a9-cc22-4b41-a1c8-96174eaca13e
-- title:
--   Local xi polynomial with selectable integer denominator
-- statement:
--   Given integer coefficients $v_n$, a positive integer denominator $Q$, a term count $N$, and real center height $T$, this function evaluates
--
--   $$
--   P(s)=\sum_{n=0}^{N-1}\frac{v_n}{Q}\bigl(-i(s-\tfrac12-iT)\bigr)^n.
--   $$
--
--   Missing list entries are zero. The Lean function is defined for every natural $Q$, including zero under Lean's total division convention. This data interface asserts no analytic error bound.
-- source:
--   Exact integer translation of the proved 304 Mellin-moment candidates, using the xi/Taylor framework of sometik179, https://prove2.me/submissions/c9908072-d99a-4431-aad8-a72c6352619a; theta/Mellin foundations are due to Gabewhigham. The height-119 and 10^12-denominator data are new.

/- Scale-parametric local polynomial for finite zeta-height certificates.
The xi/Taylor method is due to sometik179, with theta/Mellin foundations by
Gabewhigham. This definition does not assert any analytic approximation. -/
import Definitions.Def_TaoFivePrimes_RH100To1000LocalAnalyticModel
open Complex Finset
noncomputable def TaoFivePrimes_RHLocalRationalPolynomial
    (v : List ℤ) (Q N : ℕ) (T : ℝ) (s : ℂ) : ℂ :=
  ∑ n ∈ range N, ((v.getD n 0:ℝ)/(Q:ℝ):ℂ)*
    (-Complex.I*(s-RH1000Analytic.CertifiedLocalXi.center T))^n


