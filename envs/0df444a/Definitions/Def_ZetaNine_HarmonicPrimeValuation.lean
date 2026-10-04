-- Prove2me | Definitions.Def_ZetaNine_HarmonicPrimeValuation
-- name    : ZetaNine_HarmonicPrimeValuation
-- status  : Definition
-- author  : @Yuxuan Xu
-- created : 2026-10-02T14:34:57.746323+00:00
-- url     : https://prove2.me/theorems/11984167-2e2e-490b-948a-9f691338b59e
-- title:
--   Harmonic nonmultiple remainder and explicit finite numerator exception product
-- statement:
--   For natural $s,N,p$, let $H_N^{(s)}=\sum_{j=1}^{N}j^{-s}$ be the rational generalized harmonic sum. Define
--
--   $$U_{s,N,p}=\sum_{\substack{1\le j\le N\\p\nmid j}}j^{-s},\qquad E_{s,K}=\prod_{k=1}^{K}\left|\operatorname{num}(H_k^{(s)})\right|.$$
--
--   The numerator is the reduced rational numerator and the product is one when $K=0$. Both objects are defined for all natural parameters. The module adds only these two finite expressions to the existing harmonic definition module; it contains no primality, unit, valuation, limit or PNT assertion.
-- source:
--   https://github.com/Anchen0823/zeta9-research-notes/releases/tag/research-2026-10-02; research/harmonic-denominator-stability-2026-10-01.md, sections 1–2, equations (1)–(2) and the finite-prime lower-bound argument preceding equation (3).

import Definitions.Def_ZetaNine_HarmonicStability

set_option autoImplicit false
open scoped BigOperators

namespace ZetaNine.HarmonicStability

/-- The sum of the actual harmonic terms whose index is not divisible by p. -/
def primeRemainder (s N p : ℕ) : ℚ :=
  ∑ j ∈ (Finset.Icc 1 N).filter (fun j => ¬ p ∣ j), 1 / (j : ℚ) ^ s

/-- Product of the absolute reduced numerators of the actual first K harmonic prefixes. -/
def harmonicExceptionalProduct (s K : ℕ) : ℕ :=
  ∏ k ∈ Finset.Icc 1 K, (harmonicPower s k).num.natAbs

end ZetaNine.HarmonicStability


