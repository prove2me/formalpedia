-- Prove2me | Definitions.Def_NSWBetter_coinAvgE
-- name    : NSWBetter_coinAvgE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:48:37.892749+00:00
-- url     : https://prove2.me/theorems/b67ce357-0c2e-4429-afa1-ee037c2b1f4d
-- title:
--   Average over coin strings of an extended-real quantity
-- statement:
--   For an extended-real function $f$ of coin strings, $\operatorname{avg}_N f=2^{-N}\sum_{w\in\{0,1\}^N}f(w)\in[-\infty,\infty)$: the expectation over a uniformly random string of $N$ coins. If one string gives $-\infty$, the average is $-\infty$.
-- source:
--   Viswanathan, A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations, arXiv:2607.13340 (held version, sha256 08811cb468c2df39231dca4222c5af94163587c7c83e205e50bbf0b91fc1deb3), Theorem 6.1, p.36 ($\mathbb E[\mathrm{ST}(z)]$)

import Mathlib

namespace NSWBetter

/-- **Expectation over uniform coins, extended reals.**
Viswanathan, *A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations*, arXiv:2607.13340 (held version, sha256 08811cb4…), Theorem 6.1, p.36: "E[ST(z)]".

`coinAvgE N f = 2^(−N) Σ_(w ∈ {0,1}^N) f(w)` in `EReal`; a single `⊥` term (a coin string with expected log welfare `−∞`) makes the average `⊥`. -/
noncomputable def coinAvgE (N : ℕ) (f : List Bool → EReal) : EReal :=
  ((1 / 2 ^ N : ℝ) : EReal) * ∑ w : Fin N → Bool, f (List.ofFn w)

end NSWBetter


