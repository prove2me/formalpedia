-- Prove2me | Definitions.Def_NSWBetter_coinAvg
-- name    : NSWBetter_coinAvg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:48:34.264848+00:00
-- url     : https://prove2.me/theorems/f8e31a54-f714-4aa8-93e2-d7174830a0e5
-- title:
--   Average over all coin strings of a given length
-- statement:
--   For a length $N$ and a real function $f$ of coin strings,
--   $$\operatorname{avg}_N f=\frac1{2^N}\sum_{w\in\{0,1\}^N}f(w),$$
--   the expectation of $f(w)$ when $w$ is a uniformly random string of $N$ fair coins.
-- source:
--   Viswanathan, A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations, arXiv:2607.13340 (held version, sha256 08811cb468c2df39231dca4222c5af94163587c7c83e205e50bbf0b91fc1deb3), Theorem 1.1, p.3; proof of Theorem 1.1, p.48 ($\mathbb E[\mathrm{NSW}(X)]$)

import Mathlib

namespace NSWBetter

/-- **Expectation over uniform coins.**
Viswanathan, *A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations*, arXiv:2607.13340 (held version, sha256 08811cb4…), proof of Theorem 1.1, p.48: the guarantee is on `E[NSW(X)]`.

`coinAvg N f = 2^(−N) Σ_(w ∈ {0,1}^N) f(w)`, the exact expectation of `f` under a uniformly random coin string of length `N`. -/
noncomputable def coinAvg (N : ℕ) (f : List Bool → ℝ) : ℝ :=
  (1 / 2 ^ N : ℝ) * ∑ w : Fin N → Bool, f (List.ofFn w)

end NSWBetter


