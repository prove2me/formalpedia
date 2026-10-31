-- Prove2me | Definitions.Def_CongestionApproxPNE_kd
-- name    : CongestionApproxPNE_kd
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:16:12.573398+00:00
-- url     : https://prove2.me/theorems/aad7f0f1-eac6-497f-bed6-5a7a8d812548
-- title:
--   $k_d=\lceil \ln d/(2\ln\ln d)\rceil$
-- statement:
--   For an integer $d$,
--
--   $$
--   k_d=\left\lceil\frac{\ln d}{2\ln\ln d}\right\rceil .
--   $$
--
--   It is the cost exponent $k$ of the hubs in the parameter choice of the proof of Theorem 1, and the exponent in the sequence $g(d)$ of Lemma 3.
--
--   **Formalization Note** $\lceil\cdot\rceil$ is `Nat.ceil`, which equals the integer ceiling on nonnegative arguments and returns $0$ on negative ones. For $d\ge 3$ the argument is positive; for $d=2$ it lies in $(-1,0)$ and both ceilings are $0$.
-- source:
--   Christodoulou et al., Existence and Complexity of Approximate Equilibria in Weighted Congestion Games, arXiv:2002.07466v3, proof of Theorem 1, p.6 (PDF p.7), choice of k; Appendix A, Lemma 3, p.23 (PDF p.24), k_d

import Mathlib

set_option autoImplicit false

namespace CongestionApproxPNE

/-- **The exponent `k_d = ⌈ln d / (2 ln ln d)⌉`.**
Christodoulou, Gairing, Giannakopoulos, Poças, Waldmann, arXiv:2002.07466v3, proof of Theorem 1,
p.6 ("k = ⌈ln d/(2 ln ln d)⌉") and Lemma 3, p.23 ("where kd = ⌈ln d/(2 ln ln d)⌉").

**Formalization Note** `Real.log` is `ln`; `⌈·⌉` is `Nat.ceil`, which agrees with the integer
ceiling on nonnegative reals and returns `0` on negative ones. For `d ≥ 3`, `ln ln d > 0` and the
argument is positive; for `d = 2`, `ln ln 2 < 0`, the argument lies in `(−1, 0)` and both ceilings
are `0`. -/
noncomputable def kd (d : ℕ) : ℕ :=
  ⌈Real.log d / (2 * Real.log (Real.log d))⌉₊

end CongestionApproxPNE


