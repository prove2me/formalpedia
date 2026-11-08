-- Prove2me | Definitions.Def_KhintchineTwoRegime_Abound
-- name    : KhintchineTwoRegime_Abound
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:33:47.866422+00:00
-- url     : https://prove2.me/theorems/7a78a57c-235d-4f91-8be0-40263885bf04
-- title:
--   $A(q)=\frac{3q}{4}+\frac{3}{8\sqrt2}\sqrt{1-q^2}$
-- statement:
--   For $q\in[0,1]$ put
--   $$
--   A(q)=\frac{3q}4+\frac3{8\sqrt2}\sqrt{1-q^2}.
--   $$
--   It is the value of $K_n$ at the six-coordinate profile with $q=(2-\tau^2)/\sqrt2$, the minimum in Theorem 2, and the threshold in the localization Lemma 6.
--
--   **Formalization Note** `Real.sqrt` is $0$ on negative arguments; the mission uses $A(q)$ only for $0\le q\le1$.
-- source:
--   Fang–Wang, A Two-regime Khintchine Inequality and an Improved Bound on the Degree-1 Fourier Weight for Linear Threshold Functions, arXiv:2608.27908v2 (held version of 2026-11-02, sha256 1d8d9bf1…), Lemma 6, p.7; Theorem 2, p.8

import Mathlib

namespace KhintchineTwoRegime

/-- `A(q) = 3q/4 + (3/(8√2))√(1 − q²)` (Fang–Wang, *A Two-regime Khintchine Inequality and an Improved Bound on the Degree-1 Fourier Weight for Linear Threshold Functions*, arXiv:2608.27908v2 (held version of 2026-11-02, sha256 1d8d9bf1…), Lemma 6, p.7; the minimum value in
Theorem 2, p.8).

**Formalization Note** `Real.sqrt` is `0` on negative arguments; the mission uses `A(q)`
only for `0 ≤ q ≤ 1`. -/
noncomputable def Abound (q : ℝ) : ℝ :=
  3 * q / 4 + 3 / (8 * Real.sqrt 2) * Real.sqrt (1 - q ^ 2)

end KhintchineTwoRegime


