-- Prove2me | Definitions.Def_KhintchineTwoRegime_J
-- name    : KhintchineTwoRegime_J
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:33:49.766673+00:00
-- url     : https://prove2.me/theorems/2ff5bba9-30b0-4617-8014-be2367594459
-- title:
--   $J(a,b)=\frac{a+b}{2}+\frac{\sqrt{1-2ab}}{2\sqrt2}$
-- statement:
--   For real $a,b$,
--   $$
--   J(a,b)=\frac{a+b}{2}+\frac{\sqrt{1-2ab}}{2\sqrt2}.
--   $$
--   Lemma 2 shows $K_n(\omega)\ge J(\omega_1,\omega_2)$ for proper unit vectors (eq. (12)).
--
--   **Formalization Note** `Real.sqrt` is $0$ on negative arguments; for a proper unit vector ($a=\omega_1$, $b=\omega_2$) the radicand is nonnegative.
-- source:
--   Fang–Wang, A Two-regime Khintchine Inequality and an Improved Bound on the Degree-1 Fourier Weight for Linear Threshold Functions, arXiv:2608.27908v2 (held version of 2026-11-02, sha256 1d8d9bf1…), eq. (12), Lemma 2, p.6

import Mathlib

namespace KhintchineTwoRegime

/-- `J(a, b) = (a + b)/2 + √(1 − 2ab)/(2√2)` (Fang–Wang, *A Two-regime Khintchine Inequality and an Improved Bound on the Degree-1 Fourier Weight for Linear Threshold Functions*, arXiv:2608.27908v2 (held version of 2026-11-02, sha256 1d8d9bf1…), eq. (12), Lemma 2, p.6).

**Formalization Note** `Real.sqrt` is `0` on negative arguments; for a proper unit vector
(`a = ω₁`, `b = ω₂`) the radicand `1 − 2ab` is nonnegative. -/
noncomputable def J (a b : ℝ) : ℝ :=
  (a + b) / 2 + Real.sqrt (1 - 2 * a * b) / (2 * Real.sqrt 2)

end KhintchineTwoRegime


