-- Prove2me | Definitions.Def_KhintchineTwoRegime_rFun
-- name    : KhintchineTwoRegime_rFun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:33:47.305116+00:00
-- url     : https://prove2.me/theorems/287b6aed-e446-41de-99d4-860ae1214179
-- title:
--   $r(u)=\sqrt{(8+4u^2)/(8+8u^2+3u^4)}$
-- statement:
--   For $u\ge0$ put
--   $$
--   r(u)=\sqrt{\frac{8+4u^2}{8+8u^2+3u^4}}.
--   $$
--   Lemma 1 states $F(u^{-2})\ge C\,r(u)$ for $u>0$, and $r$ enters the coefficient bound $H$ of Lemma 2.
--
--   **Formalization Note** Defined for every real $u$; the radicand is positive for all $u$, and the paper uses $u\ge0$.
-- source:
--   Fang–Wang, A Two-regime Khintchine Inequality and an Improved Bound on the Degree-1 Fourier Weight for Linear Threshold Functions, arXiv:2608.27908v2 (held version of 2026-11-02, sha256 1d8d9bf1…), §2.2, p.6

import Mathlib

namespace KhintchineTwoRegime

/-- `r(u) = √((8 + 4u²)/(8 + 8u² + 3u⁴))` for `u ≥ 0` (Fang–Wang, *A Two-regime Khintchine Inequality and an Improved Bound on the Degree-1 Fourier Weight for Linear Threshold Functions*, arXiv:2608.27908v2 (held version of 2026-11-02, sha256 1d8d9bf1…), §2.2, p.6).

**Formalization Note** Defined for every real `u` (the radicand is positive for all `u`);
the paper uses it for `u ≥ 0`. -/
noncomputable def rFun (u : ℝ) : ℝ :=
  Real.sqrt ((8 + 4 * u ^ 2) / (8 + 8 * u ^ 2 + 3 * u ^ 4))

end KhintchineTwoRegime


