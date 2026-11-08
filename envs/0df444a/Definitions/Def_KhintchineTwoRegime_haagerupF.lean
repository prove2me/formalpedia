-- Prove2me | Definitions.Def_KhintchineTwoRegime_haagerupF
-- name    : KhintchineTwoRegime_haagerupF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:33:49.632075+00:00
-- url     : https://prove2.me/theorems/2b3dfcc9-efd7-418a-98ea-84cae96fee23
-- title:
--   Haagerup's function $F(s)=\frac{2}{\sqrt{\pi s}}\frac{\Gamma((s+1)/2)}{\Gamma(s/2)}$
-- statement:
--   **Haagerup's function** is
--   $$
--   F(s)=\frac{2}{\sqrt{\pi s}}\,\frac{\Gamma\bigl((s+1)/2\bigr)}{\Gamma(s/2)},\qquad s>0.
--   $$
--   It is the function in Haagerup's refined Khintchine estimate (9), with $F(1)=2/\pi$, $F(2)=1/\sqrt2$, $F(4)=3/4$ and $F(s)\to\sqrt{2/\pi}$ as $s\to\infty$.
--
--   **Formalization Note** Defined on all of $\mathbb R$ with Mathlib's `Real.Gamma`; only values at $s>0$ are used.
-- source:
--   Fang–Wang, A Two-regime Khintchine Inequality and an Improved Bound on the Degree-1 Fourier Weight for Linear Threshold Functions, arXiv:2608.27908v2 (held version of 2026-11-02, sha256 1d8d9bf1…), eq. (8), §2.2, p.6

import Mathlib

namespace KhintchineTwoRegime

/-- Haagerup's function `F(s) = (2/√(πs)) · Γ((s + 1)/2)/Γ(s/2)`, `s > 0`
(Fang–Wang, *A Two-regime Khintchine Inequality and an Improved Bound on the Degree-1 Fourier Weight for Linear Threshold Functions*, arXiv:2608.27908v2 (held version of 2026-11-02, sha256 1d8d9bf1…), eq. (8), §2.2, p.6).

**Formalization Note** Defined on all of `ℝ` with Mathlib's `Real.Gamma` and `Real.sqrt`;
only its values at `s > 0` are used. -/
noncomputable def haagerupF (s : ℝ) : ℝ :=
  2 / Real.sqrt (Real.pi * s) * (Real.Gamma ((s + 1) / 2) / Real.Gamma (s / 2))

end KhintchineTwoRegime


