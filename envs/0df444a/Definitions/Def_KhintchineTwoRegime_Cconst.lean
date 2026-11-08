-- Prove2me | Definitions.Def_KhintchineTwoRegime_Cconst
-- name    : KhintchineTwoRegime_Cconst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:33:50.311191+00:00
-- url     : https://prove2.me/theorems/775bc1d0-1819-45a7-8db5-807053fcb78c
-- title:
--   The constant $C=\sqrt{2/\pi}$
-- statement:
--   The constant
--   $$
--   C=\sqrt{\frac2\pi}
--   $$
--   is the limit of Haagerup's function $F(s)$ as $s\to\infty$ and the scale of the Wallis-ratio estimate (Lemma 1) and of the bound $H$ (Lemma 2).
-- source:
--   Fang–Wang, A Two-regime Khintchine Inequality and an Improved Bound on the Degree-1 Fourier Weight for Linear Threshold Functions, arXiv:2608.27908v2 (held version of 2026-11-02, sha256 1d8d9bf1…), §2.2, p.6

import Mathlib

namespace KhintchineTwoRegime

/-- The constant `C = √(2/π)` (Fang–Wang, *A Two-regime Khintchine Inequality and an Improved Bound on the Degree-1 Fourier Weight for Linear Threshold Functions*, arXiv:2608.27908v2 (held version of 2026-11-02, sha256 1d8d9bf1…), §2.2, p.6). -/
noncomputable def Cconst : ℝ :=
  Real.sqrt (2 / Real.pi)

end KhintchineTwoRegime


