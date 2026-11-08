-- Prove2me | Definitions.Def_KhintchineTwoRegime_H
-- name    : KhintchineTwoRegime_H
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:34:40.855945+00:00
-- url     : https://prove2.me/theorems/65c75f9f-68d9-42ce-992b-5232443ef59a
-- title:
--   $H(a,b)=C[a^2r(a)+(1-a^2)r(b)]$
-- statement:
--   For real $a,b$,
--   $$
--   H(a,b)=C\bigl[a^2r(a)+(1-a^2)\,r(b)\bigr],\qquad C=\sqrt{2/\pi}.
--   $$
--   Lemma 2 shows $K_n(\omega)\ge H(\omega_1,\omega_2)$ for proper unit vectors (eq. (13)).
-- source:
--   Fang–Wang, A Two-regime Khintchine Inequality and an Improved Bound on the Degree-1 Fourier Weight for Linear Threshold Functions, arXiv:2608.27908v2 (held version of 2026-11-02, sha256 1d8d9bf1…), eq. (13), Lemma 2, p.6

import Mathlib
import Definitions.Def_KhintchineTwoRegime_Cconst
import Definitions.Def_KhintchineTwoRegime_rFun

namespace KhintchineTwoRegime

/-- `H(a, b) = C[a² r(a) + (1 − a²) r(b)]` with `C = √(2/π)` (Fang–Wang, *A Two-regime Khintchine Inequality and an Improved Bound on the Degree-1 Fourier Weight for Linear Threshold Functions*, arXiv:2608.27908v2 (held version of 2026-11-02, sha256 1d8d9bf1…), eq. (13), Lemma 2,
p.6). -/
noncomputable def H (a b : ℝ) : ℝ :=
  Cconst * (a ^ 2 * rFun a + (1 - a ^ 2) * rFun b)

end KhintchineTwoRegime


