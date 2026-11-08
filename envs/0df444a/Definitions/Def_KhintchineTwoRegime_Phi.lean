-- Prove2me | Definitions.Def_KhintchineTwoRegime_Phi
-- name    : KhintchineTwoRegime_Phi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:33:47.003133+00:00
-- url     : https://prove2.me/theorems/d6117346-385e-4649-b87f-13bfbe186c47
-- title:
--   $A_q$, $B_q$ and $\Phi_q(x)=\frac34q-\frac38x+\frac1{8\sqrt2}(\sqrt{A_q(x)}+2\sqrt{B_q(x)})$
-- statement:
--   For real $q,x$ put
--   $$
--   A_q(x)=1-q^2+qx,\qquad B_q(x)=1-q^2+qx-x^2,
--   $$
--   $$
--   \Phi_q(x)=\frac34q-\frac38x+\frac1{8\sqrt2}\Bigl(\sqrt{A_q(x)}+2\sqrt{B_q(x)}\Bigr).
--   $$
--   Lemma 5 shows $K_n(\omega)\ge\Phi_q(x)$ with $q=\omega_1+\omega_2$, $x=q-\omega_3-\omega_4$; at $x=0$ one gets $\Phi_q(0)=A(q)$, the minimum value of Theorem 2.
--
--   **Formalization Note** The module holds the three functions $A_q$ (`Aq`), $B_q$ (`Bq`) and $\Phi_q$ (`Phi`). `Real.sqrt` is $0$ on negative arguments; statements use $\Phi_q$ only where the radicands are nonnegative or state their positivity.
-- source:
--   Fang–Wang, A Two-regime Khintchine Inequality and an Improved Bound on the Degree-1 Fourier Weight for Linear Threshold Functions, arXiv:2608.27908v2 (held version of 2026-11-02, sha256 1d8d9bf1…), Lemma 5, p.7

import Mathlib

namespace KhintchineTwoRegime

/-- `A_q(x) = 1 − q² + qx` (Fang–Wang, *A Two-regime Khintchine Inequality and an Improved Bound on the Degree-1 Fourier Weight for Linear Threshold Functions*, arXiv:2608.27908v2 (held version of 2026-11-02, sha256 1d8d9bf1…), Lemma 5, p.7). -/
def Aq (q x : ℝ) : ℝ :=
  1 - q ^ 2 + q * x

/-- `B_q(x) = 1 − q² + qx − x²` (Fang–Wang, *A Two-regime Khintchine Inequality and an Improved Bound on the Degree-1 Fourier Weight for Linear Threshold Functions*, arXiv:2608.27908v2 (held version of 2026-11-02, sha256 1d8d9bf1…), Lemma 5, p.7). -/
def Bq (q x : ℝ) : ℝ :=
  1 - q ^ 2 + q * x - x ^ 2

/-- `Φ_q(x) = (3/4)q − (3/8)x + (1/(8√2))(√(A_q(x)) + 2√(B_q(x)))` (Fang–Wang, *A Two-regime Khintchine Inequality and an Improved Bound on the Degree-1 Fourier Weight for Linear Threshold Functions*, arXiv:2608.27908v2 (held version of 2026-11-02, sha256 1d8d9bf1…), Lemma 5, p.7).

**Formalization Note** `Real.sqrt` is `0` on negative arguments, so `Φ_q` is defined for
every `x`; the statements of the mission use it only where `A_q, B_q ≥ 0` or state the
positivity explicitly. -/
noncomputable def Phi (q x : ℝ) : ℝ :=
  3 / 4 * q - 3 / 8 * x + (Real.sqrt (Aq q x) + 2 * Real.sqrt (Bq q x)) / (8 * Real.sqrt 2)

end KhintchineTwoRegime


