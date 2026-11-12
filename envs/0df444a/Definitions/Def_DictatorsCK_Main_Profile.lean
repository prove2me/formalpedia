-- Prove2me | Definitions.Def_DictatorsCK_Main_Profile
-- name    : DictatorsCK_Main_Profile
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T06:38:12.543352+00:00
-- url     : https://prove2.me/theorems/1fa24d0c-a673-43a6-be5e-8e98ca6433b5
-- title:
--   Production profile $F$, its inverse, $B_e(q)$, the singleton profile $P_f$, finite-sum profiles $Q$ and profile clocks $T_P$
-- statement:
--   1. (4.1) For $v>0$, $F(v)=H(\tanh v)/\tanh v$. By Lemma 4.1 of the source, $F:(0,\infty)\to(0,\infty)$ is a strictly decreasing bijection, and $F^{-1}:(0,\infty)\to(0,\infty)$ is its inverse.
--   2. (4.1) For $e,q>0$, $B_e(q)=q\,F^{-1}(e/q)$, and $B_e(0)=0$.
--   3. (4.4) For a Boolean $f$, the **singleton profile** $P_f(s)=\sum_{i}B_s(|\hat f(i)|)$.
--   4. (4.5) For an integer $J\ge1$, weights $c_j>0$ and arguments $q_j\in(0,1]$, the finite-sum profile $Q(y)=\sum_{j=1}^Jc_jB_y(q_j)$.
--   5. (4.4), (4.5) The **clock** of a profile $P$:
--   $$T_P(v)=\int_0^v\frac{ds}{s+P(s)}.$$
--
--   The clock $T_{P_f}$ measures, in noise time $-\log\rho$, how fast the conditional entropy can grow under the entropy-production bound; $T_Q$ with $Q\le P_f$ is the computable comparison clock.
--
--   **Formalization Note.** $F^{-1}(y)$ is defined as a chosen $v>0$ with $F(v)=y$ (and $0$ if there is none); since $F$ is a bijection of $(0,\infty)$ this is the inverse there, and the statements only evaluate it at positive arguments. $B_e(q)$ is `if 0 < q then q * Finv (e/q) else 0`. The clock is the interval integral $\int_0^v$; the source's improper integral at $0$ is finite and its integrand bounded on $(0,v]$ in every case used.
-- source:
--   Ky, Tran, Dictators are most informative, arXiv:2609.24184 (held copy, sha256 aa2515fb…0a2c7f), p. 20 (PDF 21), (4.1); p. 22 (PDF 23), (4.4); p. 23 (PDF 24), (4.5)

import Mathlib
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Basic
import Definitions.Def_DictatorsCK_Main_Fourier
import Definitions.Def_DictatorsCK_Main_Information

open OAI.LeanBlast.CourtadeKumar

namespace DictatorsCK.Main

noncomputable section

/-- The production profile ratio `F(v) = H(tanh v) / tanh v`, display (4.1), used for `v > 0`. -/
def Fprof (v : ℝ) : ℝ :=
  entropy (Real.tanh v) / Real.tanh v

open scoped Classical in
/-- The inverse `F⁻¹ : (0, ∞) → (0, ∞)`: for `y > 0`, a (the) `v > 0` with `F(v) = y`; `F` is a
strictly decreasing bijection of `(0, ∞)` (Lemma 4.1), so the choice is unique there. The value
`0` outside the range is never used by the statements. -/
def Finv (y : ℝ) : ℝ :=
  if h : ∃ v : ℝ, 0 < v ∧ Fprof v = y then Classical.choose h else 0

/-- The edge production profile `B_e(q) = q F⁻¹(e/q)` for `q > 0`, and `B_e(0) = 0`,
display (4.1). -/
def Bprof (e q : ℝ) : ℝ :=
  if 0 < q then q * Finv (e / q) else 0

/-- The singleton profile `P_f(s) = ∑_i B_s(|f̂(i)|)` of a Boolean `f`, display (4.4). -/
def singletonProfile {n : ℕ} (f : Cube n → Bool) (s : ℝ) : ℝ :=
  ∑ i, Bprof s |singletonCoeff (signEncoding f) i|

/-- The clock `T_P(v) = ∫_0^v ds / (s + P(s))` of a profile `P`, displays (4.4), (4.5). -/
def clock (P : ℝ → ℝ) (v : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..v, 1 / (s + P s)

/-- The finite-sum profile `Q(y) = ∑_{j=1}^J c_j B_y(q_j)` of display (4.5). -/
def finiteProfile {J : ℕ} (c q : Fin J → ℝ) (y : ℝ) : ℝ :=
  ∑ j, c j * Bprof y (q j)

end

end DictatorsCK.Main


