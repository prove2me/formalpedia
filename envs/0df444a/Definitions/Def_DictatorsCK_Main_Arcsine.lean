-- Prove2me | Definitions.Def_DictatorsCK_Main_Arcsine
-- name    : DictatorsCK_Main_Arcsine
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T06:41:09.144616+00:00
-- url     : https://prove2.me/theorems/a4b90a3a-eed3-4a7d-9796-61879c0cbc1c
-- title:
--   $\Psi$, the constant $C_*$, $\zeta$, $R$, the profile height $\ell_u$ and the influence function $\psi$
-- statement:
--   1. (6.1) $\Psi(t)=t^2\log2-\Phi(t)=H(t)-(1-t^2)\log2$ on $[-1,1]$.
--   2. (6.2) $C_*=\dfrac{(\pi/2-1)^2}{\log2-1/2}$.
--   3. (6.4) $\zeta(v)=\arcsin(\tanh v)$, and $R(v)=v-\zeta(v)^2/\tanh v$ for $v>0$, with $\zeta(0)=R(0)=0$.
--   4. (6.5) For $u>0$, the **profile height** $\ell_u(a)=F^{-1}(F(u)/a)$ for $0<a\le1$ and $\ell_u(0)=0$.
--   5. (7.2) $\psi(a)=\min\Big\{\dfrac{a+a^2}{2},\ \dfrac{2a(1-a/4)}{\log(4/a)}\Big\}$ for $0<a\le1$, and $\psi(0)=0$.
--
--   $\Psi$ measures the gap between the entropy of a soft bit and its quadratic lower bound, $R$ the production lost on an edge when entropy production is replaced by arcsine energy, and $\psi$ is the explicit influence function of the Talagrand-type bound of Theorem 7.1.
--
--   **Formalization Note.** Every piecewise definition is written with the source's own case split (`if 0 < v then … else 0`); outside the stated domains the functions return Lean's defaults, which no milestone uses.
-- source:
--   Ky, Tran, Dictators are most informative, arXiv:2609.24184 (held copy, sha256 aa2515fb…0a2c7f), p. 32 (PDF 33), (6.1), (6.2); p. 33 (PDF 34), (6.4), (6.5); p. 36 (PDF 37), (7.2)

import Mathlib
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Basic
import Definitions.Def_DictatorsCK_Main_Information
import Definitions.Def_DictatorsCK_Main_Profile

open OAI.LeanBlast.CourtadeKumar

namespace DictatorsCK.Main

noncomputable section

/-- `Ψ(t) = t^2 log 2 − Φ(t) = H(t) − (1 − t^2) log 2` on `[−1, 1]`, display (6.1). -/
def PsiGap (t : ℝ) : ℝ :=
  t ^ 2 * Real.log 2 - Phi t

/-- The constant `C_* = (π/2 − 1)^2 / (log 2 − 1/2)` of display (6.2). -/
def Cstar : ℝ :=
  (Real.pi / 2 - 1) ^ 2 / (Real.log 2 - 1 / 2)

/-- `ζ(v) = arcsin(tanh v)`, display (6.4) (so `ζ(0) = 0`). -/
def zeta (v : ℝ) : ℝ :=
  Real.arcsin (Real.tanh v)

/-- `R(v) = v − ζ(v)^2 / tanh v` for `v > 0`, and `R(0) = 0`, display (6.4). -/
def Rfun (v : ℝ) : ℝ :=
  if 0 < v then v - zeta v ^ 2 / Real.tanh v else 0

/-- The profile height `ℓ_u(a) = F⁻¹(F(u)/a)` for `0 < a ≤ 1`, and `ℓ_u(0) = 0`,
display (6.5) (used for `u > 0`). -/
def profileHeight (u a : ℝ) : ℝ :=
  if 0 < a then Finv (Fprof u / a) else 0

/-- `ψ(a) = min{(a + a^2)/2, 2a(1 − a/4)/log(4/a)}` for `0 < a ≤ 1`, and `ψ(0) = 0`,
display (7.2). -/
def talagrandPsi (a : ℝ) : ℝ :=
  if 0 < a then min ((a + a ^ 2) / 2) (2 * a * (1 - a / 4) / Real.log (4 / a)) else 0

end

end DictatorsCK.Main


