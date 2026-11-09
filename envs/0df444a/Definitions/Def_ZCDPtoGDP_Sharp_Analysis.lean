-- Prove2me | Definitions.Def_ZCDPtoGDP_Sharp_Analysis
-- name    : ZCDPtoGDP_Sharp_Analysis
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T09:51:18.849076+00:00
-- url     : https://prove2.me/theorems/96ec0c78-ad73-46fa-b958-0fe6532ec555
-- title:
--   App. B — $K_{\mathrm{zCDP}}$, $m_{p,q}$, $\mu^{-1}_{\mathrm{zCDP}}$, $g$, $h$, $w$ and $K(c,d)$
-- statement:
--   The auxiliary objects of the proof of the sharp zCDP-to-GDP conversion (Appendix B). Here $\Phi$ is the standard normal CDF, $\Phi^{-1}$ its inverse on $(0,1)$, $\sigma(t)=(1+e^{-t})^{-1}$, and $D_\eta$ the Rényi divergence.
--
--   1. **Bernoulli zCDP budget** (eq. (9)). For $p,q\in[0,1]$,
--   $$K_{\mathrm{zCDP}}(p,q)=\sup_{\eta>1}\frac1\eta\max\{D_\eta(\mathrm{Bern}(p)\|\mathrm{Bern}(q)),\,D_\eta(\mathrm{Bern}(q)\|\mathrm{Bern}(p))\}\in[0,+\infty].$$
--   2. **Gaussian separation.** $m_{p,q}=\Phi^{-1}(q)-\Phi^{-1}(p)$ for $0<p<q<1$.
--   3. **Inverse conversion** (eq. (11)). $\mu^{-1}_{\mathrm{zCDP}}(m)=(2\Phi(m/2)-1)\log\dfrac{\Phi(m/2)}{\Phi(-m/2)}$.
--   4. $g(t)=\Phi^{-1}(\sigma(t))$ and $h(s)=\log\cosh(s/2)$.
--   5. The weight $w(u)=\sqrt{\tanh(u/2)/u}$ for $u\ne0$ and $w(0)=1/\sqrt2$.
--   6. **Selected-order bound** (eq. (13)). $K(c,d)=\dfrac dc\,[h(c+d)-h(c-d)]$ for $c>0$, and $K(0,d)=d\tanh(d/2)$, its continuous extension.
--
--   In log-odds coordinates $p=\sigma(c-d)$, $q=\sigma(c+d)$, the quantity $K(c,d)$ lower-bounds the Bernoulli zCDP budget, and the proof compares it with $\mu^{-1}_{\mathrm{zCDP}}(m_{p,q})$.
--
--   **Formalization Note** $K_{\mathrm{zCDP}}$ is a supremum in `EReal`, so it may be $+\infty$. $K(c,d)$ is defined by cases so that $K(0,d)$ is the paper's $d\tanh(d/2)$ rather than Lean's $d/0=0$; it is only used for $c\ge0$.
-- source:
--   Chen, Pandey, Awan, Optimal Conversion from Zero-Concentrated to Gaussian Differential Privacy, STOC 2027 submission #235 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/235.pdf, App. B: m_{p,q} p. 13, eq. (9) and eq. (11) p. 14, g, h, eq. (13) and K(0,d) p. 15, w p. 16

import Mathlib
import Definitions.Def_ZCDPtoGDP_Sharp_Privacy

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ZCDPtoGDP.Sharp

/-! # Appendix B of Chen–Pandey–Awan: the objects of the proof of Theorem 6

Source: Chen, Pandey, Awan, *Optimal Conversion from Zero-Concentrated to Gaussian
Differential Privacy*, STOC 2027 submission #235, App. B, pp. 13–16. -/

/-- eq. (9), p. 14: the zCDP budget of a Bernoulli pair,
`K_zCDP(p,q) = sup_{η>1} (1/η) max{D_η(Bern p‖Bern q), D_η(Bern q‖Bern p)}`,
a supremum in the complete lattice `EReal` (it may be `+∞`). -/
noncomputable def kZCDP (p q : ℝ) : EReal :=
  ⨆ η : {η : ℝ // 1 < η},
    ((η.1⁻¹ : ℝ) : EReal) * max (renyiDiv η.1 (bern p) (bern q)) (renyiDiv η.1 (bern q) (bern p))

/-- The Gaussian mean separation `m_{p,q} = Φ⁻¹(q) - Φ⁻¹(p)` (p. 13), used for
`0 < p < q < 1`. -/
noncomputable def mSep (p q : ℝ) : ℝ := stdNormalQuantile q - stdNormalQuantile p

/-- The inverse conversion, eq. (11), p. 14:
`μ⁻¹_zCDP(m) = (2Φ(m/2) - 1) log(Φ(m/2)/Φ(-m/2))` (used for `m ≥ 0`). -/
noncomputable def muZCDPInv (m : ℝ) : ℝ :=
  (2 * stdNormalCDF (m / 2) - 1) * Real.log (stdNormalCDF (m / 2) / stdNormalCDF (-m / 2))

/-- `g(t) = Φ⁻¹(σ(t))` (p. 15); `σ(t) ∈ (0,1)`, so the quantile is the genuine inverse. -/
noncomputable def gFun (t : ℝ) : ℝ := stdNormalQuantile (Real.sigmoid t)

/-- `h(s) = log cosh(s/2)` (p. 15). -/
noncomputable def hFun (s : ℝ) : ℝ := Real.log (Real.cosh (s / 2))

/-- The weight `w(u) = √(tanh(u/2)/u)` for `u ≠ 0` and `w(0) = 1/√2` (p. 16). -/
noncomputable def wFun (u : ℝ) : ℝ :=
  if u = 0 then 1 / Real.sqrt 2 else Real.sqrt (Real.tanh (u / 2) / u)

/-- The selected-order bound, eq. (13), p. 15: `K(c,d) = (d/c)[h(c+d) - h(c-d)]` for `c > 0`,
and its continuous extension `K(0,d) = d tanh(d/2)` (p. 15, last paragraph).  Only used
for `c ≥ 0`. -/
noncomputable def kBound (c d : ℝ) : ℝ :=
  if c = 0 then d * Real.tanh (d / 2) else d / c * (hFun (c + d) - hFun (c - d))

end ZCDPtoGDP.Sharp


