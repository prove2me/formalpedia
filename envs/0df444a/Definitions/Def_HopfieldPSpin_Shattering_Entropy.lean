-- Prove2me | Definitions.Def_HopfieldPSpin_Shattering_Entropy
-- name    : HopfieldPSpin_Shattering_Entropy
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T19:07:47.271996+00:00
-- url     : https://prove2.me/theorems/0c97c968-a498-4098-a560-83554ac804d3
-- title:
--   Rate function $I(t)$ (4.4), $\Lambda_p$ (4.7), the soft-gap exponent $g_{p,\beta}(r,R)$ (4.46) and the radii $r_p,R_p$ (2.3)
-- statement:
--   Let $h(x)=-x\log x-(1-x)\log(1-x)$ be the binary entropy (natural logarithm, $0\log0=0$). Define
--   $$I(t)=\log2-h\Big(\frac{1-t}2\Big),\qquad \Lambda_p=\inf_{0<t\le1}\frac{1+t^p}{t^p}\,I(t),$$
--   $$g_{p,\beta}(r,R)=\inf_{x\in[r,R]}\Big\{\frac{\beta^2}2\,\frac{1-(1-2x)^p}{1+(1-2x)^p}-h(x)\Big\},$$
--   and, for $\varepsilon\in(0,1)$ and $\delta=\varepsilon/4$, the radii $r_p=\dfrac1{2p^{1+\delta}}$ and $R_p=\dfrac\delta{2p}=\dfrac\varepsilon{8p}$.
--
--   **Formalization Note.** $h$ is Mathlib's `Real.binEntropy`. $\Lambda_p$ is the real infimum over the nonempty set $(0,1]$, on which all values are $\ge0$, so it is the true infimum. $g_{p,\beta}(r,R)$ is used only for $0<r<R<1/2$, where it is the minimum of a continuous function on a compact interval. $p^{1+\delta}$ is a real power.
-- source:
--   Kızıldağ, Şahin, Hopfield Model with p-spin Interactions: Shattering, Disorder Chaos and Sampling Hardness, STOC 2027 submission (manuscript sha256 4bbdc838…), p. 6 (PDF 8), (2.3); p. 16 (PDF 18), (4.4), (4.7); p. 30 (PDF 32), (4.46)

import Mathlib

noncomputable section

namespace HopfieldPSpin.Shattering

/-- `I(t) = log 2 − h((1 − t)/2)` (4.4), with `h = Real.binEntropy` the binary entropy in
natural logarithms, `h(x) = −x log x − (1 − x) log(1 − x)`. -/
def rateI (t : ℝ) : ℝ := Real.log 2 - Real.binEntropy ((1 - t) / 2)

/-- `Λ_p = inf_{0 < t ≤ 1} (1 + t^p) I(t) / t^p` (4.7): the infimum over the nonempty set
`(0, 1]`, on which every value is `≥ 0`, so the real infimum is the true one. -/
def lambdaP (p : ℕ) : ℝ :=
  ⨅ t : Set.Ioc (0 : ℝ) 1, (1 + (t : ℝ) ^ p) / (t : ℝ) ^ p * rateI t

/-- The soft-gap exponent (4.46):
`g_{p,β}(r, R) = inf_{x ∈ [r, R]} { (β²/2) (1 − (1−2x)^p)/(1 + (1−2x)^p) − h(x) }`.
Used only with `0 < r < R < 1/2`, where the set is a nonempty compact interval and the
function is continuous, so the real infimum is the true minimum. -/
def gapG (p : ℕ) (β r R : ℝ) : ℝ :=
  ⨅ x : Set.Icc r R,
    (β ^ 2 / 2 * ((1 - (1 - 2 * (x : ℝ)) ^ p) / (1 + (1 - 2 * (x : ℝ)) ^ p)) -
      Real.binEntropy (x : ℝ))

/-- `r_p = 1 / (2 p^{1+δ})` with `δ = ε/4` (2.3); `p^{1+δ}` is a real power. -/
def radiusR (ε : ℝ) (p : ℕ) : ℝ := 1 / (2 * (p : ℝ) ^ (1 + ε / 4))

/-- `R_p = δ/(2p) = ε/(8p)` (2.3). -/
def radiusBigR (ε : ℝ) (p : ℕ) : ℝ := ε / (8 * (p : ℝ))

end HopfieldPSpin.Shattering


