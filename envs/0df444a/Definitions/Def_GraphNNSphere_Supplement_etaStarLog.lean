-- Prove2me | Definitions.Def_GraphNNSphere_Supplement_etaStarLog
-- name    : GraphNNSphere_Supplement_etaStarLog
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:46:16.714812+00:00
-- url     : https://prove2.me/theorems/bc1c8e23-0e9c-455b-9645-5f19b4a6dffd
-- title:
--   Logarithmic single-start exponent $\eta^*$ and the near-threshold band
-- statement:
--   In the logarithmic regime $d=\lfloor c\log n\rfloor$ with $\Delta=\lceil n^\beta\rceil$, $0<\beta<\beta^*(c)$, the angles converge: $\theta_1\to\arcsin e^{-1/c}$ and $\rho_\beta\to R=\arcsin e^{-(1-\beta)/c}$. With $S=\sin^2\theta_1$, the trap distance is defined by
--
--   $$\sin^2\theta_{\mathrm{trap}}=\frac{(1-\cos\rho)^2}{2(1-\cos\rho)-S}.$$
--
--   For a neighbor radius $\varrho$ the directional threshold and the probability exponent are
--
--   $$w^\varrho(\varphi,\psi)=\frac{\cos\varrho-\cos\varphi\cos\psi}{\sin\varphi\sin\psi},\qquad p^\varrho(\varphi,\psi)=\frac12\log\big(1-w^\varrho(\varphi,\psi)_+^2\big).$$
--
--   The **near-threshold band** is $\lim\theta_{\mathrm{trap}}\le R$, and in it the single-start exponent is
--
--   $$\eta^*=-\lim_{n\to\infty}p(\theta_{\mathrm{trap}},\theta_1).$$
--
--   **Formalization Note** The limit is evaluated at the limiting angles, which is how the paper computes it; $p$ is continuous there because $0<w<1$ in the band (Lemma 5.4(c)). The real formula for $\eta^*$ is only used under the band hypothesis.
-- source:
--   Lu, Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere, STOC 2027 submission (manuscript sha256 93565bc5…), Eq. (55), p.60; §5.2, pp.59–61; Eq. (6), p.15

import Mathlib
import Definitions.Def_GraphNNSphere_betaStar

namespace GraphNNSphere

namespace Supplement

/-- The limit `lim θ₁ = arcsin e^{-1/c}` of the nearest-neighbor scale in the logarithmic regime
`d = ⌊c log n⌋` (Lu, *Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere*, STOC 2027 submission (manuscript sha256 93565bc5…), Eq. (4), p.15, and §5.2, p.61). -/
noncomputable def theta1Lim (c : ℝ) : ℝ := Real.arcsin (Real.exp (-1 / c))

/-- The limit `R = lim ρ_β = arcsin e^{-(1-β)/c}` of the neighbor radius in the logarithmic regime
(Lu, *Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere*, STOC 2027 submission (manuscript sha256 93565bc5…), Eq. (6), p.15, §4.4, p.42, and §5.2, p.60). -/
noncomputable def rhoLim (c β : ℝ) : ℝ := Real.arcsin (Real.exp (-(1 - β) / c))

/-- The limit of the trap distance, defined like `θ_trap` by
`sin² θ_trap = (1 - cos R)²/(2(1 - cos R) - S)` with `S = sin² θ₁`, at the limiting angles
(Lu, *Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere*, STOC 2027 submission (manuscript sha256 93565bc5…), §5.2, pp.59–60). -/
noncomputable def thetaTrapLim (c β : ℝ) : ℝ :=
  Real.arcsin (Real.sqrt ((1 - Real.cos (rhoLim c β)) ^ 2 /
    (2 * (1 - Real.cos (rhoLim c β)) - Real.sin (theta1Lim c) ^ 2)))

/-- The directional threshold `w^ϱ(φ, ψ) = (cos ϱ - cos φ cos ψ)/(sin φ sin ψ)`, written with
`a = cos ϱ` (Lu, *Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere*, STOC 2027 submission (manuscript sha256 93565bc5…), §5.2, p.60). -/
noncomputable def wRate (a φ ψ : ℝ) : ℝ := (a - Real.cos φ * Real.cos ψ) / (Real.sin φ * Real.sin ψ)

/-- The near-threshold band of the logarithmic regime: `0 < β < β*(c)` and
`lim θ_trap ≤ R = lim ρ` (Lu, *Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere*, STOC 2027 submission (manuscript sha256 93565bc5…), §5.2, pp.59–60). -/
def InBandLog (c β : ℝ) : Prop := 0 < β ∧ β < betaStar c ∧ thetaTrapLim c β ≤ rhoLim c β

/-- The single-start exponent of the logarithmic regime, `η* = -lim p(θ_trap, θ₁)` (55), with
`p(φ, ψ) = ½ log(1 - w(φ, ψ)₊²)` (Lu, *Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere*, STOC 2027 submission (manuscript sha256 93565bc5…), Eq. (55), p.60).

**Formalization Note** The limit is evaluated at the limiting angles `theta1Lim`, `rhoLim` and
`thetaTrapLim`, which is how the paper computes it (p.61: "we take their angle limits"); `p` is
continuous there because `w < 1` in the band (Lemma 5.4(c)). The real formula is used only under
`InBandLog`, where `0 < w < 1`. -/
noncomputable def etaStarLog (c β : ℝ) : ℝ :=
  -(Real.log (1 - (max (wRate (Real.cos (rhoLim c β)) (thetaTrapLim c β) (theta1Lim c)) 0) ^ 2) / 2)

end Supplement

end GraphNNSphere


