-- Prove2me | Definitions.Def_SpikedWishart_Separated_Kernels
-- name    : SpikedWishart_Separated_Kernels
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T06:36:44.769381+00:00
-- url     : https://prove2.me/theorems/975eee53-a3b8-47ac-aba5-e3fd734eb389
-- title:
--   §4, pp. 1678–1679, 1690, (213)–(214), (221)–(222), (293) — 𝓗, 𝓙 on closed contours, Z_M, the limits 𝓗_∞, 𝓙_∞, and K₂
-- statement:
--   This file defines the kernel factors of §4. Let $M, N \ge 1$ with $\gamma = \sqrt{M/N}$, $k \ge 1$, $\varepsilon > 0$, and $\mu, \nu, q, f, g$ as in (211), (215), (216), (220).
--
--   1. (213): $$\mathcal H(u) = \frac{\nu M^{1/2}}{2\pi}\int_\Gamma e^{-\nu M^{1/2}u(z-q)}\,e^{Mf(z)}\,\frac{1}{(\pi_1-z)^k g(z)}\,dz,$$ where $\Gamma$ is the counterclockwise circle having as diameter the real segment from $(q+\pi_1)/2$ to $\max\{1,\pi_{k+1},\dots,\pi_r\}+1$.
--   2. (214): $$\mathcal J(v) = \frac{\nu M^{1/2}}{2\pi}\int_\Sigma e^{\nu M^{1/2}v(z-q)}\,e^{-Mf(z)}\,(\pi_1-z)^k g(z)\,dz,$$ where $\Sigma$ is the counterclockwise circle $|z| = q/2$.
--   3. (222): $Z_M = \dfrac{(-1)^k e^{-Mf(\pi_1)}g(\pi_1)}{\nu^k M^{k/2}}$.
--   4. (221): $\mathcal H_\infty(u) = i e^{-\varepsilon u}\,\mathrm{Res}_{a=0}\Big(\dfrac1{a^k}e^{-\frac12 a^2 - ua}\Big)$ and $\mathcal J_\infty(v) = \dfrac1{2\pi}e^{\varepsilon v}\displaystyle\int_{\Sigma_\infty}s^k e^{\frac12 s^2 + vs}\,ds$, with $\Sigma_\infty$ the imaginary axis oriented upwards.
--   5. (293): $K_2(u,v) = \displaystyle\int_0^\infty \mathcal H_\infty(u+y)\,\mathcal J_\infty(v+y)\,dy$.
--
--   $\mathcal H$ and $\mathcal J$ are the two factors of the finite-$M$ kernel of Proposition 2.1 after the scaling (212), and $\mathcal H_\infty$, $\mathcal J_\infty$ their limits; $K_2$ is the limiting kernel.
--
--   **Formalization Note** The paper's $\Gamma$ is any simple closed contour in $\{\operatorname{Re} z > q\}$ enclosing $\pi_1, \pi_{k+1},\dots,\pi_r$ and $1$, and $\Sigma$ any simple closed contour in $\{\operatorname{Re} z < q\}$ enclosing $0$, both counterclockwise; the circles above are such contours (for $\Sigma$ when $q > 0$, which holds for large $M$), and by Cauchy's theorem the integrals do not depend on the choice. Since $M$ and $N = M/\gamma^2$ are integers, $e^{\pm Mf(z)}$ equals $e^{\mp M\mu(z-q)}z^{\pm M}(1-z)^{\mp N}$, so the branch of $\log$ plays no role. The residue of $a^{-k}\varphi(a)$ at $0$, for $\varphi$ entire, is encoded as the Taylor coefficient $\varphi^{(k-1)}(0)/(k-1)!$. The integral over $\Sigma_\infty$ is parametrised by $s = iy$, $ds = i\,dy$, $y \in \mathbb R$; the integrand is absolutely integrable.
-- source:
--   Baik, Ben Arous and Péché, Phase transition of the largest eigenvalue for nonnull complex sample covariance matrices, Ann. Probab. 33 (2005), p. 1678, (213)–(214); p. 1679, (221)–(222); p. 1690, (293); contours Γ, Σ as in Proposition 2.1, pp. 1655–1656

import Mathlib
import Definitions.Def_SpikedWishart_Separated_Phase

open MeasureTheory Set Complex

namespace SpikedWishart.Separated

/-- `γ = √(M/N)`, so that `M/N = γ²` (90). -/
noncomputable def gamMN (M N : ℕ) : ℝ :=
  Real.sqrt ((M : ℝ) / N)

/-- (213) with `γ = √(M/N)` and `q` of (220):
`𝓗(u) = (ν√M/2π) ∫_Γ e^{−ν√M u (z−q)} e^{M f(z)} / ((π₁ − z)^k g(z)) dz`.
`Γ` is the counterclockwise circle whose diameter is the real segment from `(q + π₁)/2` to
`max{1, π_{k+1}, …, π_r} + 1`: a simple closed contour in `Re z > q` enclosing `π₁`,
`π_{k+1}, …, π_r` and `1`. -/
noncomputable def HM (k : ℕ) {m : ℕ} (πo : Fin m → ℝ) (ε π₁ : ℝ) (M N : ℕ) (u : ℝ) : ℂ :=
  let γ := gamMN M N
  let ν := nu γ π₁
  let q := qM ε γ π₁ M
  let a := (q + π₁) / 2
  let b := (List.ofFn πo).foldr max 1 + 1
  ((ν * Real.sqrt M / (2 * Real.pi) : ℝ) : ℂ) *
    ∮ z in C(((a + b) / 2 : ℝ), (b - a) / 2),
      cexp (-((ν * Real.sqrt M * u : ℝ) : ℂ) * (z - q)) * cexp ((M : ℂ) * fPhase γ π₁ q z) *
        (1 / ((π₁ - z) ^ k * gFac k πo z))

/-- (214) with `γ = √(M/N)` and `q` of (220):
`𝓙(v) = (ν√M/2π) ∫_Σ e^{ν√M v (z−q)} e^{−M f(z)} (π₁ − z)^k g(z) dz`.
`Σ` is the counterclockwise circle `|z| = q/2`: a simple closed contour in `Re z < q`
enclosing `0` (for `q > 0`). -/
noncomputable def JM (k : ℕ) {m : ℕ} (πo : Fin m → ℝ) (ε π₁ : ℝ) (M N : ℕ) (v : ℝ) : ℂ :=
  let γ := gamMN M N
  let ν := nu γ π₁
  let q := qM ε γ π₁ M
  ((ν * Real.sqrt M / (2 * Real.pi) : ℝ) : ℂ) *
    ∮ z in C(0, q / 2),
      cexp (((ν * Real.sqrt M * v : ℝ) : ℂ) * (z - q)) * cexp (-(M : ℂ) * fPhase γ π₁ q z) *
        ((π₁ - z) ^ k * gFac k πo z)

/-- (222): `Z_M = (−1)^k e^{−M f(π₁)} g(π₁) / (ν^k M^{k/2})`. -/
noncomputable def ZM (k : ℕ) {m : ℕ} (πo : Fin m → ℝ) (ε π₁ : ℝ) (M N : ℕ) : ℂ :=
  let γ := gamMN M N
  let ν := nu γ π₁
  let q := qM ε γ π₁ M
  (-1) ^ k * cexp (-(M : ℂ) * fPhase γ π₁ q π₁) * gFac k πo π₁ /
    ((ν : ℂ) ^ k * (Real.sqrt M : ℂ) ^ k)

/-- The residue `Res_{a=0} (a^{−k} e^{−a²/2 − ua})`, encoded as the Taylor coefficient
`φ^{(k−1)}(0)/(k−1)!` of the entire function `φ(a) = e^{−a²/2 − ua}` (`k ≥ 1`). -/
noncomputable def resAt0 (k : ℕ) (u : ℝ) : ℂ :=
  iteratedDeriv (k - 1) (fun a : ℂ => cexp (-(1 / 2) * a ^ 2 - (u : ℂ) * a)) 0 /
    ((k - 1).factorial : ℂ)

/-- (221): `𝓗_∞(u) = i e^{−εu} Res_{a=0}(a^{−k} e^{−a²/2 − ua})`. -/
noncomputable def Hinf (k : ℕ) (ε u : ℝ) : ℂ :=
  I * cexp (-((ε * u : ℝ) : ℂ)) * resAt0 k u

/-- (221): `𝓙_∞(v) = (1/2π) e^{εv} ∫_{Σ_∞} s^k e^{s²/2 + vs} ds`, `Σ_∞` the imaginary axis
from bottom to top, parametrised by `s = iy`, `ds = i dy`. -/
noncomputable def Jinf (k : ℕ) (ε v : ℝ) : ℂ :=
  ((1 / (2 * Real.pi) : ℝ) : ℂ) * cexp ((ε * v : ℝ) : ℂ) *
    ∫ y : ℝ, (I * y) ^ k * cexp ((1 / 2) * (I * y) ^ 2 + (v : ℂ) * (I * y)) * I

/-- (293): `K₂(u, v) = ∫_0^∞ 𝓗_∞(u + y) 𝓙_∞(v + y) dy`. -/
noncomputable def K2 (k : ℕ) (ε u v : ℝ) : ℂ :=
  ∫ y in Ioi (0 : ℝ), Hinf k ε (u + y) * Jinf k ε (v + y)

end SpikedWishart.Separated


