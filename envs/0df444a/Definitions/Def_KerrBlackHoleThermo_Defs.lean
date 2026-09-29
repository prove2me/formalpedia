-- Prove2me | Definitions.Def_KerrBlackHoleThermo_Defs
-- name    : KerrBlackHoleThermo_Defs
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-25T19:40:38.951163+00:00
-- url     : https://prove2.me/theorems/58326dae-82ec-401d-9c00-3b2459d72e28
-- title:
--   Kerr black hole: horizon radii, metric components, horizon area, $\kappa$, $\Omega_H$
-- statement:
--   Definitions for the thermodynamics of the Kerr black hole, in geometrized units $G=c=1$ (and $\hbar=k_B=1$ where quantum quantities appear), following Menezes (2021).
--
--   A Kerr black hole is described by its mass $M$ and rotation parameter $a$. The file defines:
--
--   1. the angular momentum $J = Ma$ (eq. (2.2a));
--   2. the metric functions $\Delta(r) = r^2 - 2Mr + a^2$ and $\Sigma(r,\theta) = r^2 + a^2\cos^2\theta$ (eqs. (2.2b), (2.2c));
--   3. the horizon radii $r_\pm = M \pm \sqrt{M^2-a^2}$ (eq. (2.3));
--   4. the Boyer–Lindquist metric components (eq. (2.1))
--   $$g_{\theta\theta} = \Sigma, \qquad g_{\varphi\varphi} = \frac{(r^2+a^2)^2 - \Delta\, a^2 \sin^2\theta}{\Sigma}\,\sin^2\theta;$$
--   5. the area of the event horizon, i.e. the area of the 2-surface $t=\text{const}$, $r=r_+$ with its induced metric $g_{\theta\theta}\,d\theta^2 + g_{\varphi\varphi}\,d\varphi^2$:
--   $$A(M,a) = \int_0^{\pi}\!\!\int_0^{2\pi} \sqrt{g_{\theta\theta}(r_+,\theta)\, g_{\varphi\varphi}(r_+,\theta)}\; d\varphi\, d\theta;$$
--   6. the surface gravity $\kappa = \dfrac{\sqrt{M^2-a^2}}{2M\left(M+\sqrt{M^2-a^2}\right)}$ (eq. (3.3));
--   7. the angular velocity of the horizon $\Omega_H = \dfrac{a}{2M\left(M+\sqrt{M^2-a^2}\right)}$ (eq. (2.42));
--   8. the mass of an evaporating Schwarzschild black hole with initial mass $M_0$, $M(t) = \left(M_0^3 - \dfrac{t}{256\pi}\right)^{1/3}$ (eq. (4.137)).
--
--   These are the objects in terms of which the first law of black-hole mechanics, the Smarr formula and the related identities of the mission are stated.
--
--   **Formalization Note** All quantities are real-valued functions of arbitrary real inputs; outside the physical range $M>0$, $a^2\le M^2$ the Lean conventions apply ($\sqrt{x}=0$ for $x<0$, division by $0$ gives $0$, a non-integrable integrand integrates to $0$, and the real power $x^{1/3}$ of a negative $x$ is Mathlib's `Real.rpow` value). Every theorem of the mission restricts to the physical range explicitly. The dissertation does not write the horizon area as an integral; item 5 is the standard definition of the area of the horizon cross-section, from which the dissertation's closed form (3.44) is a milestone.
-- source:
--   F. H. de C. Menezes, Termodinâmica de Buracos Negros, M.Sc. dissertation, Programa de Pós-Graduação em Física, ICEx, Universidade Federal de Minas Gerais, Belo Horizonte, 2021 (advisor: N. de O. Yokomizo), eqs. (2.1)–(2.3) pp. 40–41, eq. (2.42) p. 52, eq. (3.3) p. 54, eq. (4.137) p. 116

import Mathlib

/-!
# Kerr black-hole thermodynamics — definitions

Definition layer for the mission based on
F. H. de C. Menezes, *Termodinâmica de Buracos Negros* (M.Sc. dissertation, UFMG, 2021).
Geometrized units `G = c = ħ = k_B = 1`, as in the dissertation.
The Kerr black hole is described by its mass `M` and rotation parameter `a`,
with angular momentum `J = M a` (eq. (2.2a)).
-/

namespace KerrBlackHoleThermo

open Real

/-- Angular momentum of the Kerr solution, `J = M a` (eq. (2.2a)). -/
def angMom (M a : ℝ) : ℝ := M * a

/-- `Δ = r² − 2 M r + a²` (eq. (2.2b)). -/
def kerrDelta (M a r : ℝ) : ℝ := r ^ 2 - 2 * M * r + a ^ 2

/-- `Σ = r² + a² cos² θ` (eq. (2.2c)). -/
noncomputable def kerrSigma (a r θ : ℝ) : ℝ := r ^ 2 + a ^ 2 * cos θ ^ 2

/-- Outer horizon radius `r₊ = M + √(M² − a²)` (eq. (2.3)). -/
noncomputable def rPlus (M a : ℝ) : ℝ := M + √(M ^ 2 - a ^ 2)

/-- Inner horizon radius `r₋ = M − √(M² − a²)` (eq. (2.3)). -/
noncomputable def rMinus (M a : ℝ) : ℝ := M - √(M ^ 2 - a ^ 2)

/-- The `g_θθ` component of the Kerr metric in Boyer–Lindquist coordinates (eq. (2.1)). -/
noncomputable def gThetaTheta (a r θ : ℝ) : ℝ := kerrSigma a r θ

/-- The `g_φφ` component of the Kerr metric in Boyer–Lindquist coordinates (eq. (2.1)):
`((r² + a²)² − Δ a² sin² θ) / Σ · sin² θ`. -/
noncomputable def gPhiPhi (M a r θ : ℝ) : ℝ :=
  ((r ^ 2 + a ^ 2) ^ 2 - kerrDelta M a r * a ^ 2 * sin θ ^ 2) / kerrSigma a r θ * sin θ ^ 2

/-- Area of the event horizon: the area of the 2-surface `t = const`, `r = r₊`,
computed from the induced metric `g_θθ dθ² + g_φφ dφ²`, with `θ ∈ [0, π]`, `φ ∈ [0, 2π]`. -/
noncomputable def horizonArea (M a : ℝ) : ℝ :=
  ∫ θ in (0 : ℝ)..π, ∫ _φ in (0 : ℝ)..(2 * π),
    √(gThetaTheta a (rPlus M a) θ * gPhiPhi M a (rPlus M a) θ)

/-- Surface gravity of the Kerr horizon, `κ = √(M² − a²) / (2 M (M + √(M² − a²)))`
(eq. (3.3)). -/
noncomputable def surfaceGravity (M a : ℝ) : ℝ :=
  √(M ^ 2 - a ^ 2) / (2 * M * (M + √(M ^ 2 - a ^ 2)))

/-- Angular velocity of the horizon, `Ω_H = a / (2 M (M + √(M² − a²)))` (eq. (2.42)). -/
noncomputable def horizonAngularVelocity (M a : ℝ) : ℝ :=
  a / (2 * M * (M + √(M ^ 2 - a ^ 2)))

/-- Mass of an evaporating Schwarzschild black hole of initial mass `M₀` at time `t`,
`M(t) = (M₀³ − t / (256 π))^{1/3}` (eq. (4.137)). -/
noncomputable def evaporatingMass (M₀ t : ℝ) : ℝ :=
  (M₀ ^ 3 - t / (256 * π)) ^ ((1 : ℝ) / 3)

end KerrBlackHoleThermo


