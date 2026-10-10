-- Prove2me | Definitions.Def_SONATA_Undir_Chain
-- name    : SONATA_Undir_Chain
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T19:14:59.00184+00:00
-- url     : https://prove2.me/theorems/4a578361-46e0-48ff-a1d3-9335e37272a9
-- title:
--   (34), (41), (42), (49), (52), (55) and App. A — σ(α), η(α), the transformation S^K(z), G_P, G_X, G_Y, ω's, C₁, C₂, 𝒫(α, z), ℛ(α, z)
-- statement:
--   This module defines the scalar quantities of the small-gain chain in §3.3 of Sun, Daneshmand and Scutari. Throughout, $\tilde\mu_{\rm mn}$, $D^\ell_{\rm mn}$, $D_{\rm mx}$, $L_{\rm mx}$, $\mu$ and $\rho$ are the constants of the setting, $\alpha$ is the step size and $\varepsilon_{\rm opt},\varepsilon_x,\varepsilon_y$ are free parameters.
--
--   1. **The bracket of (34), (41), (42).** $a=\big(1-\frac\alpha2\big)\tilde\mu_{\rm mn}+\frac{D^\ell_{\rm mn}}2\alpha-\frac12\varepsilon_{\rm opt}$; condition (34) is $\varepsilon_{\rm opt}>0$ and $a>0$.
--   2. **(41)–(42).**
--   $$\sigma(\alpha)=1-\alpha\,\frac{a}{D_{\rm mx}^2/\mu+a},\qquad \eta(\alpha)=\frac{\frac12\varepsilon_{\rm opt}^{-1}\alpha\cdot D_{\rm mx}^2/\mu+\frac\alpha\mu\,a}{D_{\rm mx}^2/\mu+a}.$$
--   3. **The transformation (49)** of a real sequence $\{s^\nu\}$: $S^K(z)=\max_{\nu=0,\dots,K}|s^\nu|\,z^{-\nu}$.
--   4. **(52a)–(52d).**
--   $$G_P(\alpha,z)=\frac{\eta(\alpha)}{z-\sigma(\alpha)},\quad \omega_p=\frac{z}{z-\sigma(\alpha)}\,p^0,\quad G_X(z)=\frac{1+\varepsilon_x^{-1}}{z-\rho^2(1+\varepsilon_x)},\quad \omega_x=\frac{z}{z-\rho^2(1+\varepsilon_x)}\,\|\mathbf x_\perp^0\|^2,$$
--   $G_Y,\omega_y$ likewise with $\varepsilon_y$ and $\|\mathbf y_\perp^0\|^2$, and
--   $$C_1=\frac6\mu\Big(\Big(\frac{D_{\rm mx}}{\tilde\mu_{\rm mn}}+1\Big)^2+\frac{4L_{\rm mx}^2}{\tilde\mu_{\rm mn}^2}\Big),\qquad C_2=\frac4{\tilde\mu_{\rm mn}^2}.$$
--   5. **(55)** and the remainder of (54) computed in Appendix A:
--   $$\mathcal P(\alpha,z)=G_PG_XC_1\,4L_{\rm mx}^2\rho^2\alpha^2+(2G_PC_1+C_2)G_Y\,2L_{\rm mx}^2\rho^2\alpha^2+(2G_PC_1+C_2)G_Y\,8L_{\rm mx}^2\rho^2\,G_X\rho^2\alpha^2,$$
--   $$\mathcal R(\alpha,z)=C_1\omega_p+(2C_1G_P+C_2)\omega_y+C_1G_P\,4L_{\rm mx}^2\,\omega_x+(2C_1G_P+C_2)G_Y\,8L_{\rm mx}^2\rho^2\,\omega_x.$$
--
--   These are the gains of the loop $P^K\to D^K\to X_\perp^K, Y_\perp^K\to P^K$ that proves Theorem 3.9.
--
--   **Formalization Note.** The functions take the constants as real arguments: $G_P$, $\omega_p$ take $\sigma=\sigma(\alpha)$ and $\eta=\eta(\alpha)$; one function `GXY` (resp. `omegaXY`) serves for both $G_X$ and $G_Y$ (resp. $\omega_x$, $\omega_y$); $\mathcal P$ and $\mathcal R$ take the values of $G_P,G_X,G_Y,C_1,C_2,\omega_p,\omega_x,\omega_y$. The maximum in (49) is a finite maximum over $\nu\in\{0,\dots,K\}$, and $z^{-\nu}$ is $(z^{-1})^\nu$. The factor $\frac12\varepsilon_{\rm opt}$ in (34), (41) and (42) is $\frac12\cdot\varepsilon_{\rm opt}$, and $\frac12\varepsilon_{\rm opt}^{-1}$ is $\frac12\cdot\varepsilon_{\rm opt}^{-1}$, as in (33b). $C_2=4/\tilde\mu_{\rm mn}^2$ is the printed value of (52d) (the bound (47) has 3 in its place).
-- source:
--   Sun, Daneshmand & Scutari, Distributed Optimization Based on Gradient-tracking Revisited, arXiv:1905.02637v2, pp. 16, 18, 21, 22, 35, (34), (41), (42), (49), (52a)–(52d), (55), Appendix A

import Mathlib

namespace SONATA.Undir

/-- The bracket `(1 − α/2) μ̃_mn + (D^ℓ_mn/2) α − ½ ε_opt` shared by (34), (41) and (42)
(pp. 16, 18). Arguments: `mutmn = μ̃_mn`, `Dlmn = D^ℓ_mn`. -/
noncomputable def aBr (mutmn Dlmn α εopt : ℝ) : ℝ :=
  (1 - α / 2) * mutmn + Dlmn / 2 * α - 1 / 2 * εopt

/-- Condition (34) (p. 16) on the free parameter `ε_opt`:
`ε_opt > 0` and `(1 − α/2) μ̃_mn + α D^ℓ_mn/2 − ½ ε_opt > 0`. -/
def Cond34 (mutmn Dlmn α εopt : ℝ) : Prop :=
  0 < εopt ∧ 0 < aBr mutmn Dlmn α εopt

/-- `σ(α)` of (41) (p. 18):
`σ(α) = 1 − α · a / (D²_mx/μ + a)` with `a = aBr μ̃_mn D^ℓ_mn α ε_opt`. -/
noncomputable def sigmaA (μ mutmn Dlmn Dmx α εopt : ℝ) : ℝ :=
  1 - α * aBr mutmn Dlmn α εopt / (Dmx ^ 2 / μ + aBr mutmn Dlmn α εopt)

/-- `η(α)` of (42) (p. 18):
`η(α) = (½ ε_opt⁻¹ α · D²_mx/μ + (α/μ) · a) / (D²_mx/μ + a)` with `a = aBr μ̃_mn D^ℓ_mn α ε_opt`. -/
noncomputable def etaA (μ mutmn Dlmn Dmx α εopt : ℝ) : ℝ :=
  (1 / 2 * εopt⁻¹ * α * (Dmx ^ 2 / μ) + α / μ * aBr mutmn Dlmn α εopt) /
    (Dmx ^ 2 / μ + aBr mutmn Dlmn α εopt)

/-- The transformation (49) (p. 21) of a real sequence `s`:
`S^K(z) = max_{ν = 0, …, K} |s^ν| z^{−ν}` (a finite maximum). -/
noncomputable def trans (s : ℕ → ℝ) (K : ℕ) (z : ℝ) : ℝ :=
  (Finset.range (K + 1)).sup' Finset.nonempty_range_add_one (fun ν => |s ν| * z⁻¹ ^ ν)

/-- `G_P(α, z) = η(α)/(z − σ(α))` ((52a), p. 21), written in terms of `σ = σ(α)`, `η = η(α)`. -/
noncomputable def GP (σ η z : ℝ) : ℝ := η / (z - σ)

/-- `ω_p = z/(z − σ(α)) · p⁰` ((52a), p. 21). -/
noncomputable def omegaP (σ z p0 : ℝ) : ℝ := z / (z - σ) * p0

/-- `G_X(z) = (1 + ε_x⁻¹)/(z − ρ²(1 + ε_x))` ((52b), p. 21); with `ε = ε_y` it is `G_Y(z)` (52c). -/
noncomputable def GXY (ρ ε z : ℝ) : ℝ := (1 + ε⁻¹) / (z - ρ ^ 2 * (1 + ε))

/-- `ω_x = z/(z − ρ²(1 + ε_x)) · ‖x_⊥⁰‖²` ((52b), p. 21); with `ε = ε_y` and `s0 = ‖y_⊥⁰‖²` it is
`ω_y` (52c). -/
noncomputable def omegaXY (ρ ε z s0 : ℝ) : ℝ := z / (z - ρ ^ 2 * (1 + ε)) * s0

/-- `C₁ = (6/μ) ((D_mx/μ̃_mn + 1)² + 4L²_mx/μ̃²_mn)` ((52d), p. 21). -/
noncomputable def C1 (μ mutmn Dmx Lmx : ℝ) : ℝ :=
  6 / μ * ((Dmx / mutmn + 1) ^ 2 + 4 * Lmx ^ 2 / mutmn ^ 2)

/-- `C₂ = 4/μ̃²_mn` ((52d), p. 21). -/
noncomputable def C2 (mutmn : ℝ) : ℝ := 4 / mutmn ^ 2

/-- `𝒫(α, z)` of (55) (p. 22), in terms of `gp = G_P(α, z)`, `gx = G_X(z)`, `gy = G_Y(z)`,
`c1 = C₁`, `c2 = C₂`, `L_mx`, `ρ` and `α`:
`gp·gx·c1·4L²_mx·ρ²·α² + (gp·2c1 + c2)·gy·2L²_mx ρ²·α² + (gp·2c1 + c2)·gy·8L²_mx ρ²·gx·ρ²·α²`. -/
noncomputable def Pcal (gp gx gy c1 c2 Lmx ρ α : ℝ) : ℝ :=
  gp * gx * c1 * (4 * Lmx ^ 2) * ρ ^ 2 * α ^ 2
    + (gp * 2 * c1 + c2) * gy * (2 * Lmx ^ 2 * ρ ^ 2) * α ^ 2
    + (gp * 2 * c1 + c2) * gy * (8 * Lmx ^ 2 * ρ ^ 2) * gx * ρ ^ 2 * α ^ 2

/-- The remainder `ℛ(α, z)` of (54), as computed in Appendix A (p. 35), in terms of
`gp = G_P(α, z)`, `gy = G_Y(z)`, `c1 = C₁`, `c2 = C₂`, `L_mx`, `ρ` and `wp = ω_p`, `wx = ω_x`,
`wy = ω_y`:
`c1·wp + (c1·gp·2 + c2)·wy + c1·gp·4L²_mx·wx + (c1·gp·2 + c2)·gy·8L²_mx ρ²·wx`. -/
noncomputable def Rcal (gp gy c1 c2 Lmx ρ wp wx wy : ℝ) : ℝ :=
  c1 * wp + (c1 * gp * 2 + c2) * wy + c1 * gp * (4 * Lmx ^ 2) * wx
    + (c1 * gp * 2 + c2) * gy * (8 * Lmx ^ 2 * ρ ^ 2) * wx

end SONATA.Undir


