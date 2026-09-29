-- Prove2me | Definitions.Def_GKP1998_Defs
-- name    : GKP1998_Defs
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-26T00:42:18.332129+00:00
-- url     : https://prove2.me/theorems/872005d3-7bca-4246-818b-61586d70e97f
-- title:
--   Gubser–Klebanov–Polyakov (1998): modified Bessel functions, throat operator, flux factor, two-point function
-- statement:
--   Definitions shared by all statements of the mission (namespace `GKP1998`).
--
--   - $K_\nu(x)=\int_0^\infty e^{-x\cosh t}\cosh(\nu t)\,dt$ (`besselK`), the modified Bessel function of the second kind, for $x>0$ and real $\nu$.
--   - $I_\nu(x)=\sum_{j\ge0}\frac{(x/2)^{2j+\nu}}{j!\,\Gamma(j+\nu+1)}$ (`besselI`), with the convention $1/\Gamma(\text{pole})=0$.
--   - $(\mathcal D_{k,\mu}f)(z)=z^3\partial_z(z^{-3}\partial_zf)-k^2f-\mu z^{-2}f$ (`throatOperator`), the radial operator of Eqs. (20), (34), (40).
--   - $\tilde f_k(z)=z^2K_\nu(kz)/(R^2K_\nu(kR))$ (`radialProfile`), Eqs. (23), (35), (42).
--   - $\mathcal F(k)=[z^{-3}\partial_z\log\tilde f_k]_{z=R}$ (`fluxFactor`), Eqs. (25), (27), (37).
--   - $\frac{N^2}{16\pi^2}\mathcal F(k)$ (`twoPointFunction`), the coefficient of $(2\pi)^4\delta^4(k+q)$ in $\langle O(k)O(q)\rangle$, Eq. (26).
--   - $\nu=\sqrt{4+(mR)^2}$ (`massiveOrder`), Eq. (41), and $\Delta=2+\nu$ (`scalingDimension`), Eq. (45).
-- source:
--   S.S. Gubser, I.R. Klebanov, A.M. Polyakov, Gauge theory correlators from non-critical string theory, Phys. Lett. B 428 (1998) 105-114, arXiv:hep-th/9802109, pp. 109-112, Eqs. (20), (22)-(27), (34)-(35), (40)-(45)

import Mathlib

/-!
# Gubser–Klebanov–Polyakov (1998): definitions

Definitions for the draft Prove2Me mission on *Gauge theory correlators from
non-critical string theory* (S.S. Gubser, I.R. Klebanov, A.M. Polyakov,
Phys. Lett. B 428 (1998) 105–114).
-/

noncomputable section

namespace GKP1998

/-- Modified Bessel function of the second kind (Macdonald function), via the integral
representation `K_ν(x) = ∫₀^∞ exp(-x cosh t) cosh(ν t) dt`, valid for `x > 0` and every
real order `ν`. (For `x ≤ 0` the integral diverges and the Lean value is `0`; only `x > 0`
is used.) -/
def besselK (ν x : ℝ) : ℝ :=
  ∫ t in Set.Ioi (0 : ℝ), Real.exp (-x * Real.cosh t) * Real.cosh (ν * t)

/-- Modified Bessel function of the first kind,
`I_ν(x) = ∑_{j ≥ 0} (x/2)^{2j+ν} / (j! Γ(j+ν+1))`, for `x > 0` and every real `ν`.
When `j + ν + 1` is a non-positive integer, `Real.Gamma` is `0` and Lean's `1/0 = 0`
reproduces the standard convention `1/Γ(pole) = 0`. -/
def besselI (ν x : ℝ) : ℝ :=
  ∑' j : ℕ, (x / 2) ^ (2 * (j : ℝ) + ν) / ((j.factorial : ℝ) * Real.Gamma ((j : ℝ) + ν + 1))

/-- The radial ("throat") operator of Eqs. (20), (34), (40) in momentum space:
`(𝒟 f)(z) = z³ ∂_z (z⁻³ ∂_z f) − k² f − (msq / z²) f`.
Here `k² = η^{μν} k_μ k_ν` is the Euclidean (space-like) squared four-momentum, and
`msq` is the centrifugal coefficient: `0` for the s-wave (20), `l(l+4)` for the `l`-th
partial wave (34), and `(mR)²` for a scalar string state of mass `m` (40). -/
def throatOperator (k msq : ℝ) (f : ℝ → ℝ) (z : ℝ) : ℝ :=
  z ^ 3 * deriv (fun w => deriv f w / w ^ 3) z - k ^ 2 * f z - msq / z ^ 2 * f z

/-- The normalised regular radial wave function of Eqs. (23), (35), (42):
`f̃_k(z) = z² K_ν(kz) / (R² K_ν(kR))`, equal to `1` at `z = R`. -/
def radialProfile (ν k R z : ℝ) : ℝ :=
  z ^ 2 * besselK ν (k * z) / (R ^ 2 * besselK ν (k * R))

/-- The flux factor of Eqs. (25), (27), (37):
`𝓕 = [z⁻³ ∂_z log f̃_k(z)]_{z = R}`. -/
def fluxFactor (ν k R : ℝ) : ℝ :=
  deriv (fun z => Real.log (radialProfile ν k R z)) R / R ^ 3

/-- The two-point function coefficient of Eqs. (26) and (44):
`⟨O(k) O(q)⟩ = (2π)⁴ δ⁴(k+q) · twoPointFunction N ν k R`, where
`twoPointFunction N ν k R = N² / (16 π²) · 𝓕`. -/
def twoPointFunction (N ν k R : ℝ) : ℝ :=
  N ^ 2 / (16 * Real.pi ^ 2) * fluxFactor ν k R

/-- The Bessel order `ν = √(4 + (mR)²)` of Eq. (41) for a scalar string state of mass `m`
in the AdS₅ throat of radius `R`. -/
def massiveOrder (m R : ℝ) : ℝ :=
  Real.sqrt (4 + (m * R) ^ 2)

/-- The scaling dimension `Δ = 2 + ν` of Eq. (45) of the gauge theory operator coupling to
a bulk field whose radial wave function has Bessel order `ν`. -/
def scalingDimension (ν : ℝ) : ℝ :=
  2 + ν

end GKP1998

end


