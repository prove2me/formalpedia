-- Prove2me | Definitions.Def_Arxiv1506_07229_Basic
-- name    : Arxiv1506_07229_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-24T02:01:49.707866+00:00
-- url     : https://prove2.me/theorems/04c4c09a-978d-42d1-b70d-03772b639144
-- title:
--   Kramers-Kronig relations, Dirac-model permittivity and the local slab model
-- statement:
--   Objects of Nazarov (2015), Eq. (5), Eq. (10), Appendix A and Appendix B. Atomic units are used, so $e^2=\hbar=m_e=1$.
--
--   1. **Upper half-plane.** $\mathbb{C}_+=\{\omega\in\mathbb{C}:\operatorname{Im}\omega>0\}$, and its closure $\overline{\mathbb{C}_+}=\{\operatorname{Im}\omega\ge0\}$.
--   2. **Kramers-Kronig relations (Eq. 5).** A response function $R:\mathbb{R}\to\mathbb{C}$ of real frequency (only its values at $\omega\ge0$ enter) satisfies the KK relations if $R(\omega)$ tends to a real limit $R(\infty)$ as $\omega\to\infty$ and, for every $\omega\ge0$,
--   $$\operatorname{Re}R(\omega)=R(\infty)+\frac{2}{\pi}\,\mathcal P\!\int_0^\infty\frac{\omega'\operatorname{Im}R(\omega')}{\omega'^2-\omega^2}\,d\omega',\qquad \operatorname{Im}R(\omega)=-\frac{2\omega}{\pi}\,\mathcal P\!\int_0^\infty\frac{\operatorname{Re}R(\omega')-R(\infty)}{\omega'^2-\omega^2}\,d\omega'.$$
--   The principal value is the limit as $\delta\to0^+$ of the integral over $(0,\infty)\setminus(\omega-\delta,\omega+\delta)$.
--   3. **Array-to-layer relation (Eq. 10).** For a layer in an array with separation $d$, wave number $q$ and array permittivity $\varepsilon_{3D}$,
--   $$\frac1\varepsilon=1+\frac12\,\frac{1}{\frac{1}{[1/\varepsilon_{3D}-1]\,qd}+\frac{1}{e^{qd}-1}}.$$
--   4. **Strictly-2D Dirac model of graphene (Appendix A).** Undoped graphene with Fermi velocity $v$, bands $\pm v|k|$ and spin-valley degeneracy $4$, at wave vector $Q=(q,0)$ and imaginary frequency $iu$, has RPA density response
--   $$\chi(q,iu)=-\frac{4}{(2\pi)^2}\int_{\mathbb{R}^2}\big(1-\cos\theta_{k,k+Q}\big)\frac{S}{S^2+u^2}\,d^2k,\qquad S=v(|k|+|k+Q|).$$
--   Its permittivity is $\varepsilon(q,iu)=1-\frac{2\pi}{q}\chi(q,iu)$.
--   5. **Slab model (Appendix B).** A slab $|z|\le a/2$ has local permittivity $\varepsilon=\varepsilon(\omega)$ and vacuum outside. Under the external potential $1$, the total potential is $1+A_1e^{-qz}$ for $z>a/2$, $1/\varepsilon+A_2e^{-qz}+B_2e^{qz}$ for $|z|\le a/2$, and $1+B_3e^{qz}$ for $z<-a/2$ (B2). The boundary conditions (B3) are continuity of $\phi$ and of $\varepsilon(z)\phi'(z)$ at $z=\pm a/2$. The coefficients of (B4) are
--   $$A_2=B_2=\frac{\varepsilon-1}{\varepsilon}\frac{e^{aq/2}}{1+e^{aq}+\varepsilon(e^{aq}-1)},\qquad A_1=B_3=\varepsilon(1-e^{aq})A_2.$$
--   The induced charge (B6) is the density $\frac{q^2}{4\pi}(\frac1\varepsilon-1)$ on $|z|<a/2$, plus the point charges $\frac{q}{4\pi}[(A_1-A_2)e^{-qa/2}+B_2e^{qa/2}]$ at $z=a/2$ and $\frac{q}{4\pi}[(B_3-B_2)e^{-qa/2}+A_2e^{qa/2}]$ at $z=-a/2$. The Q2D inverse permittivity of the slab (B8) is
--   $$\frac{1}{\varepsilon(q,\omega)}=1+\frac{qa}{2}\Big[\frac{1}{\varepsilon(\omega)}-1\Big]+A_1e^{-qa/2}+2A_2\sinh\frac{qa}{2}.$$
--   6. **Drude permittivity and 2D electron gas.** (B9) is $\varepsilon(\omega)=1-\omega_p^2/(\omega+i\eta)^2$. (B10) is $\varepsilon(q,\omega)=1-2\pi n_{2D}q/(\omega+i\eta)^2$.
--
--   **Formalization Note** In the Dirac model the wave vector is taken along the first axis; the model is isotropic. The cosine factor is written as $k\cdot(k+Q)/(|k||k+Q|)$. It is undefined only at $k=0$ and $k=-Q$, a set of measure zero. The charge density (B6) is encoded by its action $\int\rho\,t\,dz$ on functions $t$, and $\int\rho\,dz$ is its value at $t=1$. $\omega_p^2$ is a real parameter `wp2`.
-- source:
--   V. U. Nazarov, Negative static permittivity and violation of Kramers-Kronig relations in quasi-two-dimensional crystals, arXiv:1506.07229v3 (2015), main text Eqs. (5), (6), (10), PDF pp. 2-3; Appendix A, Eq. (A1), PDF p. 6; Appendix B, Eqs. (B2)-(B10), PDF pp. 6-8

import Mathlib

/-!
V. U. Nazarov, *Negative static permittivity and violation of Kramers-Kronig relations in
quasi-two-dimensional crystals*, arXiv:1506.07229v3 (2015): the Kramers-Kronig relations (Eq. (5)),
the upper half of the complex frequency plane, the array-to-layer relation (Eq. (10)), the
strictly-2D Dirac model of graphene (Appendix A, Eq. (A1)), and the local slab model of
Appendix B (Eqs. (B2)-(B4), (B6), (B8), (B9), (B10)).
-/

open MeasureTheory Filter Topology Real

noncomputable section

namespace Arxiv1506_07229

/-- Introduction and Eq. (6), p. 1-2: the upper half of the complex `ω`-plane, `Im ω > 0`. -/
def upperHalf : Set ℂ := {z : ℂ | 0 < z.im}

/-- The closed upper half of the complex `ω`-plane, `Im ω ≥ 0` (the real axis included), on which
the Cauchy formula of Eq. (7), p. 3, is applied. -/
def closedUpperHalf : Set ℂ := {z : ℂ | 0 ≤ z.im}

/-- Eq. (5), p. 2: the Kramers-Kronig relations for a response function `R(ω)` of real frequency
`ω ≥ 0`. `R(∞)` is the (real) limit of `R(ω)` as `ω → ∞`, and the principal value `𝒫∫₀^∞` is the
limit as `δ → 0⁺` of the integral over `(0, ∞)` with `(ω - δ, ω + δ)` removed:
`Re R(ω) = R(∞) + (2/π) 𝒫∫₀^∞ ω' Im R(ω') / (ω'² - ω²) dω'` and
`Im R(ω) = -(2ω/π) 𝒫∫₀^∞ (Re R(ω') - R(∞)) / (ω'² - ω²) dω'` for every `ω ≥ 0`. -/
def KKRelations (R : ℝ → ℂ) : Prop :=
  ∃ Rinf : ℝ, Tendsto R atTop (𝓝 (Rinf : ℂ)) ∧
    ∀ ω : ℝ, 0 ≤ ω →
      Tendsto (fun δ : ℝ => Rinf + (2 / π) *
          ∫ x in Set.Ioi (0 : ℝ) \ Set.Ioo (ω - δ) (ω + δ), x * (R x).im / (x ^ 2 - ω ^ 2))
        (𝓝[>] 0) (𝓝 (R ω).re) ∧
      Tendsto (fun δ : ℝ => -(2 * ω / π) *
          ∫ x in Set.Ioi (0 : ℝ) \ Set.Ioo (ω - δ) (ω + δ), ((R x).re - Rinf) / (x ^ 2 - ω ^ 2))
        (𝓝[>] 0) (𝓝 (R ω).im)

/-- Eq. (10), p. 3 (from Nazarov et al., PRB 89, 195423 (2014)): the approximate inverse
permittivity `1/ε(q, ω)` of a single layer in terms of the 3D permittivity `ε_3D = ε_3D(q, ω; d)`
of the array of layers with separation `d`:
`1/ε = 1 + (1/2) / ( 1/([1/ε_3D - 1] q d) + 1/(e^{qd} - 1) )`. -/
def invEpsFrom3D (q d : ℝ) (eps3D : ℂ) : ℂ :=
  1 + (1 / 2) * (1 / (1 / ((eps3D⁻¹ - 1) * (q * d)) + 1 / ((Real.exp (q * d) : ℂ) - 1)))

/-- Appendix A, p. 6 (refs. Dobson et al. 2006, Wunsch et al. 2006): the RPA density-response
function `χ(q, iu)` at imaginary frequency `iu` of undoped graphene viewed as a strictly 2D system
of massless Dirac electrons with Fermi velocity `v`, bands `E_{k,±} = ±v|k|`, spin times valley
degeneracy `4`, the lower band filled, and in-plane wave vector `Q = (q, 0)`:
`χ(q, iu) = -(4/(2π)²) ∫_{ℝ²} (1 - cos θ_{k,k+Q}) S/(S² + u²) d²k`, with
`S = v(|k| + |k + Q|)` and `cos θ_{k,k+Q} = k·(k+Q)/(|k||k+Q|)`. -/
def diracChi (v q u : ℝ) : ℝ :=
  -(4 / (2 * π) ^ 2) * ∫ k : ℝ × ℝ,
    (1 - (k.1 * (k.1 + q) + k.2 ^ 2) /
        (Real.sqrt (k.1 ^ 2 + k.2 ^ 2) * Real.sqrt ((k.1 + q) ^ 2 + k.2 ^ 2))) *
      (v * (Real.sqrt (k.1 ^ 2 + k.2 ^ 2) + Real.sqrt ((k.1 + q) ^ 2 + k.2 ^ 2)) /
        ((v * (Real.sqrt (k.1 ^ 2 + k.2 ^ 2) + Real.sqrt ((k.1 + q) ^ 2 + k.2 ^ 2))) ^ 2 + u ^ 2))

/-- Appendix A, p. 6: the RPA permittivity of graphene viewed as a strictly 2D system at
imaginary frequency `iu`, `ε(q, iu) = 1 - (2π/q) χ(q, iu)`, with the 2D Coulomb interaction
`2π/q` and `χ` the Dirac-model response `diracChi`. -/
def dirac2DEps (v q u : ℝ) : ℝ := 1 - (2 * π / q) * diracChi v q u

/-- Appendix B, Eq. (B4), p. 7: the coefficient
`A₂ = B₂ = ((ε - 1)/ε) e^{aq/2} / (1 + e^{aq} + ε (e^{aq} - 1))` of the slab of thickness `a`
with local permittivity `ε = ε(ω)`, at in-plane wave number `q`. -/
def slabA2 (eps : ℂ) (a q : ℝ) : ℂ :=
  (eps - 1) / eps * (Real.exp (a * q / 2) : ℂ) /
    (1 + (Real.exp (a * q) : ℂ) + eps * ((Real.exp (a * q) : ℂ) - 1))

/-- Appendix B, Eq. (B4), p. 7: the coefficient `A₁ = B₃ = ε (1 - e^{aq}) A₂` of the slab. -/
def slabA1 (eps : ℂ) (a q : ℝ) : ℂ :=
  eps * (1 - (Real.exp (a * q) : ℂ)) * slabA2 eps a q

/-- Appendix B, Eq. (B3), p. 6-7: the boundary conditions at `z = ± a/2` on the coefficients
`A₁, A₂, B₂, B₃` of the total potential (B2): continuity of `φ` (first two) and of
`D_z = -ε(z) dφ/dz` (last two). -/
def slabBC (eps : ℂ) (a q : ℝ) (A1 A2 B2 B3 : ℂ) : Prop :=
  1 + A1 * (Real.exp (-(q * a / 2)) : ℂ) =
      1 / eps + A2 * (Real.exp (-(q * a / 2)) : ℂ) + B2 * (Real.exp (q * a / 2) : ℂ) ∧
    1 + B3 * (Real.exp (-(q * a / 2)) : ℂ) =
      1 / eps + A2 * (Real.exp (q * a / 2) : ℂ) + B2 * (Real.exp (-(q * a / 2)) : ℂ) ∧
    -(A1 * (Real.exp (-(q * a / 2)) : ℂ)) =
      eps * (-(A2 * (Real.exp (-(q * a / 2)) : ℂ)) + B2 * (Real.exp (q * a / 2) : ℂ)) ∧
    B3 * (Real.exp (-(q * a / 2)) : ℂ) =
      eps * (-(A2 * (Real.exp (q * a / 2) : ℂ)) + B2 * (Real.exp (-(q * a / 2)) : ℂ))

/-- Appendix B, Eq. (B2), p. 6: the `z`-profile of the total potential of the slab under the
external potential `φ_ext = 1` (the factor `e^{i(q·r - ωt)}` removed): `1 + A₁ e^{-qz}` in region I
(`z > a/2`), `1/ε + A₂ e^{-qz} + B₂ e^{qz}` in region II (`|z| ≤ a/2`), `1 + B₃ e^{qz}` in region III
(`z < -a/2`). -/
def slabPot (eps : ℂ) (a q : ℝ) (A1 A2 B2 B3 : ℂ) (z : ℝ) : ℂ :=
  if a / 2 < z then 1 + A1 * (Real.exp (-(q * z)) : ℂ)
  else if -(a / 2) ≤ z then
    1 / eps + A2 * (Real.exp (-(q * z)) : ℂ) + B2 * (Real.exp (q * z) : ℂ)
  else 1 + B3 * (Real.exp (q * z) : ℂ)

/-- Appendix B, Eq. (B6), p. 7: the induced charge density of the slab, a density
`(q²/4π)(1/ε - 1)` on `|z| < a/2` plus point charges at `z = ± a/2`, given by its action
`∫ ρ(z) t(z) dz` on a function `t`:
`(q/4π) { q (1/ε - 1) ∫_{-a/2}^{a/2} t + [(A₁ - A₂) e^{-qa/2} + B₂ e^{qa/2}] t(a/2)
  + [(B₃ - B₂) e^{-qa/2} + A₂ e^{qa/2}] t(-a/2) }`. With `t = 1` it is `∫ ρ dz`. -/
def slabRho (eps : ℂ) (a q : ℝ) (A1 A2 B2 B3 : ℂ) (t : ℝ → ℂ) : ℂ :=
  (q / (4 * π) : ℂ) *
    ((q : ℂ) * (1 / eps - 1) * (∫ z in (-(a / 2))..(a / 2), t z) +
      ((A1 - A2) * (Real.exp (-(q * a / 2)) : ℂ) + B2 * (Real.exp (q * a / 2) : ℂ)) * t (a / 2) +
      ((B3 - B2) * (Real.exp (-(q * a / 2)) : ℂ) + A2 * (Real.exp (q * a / 2) : ℂ)) * t (-(a / 2)))

/-- Appendix B, Eq. (B8), p. 7: the Q2D inverse permittivity of the slab,
`1/ε(q, ω) = 1 + (qa/2)[1/ε(ω) - 1] + A₁ e^{-qa/2} + 2 A₂ sinh(qa/2)`, with `A₁, A₂` from (B4)
and `eps = ε(ω)` the local constituent permittivity. -/
def slabInvEps (eps : ℂ) (a q : ℝ) : ℂ :=
  1 + (q * a / 2 : ℂ) * (1 / eps - 1) + slabA1 eps a q * (Real.exp (-(q * a / 2)) : ℂ) +
    2 * slabA2 eps a q * (Real.sinh (q * a / 2) : ℂ)

/-- Appendix B, Eq. (B9), p. 8: the Drude constituent permittivity
`ε(ω) = 1 - ω_p² / (ω + iη)²`, with `wp2 = ω_p²` and damping `η`. -/
def drudeEps (wp2 η ω : ℝ) : ℂ := 1 - (wp2 : ℂ) / ((ω : ℂ) + (η : ℂ) * Complex.I) ^ 2

/-- Appendix B, Eq. (B10), p. 8: the long-wave permittivity of the 2D electron gas of areal density
`n = n_2D` with damping `η`, `ε(q, ω) = 1 - 2π n q / (ω + iη)²`. -/
def twoDEGEps (n η q ω : ℝ) : ℂ :=
  1 - (2 * π * n * q : ℂ) / ((ω : ℂ) + (η : ℂ) * Complex.I) ^ 2

end Arxiv1506_07229


