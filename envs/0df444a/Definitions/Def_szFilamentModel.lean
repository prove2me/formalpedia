-- Prove2me | Definitions.Def_szFilamentModel
-- name    : szFilamentModel
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-23T19:19:43.698789+00:00
-- url     : https://prove2.me/theorems/df8b7ed3-d5ef-4a03-a059-1fe98049de91
-- title:
--   Cylindrical Gaussian filament model (SZ and lensing projections)
-- statement:
--   The model layer of the cylindrical Gaussian filament analysis of de Graaff et al. (2019). All quantities are real numbers; no physical units are carried by the formalization, so every constant appears as an explicit real variable.
--
--   - **SZ prefactor.** $P = \dfrac{k_B T_e \sigma_T}{m_e c^2}$, the constant multiplying the line-of-sight integral in the Compton parameter of Eq. (1).
--
--   - **Gaussian cylinder profile.** For a central amplitude $n_0$, an intrinsic Gaussian width $\sigma$ and a beam width $\sigma_B$, the profile of Eq. (A.1)
--   $$n_e(\ell, r_\perp) = n_0 \exp\!\left(-\frac{\ell^2}{2\sigma^2}\right) \exp\!\left(-\frac{r_\perp^2}{2(\sigma^2 + \sigma_B^2)}\right),$$
--   where $\ell$ is the line-of-sight coordinate and $r_\perp$ the transverse coordinate in the plane of the sky; the transverse direction carries the extra beam smoothing $\sigma_B$.
--
--   - **Compton parameter.** For a prefactor $P$ and a line-of-sight profile $f$, $y = P \int_{\mathbb{R}} f(\ell)\, d\ell$, which is Eq. (1) with the integral taken over the whole line of sight.
--
--   - **Lensing efficiency prefactor.** For a thin lens at comoving distance $D_L$ with source distance $D_S$ and scale factor $a$,
--   $$Q = \frac{3 H_0^2 \Omega_m}{2c^2} \cdot \frac{D_L (D_S - D_L)}{D_S} \cdot \frac{1}{a},$$
--   the geometric factor appearing in the convergence integral of Eq. (2).
--
--   - **Convergence.** For a prefactor $Q$ and a density-contrast profile $\delta$ along the line of sight, $\kappa = Q \int_{\mathbb{R}} \delta(\ell)\, d\ell$: Eq. (2) specialized to a structure thin enough that the geometric factor is constant across it.
--
--   - **Total electron content.** For a filament of length $L$ and a two-dimensional profile $n_e$, $N_e = L \iint n_e(\ell, r_\perp)\, d\ell\, dr_\perp$, the left-hand side of Eq. (A.4).
--
--   These definitions are shared by every statement in the mission, so that the projection integral, the density calibration and the lensing counterpart are all phrased against one model.
-- source:
--   de Graaff A., Cai Y.-C., Heymans C., Peacock J. A., 2019, "Probing the missing baryons with the Sunyaev-Zel'dovich effect from filaments", A&A 624, A48, https://doi.org/10.1051/0004-6361/201935159, p. 2 Eq. (1), p. 3 Eq. (2), p. 12 Appendix A Eq. (A.1)

import Mathlib

namespace SZFilaments

open MeasureTheory Real

/-- The thermal Sunyaev–Zel'dovich prefactor `k_B T_e σ_T / (m_e c²)`. -/
noncomputable def szPrefactor (kB Te sigmaT me c : ℝ) : ℝ :=
  kB * Te * sigmaT / (me * c ^ 2)

/-- The beam-convolved Gaussian cylinder profile of a filament:
`n₀ exp(-ℓ²/(2σ²)) exp(-r⊥²/(2(σ² + σ_B²)))`. -/
noncomputable def gaussianFilamentProfile (n0 sigma sigmaB l r : ℝ) : ℝ :=
  n0 * Real.exp (-l ^ 2 / (2 * sigma ^ 2)) *
    Real.exp (-r ^ 2 / (2 * (sigma ^ 2 + sigmaB ^ 2)))

/-- The Compton `y` parameter of a line-of-sight electron density profile:
`y = pref * ∫ n_e dℓ`, the prefactor `pref` being `k_B T_e σ_T / (m_e c²)`. -/
noncomputable def comptonY (pref : ℝ) (ne : ℝ → ℝ) : ℝ := pref * ∫ l : ℝ, ne l

/-- The thin-lens lensing efficiency prefactor
`(3 H₀² Ω_m / (2 c²)) · (D_L (D_S - D_L) / D_S) / a`. -/
noncomputable def lensingPrefactor (H0 Om c a DL DS : ℝ) : ℝ :=
  3 * H0 ^ 2 * Om / (2 * c ^ 2) * (DL * (DS - DL) / DS) / a

/-- The convergence obtained by integrating a density-contrast profile along the line
of sight against a lensing efficiency prefactor. -/
noncomputable def convergence (pref : ℝ) (delta : ℝ → ℝ) : ℝ := pref * ∫ l : ℝ, delta l

/-- The total number of electrons in a filament of length `L`:
`N_e = L ∫∫ n_e(ℓ, r⊥) dℓ dr⊥`. -/
noncomputable def totalElectrons (L : ℝ) (ne : ℝ → ℝ → ℝ) : ℝ :=
  L * ∫ r : ℝ, ∫ l : ℝ, ne l r

end SZFilaments


