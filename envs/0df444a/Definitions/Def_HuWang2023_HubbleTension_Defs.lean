-- Prove2me | Definitions.Def_HuWang2023_HubbleTension_Defs
-- name    : HuWang2023_HubbleTension_Defs
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-13T00:38:07.720027+00:00
-- url     : https://prove2.me/theorems/c533766a-db1c-4ffd-939f-471189abc86f
-- title:
--   Hu–Wang 2023: flat ΛCDM distances, FRB dispersion measure and $H_0$ diagnostics (Eqs. (1)–(8))
-- statement:
--   Definitions for the quantitative relations used in the review of Hu and Wang (2023), all in a **spatially flat ΛCDM** background with present-day matter density parameter $\Omega_m$ and $\Omega_\Lambda = 1-\Omega_m$.
--
--   1. **Expansion rate.** $E(z) = \sqrt{\Omega_m(1+z)^3 + 1 - \Omega_m}$ and $H(z) = H_0\,E(z)$.
--   2. **Angular diameter distance between two redshifts** (Eq. (2)):
--   $$D_{12} = \frac{c}{H_0(1+z_2)}\int_{z_1}^{z_2}\frac{dz'}{E(z')}.$$
--   3. **Angular diameter distance from the observer** (Eq. (3)): $D(z) = D_{12}$ with $z_1 = 0$, $z_2 = z$.
--   4. **Time-delay distance** of a lens at $z_{\rm lens}$ and a source at $z_s$ (Eq. (1)):
--   $$D_{\Delta t} = (1+z_{\rm lens})\frac{D_d D_s}{D_{ds}},$$
--   with $D_d = D(z_{\rm lens})$, $D_s = D(z_s)$, $D_{ds} = D_{12}(z_{\rm lens}, z_s)$.
--   5. **FRB dispersion measure.** $A = 3c/(8\pi G m_p)$; electron fraction $f_e = Y_H X_{e,H} + \tfrac12 Y_{He} X_{e,He}$; mean IGM dispersion measure (Eq. (5))
--   $$\langle {\rm DM_{IGM}}(z)\rangle = \frac{A\Omega_b H_0^2}{H_0}\int_0^{z}\frac{f_{\rm IGM}(z')f_e(z')(1+z')}{\sqrt{\Omega_m(1+z')^3+1-\Omega_m}}\,dz';$$
--   observed dispersion measure (Eq. (4)) ${\rm DM_{obs}}(z) = {\rm DM_{MW}} + {\rm DM_{IGM}}(z) + {\rm DM_{host}}(z)/(1+z)$.
--   6. **Weighted bin redshift** (Eq. (6)): $\bar z = \sum_n z_n\sigma_n^{-2} \big/ \sum_n \sigma_n^{-2}$ over a finite set of data points.
--   7. **Evolution function** (Eq. (7)): $g(z) = \tilde H_0/(1+z)^{\alpha}$.
--   8. **$H_0$ diagnostic** (Eq. (8)) of an arbitrary expansion history $H$: $H_0(z) = H(z)/\sqrt{1-\Omega_{m0}+\Omega_{m0}(1+z)^3}$.
--
--   These are the shared objects of every statement in the mission.
--
--   **Formalization Note** All quantities are real-valued functions of real parameters; no positivity is built into the definitions, so each theorem states the hypotheses it needs. Division by zero returns $0$ in Lean. Eq. (3) of the paper prints the integrand as $\sqrt{\Omega_m(1+z')^3+\Omega_\Lambda}$; the definition uses the reciprocal $(\Omega_m(1+z')^3+\Omega_\Lambda)^{-1/2}$, as in Eq. (2) and in the standard flat-ΛCDM distance formula; with the printed integrand Eqs. (2) and (3) would be mutually inconsistent.
-- source:
--   Jian-Ping Hu and Fa-Yin Wang, *Hubble Tension: The Evidence of New Physics*, Universe 2023, 9(2), 94, https://doi.org/10.3390/universe9020094, Section 3.1 (p. 4, Eqs. (1)–(3)), Section 3.4 (p. 6, Eqs. (4)–(5)), Section 5 (pp. 12–14, Eqs. (6)–(8))

import Mathlib

/-!
Definitions for the formal content of
Hu & Wang, "Hubble Tension: The Evidence of New Physics", Universe 2023, 9, 94,
https://doi.org/10.3390/universe9020094 (Eqs. (1)–(8)).
-/

namespace HuWang2023

/-- Dimensionless expansion rate of a spatially flat ΛCDM universe,
`E(z) = √(Ωₘ (1+z)³ + Ω_Λ)` with `Ω_Λ = 1 - Ωₘ` (flatness). -/
noncomputable def flatE (Ωm z : ℝ) : ℝ :=
  Real.sqrt (Ωm * (1 + z) ^ 3 + (1 - Ωm))

/-- Hubble rate of flat ΛCDM, `H(z) = H₀ E(z)`. -/
noncomputable def flatHubble (H0 Ωm z : ℝ) : ℝ :=
  H0 * flatE Ωm z

/-- Eq. (2): angular diameter distance between redshifts `z₁ ≤ z₂` in flat ΛCDM,
`D₁₂ = c / (H₀ (1+z₂)) ∫_{z₁}^{z₂} (Ωₘ(1+z')³ + Ω_Λ)^{-1/2} dz'`. -/
noncomputable def angDistBetween (c H0 Ωm z1 z2 : ℝ) : ℝ :=
  c / (H0 * (1 + z2)) * ∫ z' in z1..z2, (flatE Ωm z')⁻¹

/-- Eq. (3) (with the standard integrand `(Ωₘ(1+z')³ + Ω_Λ)^{-1/2}`, as in Eq. (2)):
angular diameter distance from the observer (`z = 0`) to redshift `z`. -/
noncomputable def angDist (c H0 Ωm z : ℝ) : ℝ :=
  angDistBetween c H0 Ωm 0 z

/-- Eq. (1): time-delay distance of a strong lens at redshift `z_lens` with source at `z_s`,
`D_Δt = (1 + z_lens) D_d D_s / D_ds`. -/
noncomputable def timeDelayDistance (c H0 Ωm zl zs : ℝ) : ℝ :=
  (1 + zl) * angDist c H0 Ωm zl * angDist c H0 Ωm zs / angDistBetween c H0 Ωm zl zs

/-- The constant `A = 3c / (8π G m_p)` of Eq. (5). -/
noncomputable def dmConstA (c G mp : ℝ) : ℝ :=
  3 * c / (8 * Real.pi * G * mp)

/-- Electron fraction `f_e = Y_H X_{e,H} + ½ Y_He X_{e,He}` (text after Eq. (5)). -/
noncomputable def electronFraction (YH XeH YHe XeHe : ℝ) : ℝ :=
  YH * XeH + (1 / 2) * YHe * XeHe

/-- Eq. (5): mean intergalactic dispersion measure of an FRB at redshift `z` in a flat universe,
`⟨DM_IGM(z)⟩ = (A Ω_b H₀² / H₀) ∫₀^z f_IGM(z') f_e(z') (1+z') / √(Ωₘ(1+z')³ + 1 - Ωₘ) dz'`. -/
noncomputable def meanDMIGM (A Ωb H0 Ωm : ℝ) (fIGM fe : ℝ → ℝ) (z : ℝ) : ℝ :=
  A * Ωb * H0 ^ 2 / H0 *
    ∫ z' in (0 : ℝ)..z, fIGM z' * fe z' * (1 + z') / Real.sqrt (Ωm * (1 + z') ^ 3 + 1 - Ωm)

/-- Eq. (4): observed FRB dispersion measure
`DM_obs(z) = DM_MW + DM_IGM(z) + DM_host(z) / (1+z)`. -/
noncomputable def dmObs (DMMW : ℝ) (DMIGM DMhost : ℝ → ℝ) (z : ℝ) : ℝ :=
  DMMW + DMIGM z + DMhost z / (1 + z)

/-- Eq. (6): inverse-variance weighted mean redshift of a bin,
`z̄ = (∑ₙ zₙ σₙ⁻²) / (∑ₙ σₙ⁻²)`. -/
noncomputable def weightedMeanRedshift {ι : Type} (s : Finset ι) (z σ : ι → ℝ) : ℝ :=
  (∑ n ∈ s, z n * (σ n) ^ (-2 : ℤ)) / (∑ n ∈ s, (σ n) ^ (-2 : ℤ))

/-- Eq. (7): the evolution function `g(z) = H₀(z) = H̃₀ / (1+z)^α`. -/
noncomputable def gEvolution (H0tilde α z : ℝ) : ℝ :=
  H0tilde / (1 + z) ^ α

/-- Eq. (8): the `H₀` diagnostic `H0(z) = H(z) / √(1 - Ωₘ₀ + Ωₘ₀ (1+z)³)`
of an arbitrary expansion history `H`. -/
noncomputable def h0Diagnostic (Ωm0 : ℝ) (H : ℝ → ℝ) (z : ℝ) : ℝ :=
  H z / Real.sqrt (1 - Ωm0 + Ωm0 * (1 + z) ^ 3)

end HuWang2023


