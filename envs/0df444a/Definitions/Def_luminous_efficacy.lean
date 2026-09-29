-- Prove2me | Definitions.Def_luminous_efficacy
-- name    : luminous_efficacy
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-23T17:13:25.753731+00:00
-- url     : https://prove2.me/theorems/9530b107-cbda-490f-816a-ccd856ea50dc
-- title:
--   Photometric model: luminosity function, radiant flux, luminous flux, luminous efficacy
-- statement:
--   The photometric model underlying the mission, transcribed from the "Mathematical definition" section of the source.
--
--   A **spectral radiant flux distribution** is modelled as a finite Borel measure $\mu$ on the wavelength axis $\mathbb{R}$ (wavelengths in nanometres). Using a measure rather than a density covers both cases the source discusses: an ordinary spectrum with spectral radiant flux $\Phi_{e,\lambda}$ is the measure $\mathrm{d}\mu = \Phi_{e,\lambda}\,\mathrm{d}\lambda$, while an ideal monochromatic source is a point mass, which has no density.
--
--   - $K_m = 683.002$ lm/W is the photopic maximum spectral luminous efficacy (attained at $555$ nm), and $1700$ lm/W is its scotopic counterpart (at $507$ nm).
--   - A **luminosity function with peak at $\lambda_0$** is a measurable $V : \mathbb{R} \to \mathbb{R}$ with $0 \le V(\lambda) \le 1$ for all $\lambda$ and $V(\lambda_0) = 1$. Only these normalization properties of the CIE curve are assumed; no further shape is imposed.
--   - **Radiant flux** $\Phi_e = \mu(\mathbb{R})$.
--   - **Luminous flux** $\Phi_v = K_{\max} \int V \,\mathrm{d}\mu$, i.e. the integral of the spectral luminous efficacy $K(\lambda) = K_{\max} V(\lambda)$ against the spectral radiant flux.
--   - **Luminous efficacy of radiation** $K = \Phi_v / \Phi_e$, **luminous efficiency** $K / K_{\max}$, and **luminous efficacy of a source** $\Phi_v / P$, where $P$ is the total input power consumed by the source.
--   - $\mathrm{ofDensity}(\Phi)$ is the measure with density $\Phi$ with respect to Lebesgue measure on the wavelength axis, used to connect the measure model with the source's integral formula.
-- source:
--   Wikipedia, Luminous efficacy, https://en.wikipedia.org/wiki/Luminous_efficacy (revision supplied as Luminous_efficacy.pdf), sections 'Luminous efficacy of radiation' (Explanation; Mathematical definition; Examples) and 'Lighting efficiency'

import Mathlib

open MeasureTheory

namespace LuminousEfficacy

/-- The photopic maximum spectral luminous efficacy `K_m = 683.002` lm/W,
attained at the wavelength 555 nm. -/
noncomputable def Km : ℝ := 683.002

/-- The scotopic maximum spectral luminous efficacy `1700` lm/W,
attained at the wavelength 507 nm. -/
noncomputable def KmScotopic : ℝ := 1700

/-- `IsLuminosityFunction V peak` says that `V` is a normalized luminous efficiency function
(luminosity function) of the wavelength, with its maximum value `1` attained at the
wavelength `peak`: `V` is measurable, takes values in `[0, 1]`, and `V peak = 1`. -/
structure IsLuminosityFunction (V : ℝ → ℝ) (peak : ℝ) : Prop where
  measurable : Measurable V
  nonneg : ∀ l, 0 ≤ V l
  le_one : ∀ l, V l ≤ 1
  peak_eq_one : V peak = 1

/-- The radiant flux `Φ_e` of a spectral radiant flux distribution `mu`, modelled as a
finite Borel measure on the wavelength axis: the total mass of `mu`. -/
noncomputable def radiantFlux (mu : Measure ℝ) : ℝ := (mu Set.univ).toReal

/-- The luminous flux `Φ_v = K_max * ∫ V dmu` of the spectral radiant flux distribution `mu`,
where the spectral luminous efficacy is `K(λ) = K_max * V λ`. -/
noncomputable def luminousFlux (Kmax : ℝ) (V : ℝ → ℝ) (mu : Measure ℝ) : ℝ :=
  Kmax * ∫ l, V l ∂mu

/-- The luminous efficacy of radiation `K = Φ_v / Φ_e`. -/
noncomputable def efficacyOfRadiation (Kmax : ℝ) (V : ℝ → ℝ) (mu : Measure ℝ) : ℝ :=
  luminousFlux Kmax V mu / radiantFlux mu

/-- The luminous efficiency: the luminous efficacy of radiation divided by its maximum
possible value `K_max`. -/
noncomputable def luminousEfficiency (Kmax : ℝ) (V : ℝ → ℝ) (mu : Measure ℝ) : ℝ :=
  efficacyOfRadiation Kmax V mu / Kmax

/-- The luminous efficacy of a source (overall luminous efficacy): the luminous flux
divided by the total input power `P` consumed by the source. -/
noncomputable def efficacyOfSource (Kmax : ℝ) (V : ℝ → ℝ) (mu : Measure ℝ) (P : ℝ) : ℝ :=
  luminousFlux Kmax V mu / P

/-- The spectral radiant flux distribution whose spectral radiant flux (density with respect
to wavelength) is `Phi`. -/
noncomputable def ofDensity (Phi : ℝ → ℝ) : Measure ℝ :=
  volume.withDensity (fun l => ENNReal.ofReal (Phi l))

end LuminousEfficacy


