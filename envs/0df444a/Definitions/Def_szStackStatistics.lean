-- Prove2me | Definitions.Def_szStackStatistics
-- name    : szStackStatistics
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-23T19:41:32.019248+00:00
-- url     : https://prove2.me/theorems/fcc1ed09-1cf1-45ff-b69a-33446dad4fe7
-- title:
--   Stacking statistics: covariance, jackknife covariance and $\chi^2$
-- statement:
--   The statistical layer of the stacking analysis of de Graaff et al. (2019), Sect. 3.3. A stack consists of $N$ binned one-dimensional profiles, indexed by the sample index $k$ and the bin index $i$; profiles are real-valued and there are $n$ bins.
--
--   - **Mean profile, Eq. (6).** $\bar{y}_i = \dfrac{1}{N}\sum_{k} y^k_i$.
--
--   - **Covariance estimator, Eq. (3).** $C_{i,j} = \dfrac{1}{N}\sum_{k}(y^k_i - \bar{y}_i)(y^k_j - \bar{y}_j)$, the covariance of a single map in the stack.
--
--   - **Jackknife covariance, Eq. (5).** $C^{JK}_{i,j} = \dfrac{N_{\mathrm{sub}}-1}{N_{\mathrm{sub}}}\sum_{k}(y^k_i - \bar{y}_i)(y^k_j - \bar{y}_j)$, where $k$ now indexes the $N_{\mathrm{sub}}$ jackknife sub-samples and $\bar{y}$ is their mean as in Eq. (6).
--
--   - **Chi-squared, Eq. (4).** $\chi^2 = \sum_{i,j} \bar{y}_i (C^{-1})_{i,j} \bar{y}_j$ for a covariance matrix $C$ and a mean profile $\bar{y}$.
--
--   - **Hartlap-corrected chi-squared, Eq. (7).** $\chi^2 = \sum_{i,j}\bar{y}_i\left[\dfrac{N_{\mathrm{sub}}-n-2}{N_{\mathrm{sub}}-1}C^{-1}\right]_{i,j}\bar{y}_j$, the same quadratic form with the Hartlap et al. (2007) correction for the bias of the inverse of an estimated covariance.
--
--   Matrix inversion is the nonsingular inverse, which returns the zero matrix on a singular argument; the counts $N$, $N_{\mathrm{sub}}$ and $n$ are natural numbers and all arithmetic in the correction factors is performed over the reals, so no truncated subtraction occurs.
-- source:
--   de Graaff A., Cai Y.-C., Heymans C., Peacock J. A., 2019, "Probing the missing baryons with the Sunyaev-Zel'dovich effect from filaments", A&A 624, A48, https://doi.org/10.1051/0004-6361/201935159, pp. 3-5, Sect. 3.3, Eqs. (3), (4), (5), (6), (7)

import Mathlib

namespace SZFilaments

open Finset Matrix

/-- The mean profile over a sample of `N` binned profiles: `ȳ_i = (∑_k y^k_i) / N`. -/
noncomputable def binMean {N n : ℕ} (y : Fin N → Fin n → ℝ) (i : Fin n) : ℝ :=
  (∑ k, y k i) / N

/-- The covariance estimator of a stack of `N` binned profiles:
`C_{i,j} = (1/N) ∑_k (y^k_i - ȳ_i)(y^k_j - ȳ_j)`. -/
noncomputable def sampleCovariance {N n : ℕ} (y : Fin N → Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => (∑ k, (y k i - binMean y i) * (y k j - binMean y j)) / N

/-- The jackknife covariance estimator built from `Nsub` sub-sample profiles:
`C^JK_{i,j} = ((Nsub - 1)/Nsub) ∑_k (y^k_i - ȳ_i)(y^k_j - ȳ_j)`. -/
noncomputable def jackknifeCovariance {Nsub n : ℕ} (y : Fin Nsub → Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j =>
    (((Nsub : ℝ) - 1) / (Nsub : ℝ)) * ∑ k, (y k i - binMean y i) * (y k j - binMean y j)

/-- The chi-squared statistic of a mean profile against a covariance matrix:
`χ² = ∑_{i,j} ȳ_i (C⁻¹)_{i,j} ȳ_j`. -/
noncomputable def chiSquared {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) (ybar : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, ybar i * C⁻¹ i j * ybar j

/-- The chi-squared statistic with the Hartlap correction factor for the bias of the
inverse covariance: `χ² = ∑_{i,j} ȳ_i [((Nsub - n - 2)/(Nsub - 1)) C⁻¹]_{i,j} ȳ_j`. -/
noncomputable def chiSquaredHartlap {n : ℕ} (Nsub : ℕ) (C : Matrix (Fin n) (Fin n) ℝ)
    (ybar : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, ybar i * ((((Nsub : ℝ) - (n : ℝ) - 2) / ((Nsub : ℝ) - 1)) * C⁻¹ i j) * ybar j

end SZFilaments


