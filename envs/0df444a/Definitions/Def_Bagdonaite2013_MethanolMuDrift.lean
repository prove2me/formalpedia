-- Prove2me | Definitions.Def_Bagdonaite2013_MethanolMuDrift
-- name    : Bagdonaite2013_MethanolMuDrift
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-04T18:53:15.182463+00:00
-- url     : https://prove2.me/theorems/f82e1c76-034f-4337-8a20-72c8bd76b50b
-- title:
--   Sensitivity coefficient, weighted line fit and Table 1 data (Bagdonaite et al. 2013)
-- statement:
--   This definition file fixes the vocabulary and the data used by every statement of the mission. Everything lives in the namespace `MethanolMuDrift`.
--
--   1. **Sensitivity coefficient.** For a transition frequency $\nu$, viewed as a function of the proton-to-electron mass ratio $\mu$, the sensitivity coefficient at $\mu$ is
--   $$K_\mu(\nu;\mu)=\frac{\mu}{\nu(\mu)}\,\frac{d\nu}{d\mu}(\mu),$$
--   the infinitesimal form of the defining relation $\Delta\nu/\nu = K_\mu\,\Delta\mu/\mu$.
--   2. **Speed of light** $c = 299792.458$ km/s.
--   3. **Weighted least-squares line fit.** For $n$ points $(K_i,V_i)$ with uncertainties $\sigma_i$ and weights $w_i=1/\sigma_i^2$, put $S=\sum w_i$, $S_K=\sum w_iK_i$, $S_V=\sum w_iV_i$, $S_{KK}=\sum w_iK_i^2$, $S_{KV}=\sum w_iK_iV_i$ and $\Delta = S S_{KK}-S_K^2$. The fitted line $V=a+bK$ has
--   $$b=\frac{S S_{KV}-S_K S_V}{\Delta},\qquad a=\frac{S_{KK}S_V-S_K S_{KV}}{\Delta},\qquad \sigma_b=\sqrt{S/\Delta},$$
--   chi-squared $\chi^2=\sum_i\big((V_i-a-bK_i)/\sigma_i\big)^2$ and reduced chi-squared $\chi^2_\nu=\chi^2/(n-2)$.
--   4. **Estimate of $\Delta\mu/\mu$.** From the velocity relation $V/c=-K_\mu\,\Delta\mu/\mu$ (up to a common velocity offset), the estimate is $-b/c$ with statistical uncertainty $\sigma_b/c$.
--   5. **Table 1 data** (line order $3_{-1}$–$2_0\,E$, $0_0$–$1_0\,A^+$, $0_0$–$1_0\,E$, $2_{-1}$–$1_0\,E$): sensitivity coefficients $K_\mu=(-32.8,-1,-1,-7.4)$, positions $V=(9.06,8.40,9.12,9.83)$ km/s and uncertainties $\sigma=(0.67,0.10,0.30,0.43)$ km/s (LSR velocities relative to $z=0.88582$); the E-symmetry subset $K=(-32.8,-1,-7.4)$, $V=(9.06,9.12,9.83)$, $\sigma=(0.67,0.30,0.43)$; and the adopted systematic uncertainty $7.0\times10^{-8}$ on $\Delta\mu/\mu$.
--
--   These objects let the paper's numerical analysis be restated as exact statements about real numbers.
--
--   **Formalization Note** All quantities are real numbers; division by zero returns $0$ and the square root of a negative number returns $0$, so statements about general data carry explicit non-degeneracy hypotheses. The fit formulas are the standard closed-form weighted least-squares formulas (the paper cites Bevington & Robinson for its data analysis); the paper does not print them explicitly.
-- source:
--   J. Bagdonaite, P. Jansen, C. Henkel, H. L. Bethlem, K. M. Menten, W. Ubachs, "A Stringent Limit on a Drifting Proton-to-Electron Mass Ratio from Alcohol in the Early Universe", Science (First Release, 13 December 2012), doi:10.1126/science.1224898, https://doi.org/10.1126/science.1224898, p. 1 (definition of K_mu), p. 2 (velocity relation and fits), Table 1 (p. 4); fit formulas: Bevington & Robinson (ref. 34 of the paper)

import Mathlib

/-!
# Definitions for: Bagdonaite et al. (2013), "A stringent limit on a drifting
proton-to-electron mass ratio from alcohol in the early Universe", Science 339, 46.

* the sensitivity coefficient `K_μ` of a transition frequency to `μ`;
* the weighted least-squares straight-line fit `V ≈ a + b K` (closed form, with
  weights `1/σ_i²`), its slope standard error and reduced chi-squared;
* the derived estimate `Δμ/μ = -b/c` and its statistical error `σ_b/c`;
* the measured data of Table 1 (sensitivity coefficients and line positions).
-/

namespace MethanolMuDrift

open Finset

/-- Sensitivity coefficient of a transition frequency `ν` (as a function of the
proton-to-electron mass ratio `μ`) at `μ`: `K_μ = (μ / ν(μ)) · dν/dμ`, i.e. the
infinitesimal form of `Δν/ν = K_μ · Δμ/μ`. -/
noncomputable def sensitivityCoeff (ν : ℝ → ℝ) (μ : ℝ) : ℝ :=
  μ / ν μ * deriv ν μ

/-- Speed of light in km/s (exact SI value). -/
noncomputable def speedOfLight : ℝ := 299792.458

/-- Sum of weights `S = ∑ 1/σ_i²`. -/
noncomputable def wSum {n : ℕ} (σ : Fin n → ℝ) : ℝ := ∑ i, 1 / σ i ^ 2

/-- `S_K = ∑ K_i/σ_i²`. -/
noncomputable def wSumK {n : ℕ} (K σ : Fin n → ℝ) : ℝ := ∑ i, K i / σ i ^ 2

/-- `S_V = ∑ V_i/σ_i²`. -/
noncomputable def wSumV {n : ℕ} (V σ : Fin n → ℝ) : ℝ := ∑ i, V i / σ i ^ 2

/-- `S_KK = ∑ K_i²/σ_i²`. -/
noncomputable def wSumKK {n : ℕ} (K σ : Fin n → ℝ) : ℝ := ∑ i, K i ^ 2 / σ i ^ 2

/-- `S_KV = ∑ K_i V_i/σ_i²`. -/
noncomputable def wSumKV {n : ℕ} (K V σ : Fin n → ℝ) : ℝ := ∑ i, K i * V i / σ i ^ 2

/-- Determinant `Δ = S · S_KK - S_K²` of the weighted normal equations. -/
noncomputable def wlsDet {n : ℕ} (K σ : Fin n → ℝ) : ℝ :=
  wSum σ * wSumKK K σ - wSumK K σ ^ 2

/-- Weighted least-squares slope `b = (S · S_KV - S_K · S_V) / Δ` of the line
`V = a + b K` fitted to points `(K_i, V_i)` with uncertainties `σ_i`. -/
noncomputable def wlsSlope {n : ℕ} (K V σ : Fin n → ℝ) : ℝ :=
  (wSum σ * wSumKV K V σ - wSumK K σ * wSumV V σ) / wlsDet K σ

/-- Weighted least-squares intercept `a = (S_KK · S_V - S_K · S_KV) / Δ`. -/
noncomputable def wlsIntercept {n : ℕ} (K V σ : Fin n → ℝ) : ℝ :=
  (wSumKK K σ * wSumV V σ - wSumK K σ * wSumKV K V σ) / wlsDet K σ

/-- Standard error of the weighted least-squares slope, `σ_b = √(S / Δ)`. -/
noncomputable def wlsSlopeStdErr {n : ℕ} (K σ : Fin n → ℝ) : ℝ :=
  Real.sqrt (wSum σ / wlsDet K σ)

/-- Chi-squared of the fit: `χ² = ∑ ((V_i - a - b K_i)/σ_i)²`. -/
noncomputable def wlsChiSq {n : ℕ} (K V σ : Fin n → ℝ) : ℝ :=
  ∑ i, ((V i - wlsIntercept K V σ - wlsSlope K V σ * K i) / σ i) ^ 2

/-- Reduced chi-squared `χ²_ν = χ² / (n - 2)` (two fitted parameters). -/
noncomputable def wlsReducedChiSq {n : ℕ} (K V σ : Fin n → ℝ) : ℝ :=
  wlsChiSq K V σ / ((n : ℝ) - 2)

/-- Estimate of `Δμ/μ` from the velocity relation `V/c = -K_μ Δμ/μ`:
minus the fitted slope (km/s per unit `K_μ`) divided by `c` (km/s). -/
noncomputable def muDriftEstimate {n : ℕ} (K V σ : Fin n → ℝ) : ℝ :=
  -wlsSlope K V σ / speedOfLight

/-- Statistical (1σ) uncertainty of the `Δμ/μ` estimate: `σ_b / c`. -/
noncomputable def muDriftStatErr {n : ℕ} (K σ : Fin n → ℝ) : ℝ :=
  wlsSlopeStdErr K σ / speedOfLight

/-! ### Table 1 data. Line order: `3₋₁–2₀ E`, `0₀–1₀ A⁺`, `0₀–1₀ E`, `2₋₁–1₀ E`.
Velocities are LSR velocities in km/s relative to `z = 0.88582`. -/

/-- Sensitivity coefficients `K_μ` of the four lines (Table 1). -/
noncomputable def allK : Fin 4 → ℝ := ![-32.8, -1, -1, -7.4]

/-- Measured line positions in km/s (Table 1). -/
noncomputable def allV : Fin 4 → ℝ := ![9.06, 8.40, 9.12, 9.83]

/-- 1σ uncertainties of the line positions in km/s (Table 1). -/
noncomputable def allSigma : Fin 4 → ℝ := ![0.67, 0.10, 0.30, 0.43]

/-- Sensitivity coefficients of the three E-symmetry lines
(`3₋₁–2₀ E`, `0₀–1₀ E`, `2₋₁–1₀ E`). -/
noncomputable def eK : Fin 3 → ℝ := ![-32.8, -1, -7.4]

/-- Positions (km/s) of the three E-symmetry lines. -/
noncomputable def eV : Fin 3 → ℝ := ![9.06, 9.12, 9.83]

/-- Position uncertainties (km/s) of the three E-symmetry lines. -/
noncomputable def eSigma : Fin 3 → ℝ := ![0.67, 0.30, 0.43]

/-- Conservative systematic uncertainty on `Δμ/μ` from source variability,
`7.0 × 10⁻⁸`, as adopted in the paper. -/
noncomputable def muDriftSysErr : ℝ := 7.0e-8

end MethanolMuDrift


