-- Prove2me | Definitions.Def_Maldacena2003_InflationDefs
-- name    : Maldacena2003_InflationDefs
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-12T12:49:11.085654+00:00
-- url     : https://prove2.me/theorems/99ed4499-beba-47f2-846e-3605c4bf3ecb
-- title:
--   Maldacena (2003): slow-roll spectra, tilts and three-point functions, eqs. (2.20)–(4.16)
-- statement:
--   Definitions for the slow-roll three-point functions of Maldacena (2003), in units $M_{pl}^{-2}=8\pi G_N=1$. Background quantities at horizon crossing are real parameters $\dot\rho_* = H_*$, $\dot\phi_*$, $\ddot\phi_*$. All correlators omit the factor $(2\pi)^3\delta^3(\sum_i\vec k_i)$. Write $k_t = k_1+k_2+k_3$.
--
--   1. `IsMomentumTriangle k₁ k₂ k₃`: $k_1,k_2,k_3>0$ and $k_1\le k_2+k_3$, $k_2\le k_1+k_3$, $k_3\le k_1+k_2$. These are the magnitudes of three vectors summing to zero.
--   2. `shapeBracket`: $\frac12\sum_i k_i^3 + \frac12\sum_{i\ne j}k_ik_j^2 + 4\frac{\sum_{i>j}k_i^2k_j^2}{k_t}$, the bracket in eq. (4.6).
--   3. `amplitudeA`: $\mathcal A = 2\frac{\ddot\phi_*}{\dot\phi_*\dot\rho_*}\sum_i k_i^3 + \frac{\dot\phi_*^2}{\dot\rho_*^2}\cdot\texttt{shapeBracket}$ (eq. 4.6).
--   4. `zetaPowerSpectrum`: $P_\zeta(k) = \frac{1}{2k^3}\dot\rho_*^2\frac{\dot\rho_*^2}{\dot\phi_*^2}$ (eq. 2.20).
--   5. `zetaBispectrum`: $\frac{\dot\rho_*^4}{\dot\phi_*^4}H_*^4\frac{1}{\prod_i(2k_i^3)}\mathcal A$ (eq. 4.5).
--   6. `scalarTilt`: $n_s = -2\big(\frac{\ddot\phi_*}{\dot\rho_*\dot\phi_*}+\frac{\dot\phi_*^2}{\dot\rho_*^2}\big)$ (eq. 2.22, misprint corrected).
--   7. `tensorTilt`: $n_t = -\frac{\dot\phi_*^2}{\dot\rho_*^2}$ (eq. 2.30).
--   8. `shapeF`: $f(k) = \texttt{shapeBracket}/\sum_i k_i^3 - 2$. This is the function defined implicitly by eq. (4.9) through $\mathcal A/\sum_i k_i^3 = 2\frac{\ddot\phi_*}{\dot\phi_*\dot\rho_*} + \frac{\dot\phi_*^2}{\dot\rho_*^2}(2+f(k))$.
--   9. `integralI`: $I = -k_t + \frac{\sum_{i>j}k_ik_j}{k_t} + \frac{k_1k_2k_3}{k_t^2}$ (eq. 4.11, closed form).
--   10. `tensorPowerSpectrum`: $P_\gamma(k) = \frac{1}{2k^3}\,2\dot\rho_*^2$ (eq. 2.29 with $s=s'$).
--   11. `gammaZetaZetaBispectrum ρd φd ε k⃗₁ k⃗₂ k⃗₃`: $\frac{1}{\prod_i(2k_i^3)}\dot\rho_*^4\frac{\dot\rho_*^2}{\dot\phi_*^2}\,\epsilon_{ij}k_2^ik_3^j\,4I$ (eq. 4.10), where $\epsilon$ is the polarization of the graviton with momentum $\vec k_1$.
--   12. `zetaGammaGammaBispectrum ρd k₁ k₂ k₃ E`: $\frac{1}{\prod_i(2k_i^3)}\dot\rho_*^4\big[-\frac14k_1^3+\frac12k_1(k_2^2+k_3^2)+4\frac{k_2^2k_3^2}{k_t}\big]E$ (eq. 4.13), where $E = \epsilon^{s_2}_{ij}\epsilon^{s_3}_{ij}$.
--   13. `tTensor`: $t_{ijl} = k_2^i\delta_{jl} + k_3^j\delta_{il} + k_1^l\delta_{ij}$ (eq. 4.16).
--   14. `threeGravitonBispectrum`: $\frac{\dot\rho_*^4}{\prod_i(2k_i^3)}(-4)\big(\epsilon^{1}_{ii'}\epsilon^{2}_{jj'}\epsilon^{3}_{ll'}t_{ijl}t_{i'j'l'}\big)I$ (eq. 4.15).
--
--   These definitions are shared by all statements of the mission.
--
--   **Formalization Note** In the vector-valued definitions, $k_i$ is the Euclidean norm of $\vec k_i\in$ `EuclideanSpace ℝ (Fin 3)`, and polarization tensors are real $3\times3$ matrices.
-- source:
--   J. Maldacena, Non-Gaussian features of primordial fluctuations in single field inflationary models, JHEP 05 (2003) 013, https://doi.org/10.1088/1126-6708/2003/05/013 (arXiv:astro-ph/0210603); p. 3 (units), eq. (2.3) p. 4, eqs. (2.20), (2.22) p. 7, eqs. (2.29), (2.30) p. 9, eqs. (4.5), (4.6) p. 16, eqs. (4.9)–(4.11) p. 18, eqs. (4.13), (4.15), (4.16) p. 19

import Mathlib

/-!
# Maldacena (2003): slow-roll quantities and the three-scalar bispectrum

Units: `M_pl^{-2} = 8πG_N = 1`, as in the paper (Sec. 2). Background quantities are the
values at horizon crossing: `ρd = ρ̇_* = H_*`, `φd = φ̇_*`, `φdd = φ̈_*`.
-/

namespace Maldacena2003

/-- Momentum magnitudes `k₁, k₂, k₃` of three wave vectors with `k⃗₁ + k⃗₂ + k⃗₃ = 0`:
all positive and satisfying the (non-strict) triangle inequalities. -/
def IsMomentumTriangle (k₁ k₂ k₃ : ℝ) : Prop :=
  0 < k₁ ∧ 0 < k₂ ∧ 0 < k₃ ∧ k₁ ≤ k₂ + k₃ ∧ k₂ ≤ k₁ + k₃ ∧ k₃ ≤ k₁ + k₂

/-- The momentum-dependent bracket of eq. (4.6):
`½ Σᵢ kᵢ³ + ½ Σ_{i≠j} kᵢ kⱼ² + 4 (Σ_{i>j} kᵢ² kⱼ²) / k_t`, with `k_t = k₁ + k₂ + k₃`. -/
noncomputable def shapeBracket (k₁ k₂ k₃ : ℝ) : ℝ :=
  (1 / 2) * (k₁ ^ 3 + k₂ ^ 3 + k₃ ^ 3)
    + (1 / 2) * (k₁ * k₂ ^ 2 + k₁ * k₃ ^ 2 + k₂ * k₁ ^ 2 + k₂ * k₃ ^ 2
        + k₃ * k₁ ^ 2 + k₃ * k₂ ^ 2)
    + 4 * (k₂ ^ 2 * k₁ ^ 2 + k₃ ^ 2 * k₁ ^ 2 + k₃ ^ 2 * k₂ ^ 2) / (k₁ + k₂ + k₃)

/-- The amplitude `𝒜` of eq. (4.6):
`𝒜 = 2 (φ̈_*/(φ̇_* ρ̇_*)) Σᵢ kᵢ³ + (φ̇_*²/ρ̇_*²) · shapeBracket`. -/
noncomputable def amplitudeA (ρd φd φdd k₁ k₂ k₃ : ℝ) : ℝ :=
  2 * (φdd / (φd * ρd)) * (k₁ ^ 3 + k₂ ^ 3 + k₃ ^ 3)
    + (φd ^ 2 / ρd ^ 2) * shapeBracket k₁ k₂ k₃

/-- Scalar power spectrum, eq. (2.20) with `H = ρ̇` and `M_pl = 1`, without the factor
`(2π)³ δ³(k⃗ + k⃗')`: `P_ζ(k) = (1/(2k³)) · ρ̇_*² · ρ̇_*²/φ̇_*²`. -/
noncomputable def zetaPowerSpectrum (ρd φd k : ℝ) : ℝ :=
  1 / (2 * k ^ 3) * ρd ^ 2 * (ρd ^ 2 / φd ^ 2)

/-- Three-scalar correlator, eq. (4.5) with `H_* = ρ̇_*` and `M_pl = 1`, without the factor
`(2π)³ δ³(Σ k⃗ᵢ)`: `(ρ̇_*⁴/φ̇_*⁴) · H_*⁴ · 𝒜 / Πᵢ (2kᵢ³)`. -/
noncomputable def zetaBispectrum (ρd φd φdd k₁ k₂ k₃ : ℝ) : ℝ :=
  ρd ^ 4 / φd ^ 4 * ρd ^ 4 * (1 / ((2 * k₁ ^ 3) * (2 * k₂ ^ 3) * (2 * k₃ ^ 3)))
    * amplitudeA ρd φd φdd k₁ k₂ k₃

/-- Scalar tilt (the exponent `n_s` in `k^{-3+n_s}`), the exact right-hand side of
eq. (2.22): `n_s = -2 (φ̈_*/(ρ̇_* φ̇_*) + φ̇_*²/ρ̇_*²)`. -/
noncomputable def scalarTilt (ρd φd φdd : ℝ) : ℝ :=
  -2 * (φdd / (ρd * φd) + φd ^ 2 / ρd ^ 2)

/-- Tensor tilt, eq. (2.30): `n_t = -φ̇_*²/ρ̇_*²`. -/
noncomputable def tensorTilt (ρd φd : ℝ) : ℝ :=
  -(φd ^ 2 / ρd ^ 2)

/-- The shape function `f(k)` of eq. (4.9), i.e. the function for which
`𝒜 / Σᵢ kᵢ³ = 2 φ̈_*/(φ̇_* ρ̇_*) + (φ̇_*²/ρ̇_*²) (2 + f(k))`. -/
noncomputable def shapeF (k₁ k₂ k₃ : ℝ) : ℝ :=
  shapeBracket k₁ k₂ k₃ / (k₁ ^ 3 + k₂ ^ 3 + k₃ ^ 3) - 2

end Maldacena2003

namespace Maldacena2003

/-- Closed form of the time integral `I` of eq. (4.11):
`I = -k_t + (Σ_{i>j} kᵢ kⱼ)/k_t + k₁k₂k₃/k_t²`, with `k_t = k₁ + k₂ + k₃`. -/
noncomputable def integralI (k₁ k₂ k₃ : ℝ) : ℝ :=
  -(k₁ + k₂ + k₃) + (k₂ * k₁ + k₃ * k₁ + k₃ * k₂) / (k₁ + k₂ + k₃)
    + k₁ * k₂ * k₃ / (k₁ + k₂ + k₃) ^ 2

/-- Tensor power spectrum, eq. (2.29) for equal polarizations `s = s'`, with `M_pl = 1` and
without `(2π)³ δ³(k⃗ + k⃗')`: `P_γ(k) = (1/(2k³)) · 2ρ̇_*²`. -/
noncomputable def tensorPowerSpectrum (ρd k : ℝ) : ℝ :=
  1 / (2 * k ^ 3) * (2 * ρd ^ 2)

/-- Graviton–scalar–scalar correlator, eq. (4.10) with `M_pl = 1`, without
`(2π)³ δ³(Σ k⃗ᵢ)`: `(1/Πᵢ(2kᵢ³)) (ρ̇_*⁴) (ρ̇_*²/φ̇_*²) ε_{ij} k₂ⁱ k₃ʲ · 4 I`,
where `ε` is the polarization tensor of the graviton of momentum `k⃗₁` and `kᵢ = |k⃗ᵢ|`. -/
noncomputable def gammaZetaZetaBispectrum (ρd φd : ℝ) (ε : Matrix (Fin 3) (Fin 3) ℝ)
    (k₁ k₂ k₃ : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  1 / ((2 * ‖k₁‖ ^ 3) * (2 * ‖k₂‖ ^ 3) * (2 * ‖k₃‖ ^ 3)) * ρd ^ 4 * (ρd ^ 2 / φd ^ 2)
    * (∑ i, ∑ j, ε i j * k₂ i * k₃ j) * (4 * integralI ‖k₁‖ ‖k₂‖ ‖k₃‖)

/-- Scalar–graviton–graviton correlator, eq. (4.13) with `M_pl = 1`, without
`(2π)³ δ³(Σ k⃗ᵢ)`: `(1/Πᵢ(2kᵢ³)) ρ̇_*⁴ [-¼k₁³ + ½k₁(k₂²+k₃²) + 4k₂²k₃²/k_t] · E`,
where `E = ε^{s₂}_{ij} ε^{s₃}_{ij}` is the contraction of the two graviton polarizations. -/
noncomputable def zetaGammaGammaBispectrum (ρd k₁ k₂ k₃ E : ℝ) : ℝ :=
  1 / ((2 * k₁ ^ 3) * (2 * k₂ ^ 3) * (2 * k₃ ^ 3)) * ρd ^ 4
    * (-(1 / 4) * k₁ ^ 3 + (1 / 2) * k₁ * (k₂ ^ 2 + k₃ ^ 2)
        + 4 * k₂ ^ 2 * k₃ ^ 2 / (k₁ + k₂ + k₃)) * E

/-- The flat-space tensor of eq. (4.16): `t_{ijl} = k₂ⁱ δ_{jl} + k₃ʲ δ_{il} + k₁ˡ δ_{ij}`. -/
noncomputable def tTensor (k₁ k₂ k₃ : EuclideanSpace ℝ (Fin 3)) (i j l : Fin 3) : ℝ :=
  k₂ i * (if j = l then 1 else 0) + k₃ j * (if i = l then 1 else 0)
    + k₁ l * (if i = j then 1 else 0)

/-- Three-graviton correlator, eq. (4.15) with `M_pl = 1`, without `(2π)³ δ³(Σ k⃗ᵢ)`:
`(ρ̇_*⁴/Πᵢ(2kᵢ³)) (-4) (ε¹_{ii'} ε²_{jj'} ε³_{ll'} t_{ijl} t_{i'j'l'}) I`. -/
noncomputable def threeGravitonBispectrum (ρd : ℝ) (ε₁ ε₂ ε₃ : Matrix (Fin 3) (Fin 3) ℝ)
    (k₁ k₂ k₃ : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  ρd ^ 4 * (1 / ((2 * ‖k₁‖ ^ 3) * (2 * ‖k₂‖ ^ 3) * (2 * ‖k₃‖ ^ 3))) * (-4)
    * (∑ i, ∑ i', ∑ j, ∑ j', ∑ l, ∑ l',
        ε₁ i i' * ε₂ j j' * ε₃ l l' * tTensor k₁ k₂ k₃ i j l * tTensor k₁ k₂ k₃ i' j' l')
    * integralI ‖k₁‖ ‖k₂‖ ‖k₃‖

end Maldacena2003


