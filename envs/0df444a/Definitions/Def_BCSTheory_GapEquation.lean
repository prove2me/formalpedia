-- Prove2me | Definitions.Def_BCSTheory_GapEquation
-- name    : BCSTheory_GapEquation
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-09T21:22:06.109875+00:00
-- url     : https://prove2.me/theorems/1726c320-eb4c-4b6d-af01-2dec3efd308f
-- title:
--   BCS gap equation: gap integrals, $\Delta(0)$, $T_c$ and $\Delta(T)$
-- statement:
--   Weak-coupling BCS model with Debye cutoff. Parameters: Boltzmann constant $k_B>0$, Debye energy $\hbar\omega_D>0$, coupling $\lambda = V_0Z(E_F)>0$ (attractive potential times half the density of states at the Fermi energy).
--
--   * Fermi–Dirac distribution $f(E,T) = 1/(e^{E/k_BT}+1)$.
--   * Quasiparticle energy $E(\eta,\Delta) = \sqrt{\eta^2+\Delta^2}$.
--   * $I_0(\hbar\omega_D,\Delta) = \int_0^{\hbar\omega_D} d\eta/\sqrt{\eta^2+\Delta^2}$ (right-hand side of the $T=0$ gap equation).
--   * $I(k_B,\hbar\omega_D,\Delta,T) = \int_0^{\hbar\omega_D} \frac{d\eta}{\sqrt{\eta^2+\Delta^2}}\tanh\frac{\sqrt{\eta^2+\Delta^2}}{2k_BT}$ (right-hand side of the finite-$T$ gap equation; for $\Delta=0$ it is the $T_c$ integral).
--   * $\Delta(0) = \sup\{\Delta>0 : I_0(\hbar\omega_D,\Delta) = 1/\lambda\}$.
--   * $T_c = \sup\{T>0 : I(k_B,\hbar\omega_D,0,T) = 1/\lambda\}$.
--   * $\Delta(T) = \sup\{\Delta>0 : I(k_B,\hbar\omega_D,\Delta,T) = 1/\lambda\}$.
--
--   Conventions: suprema of empty sets (or sets unbounded above) are $0$; division by $0$ is $0$. Uniqueness of the solutions is stated as separate milestones.
-- source:
--   Wikipedia (de), Artikel „BCS-Theorie“ (PDF-Ausdruck vom 05.10.2026), Abschnitt „Erfolge der BCS-Theorie“, Unterabschnitte „Existenz einer Energielücke“ und „Isotopeneffekt“.

import Mathlib

/-!
# BCS gap equation (weak-coupling BCS model with Debye cutoff)

Parameters used throughout:
* `kB > 0` — the Boltzmann constant,
* `hbarOmegaD > 0` — the Debye cutoff energy `ħ ω_D`,
* `coupling > 0` — the dimensionless coupling `V₀ · Z(E_F)` (attractive potential times
  half the density of states at the Fermi energy).
-/

namespace BCSTheory

/-- The Fermi–Dirac distribution `f(E, T) = 1 / (exp(E / (k_B T)) + 1)`. -/
noncomputable def fermiDirac (kB E T : ℝ) : ℝ :=
  1 / (Real.exp (E / (kB * T)) + 1)

/-- The quasiparticle energy `√(η² + Δ²)`. -/
noncomputable def quasiparticleEnergy (η Δ : ℝ) : ℝ :=
  Real.sqrt (η ^ 2 + Δ ^ 2)

/-- The right-hand side of the zero-temperature gap equation,
`∫₀^{ħω_D} dη / √(η² + Δ²)`. -/
noncomputable def gapIntegralZeroTemp (hbarOmegaD Δ : ℝ) : ℝ :=
  ∫ η in (0 : ℝ)..hbarOmegaD, 1 / quasiparticleEnergy η Δ

/-- The right-hand side of the finite-temperature BCS gap equation,
`∫₀^{ħω_D} dη · tanh(√(η² + Δ²) / (2 k_B T)) / √(η² + Δ²)`.
For `Δ = 0` the integrand is `tanh(η / (2 k_B T)) / η` (the critical-temperature equation). -/
noncomputable def gapIntegral (kB hbarOmegaD Δ T : ℝ) : ℝ :=
  ∫ η in (0 : ℝ)..hbarOmegaD,
    Real.tanh (quasiparticleEnergy η Δ / (2 * kB * T)) / quasiparticleEnergy η Δ

/-- The zero-temperature gap `Δ(0)`: the supremum of all `Δ > 0` solving
`1 / (V₀ Z(E_F)) = ∫₀^{ħω_D} dη / √(η² + Δ²)`. -/
noncomputable def zeroTemperatureGap (hbarOmegaD coupling : ℝ) : ℝ :=
  sSup {Δ : ℝ | 0 < Δ ∧ gapIntegralZeroTemp hbarOmegaD Δ = 1 / coupling}

/-- The critical (transition) temperature `T_c`: the supremum of all `T > 0` solving
`1 / (V₀ Z(E_F)) = ∫₀^{ħω_D} (dη / η) tanh(η / (2 k_B T))`. -/
noncomputable def criticalTemperature (kB hbarOmegaD coupling : ℝ) : ℝ :=
  sSup {T : ℝ | 0 < T ∧ gapIntegral kB hbarOmegaD 0 T = 1 / coupling}

/-- The temperature-dependent gap `Δ(T)`: the supremum of all `Δ > 0` solving the
finite-temperature gap equation `1 / (V₀ Z(E_F)) = gapIntegral kB ħω_D Δ T`
(this is `0` when no positive solution exists, e.g. for `T ≥ T_c`). -/
noncomputable def gap (kB hbarOmegaD coupling T : ℝ) : ℝ :=
  sSup {Δ : ℝ | 0 < Δ ∧ gapIntegral kB hbarOmegaD Δ T = 1 / coupling}

end BCSTheory


