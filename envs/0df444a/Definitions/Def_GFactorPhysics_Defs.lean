-- Prove2me | Definitions.Def_GFactorPhysics_Defs
-- name    : GFactorPhysics_Defs
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-23T20:40:50.886395+00:00
-- url     : https://prove2.me/theorems/48a67019-6ec4-4f3e-8581-5f4adbad525d
-- title:
--   g-factor conventions: Dirac, nuclear-magneton, Bohr-magneton and classical moments
-- statement:
--   This bundle fixes the objects used throughout the mission. Vectors are elements of $\mathbb R^3$ (component $2$ is the $z$ component), and all physical constants are real numbers.
--
--   1. **Dirac-particle moment.** $\boldsymbol\mu(g,e,m,\mathbf S) = \dfrac{g\,e}{2m}\,\mathbf S$.
--   2. **Nuclear magneton.** $\mu_N(e,\hbar,m_p) = \dfrac{e\hbar}{2m_p}$.
--   3. **Nuclear-magneton moment.** $\boldsymbol\mu(g,\mu_N,\hbar,\mathbf I) = \dfrac{g\,\mu_N}{\hbar}\,\mathbf I$.
--   4. **Bohr magneton.** $\mu_B(e,\hbar,m_e) = \dfrac{e\hbar}{2m_e}$.
--   5. **Electron orbital moment.** $\boldsymbol\mu_L(g_L,\mu_B,\hbar,\mathbf L) = -\dfrac{g_L\,\mu_B}{\hbar}\,\mathbf L$.
--   6. **Classical magnetic moment** of $n$ point charges with charges $q_i$, positions $\mathbf r_i$, velocities $\mathbf v_i$:
--   $$\boldsymbol\mu = \sum_{i=1}^n \frac{q_i}{2}\,\mathbf r_i\times\mathbf v_i .$$
--   7. **Classical angular momentum** of $n$ point masses $m_i$:
--   $$\mathbf L = \sum_{i=1}^n m_i\,\mathbf r_i\times\mathbf v_i .$$
--
--   Items 1–5 transcribe the defining formulas of the article; items 6–7 are the standard non-relativistic expressions behind the article's phrase "a classical particle of the same charge and angular momentum".
--
--   **Formalization Note** Vectors are `Fin 3 → ℝ` and `×` is Mathlib's `crossProduct`. Division is total, so each formula returns $0$ when its denominator is $0$; theorems using these definitions assume the relevant constants are nonzero.
-- source:
--   Wikipedia, "g-factor (physics)" (PDF snapshot supplied by the user, `G-factor_(physics).pdf`), https://en.wikipedia.org/wiki/G-factor_(physics); sections "Dirac particle", "Baryon or nucleus", "Electron spin g-factor" (Bohr magneton), "Electron orbital g-factor"; opening paragraph (classical particle of the same charge and angular momentum).

import Mathlib

namespace GFactorPhysics

open Matrix

/-- Spin magnetic moment of a Dirac particle with g-factor `g`, charge `e`, mass `m`
and spin angular momentum `S`: `μ = g * e / (2 m) * S`. -/
noncomputable def diracMagneticMoment (g e m : ℝ) (S : Fin 3 → ℝ) : Fin 3 → ℝ :=
  (g * e / (2 * m)) • S

/-- The nuclear magneton `μ_N = e ħ / (2 m_p)`. -/
noncomputable def nuclearMagneton (e hbar m_p : ℝ) : ℝ :=
  e * hbar / (2 * m_p)

/-- Magnetic moment of a nucleon or nucleus under the nuclear-magneton convention:
`μ = g * μ_N / ħ * I`. -/
noncomputable def nuclearMagneticMoment (g μN hbar : ℝ) (I : Fin 3 → ℝ) : Fin 3 → ℝ :=
  (g * μN / hbar) • I

/-- The Bohr magneton `μ_B = e ħ / (2 m_e)`. -/
noncomputable def bohrMagneton (e hbar m_e : ℝ) : ℝ :=
  e * hbar / (2 * m_e)

/-- Orbital magnetic moment of an electron: `μ_L = - g_L * μ_B / ħ * L`. -/
noncomputable def electronOrbitalMagneticMoment (g_L μB hbar : ℝ) (L : Fin 3 → ℝ) :
    Fin 3 → ℝ :=
  (-(g_L * μB / hbar)) • L

/-- Magnetic moment of a finite system of classical point charges with charges `q i`,
positions `r i` and velocities `v i`: `μ = ∑ᵢ (q i / 2) (r i × v i)`. -/
noncomputable def classicalMagneticMoment {n : ℕ} (q : Fin n → ℝ) (r v : Fin n → Fin 3 → ℝ) : Fin 3 → ℝ :=
  ∑ i, (q i / 2) • (r i ⨯₃ v i)

/-- Angular momentum of a finite system of classical point masses with masses `m i`,
positions `r i` and velocities `v i`: `L = ∑ᵢ m i (r i × v i)`. -/
noncomputable def classicalAngularMomentum {n : ℕ} (m : Fin n → ℝ) (r v : Fin n → Fin 3 → ℝ) : Fin 3 → ℝ :=
  ∑ i, m i • (r i ⨯₃ v i)

end GFactorPhysics


