-- Prove2me | Definitions.Def_LipariNeutrino_OscillationProbability
-- name    : LipariNeutrino_OscillationProbability
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-24T04:56:39.118643+00:00
-- url     : https://prove2.me/theorems/c9df8b3e-7bcd-4354-99d4-179b4b6f5f93
-- title:
--   Vacuum oscillation amplitude and probability; coefficients $A^{jk}_{\alpha\beta}$ and $J^{\alpha\beta}_{jk}$
-- statement:
--   Fix $n$ flavours and $n$ mass eigenstates, a complex $n\times n$ mixing matrix $U$ (rows: flavours $\alpha$, columns: mass eigenstates $j$, with $|\nu_\alpha\rangle=\sum_j U^*_{\alpha j}|\nu_j\rangle$), real squared masses $m_j^2$, a path length $L$ and an energy $E$.
--
--   1. **Amplitude** $A(\nu_\alpha\to\nu_\beta)=\sum_j U_{\beta j}U^*_{\alpha j}\,e^{-i m_j^2 L/(2E)}$.
--   2. **Probability** $P(\nu_\alpha\to\nu_\beta)=|A(\nu_\alpha\to\nu_\beta)|^2$.
--   3. **Antineutrino probability** $P(\bar\nu_\alpha\to\bar\nu_\beta)$: the probability computed with $U$ replaced by its entrywise complex conjugate $U^*$.
--   4. **CP/T-odd coefficients** $J^{\alpha\beta}_{jk}=-\mathrm{Im}[U_{\alpha j}U^*_{\alpha k}U^*_{\beta j}U_{\beta k}]$.
--   5. **CP-even amplitudes** $A^{jk}_{\alpha\beta}=-4\,\mathrm{Re}[U_{\alpha j}U^*_{\beta j}U^*_{\alpha k}U_{\beta k}]$.
--
--   These are the objects in which the vacuum oscillation formulas of the lecture notes are stated.
--
--   **Formalization Note** The amplitude uses the relativistic approximation of the notes: $L\simeq t$ and $E_j\simeq E+m_j^2/(2E)$, with the flavour-independent overall phase $e^{-iEt}$ dropped (it does not affect probabilities). For $E=0$, Lean's convention $x/0=0$ makes all phases zero.
-- source:
--   P. Lipari, *Introduction to Neutrino Physics* (lecture notes, uploaded PDF), Section 4, Eqs. (44)-(48), (61), (73) and the definition of $J^{\alpha\beta}_{jk}$ on p. 136; antineutrino rule $U\to U^*$ on p. 135.

import Mathlib

namespace LipariNeutrino

/-- Transition amplitude `A(ν_α → ν_β)` in vacuum (Lipari, Eqs. (47) and (61)):
`∑_j U_{βj} U_{αj}^* exp(-i m_j^2 L / (2E))`.
Here `U` is the mixing matrix with rows indexed by flavour and columns by mass eigenstate,
`m2 j` is the squared mass `m_j^2`, `L` the path length and `E` the neutrino energy. -/
noncomputable def oscAmp {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ) (m2 : Fin n → ℝ) (L E : ℝ)
    (α β : Fin n) : ℂ :=
  ∑ j, U β j * star (U α j) * Complex.exp (-(Complex.I * ((m2 j * L / (2 * E) : ℝ) : ℂ)))

/-- Oscillation probability `P(ν_α → ν_β) = |A(ν_α → ν_β)|^2` (Lipari, Eqs. (48) and (61)). -/
noncomputable def oscProb {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ) (m2 : Fin n → ℝ) (L E : ℝ)
    (α β : Fin n) : ℝ :=
  Complex.normSq (oscAmp U m2 L E α β)

/-- Antineutrino oscillation probability `P(ν̄_α → ν̄_β)`: the neutrino probability with the
mixing matrix replaced by its entrywise complex conjugate `U ↦ U^*` (Lipari, p. 135). -/
noncomputable def oscProbBar {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ) (m2 : Fin n → ℝ) (L E : ℝ)
    (α β : Fin n) : ℝ :=
  oscProb (U.map star) m2 L E α β

/-- The CP/T-odd coefficients `J^{αβ}_{jk} = -Im[U_{αj} U_{αk}^* U_{βj}^* U_{βk}]`
(Lipari, p. 136, first display). -/
def jarlskogCoeff {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ) (α β j k : Fin n) : ℝ :=
  -(U α j * star (U α k) * star (U β j) * U β k).im

/-- The CP-even amplitudes `A^{jk}_{αβ} = -4 Re[U_{αj} U_{βj}^* U_{αk}^* U_{βk}]`
(Lipari, Eq. (73)). -/
def ampCoeff {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ) (α β j k : Fin n) : ℝ :=
  -4 * (U α j * star (U β j) * star (U α k) * U β k).re

end LipariNeutrino


