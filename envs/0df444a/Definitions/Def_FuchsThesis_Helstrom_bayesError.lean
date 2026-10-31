-- Prove2me | Definitions.Def_FuchsThesis_Helstrom_bayesError
-- name    : FuchsThesis_Helstrom_bayesError
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T15:55:35.293595+00:00
-- url     : https://prove2.me/theorems/4ef6fca4-95c8-4b8f-9b38-2ef3d3d93ab7
-- title:
--   Bayes error of a fixed measurement, $\sum_b \min\{\pi_0\,\mathrm{tr}(\hat\rho_0\hat E_b),\ \pi_1\,\mathrm{tr}(\hat\rho_1\hat E_b)\}$
-- statement:
--   Let $\hat\rho_0, \hat\rho_1$ be $D\times D$ complex matrices (in the theorems, density operators), let $\pi_0, \pi_1$ be real numbers (the prior probabilities of the two states), and let $\{\hat E_b\}_{b=1}^{m}$ be a finite family of $D\times D$ matrices (in the theorems, a POVM). The **Bayes error of the measurement** $\{\hat E_b\}$ is
--
--   $$
--   \sum_{b} \min\big\{\pi_0\,\mathrm{tr}(\hat\rho_0\hat E_b),\ \pi_1\,\mathrm{tr}(\hat\rho_1\hat E_b)\big\}.
--   $$
--
--   It is the classical Bayes error probability (2.11), $\sum_b \min\{\pi_0 p_0(b), \pi_1 p_1(b)\}$, for the outcome distributions $p_i(b) = \mathrm{tr}(\hat\rho_i\hat E_b)$ that the measurement produces on the two states: the smallest probability of a wrong guess about the state that an observer can achieve from the outcome of this one measurement. Minimizing it over all measurements gives the quantum error probability (3.9).
--
--   **Formalization Note** Outcomes are indexed by $\mathrm{Fin}\,m$; $\mathrm{tr}(\hat\rho\hat E_b)$ is the real part of the matrix trace (`FuchsVdGraaf.outcomeDist`), which for a density operator and a positive semidefinite $\hat E_b$ is the trace itself.
-- source:
--   Fuchs, Distinguishability and Accessible Information in Quantum Theory, arXiv:quant-ph/9601020v1, eq. (3.9), p.44 (PDF p.53); eq. (2.11), p.15 (PDF p.24)

import Mathlib
import Definitions.Def_FuchsVdGraaf_outcomeDist

namespace FuchsThesis.Helstrom

/-- Fuchs, *Distinguishability and Accessible Information in Quantum Theory*,
arXiv:quant-ph/9601020v1, eq. (3.9), p.44 (PDF p.53): the expected error probability of the Bayes
decision based on the outcome of a measurement `{Ê_b}` performed on a system prepared in `ρ̂₀` with
prior `π₀` or in `ρ̂₁` with prior `π₁`,
`∑_b min{π₀ tr(ρ̂₀Ê_b), π₁ tr(ρ̂₁Ê_b)}` (the quantity minimized in (3.9); it is (2.11), p.15 (PDF p.24),
for `p_i(b) = tr(ρ̂_i Ê_b)`).

**Formalization Note.** Outcomes are `Fin m`. `tr(ρ̂Ê_b)` is
`FuchsVdGraaf.outcomeDist ρ E b`, the real part of `Matrix.trace (ρ * E b)`; for a density matrix
and a positive semidefinite `Ê_b` the trace is real. -/
noncomputable def bayesError {n : Type} [Fintype n] {m : ℕ} (π0 π1 : ℝ) (ρ0 ρ1 : Matrix n n ℂ)
    (E : Fin m → Matrix n n ℂ) : ℝ :=
  ∑ b, min (π0 * FuchsVdGraaf.outcomeDist ρ0 E b) (π1 * FuchsVdGraaf.outcomeDist ρ1 E b)

end FuchsThesis.Helstrom


