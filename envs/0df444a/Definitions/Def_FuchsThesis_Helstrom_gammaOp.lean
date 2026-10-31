-- Prove2me | Definitions.Def_FuchsThesis_Helstrom_gammaOp
-- name    : FuchsThesis_Helstrom_gammaOp
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T15:55:11.076446+00:00
-- url     : https://prove2.me/theorems/1b3a2b51-f52e-4f91-8b0b-6a59430cb092
-- title:
--   Helstrom operator $\hat\Gamma = \pi_1\hat\rho_1 - \pi_0\hat\rho_0$ (eq. 3.12)
-- statement:
--   For two operators $\hat\rho_0, \hat\rho_1$ on a finite-dimensional Hilbert space and real priors $\pi_0, \pi_1$, the operator
--
--   $$
--   \hat\Gamma \equiv \pi_1\hat\rho_1 - \pi_0\hat\rho_0 .
--   $$
--
--   When $\hat\rho_0, \hat\rho_1$ are Hermitian (in particular, density operators), $\hat\Gamma$ is Hermitian; its eigenvalues $\gamma_j$ determine the quantum error probability, $P_e(\hat\rho_0|\hat\rho_1) = \pi_0 + \sum_{\gamma_j\le 0}\gamma_j$, and its negative eigenspace gives Helstrom's optimal measurement.
--
--   **Formalization Note** The real priors act on complex matrices through the coercion $\mathbb R\to\mathbb C$. The module also contains the structural lemma `gammaOp_isHermitian` ($\hat\Gamma$ is Hermitian when $\hat\rho_0,\hat\rho_1$ are), which the theorems use to name the eigenvalues of $\hat\Gamma$ via `Matrix.IsHermitian.eigenvalues`.
-- source:
--   Fuchs, Distinguishability and Accessible Information in Quantum Theory, arXiv:quant-ph/9601020v1, eq. (3.12), p.45 (PDF p.54)

import Mathlib

namespace FuchsThesis.Helstrom

/-- Fuchs, *Distinguishability and Accessible Information in Quantum Theory*,
arXiv:quant-ph/9601020v1, eq. (3.12), p.45 (PDF p.54): the Hermitian operator
`Γ̂ ≡ π₁ρ̂₁ − π₀ρ̂₀`.

**Formalization Note.** The priors are real and act on complex matrices through the coercion
`ℝ → ℂ`. -/
noncomputable def gammaOp {n : Type} (π0 π1 : ℝ) (ρ0 ρ1 : Matrix n n ℂ) : Matrix n n ℂ :=
  (π1 : ℂ) • ρ1 - (π0 : ℂ) • ρ0

/-- `Γ̂ = π₁ρ̂₁ − π₀ρ̂₀` is Hermitian when `ρ̂₀` and `ρ̂₁` are (structural lemma, used to name the
eigenvalues `γ_j` of `Γ̂` through `Matrix.IsHermitian.eigenvalues`). -/
theorem gammaOp_isHermitian {n : Type} {π0 π1 : ℝ} {ρ0 ρ1 : Matrix n n ℂ}
    (h0 : ρ0.IsHermitian) (h1 : ρ1.IsHermitian) : (gammaOp π0 π1 ρ0 ρ1).IsHermitian := by
  unfold gammaOp
  refine Matrix.IsHermitian.sub ?_ ?_
  · simp [Matrix.IsHermitian, Matrix.conjTranspose_smul, h1.eq]
  · simp [Matrix.IsHermitian, Matrix.conjTranspose_smul, h0.eq]

end FuchsThesis.Helstrom


