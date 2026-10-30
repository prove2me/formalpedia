-- Prove2me | Definitions.Def_WinterExtrinsic_canonWeight
-- name    : WinterExtrinsic_canonWeight
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:17:39.855265+00:00
-- url     : https://prove2.me/theorems/855d10f3-f45e-46b9-834a-123895c589e8
-- title:
--   Canonical ensemble weights $\lambda_j = \mathrm{Tr}(\rho a_j)$
-- statement:
--   Let $\rho$ be a state on $\mathbb C^d$ and let $a = (a_1, \dots, a_m)$ be a POVM on $\mathbb C^d$. The **weights of the canonical ensemble** of $(\rho, a)$ are
--
--   $$\lambda_j = \mathrm{Tr}(\rho\, a_j), \qquad j = 1, \dots, m .$$
--
--   For a density matrix $\rho$ and a POVM $a$ these are the outcome probabilities of measuring $a$ on $\rho$, so $\lambda$ is a probability distribution on $\{1, \dots, m\}$. Its Shannon entropy $H(\lambda)$ governs the total output rate of the measurement $a^{\otimes l}$ in Winter's decomposition theorem.
--
--   **Formalization Note** Outcomes are indexed by `Fin m`. The trace of the product of two positive semidefinite matrices is real; its real part is taken to land in $\mathbb R$.
-- source:
--   Winter, "Extrinsic" and "intrinsic" data in quantum measurements, arXiv:quant-ph/0109050v3, §I, p.1 ("λj = Tr (ρaj)") and Theorem 6, p.6 (canonical ensemble, "probabilities λj = Tr (ρaj)"), used in Theorem 2, p.3

import Mathlib

namespace WinterExtrinsic

/-- The weights `λ_j = Tr(ρ a_j)` of the canonical ensemble of a state `ρ` and a POVM
`a = (a_1, …, a_m)`.

Winter, *"Extrinsic" and "intrinsic" data in quantum measurements*, arXiv:quant-ph/0109050v3,
§I, p.1 ("λ_j = Tr(ρa_j)"), and Theorem 6, p.6 ("define a canonical ensemble {ρ̂_j, λ_j}, …
and probabilities λ_j = Tr(ρa_j)"), the ensemble of Theorem 2, p.3.

**Formalization Note.** The Hilbert space is `ℂ^d` with basis `Fin d`, and outcomes are indexed
by `Fin m` (the paper's `1, …, m`). The trace of the product of two positive semidefinite
matrices is real; its real part is taken to land in `ℝ`. -/
noncomputable def canonWeight {d m : ℕ} (ρ : Matrix (Fin d) (Fin d) ℂ)
    (a : Fin m → Matrix (Fin d) (Fin d) ℂ) (j : Fin m) : ℝ :=
  (ρ * a j).trace.re

end WinterExtrinsic


