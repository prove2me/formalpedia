-- Prove2me | Definitions.Def_TeschlQM_Dynamics_pointSpectrum
-- name    : TeschlQM_Dynamics_pointSpectrum
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T06:44:41.819524+00:00
-- url     : https://prove2.me/theorems/6c012c6b-0035-46ab-bfbb-d5da361fc1f8
-- title:
--   The set of eigenvalues σ_p(A) (3.76)
-- statement:
--   For a self-adjoint operator $A$ in $\mathfrak H$, the set of eigenvalues is
--   $$\sigma_p(A) = \{\lambda \in \mathbb R \mid \lambda \text{ is an eigenvalue of } A\},$$
--   that is, the set of real $\lambda$ for which there is $\psi \in \mathfrak D(A)$, $\psi \neq 0$, with $A\psi = \lambda\psi$.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 103, Section 3.2, Eq. (3.76)

import Mathlib

namespace TeschlQM.Dynamics

/-- Teschl, p. 103, (3.76): the set of eigenvalues of the self-adjoint operator `A`,
`σ_p(A) = {λ ∈ ℝ | λ is an eigenvalue of A}`, i.e. there is `ψ ∈ 𝔇(A)`, `ψ ≠ 0`, with
`Aψ = λψ`. -/
def pointSpectrum {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →ₗ.[ℂ] H) : Set ℝ :=
  {x | ∃ ψ : A.domain, (ψ : H) ≠ 0 ∧ A ψ = (x : ℂ) • (ψ : H)}

end TeschlQM.Dynamics


