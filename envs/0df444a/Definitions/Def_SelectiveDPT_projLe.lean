-- Prove2me | Definitions.Def_SelectiveDPT_projLe
-- name    : SelectiveDPT_projLe
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:48:53.208592+00:00
-- url     : https://prove2.me/theorems/1e20810f-5857-43c4-9c57-820171adddf4
-- title:
--   Spectral projections $\Pi_{\Gamma,\le\lambda}$ and $\Pi_{\Gamma,\ge\lambda}$
-- statement:
--   For a Hermitian matrix $\Gamma$ and $\lambda \in \mathbb R$, $\Pi_{\Gamma,\le\lambda}$ is the orthogonal projection onto the span of the eigenspaces of $\Gamma$ with eigenvalue at most $\lambda$, and $\Pi_{\Gamma,\ge\lambda}$ the projection onto the span of the eigenspaces with eigenvalue at least $\lambda$. If $\Gamma = \sum_j \lambda_j v_j v_j^\dagger$ is a spectral decomposition,
--   $$\Pi_{\Gamma,\le\lambda} = \sum_{j:\ \lambda_j \le \lambda} v_j v_j^\dagger, \qquad \Pi_{\Gamma,\ge\lambda} = \sum_{j:\ \lambda_j \ge \lambda} v_j v_j^\dagger .$$
--
--   **Formalization Note** Both are defined by the continuous functional calculus applied to an indicator function, which does not depend on the choice of eigenbasis. For a non-Hermitian matrix the value is $0$; every statement assumes $\Gamma$ Hermitian.
-- source:
--   Beame–Kornerup–Whitmeyer, Strong Selective and List-Decoding Direct Product Theorems for Quantum Query Complexity, arXiv:2609.26678, §2.4, p.14 (Π_{Γ,<λ}, Π_{Γ,>λ}, Π_{Γ,≤λ}, Π_{Γ,≥λ})

import Mathlib

namespace SelectiveDPT

/-- The spectral projection `Π_{Γ,≤λ}` of a Hermitian matrix `Γ` onto the span of its
eigenspaces with eigenvalues at most `λ` (arXiv:2609.26678, §2.4, p.14: "We use `Π_{Γ,<λ}` to
denote the projection onto the eigenspaces of `Γ` with eigenvalues less than `λ` and similarly
define `Π_{Γ,>λ}`, `Π_{Γ,≤λ}`, and `Π_{Γ,≥λ}`").

**Formalization Note.** Defined by the continuous functional calculus applied to the indicator of
`(−∞, λ]`, which is basis independent; on a matrix the spectrum is finite, so the indicator is
continuous on it. For a non-Hermitian `Γ` the value is the junk `0`; every statement using it
assumes `Γ` Hermitian. -/
noncomputable def projLe {n : Type*} [Fintype n] [DecidableEq n] (Γ : Matrix n n ℂ) (lam : ℝ) :
    Matrix n n ℂ :=
  cfc (fun t : ℝ => if t ≤ lam then (1 : ℝ) else 0) Γ

/-- The spectral projection `Π_{Γ,≥λ}` onto the span of the eigenspaces of the Hermitian matrix
`Γ` with eigenvalues at least `λ` (arXiv:2609.26678, §2.4, p.14). Same conventions as `projLe`. -/
noncomputable def projGe {n : Type*} [Fintype n] [DecidableEq n] (Γ : Matrix n n ℂ) (lam : ℝ) :
    Matrix n n ℂ :=
  cfc (fun t : ℝ => if lam ≤ t then (1 : ℝ) else 0) Γ

end SelectiveDPT


