-- Prove2me | Definitions.Def_ChenMaxEnt_maximallyMixedOn
-- name    : ChenMaxEnt_maximallyMixedOn
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:20:34.613094+00:00
-- url     : https://prove2.me/theorems/e4578436-f184-4f18-96ea-06ae8a6a3ca3
-- title:
--   Maximally mixed state $P_V/\dim V$ supported on a subspace $V$
-- statement:
--   Let $V$ be a nonzero subspace of $\mathcal H = \mathbb C^n$ of dimension $m$, and let $P_V$ be the orthogonal projector onto $V$. The **maximally mixed state supported on $V$** is
--
--   $$
--   \rho_V = \frac{1}{m} P_V = \frac{1}{m}\sum_{a=1}^m |\psi_a\rangle\langle\psi_a| ,
--   $$
--
--   for any orthonormal basis $(\psi_a)$ of $V$. It is the state of largest von Neumann entropy ($\log m$) among the states supported on $V$. In Observation 3 it is the state $\rho^*$ on the ground space $V_0$, whose data are the point $\alpha$ where the discontinuity occurs.
--
--   **Formalization Note** $P_V$ is Mathlib's orthogonal projection `V.starProjection`, converted to an $n\times n$ matrix. For $V = 0$ the value is the junk matrix $0$ (since $0^{-1} = 0$ in Lean); the statements use it for nonzero $V$.
-- source:
--   Chen et al., Discontinuity of Maximum Entropy Inference and Quantum Phase Transitions, arXiv:1406.5046v2, §5.3, Observation 3, first bullet, p.22 ("the maximally mixed state supported on V0")

import Mathlib

namespace ChenMaxEnt

/-- Chen et al., arXiv:1406.5046v2, Observation 3, first bullet, p.22: "the maximally mixed state
supported on V0", i.e. `ρ_V = P_V / m` with `P_V` the orthogonal projector onto the subspace `V`
and `m = dim V`; equivalently `m⁻¹ Σ_a |ψ_a⟩⟨ψ_a|` for any orthonormal basis `(ψ_a)` of `V`
(compare eq. (14), p.11, and eq. (29), p.21).

**Formalization Note.** `V` is a subspace of `EuclideanSpace ℂ n`; `P_V` is
`V.starProjection` (the orthogonal projection onto `V`, as an operator on the whole space), turned
into an `n × n` matrix by `Matrix.toEuclideanLin.symm`. For `V = 0` the value is the junk `0`
(`(0 : ℂ)⁻¹ = 0`); the theorems use it for nonzero `V`. -/
noncomputable def maximallyMixedOn {n : Type*} [Fintype n] [DecidableEq n]
    (V : Submodule ℂ (EuclideanSpace ℂ n)) : Matrix n n ℂ :=
  ((Module.finrank ℂ V : ℂ))⁻¹ •
    Matrix.toEuclideanLin.symm (V.starProjection : EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n)

end ChenMaxEnt


