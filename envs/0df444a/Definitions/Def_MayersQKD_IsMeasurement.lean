-- Prove2me | Definitions.Def_MayersQKD_IsMeasurement
-- name    : MayersQKD_IsMeasurement
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:41:27.810173+00:00
-- url     : https://prove2.me/theorems/8a4f146b-5092-4621-8e32-588ed127b027
-- title:
--   Measurement: operators $M_k$ with $\sum_k M_k^\dagger M_k=\mathbf I$
-- statement:
--   A measurement on a state space $\mathcal H$ is a set of outcomes $k$, each associated with an operator $M_k$ from $\mathcal H$ into a state space, subject only to
--
--   $$
--   \sum_k M_k^\dagger M_k=\mathbf I .
--   $$
--
--   The probability of $k$ on $|\psi\rangle$ is $\|M_k|\psi\rangle\|^2$. This is the general measurement used for Bob's operation on the photons and for his final measurement.
--
--   **Formalization Note** The outcome set is finite, the spaces are finite-dimensional, and all $M_k$ share one target space.
-- source:
--   Mayers, Quantum Key Distribution and String Oblivious Transfer in Noisy Channels, arXiv:quant-ph/9606003v1, §4, p.6

import Mathlib

namespace MayersQKD

/-- Mayers, arXiv:quant-ph/9606003v1, §4, p.6: a measurement is a set of outcomes `k`, each
associated with an operator `M_k`, whose only requirement is `∑_k M_k† M_k = I`. The image of
`M_k` may be any sufficiently large state space; the probability of `k` on `|ψ⟩` is
`‖M_k |ψ⟩‖²`.

**Formalization Note.** Finite outcome set and finite-dimensional spaces, with one common target
space `F`. -/
def IsMeasurement {ι E F : Type} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
    (M : ι → E →ₗ[ℂ] F) : Prop :=
  ∑ k, LinearMap.adjoint (M k) ∘ₗ M k = LinearMap.id

end MayersQKD


