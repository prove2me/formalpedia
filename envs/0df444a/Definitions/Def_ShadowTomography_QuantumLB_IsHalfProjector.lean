-- Prove2me | Definitions.Def_ShadowTomography_QuantumLB_IsHalfProjector
-- name    : ShadowTomography_QuantumLB_IsHalfProjector
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T00:48:50.291313+00:00
-- url     : https://prove2.me/theorems/e988822c-66eb-4c7f-a5cf-850606fb00ca
-- title:
--   Orthogonal projection onto an $N/2$-dimensional subspace of $\mathbb C^N$
-- statement:
--   An $N\times N$ complex matrix $\mathbb P$ is the **orthogonal projection onto an $N/2$-dimensional subspace** $S\le\mathbb C^N$ when
--
--   $$
--   \mathbb P^\dagger = \mathbb P, \qquad \mathbb P^2 = \mathbb P, \qquad \operatorname{Tr}(\mathbb P) = \tfrac N2 .
--   $$
--
--   For an orthogonal projection the trace equals the rank, which is $\dim S$, so these conditions say exactly that $\mathbb P = \mathbb P_S$ with $\dim S = N/2$. In the proof of Theorem 19 the projections $\mathbb P_1,\dots,\mathbb P_K$ onto the subspaces $S_1,\dots,S_K$ are both the two-outcome measurements and the building blocks of the hard states.
--
--   **Formalization Note** The subspace is represented by its projection rather than as a submodule. If $N$ is odd no matrix satisfies the definition, matching the paper's requirement that $N$ be even.
-- source:
--   Aaronson, Shadow Tomography of Quantum States, arXiv:1711.01053v2, p. 23, proof of Theorem 19 ("Let ℙ_i be the projection onto S_i", dim(S_i) = N/2)

import Mathlib

namespace ShadowTomography.QuantumLB

/-- `P` is the orthogonal projection onto an `N/2`-dimensional subspace of `ℂ^N`:
Hermitian, idempotent, and of trace (= rank) `N/2`. -/
def IsHalfProjector {N : ℕ} (P : Matrix (Fin N) (Fin N) ℂ) : Prop :=
  P.IsHermitian ∧ P * P = P ∧ P.trace = ((N : ℂ) / 2)

end ShadowTomography.QuantumLB


