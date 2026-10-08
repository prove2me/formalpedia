-- Prove2me | Definitions.Def_ShadowTomography_QuantumLB_rhoState
-- name    : ShadowTomography_QuantumLB_rhoState
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T00:49:17.217565+00:00
-- url     : https://prove2.me/theorems/a7655372-379c-4ba1-b0bd-16635a368c1c
-- title:
--   The maximally mixed state on a subspace, $\rho_i = (2/N)\,\mathbb P_i$
-- statement:
--   Given the projection $\mathbb P$ onto an $N/2$-dimensional subspace $S\le\mathbb C^N$, the **maximally mixed state projected onto $S$** is
--
--   $$
--   \rho_{\mathbb P} := \frac{2}{N}\,\mathbb P .
--   $$
--
--   It is the uniform mixture over an orthonormal basis of $S$. In the proof of Theorem 19 the paper writes $\rho_i := \tfrac2N \mathbb P_i$.
--
--   **Formalization Note** The definition is the matrix $\tfrac 2N \mathbb P$ for any $N\times N$ matrix $\mathbb P$; it is a density operator when $\mathbb P$ is an orthogonal projection of rank $N/2$ with $N\ge 2$.
-- source:
--   Aaronson, Shadow Tomography of Quantum States, arXiv:1711.01053v2, p. 23, proof of Theorem 19 (ρ_i := (2/N)ℙ_i)

import Mathlib

namespace ShadowTomography.QuantumLB

/-- `ρ_P := (2/N) ℙ`, the maximally mixed state projected onto the range of `ℙ`
(p. 23, written `ρ_i := (2/N) ℙ_i`). -/
noncomputable def rhoState {N : ℕ} (P : Matrix (Fin N) (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  ((2 : ℂ) / (N : ℂ)) • P

end ShadowTomography.QuantumLB


