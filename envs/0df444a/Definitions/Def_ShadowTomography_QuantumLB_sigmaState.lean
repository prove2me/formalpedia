-- Prove2me | Definitions.Def_ShadowTomography_QuantumLB_sigmaState
-- name    : ShadowTomography_QuantumLB_sigmaState
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T01:13:13.912646+00:00
-- url     : https://prove2.me/theorems/39c87ea4-eead-41b4-923f-a3678223af11
-- title:
--   The hard state $\sigma_i = (1-6\varepsilon)\,\mathbb I/N + 6\varepsilon\rho_i$
-- statement:
--   Given the projection $\mathbb P$ onto an $N/2$-dimensional subspace of $\mathbb C^N$ and $\varepsilon\in\mathbb R$, the mixed state used in the lower bound of Theorem 19 is the mixture of the maximally mixed state $\mathbb I/N$ and the state $\rho_{\mathbb P}=\tfrac 2N\mathbb P$:
--
--   $$
--   \sigma_{\mathbb P,\varepsilon} := (1-6\varepsilon)\,\frac{\mathbb I}{N} + 6\varepsilon\,\rho_{\mathbb P} .
--   $$
--
--   The paper writes $\sigma_i$ for $\sigma_{\mathbb P_i,\varepsilon}$. It is slightly biased towards the subspace $S_i$, so that the measurement $\mathbb P_i$ accepts it with probability $\tfrac12+3\varepsilon$, while every other $\mathbb P_j$ accepts it with probability within $\varepsilon/2$ of $\tfrac12$.
--
--   **Formalization Note** The definition is a matrix expression for all real $\varepsilon$; it is a density operator when $0\le\varepsilon\le\tfrac16$.
-- source:
--   Aaronson, Shadow Tomography of Quantum States, arXiv:1711.01053v2, p. 23, proof of Theorem 19 (σ_i := (1 − 6ε)𝕀/N + 6ερ_i)

import Mathlib
import Definitions.Def_ShadowTomography_QuantumLB_rhoState

namespace ShadowTomography.QuantumLB

/-- `σ_P := (1 − 6ε) 𝕀/N + 6ε ρ_P` (p. 23, written `σ_i`). -/
noncomputable def sigmaState {N : ℕ} (P : Matrix (Fin N) (Fin N) ℂ) (ε : ℝ) :
    Matrix (Fin N) (Fin N) ℂ :=
  ((1 - 6 * ε : ℝ) : ℂ) • ((1 : ℂ) / (N : ℂ)) • (1 : Matrix (Fin N) (Fin N) ℂ)
    + ((6 * ε : ℝ) : ℂ) • rhoState P

end ShadowTomography.QuantumLB


