-- Prove2me | Definitions.Def_ShadowTomography_QuantumLB_holevoInfo
-- name    : ShadowTomography_QuantumLB_holevoInfo
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T01:14:47.119742+00:00
-- url     : https://prove2.me/theorems/1628a72f-2ee7-4846-a321-bca7cee74ae5
-- title:
--   Quantum mutual information $I(\zeta; i)$ with a uniform classical index $i\in[K]$
-- statement:
--   Let $\sigma_1,\dots,\sigma_K$ be states, let $T\in\mathbb N$, and let $i$ be uniform on $[K]$. The state of $T$ copies averaged over $i$ is
--
--   $$
--   \zeta := \mathbb E_{i\in[K]}\bigl[\sigma_i^{\otimes T}\bigr] = \frac1K\sum_{i=1}^{K}\sigma_i^{\otimes T},
--   $$
--
--   and since $i$ is classical, the quantum mutual information between $\zeta$ and $i$ is
--
--   $$
--   I(\zeta; i) := S(\zeta) - S(\zeta\mid i) = S(\zeta) - \frac1K\sum_{i=1}^{K} S\bigl(\sigma_i^{\otimes T}\bigr),
--   $$
--
--   where $S$ is the von Neumann entropy in bits. This is the Holevo quantity of the ensemble $\{1/K,\ \sigma_i^{\otimes T}\}$ and bounds how much a measurement of $\zeta$ can reveal about $i$.
--
--   **Formalization Note** The conditional entropy $S(\zeta\mid i)$ of the classical–quantum state is written out directly as the average entropy, so no partial trace is needed.
-- source:
--   Aaronson, Shadow Tomography of Quantum States, arXiv:1711.01053v2, p. 24, proof of Theorem 19 (ζ := E_{i∈[K]}[σ_i^{⊗T}] and I(ζ; i) = S(ζ) − S(ζ | i))

import Mathlib
import Definitions.Def_ShadowTomography_ClassicalLB_tensorPow
import Definitions.Def_ShadowTomography_QuantumLB_vnEntropy

namespace ShadowTomography.QuantumLB

/-- The quantum mutual information `I(ζ; i) = S(ζ) − S(ζ | i)` between a uniformly random
classical index `i ∈ [K]` and `ζ := E_{i∈[K]}[σ_i^{⊗T}]` (p. 24):
`S((1/K) ∑ᵢ σ_i^{⊗T}) − (1/K) ∑ᵢ S(σ_i^{⊗T})`. -/
noncomputable def holevoInfo {n : Type} [Fintype n] [DecidableEq n] {K : ℕ}
    (σ : Fin K → Matrix n n ℂ) (T : ℕ) : ℝ :=
  vnEntropy (((1 : ℂ) / (K : ℂ)) • ∑ i, ShadowTomography.ClassicalLB.tensorPow (σ i) T)
    - (1 / (K : ℝ)) * ∑ i, vnEntropy (ShadowTomography.ClassicalLB.tensorPow (σ i) T)

end ShadowTomography.QuantumLB


