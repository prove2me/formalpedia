-- Prove2me | Definitions.Def_RainsSep_Distill_entFidelity
-- name    : RainsSep_Distill_entFidelity
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T15:56:00.851728+00:00
-- url     : https://prove2.me/theorems/d5033ad0-792b-403b-bb37-074cf29af50e
-- title:
--   Entanglement fidelity $F(\sigma)=\phi^+(W)^\dagger\sigma\,\phi^+(W)$
-- statement:
--   Let $W$ be a finite-dimensional Hilbert space with computational basis $\{|i\rangle\}$, and let $\sigma$ be an operator on $W\otimes W$ (the first factor is Alice's, the second Bob's). The **entanglement fidelity** of $\sigma$ is its overlap with the maximally entangled state $\phi^+(W)=\frac{1}{\sqrt{\dim W}}\sum_i |i\rangle\otimes|i\rangle$:
--
--   $$
--   F(\sigma)=\phi^+(W)^\dagger\,\sigma\,\phi^+(W)=\frac{1}{\dim W}\sum_{i,j}\sigma_{(i,i),(j,j)} .
--   $$
--
--   It measures how close a bipartite state is to a maximally entangled pair of local dimension $\dim W$; distillation protocols aim to drive it to $1$.
--
--   **Formalization Note** The value is the real part of the complex number above (which is real for Hermitian $\sigma$). The basis of $W$ is fixed; the paper notes that $\phi^+$ depends on it only up to local unitaries.
-- source:
--   Rains, Entanglement purification via separable superoperators, arXiv:quant-ph/9707002v3, Eqs. (1)–(2), p. 1

import Mathlib

namespace RainsSep.Distill

/-- **Entanglement fidelity** `F(σ) = φ⁺(W)† σ φ⁺(W)`.
Rains, *Entanglement purification via separable superoperators*, arXiv:quant-ph/9707002v3, Eqs. (1)–(2), p. 1: "Let ρ be a mixed state on a bipartite Hilbert space V ⊗ V. We
define the entanglement fidelity of ρ as F(ρ) = φ+(V)† ρ φ+(V), (1) where φ+(V) is the
maximally entangled state (1/√dim(V)) Σ_{0≤i<dim(V)} |i⟩ ⊗ |i⟩. (2)"

For an operator `σ` on `W ⊗ W` (indexed by `W × W`, the first factor is Alice's), this is
`(1/|W|) Σ_{i,j} σ_{(i,i),(j,j)}`.

**Formalization Note.** The value is the real part of `φ⁺† σ φ⁺` (which is real for Hermitian
`σ`). `φ⁺(W)` uses the computational basis of `W`; the paper notes that the choice of basis
matters only up to local unitaries. For an empty `W` the value is `0` (no state exists). -/
noncomputable def entFidelity {W : Type*} [Fintype W] (σ : Matrix (W × W) (W × W) ℂ) : ℝ :=
  ((Fintype.card W : ℂ)⁻¹ * ∑ i, ∑ j, σ (i, i) (j, j)).re

end RainsSep.Distill


