-- Prove2me | Definitions.Def_DHRUniq_IsUnitVec
-- name    : DHRUniq_IsUnitVec
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:32:42.741192+00:00
-- url     : https://prove2.me/theorems/fcefc98b-3fa5-46f1-a037-11e9f74a8c9e
-- title:
--   Wavefunction: a unit vector of $\mathbb C^\iota$
-- statement:
--   A **wavefunction** is a unit vector $\psi$ of a finite-dimensional Hilbert space $\mathbb C^\iota$, that is, a function $\psi:\iota\to\mathbb C$ on a finite set with
--
--   $$
--   \sum_{z\in\iota}|\psi(z)|^2=1.
--   $$
--
--   A bipartite wavefunction has $\iota=a\times b$. Unit vectors are exactly the vectors whose projector $P_\psi=|\psi\rangle\langle\psi|$ is a state.
--
--   **Formalization Note** The published `ObliviousRSP.pureState` builds in no normalization, so every condition of this mission assumes this predicate explicitly.
-- source:
--   Donald, Horodecki, Rudolph, The uniqueness theorem for entanglement measures, arXiv:quant-ph/0105017v2, §2, p. 3

import Mathlib

namespace DHRUniq

/-- **Wavefunction.** A unit vector of a finite-dimensional Hilbert space `ℂ^ι` (Donald, Horodecki, Rudolph, *The uniqueness theorem for entanglement measures*, arXiv:quant-ph/0105017v2, §2,
p. 3: "For a wavefunction `|ψ⟩ ∈ H` the corresponding state will be denoted by
`P_ψ ≡ |ψ⟩⟨ψ|`"; a state has trace one, so a wavefunction has norm one).

**Formalization Note** A vector is a function `ι → ℂ` on a finite type; a bipartite wavefunction
has `ι = a × b`. Every condition of the mission assumes this predicate explicitly, because the
published `ObliviousRSP.pureState` builds in no normalization. -/
def IsUnitVec {ι : Type} [Fintype ι] (ψ : ι → ℂ) : Prop :=
  ∑ z, ‖ψ z‖ ^ 2 = 1

end DHRUniq


