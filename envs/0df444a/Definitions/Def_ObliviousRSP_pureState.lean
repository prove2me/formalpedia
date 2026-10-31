-- Prove2me | Definitions.Def_ObliviousRSP_pureState
-- name    : ObliviousRSP_pureState
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T15:21:07.596959+00:00
-- url     : https://prove2.me/theorems/7d4b51f6-c1f7-4cd5-b502-bc2deaad7209
-- title:
--   Pure state $|\psi\rangle\langle\psi|$
-- statement:
--   For a vector $\psi\in\mathbb C^\iota$, the **pure state** it defines is the rank-one matrix
--   $$
--   \varphi = |\psi\rangle\langle\psi| ,\qquad \varphi_{ij} = \psi_i\,\overline{\psi_j}.
--   $$
--
--   The states prepared by the remote state preparation protocol are of this form, with $\psi$ a unit vector.
--
--   **Formalization Note** No normalization is built in; statements that need a unit vector assume $\langle\psi|\psi\rangle = 1$ (it is part of the generic-ensemble predicate).
-- source:
--   Leung–Shor, Oblivious remote state preparation, arXiv:quant-ph/0201008v1, p.2, "an ensemble of pure states"

import Mathlib

namespace ObliviousRSP

/-- Leung–Shor, *Oblivious remote state preparation*, arXiv:quant-ph/0201008v1, p.2 ("an ensemble of pure states"): the density matrix `φ = |ψ⟩⟨ψ|` of a pure state
given by a vector `ψ : ι → ℂ`, entrywise `φ i j = ψ i * conj (ψ j)`.

**Formalization Note.** No normalization is built in; the theorems that need a unit vector
assume `star ψ ⬝ᵥ ψ = 1` (it is part of `IsGeneric`). -/
def pureState {ι : Type} (ψ : ι → ℂ) : Matrix ι ι ℂ :=
  Matrix.vecMulVec ψ (star ψ)

end ObliviousRSP


