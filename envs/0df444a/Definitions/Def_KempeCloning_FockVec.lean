-- Prove2me | Definitions.Def_KempeCloning_FockVec
-- name    : KempeCloning_FockVec
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T15:22:37.400241+00:00
-- url     : https://prove2.me/theorems/f1b9b69a-e437-46c0-a6c2-1749c81d7e32
-- title:
--   Finite superpositions of five-mode number states
-- statement:
--   A Fock vector is a finite superposition
--
--   $$|\psi\rangle = \sum_{n} \psi(n)\, |n\rangle ,\qquad \psi(n)\in\mathbb C,$$
--
--   of number states $|n\rangle = |n_{a_1}, n_{a_2}, n_{b_1}, n_{b_2}, n_c\rangle$, with only finitely many nonzero amplitudes $\psi(n)$. Every state the paper writes down, the initial state (13), the sector states (15) and the cloner states (19), is of this kind, and the ladder operators and the Hamiltonian (14) map such vectors to such vectors.
--
--   **Formalization Note** Finitely supported functions from Fock indices to $\mathbb C$ (`FockIndex →₀ ℂ`): the algebraic core of the five-mode bosonic Fock space, without Hilbert-space completion. No completion is needed, because the dynamics of the paper stays in the finite sector (15).
-- source:
--   Kempe, Simon, Weihs, Λ's, V's, and optimal cloning with stimulated emission, arXiv:quant-ph/0003025v1, Sec. II B, (13)–(15), p.4; Sec. II C, (18)–(19), p.5

import Definitions.Def_KempeCloning_FockIndex

namespace KempeCloning

/-- **Finite superpositions of five-mode number states.**
Kempe, Simon, Weihs, arXiv:quant-ph/0003025v1, Sec. II B, (13)–(15), p.4, and Sec. II C,
(18)–(19), p.5: every state the paper writes is a finite linear combination of Fock basis states
`|n_{a1}, n_{a2}, n_{b1}, n_{b2}, n_c⟩`.

A vector `ψ : FockVec` is a finitely supported map from Fock indices to complex amplitudes:
`ψ = Σ_n ψ(n) |n⟩`.

**Formalization Note.** This is the algebraic (finite-particle) core of the five-mode bosonic
Fock space, without completion. The ladder operators and the Hamiltonian (14) map it to itself,
and the dynamics of Sec. II C stays in a finite-dimensional sector (15), so no Hilbert-space
completion is needed for the statements of the mission. -/
abbrev FockVec : Type := FockIndex →₀ ℂ

end KempeCloning


