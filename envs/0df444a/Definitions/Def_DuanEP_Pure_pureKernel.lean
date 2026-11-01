-- Prove2me | Definitions.Def_DuanEP_Pure_pureKernel
-- name    : DuanEP_Pure_pureKernel
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:20:51.12764+00:00
-- url     : https://prove2.me/theorems/87dbc936-11ef-47ed-8720-d7e52cd05bc3
-- title:
--   Rank-one operator $|\psi\rangle\langle\psi|$ of a coefficient function
-- statement:
--   For a coefficient function $\psi:I\to\mathbb C$ on an orthonormal basis indexed by $I$, the **density operator of the pure state** $\psi$ is the rank-one operator $|\psi\rangle\langle\psi|$, with matrix entries
--
--   $$
--   (|\psi\rangle\langle\psi|)_{p,q}=\psi(p)\,\overline{\psi(q)}.
--   $$
--
--   **Formalization Note** This is the body of the platform's `rankOne` (Dependency50.P33), applied to a raw coefficient function rather than an element of $\ell^2(I)$.
-- source:
--   Duan, Giedke, Cirac, Zoller, Entanglement purification of Gaussian continuous variable quantum states, arXiv:quant-ph/9912017v2, p. 1 (density operator of a pure state, implicit in the definition of entanglement)

import Mathlib

namespace DuanEP.Pure

/-- The rank-one operator `|ψ⟩⟨ψ|` of a pure state given by its coefficient function `ψ : I → ℂ`
in an orthonormal basis indexed by `I`: the matrix `(p, q) ↦ ψ p · conj (ψ q)`
(Duan, Giedke, Cirac, Zoller, *Entanglement purification of Gaussian continuous variable quantum states*, arXiv:quant-ph/9912017v2, p. 1: the density operator of a pure state).

**Formalization Note** This is the body of the platform's
`QAlgorithms.Papers.Independent.Dependency50.P33.rankOne` on raw coefficient functions, so that no
`ℓ²`-membership proof is needed inside the definitions; the states of this mission are shown to be
square-summable in the milestones. -/
def pureKernel {I : Type} (ψ : I → ℂ) : Matrix I I ℂ := fun p q => ψ p * star (ψ q)

end DuanEP.Pure


