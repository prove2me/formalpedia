-- Prove2me | Definitions.Def_BaconThesis_Commutant_blockA
-- name    : BaconThesis_Commutant_blockA
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T16:36:39.692782+00:00
-- url     : https://prove2.me/theorems/b3237351-ed36-4391-8c27-8200274658e5
-- title:
--   The block operators $\bigoplus_J I_{n_J}\otimes X_J$
-- statement:
--   Let $\mathcal J$ be a finite set of irrep labels and, for each $J\in\mathcal J$, let $n_J$ (the **degeneracy** of the $J$-th irrep) and $d_J$ (its dimension) be natural numbers. Consider the space
--   $$
--   \bigoplus_{J\in\mathcal J}\mathbb C^{n_J}\otimes\mathbb C^{d_J}
--   $$
--   with orthonormal basis $|J,\lambda,m\rangle$, where $J$ labels the irrep, $\lambda=1,\dots,n_J$ the degenerate component and $m=1,\dots,d_J$ the component acted upon by the irrep. For a family of $d_J\times d_J$ complex matrices $X=(X_J)_{J\in\mathcal J}$ define the block-diagonal operator
--   $$
--   \mathrm{blockA}(X)=\bigoplus_{J\in\mathcal J} I_{n_J}\otimes X_J .
--   $$
--   These are exactly the operators $S=\bigoplus_J I_{n_J}\otimes S_{d_J}$ of (5.31), the elements of an algebra $A\cong\bigoplus_J I_{n_J}\otimes M_{d_J}$ written in the basis $|J,\lambda,m\rangle$.
--
--   **Formalization Note** The space is indexed by $\Sigma J,\ \mathrm{Fin}\,n_J\times\mathrm{Fin}\,d_J$ (0-based $\lambda,m$), the degeneracy factor first and the irrep factor second; the $J$-th block is the Kronecker product `1 ⊗ₖ X J`.
-- source:
--   Bacon, Decoherence, Control, and Symmetry in Quantum Computers, arXiv:quant-ph/0305025v1, Theorem 5.4.1 and eqs. (5.30)–(5.32), pp.77–78 (PDF pp.94–95); eq. (5.38), p.80 (PDF p.97)

import Mathlib

open scoped Kronecker

namespace BaconThesis.Commutant

/-- **The block operators `⊕_{J∈𝒥} I_{n_J} ⊗ X_J` of the algebra `A`.**
Bacon, *Decoherence, Control, and Symmetry in Quantum Computers*, arXiv:quant-ph/0305025v1,
§5.4.1, Theorem 5.4.1, eqs. (5.30)–(5.32), pp.77–78 (PDF pp.94–95), and §5.4.3, eq. (5.38), p.80
(PDF p.97): in the basis `|J, λ, m⟩` (`J` labels the irrep, `λ = 1, …, n_J` the degeneracy,
`m = 1, …, d_J` the component acted upon by the irrep) every element of the algebra
`A ≅ ⊕_{J∈𝒥} I_{n_J} ⊗ M_{d_J}` acts as `S = ⊕_{J∈𝒥} I_{n_J} ⊗ S_{d_J}` (5.31).

Given, for each irrep label `J`, an arbitrary `d_J × d_J` complex matrix `X J`, `blockA n d X` is
the block-diagonal matrix whose `J`-th diagonal block is `I_{n_J} ⊗ X J`.

**Formalization Note.** The space `⊕_J ℂ^{n_J} ⊗ ℂ^{d_J}` is indexed by
`Σ J : 𝒥, Fin (n J) × Fin (d J)`, the basis vector `(J, λ, m)` being `|J, λ, m⟩` (0-based `λ, m`);
the degeneracy factor is the first tensor factor and the irrep factor the second, so the `J`-th
block is `Matrix.kronecker (1 : Matrix (Fin (n J)) (Fin (n J)) ℂ) (X J)`. -/
noncomputable def blockA {𝒥 : Type} [Fintype 𝒥] [DecidableEq 𝒥] (n d : 𝒥 → ℕ)
    (X : (J : 𝒥) → Matrix (Fin (d J)) (Fin (d J)) ℂ) :
    Matrix (Σ J : 𝒥, Fin (n J) × Fin (d J)) (Σ J : 𝒥, Fin (n J) × Fin (d J)) ℂ :=
  Matrix.blockDiagonal' fun J => (1 : Matrix (Fin (n J)) (Fin (n J)) ℂ) ⊗ₖ X J

end BaconThesis.Commutant


