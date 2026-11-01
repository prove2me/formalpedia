-- Prove2me | Definitions.Def_BaconThesis_Commutant_blockC
-- name    : BaconThesis_Commutant_blockC
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T16:36:43.553053+00:00
-- url     : https://prove2.me/theorems/867191f2-e720-4a5e-8711-2a1412a28029
-- title:
--   The block operators $\bigoplus_J Y_J\otimes I_{d_J}$ on the degeneracies
-- statement:
--   In the setting of $\mathrm{blockA}$ (irrep labels $J\in\mathcal J$, degeneracies $n_J$, irrep dimensions $d_J$, basis $|J,\lambda,m\rangle$), for a family of $n_J\times n_J$ complex matrices $Y=(Y_J)_{J\in\mathcal J}$ define
--   $$
--   \mathrm{blockC}(Y)=\bigoplus_{J\in\mathcal J} Y_J\otimes I_{d_J} .
--   $$
--   Such an operator acts on the degeneracy index $\lambda$ of each irrep and as the identity on the irrep index $m$. By (5.39) and (7.2), these are the elements of the commutant $A'\cong\bigoplus_J M_{n_J}\otimes I_{d_J}$ of $A\cong\bigoplus_J I_{n_J}\otimes M_{d_J}$.
--
--   **Formalization Note** Same index type as $\mathrm{blockA}$; the $J$-th block is the Kronecker product `Y J ⊗ₖ 1`.
-- source:
--   Bacon, Decoherence, Control, and Symmetry in Quantum Computers, arXiv:quant-ph/0305025v1, eq. (5.39), p.80 (PDF p.97); eq. (7.2), p.100 (PDF p.117)

import Mathlib

open scoped Kronecker

namespace BaconThesis.Commutant

/-- **The block operators `⊕_{J∈𝒥} Y_J ⊗ I_{d_J}` acting on the degeneracies.**
Bacon, *Decoherence, Control, and Symmetry in Quantum Computers*, arXiv:quant-ph/0305025v1,
§5.4.3, eq. (5.39), p.80 (PDF p.97), and §7.3, eq. (7.2), p.100 (PDF p.117): the commutant of
`A ≅ ⊕_{J∈𝒥} I_{n_J} ⊗ M_{d_J}` is `A′ ≅ ⊕_{J∈𝒥} M_{n_J} ⊗ I_{d_J}`.

Given, for each irrep label `J`, an arbitrary `n_J × n_J` complex matrix `Y J` (an operator on the
degeneracy of the `J`-th irrep), `blockC n d Y` is the block-diagonal matrix whose `J`-th diagonal
block is `Y J ⊗ I_{d_J}`.

**Formalization Note.** Same index type `Σ J : 𝒥, Fin (n J) × Fin (d J)` as `blockA` (basis
`|J, λ, m⟩`, degeneracy factor first, irrep factor second); the `J`-th block is
`Matrix.kronecker (Y J) (1 : Matrix (Fin (d J)) (Fin (d J)) ℂ)`. -/
noncomputable def blockC {𝒥 : Type} [Fintype 𝒥] [DecidableEq 𝒥] (n d : 𝒥 → ℕ)
    (Y : (J : 𝒥) → Matrix (Fin (n J)) (Fin (n J)) ℂ) :
    Matrix (Σ J : 𝒥, Fin (n J) × Fin (d J)) (Σ J : 𝒥, Fin (n J) × Fin (d J)) ℂ :=
  Matrix.blockDiagonal' fun J => Y J ⊗ₖ (1 : Matrix (Fin (d J)) (Fin (d J)) ℂ)

end BaconThesis.Commutant


