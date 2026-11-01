-- Prove2me | Definitions.Def_BaconThesis_Stability_blockOp
-- name    : BaconThesis_Stability_blockOp
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:58:19.369988+00:00
-- url     : https://prove2.me/theorems/41ac316f-165e-4bee-9231-3dc747ade93c
-- title:
--   Block operator $\bigoplus_{J\in\mathcal J} I_{n_J}\otimes X_J$
-- statement:
--   Let the system Hilbert space carry an orthonormal basis $|J,\lambda,m\rangle$, where $J$ ranges over a finite index set $\mathcal J$ (the blocks), $\lambda\in\{1,\dots,n_J\}$ labels the **degeneracy** of block $J$ and $m\in\{1,\dots,d_J\}$ labels the factor on which block $J$ acts non-trivially. Given a $d_J\times d_J$ complex matrix $X_J$ for every block, the **block operator**
--   $$
--   \bigoplus_{J\in\mathcal J} I_{n_J}\otimes X_J
--   $$
--   is block diagonal over $J$, and on block $J$ it is the tensor product of the $n_J\times n_J$ identity with $X_J$. Its matrix elements are
--   $$
--   \langle J,\lambda,m|\Big(\bigoplus_{K} I_{n_K}\otimes X_K\Big)|J',\lambda',m'\rangle=\delta_{JJ'}\,\delta_{\lambda\lambda'}\,(X_J)_{mm'} .
--   $$
--
--   This is the form (5.31)–(5.32) that every operator of a $\dagger$-closed algebra takes in the basis adapted to its irreducible representations; Chapter 6 uses it for the expansion operators of the decoherence-free evolution, eq. (6.21).
--
--   **Formalization Note** The system index type is the dependent sum $\Sigma_{J}\,\mathrm{Fin}\,n_J\times\mathrm{Fin}\,d_J$ with 0-based indices; the operator is `Matrix.blockDiagonal'` of the Kronecker products `1 ⊗ₖ X J`, the degeneracy factor first.
-- source:
--   Bacon, Decoherence, Control, and Symmetry in Quantum Computers, arXiv:quant-ph/0305025v1, §5.4.1, eqs. (5.31)–(5.32), p.78 (PDF p.95); eq. (6.21), p.91 (PDF p.108)

import Mathlib

open scoped Kronecker

namespace BaconThesis.Stability

/-- **Block operator `⊕_{J∈𝒥} I_{n_J} ⊗ X_J`.**
Bacon, *Decoherence, Control, and Symmetry in Quantum Computers*, arXiv:quant-ph/0305025v1,
§5.4.1, eqs. (5.31)–(5.32), p.78 (PDF p.95), and eq. (6.21), p.91 (PDF p.108).

The system Hilbert space has the orthonormal basis `|J, λ, m⟩` with `J` in a finite index set `𝒥`,
`λ ∈ Fin (n J)` (the degeneracy of the `J`th block) and `m ∈ Fin (d J)` (the factor acted on
non-trivially). Given one `d_J × d_J` matrix `X J` for every block, `blockOp n d X` is the operator
`⊕_J I_{n_J} ⊗ X_J`: block diagonal over `J`, and on block `J` the Kronecker product of the
`n_J × n_J` identity with `X J`. Its matrix entries are
`⟨J,λ,m| blockOp n d X |J',λ',m'⟩ = δ_{JJ'} δ_{λλ'} (X J) m m'`, which is (5.32).

**Formalization Note.** The system index type is `Σ J : 𝒥, Fin (n J) × Fin (d J)`, the basis
`|J, λ, m⟩` written as `⟨J, (λ, m)⟩` (indices 0-based, the book's are 1-based). The degeneracy
factor `λ` comes first in the Kronecker product, as in the book's `I_{n_J} ⊗ S_{d_J}`. -/
def blockOp {𝒥 : Type} [DecidableEq 𝒥] (n d : 𝒥 → ℕ)
    (X : ∀ J, Matrix (Fin (d J)) (Fin (d J)) ℂ) :
    Matrix (Σ J : 𝒥, Fin (n J) × Fin (d J)) (Σ J : 𝒥, Fin (n J) × Fin (d J)) ℂ :=
  Matrix.blockDiagonal' fun J => (1 : Matrix (Fin (n J)) (Fin (n J)) ℂ) ⊗ₖ X J

end BaconThesis.Stability


