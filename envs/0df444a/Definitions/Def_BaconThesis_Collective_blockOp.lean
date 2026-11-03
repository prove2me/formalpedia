-- Prove2me | Definitions.Def_BaconThesis_Collective_blockOp
-- name    : BaconThesis_Collective_blockOp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:12:55.374696+00:00
-- url     : https://prove2.me/theorems/33541f9e-ffb8-4528-b400-1059bff33f62
-- title:
--   Block operator $\bigoplus_J I_{n_J}\otimes X_J$
-- statement:
--   Given multiplicities $n_J$ and an operator $X_J$ on $\mathbb C^{2J+1}$ for each $J$, the **block operator**
--   $$
--   \bigoplus_{J=0(1/2)}^{n/2} I_{n_J}\otimes X_J
--   $$
--   acts on $\bigoplus_J\mathbb C^{n_J}\otimes\mathbb C^{2J+1}$ block-diagonally, as $X_J$ on the irrep factor and as the identity on the degeneracy factor of each block. Operators of this form make up the algebra $\bigoplus_J I_{n_J}\otimes M_{2J+1}$ of (8.41); (8.43) says $S_\alpha$ is the case $X_J=S_\alpha(2J+1)$.
--
--   **Formalization Note** A block-diagonal matrix (`Matrix.blockDiagonal'`) whose block $r$ (with $J=n/2-r$) is the Kronecker product $I_{n_J}\otimes X_J$, degeneracy factor first.
-- source:
--   Bacon, Decoherence, Control, and Symmetry in Quantum Computers, arXiv:quant-ph/0305025v1, (8.41), (8.43), §8.6, p.118 (PDF p.135)

import Mathlib
import Definitions.Def_BaconThesis_Collective_BlockIdx

open scoped Matrix

namespace BaconThesis.Collective

/-- **The block operator `⊕_J I_(n_J) ⊗ X_J`.**
Bacon, *Decoherence, Control, and Symmetry in Quantum Computers*, arXiv:quant-ph/0305025v1, (8.41) and (8.43), §8.6, p.118 (PDF p.135): operators of the form
`⊕_{J=0(1/2)}^{n/2} I_(n_J) ⊗ X_J`, with `X_J` an operator on the `(2J+1)`-dimensional irrep
space and `I_(n_J)` the identity on the `n_J`-dimensional degeneracy space.

For multiplicities `m` and a family `X r` of `(n − 2r + 1) × (n − 2r + 1)` matrices
(`J = n/2 − r`), `blockOp n m X` is the block-diagonal matrix on `BlockIdx n m` whose block `r`
is the Kronecker product `I_(m r) ⊗ X r`.

**Formalization Note.** Built from `Matrix.blockDiagonal'` and `Matrix.kronecker`, degeneracy
factor first, irrep factor second, as in (8.43). -/
noncomputable def blockOp (n : ℕ) (m : Fin (n / 2 + 1) → ℕ)
    (X : (r : Fin (n / 2 + 1)) → Matrix (Fin (n - 2 * r.val + 1)) (Fin (n - 2 * r.val + 1)) ℂ) :
    Matrix (BlockIdx n m) (BlockIdx n m) ℂ :=
  Matrix.blockDiagonal' fun r =>
    Matrix.kronecker (1 : Matrix (Fin (m r)) (Fin (m r)) ℂ) (X r)

end BaconThesis.Collective


