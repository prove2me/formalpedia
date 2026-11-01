-- Prove2me | Definitions.Def_BaconThesis_Stability_IsBlockForm
-- name    : BaconThesis_Stability_IsBlockForm
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:58:56.512686+00:00
-- url     : https://prove2.me/theorems/3c8c4aa0-43c5-4aea-864d-1780fed82a8b
-- title:
--   Operators of the reducible block form $\bigoplus_J I_{n_J}\otimes S_{d_J}$
-- statement:
--   In the block basis $|J,\lambda,m\rangle$ of `blockOp`, a system operator $A$ **has block form** when
--   $$
--   A=\bigoplus_{J\in\mathcal J} I_{n_J}\otimes S_{d_J}
--   $$
--   for some family of $d_J\times d_J$ matrices $S_{d_J}$: it does not act on the degeneracy index $\lambda$ and does not mix different blocks.
--
--   Every operator of the operator-sum-representation (OSR) algebra of a decoherence-free evolution has this form in the basis given by the representation theorem for $\dagger$-closed algebras (Theorem 5.4.1); in the stability analysis it is the hypothesis on the system operators of the unperturbed coupling.
--
--   **Formalization Note** The block structure (sizes $n_J$, $d_J$ and the basis) is given as data rather than derived from an algebra; `IsBlockForm n d A` says $A$ equals `blockOp n d X` for some `X`.
-- source:
--   Bacon, Decoherence, Control, and Symmetry in Quantum Computers, arXiv:quant-ph/0305025v1, §5.4.1, eq. (5.31), p.78 (PDF p.95); eq. (6.21), p.91 (PDF p.108)

import Mathlib
import Definitions.Def_BaconThesis_Stability_blockOp

namespace BaconThesis.Stability

/-- **Operators of the reducible block form `⊕_J I_{n_J} ⊗ S_{d_J}`.**
Bacon, *Decoherence, Control, and Symmetry in Quantum Computers*, arXiv:quant-ph/0305025v1,
§5.4.1, eq. (5.31), p.78 (PDF p.95), and eq. (6.21), p.91 (PDF p.108): "there is a basis such
that the operation of every operator `S` in a †-closed complex associative algebra acts on the
Hilbert space as `S = ⊕_{J∈𝒥} I_{n_J} ⊗ S_{d_J}`".

`IsBlockForm n d A` holds when the system operator `A` equals `⊕_J I_{n_J} ⊗ X_J` for some family
of `d_J × d_J` matrices `X_J`, i.e. `A = blockOp n d X`.

**Formalization Note.** The block structure (the sizes `n J`, `d J` and the basis) is given as
data; the book obtains it from Theorem 5.4.1 applied to the OSR algebra. Every operator of that
algebra has this form, which is all the stability analysis of §6.2 uses. -/
def IsBlockForm {𝒥 : Type} [DecidableEq 𝒥] (n d : 𝒥 → ℕ)
    (A : Matrix (Σ J : 𝒥, Fin (n J) × Fin (d J)) (Σ J : 𝒥, Fin (n J) × Fin (d J)) ℂ) : Prop :=
  ∃ X : ∀ J, Matrix (Fin (d J)) (Fin (d J)) ℂ, A = blockOp n d X

end BaconThesis.Stability


