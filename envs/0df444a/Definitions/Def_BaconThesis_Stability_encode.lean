-- Prove2me | Definitions.Def_BaconThesis_Stability_encode
-- name    : BaconThesis_Stability_encode
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:58:09.046021+00:00
-- url     : https://prove2.me/theorems/798f8212-3336-4c06-8b27-7baf7709f27d
-- title:
--   Encoded state $\rho(0)=\sigma\otimes\rho_{d_J}$ in the degeneracy of block $J$
-- statement:
--   Fix a block $J$. For an $n_J\times n_J$ matrix $\sigma$ (the encoded information) and a $d_J\times d_J$ matrix $\rho_{d_J}$, the **encoded state** is the system operator
--   $$
--   \rho(0)=\sigma\otimes\rho_{d_J}\quad\text{on block }J,\qquad 0\ \text{on every other block}.
--   $$
--   For a pure input, $\sigma=|j\rangle\langle j|$ with $|j\rangle\in\mathbb C^{n_J}$ a unit vector, which is the book's $\rho(0)=|j\rangle\langle j|\otimes\rho_{d_J}$; for a mixed input, $\sigma=\sum_k p_k|j_k\rangle\langle j_k|$.
--
--   Information stored this way sits in the degeneracy of block $J$, which operators of block form do not touch; this is where a decoherence-free subsystem keeps its quantum information.
--
--   **Formalization Note** The state is `Matrix.blockDiagonal'` of the family that is `σ ⊗ₖ ρd` at `J` and zero elsewhere (`Pi.single`); the degeneracy factor comes first.
-- source:
--   Bacon, Decoherence, Control, and Symmetry in Quantum Computers, arXiv:quant-ph/0305025v1, §6.2, before eq. (6.15), p.90 (PDF p.107); eq. (6.27), p.92 (PDF p.109)

import Mathlib

open scoped Kronecker

namespace BaconThesis.Stability

/-- **State encoded into the degeneracy of the `J`th block: `ρ(0) = σ ⊗ ρ_{d_J}`.**
Bacon, *Decoherence, Control, and Symmetry in Quantum Computers*, arXiv:quant-ph/0305025v1,
§6.2, before eq. (6.15), p.90 (PDF p.107): "quantum information `|j⟩` is encoded into the
degeneracy of the `J`th irrep …: `Υ_J[ρ(0)] = |j⟩⟨j|`, or `ρ(0) = |j⟩⟨j| ⊗ ρ_{d_J}`", and the mixed
input states of eq. (6.27), p.92 (PDF p.109).

For an `n_J × n_J` matrix `σ` (the encoded information: `σ = |j⟩⟨j|` for a pure input, a density
matrix for a mixed one) and a `d_J × d_J` matrix `ρd`, `encode n d J σ ρd` is the system operator
which is `σ ⊗ ρd` on the block `J` and zero on every other block.

**Formalization Note.** The system index type is `Σ J : 𝒥, Fin (n J) × Fin (d J)` (see `blockOp`);
the operator is `Matrix.blockDiagonal'` of the family which is `σ ⊗ₖ ρd` at `J` and `0` elsewhere
(`Pi.single`). The degeneracy factor comes first in the Kronecker product. -/
def encode {𝒥 : Type} [DecidableEq 𝒥] (n d : 𝒥 → ℕ) (J : 𝒥)
    (σ : Matrix (Fin (n J)) (Fin (n J)) ℂ) (ρd : Matrix (Fin (d J)) (Fin (d J)) ℂ) :
    Matrix (Σ K : 𝒥, Fin (n K) × Fin (d K)) (Σ K : 𝒥, Fin (n K) × Fin (d K)) ℂ :=
  Matrix.blockDiagonal'
    (Pi.single (M := fun K => Matrix (Fin (n K) × Fin (d K)) (Fin (n K) × Fin (d K)) ℂ) J
      (σ ⊗ₖ ρd))

end BaconThesis.Stability


