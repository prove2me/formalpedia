-- Prove2me | Definitions.Def_TwoFoldOPI_regEmbed
-- name    : TwoFoldOPI_regEmbed
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:45:41.163127+00:00
-- url     : https://prove2.me/theorems/695ff37a-8841-4701-940b-395c54503de3
-- title:
--   A state of $M$ symbols on qubits, with clean ancillas
-- statement:
--   For a vector $\varphi=\sum_x\varphi(x)|x\rangle$ on $K^M$ and $w\ge0$, the state
--   $$\sum_{x\in K^M}\varphi(x)\,|\mathrm{bits}(x)\rangle\otimes|0^w\rangle$$
--   on $M\cdot b+w$ qubits, where $\mathrm{bits}(x)$ is the layout `wordBits`. It is how the decoder input $X^c\mathrm{QFT}^\dagger|\psi\rangle$ and a target state $|\psi_A\rangle$ are placed on a qubit register whose other wires are $|0\rangle$.
-- source:
--   Ragavan, Shutty, Quantum Algorithms for OPI Variants Beyond Locality and Classical Decodability, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §5.2, Computational conventions and Definition 5.25, p. 26

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_TwoFoldOPI_wordBits

namespace TwoFoldOPI

/-- **A state of `M` field symbols on qubits, followed by clean ancillas.**
Ragavan, Shutty, *Quantum Algorithms for OPI Variants Beyond Locality and Classical
Decodability*, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §5.2, "Computational conventions", p.26, and Definition 5.25, p.26 (the decoder's input
state, "X^c |ψ_err⟩").

For `φ = Σ_x φ(x)|x⟩` on `K^M`, the state `Σ_x φ(x) |wordBits x⟩ ⊗ |0^w⟩` on `M·b + w`
qubits.

**Formalization Note.** Symbols are laid out by `wordBits`; the `w` remaining wires are `|0⟩`. -/
noncomputable def regEmbed (F : AvgCaseTI.FieldPres) (M w : ℕ)
    (φ : EuclideanSpace ℂ (Fin M → F.F)) :
    EuclideanSpace ℂ (QAlgorithms.Qubits (M * bitsPerSymbol F + w)) :=
  ∑ x, φ x • QAlgorithms.ket (Fin.append (wordBits F M x) (fun _ : Fin w => false))

end TwoFoldOPI


