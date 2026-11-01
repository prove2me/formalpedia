-- Prove2me | Definitions.Def_BaconThesis_Stability_upsilon
-- name    : BaconThesis_Stability_upsilon
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:58:12.656231+00:00
-- url     : https://prove2.me/theorems/e3f08626-a64e-4675-a141-28fb3240191b
-- title:
--   The subsystem trace $\Upsilon_J[X]=\sum_m\langle J,m|X|J,m\rangle$
-- statement:
--   For a block $J$ and an operator $X$ on the full system space, $\Upsilon_J[X]$ is the $n_J\times n_J$ matrix
--   $$
--   \big(\Upsilon_J[X]\big)_{\lambda\lambda'}=\sum_{m=1}^{d_J}\langle J,\lambda,m|\,X\,|J,\lambda',m\rangle .
--   $$
--   It restricts $X$ to block $J$, viewed as $\mathbb C^{n_J}\otimes\mathbb C^{d_J}$, and traces out the second factor, producing an operator on the degeneracy of block $J$ alone.
--
--   $\Upsilon_J$ extracts the encoded information from a state of the full system; the decoherence rates of a decoherence-free subsystem are defined through it.
--
--   **Formalization Note** Written as `WildeQIT.partialTraceRight` of the restriction of $X$ to the block $J\cong\mathrm{Fin}\,n_J\times\mathrm{Fin}\,d_J$.
-- source:
--   Bacon, Decoherence, Control, and Symmetry in Quantum Computers, arXiv:quant-ph/0305025v1, §5.4.1, eq. (5.33), p.78 (PDF p.95); eq. (6.16), p.90 (PDF p.107)

import Mathlib
import Definitions.Def_WildeQIT_partialTrace

namespace BaconThesis.Stability

/-- **The subsystem trace `Υ_J[X] = Σ_m ⟨J, m| X |J, m⟩`.**
Bacon, *Decoherence, Control, and Symmetry in Quantum Computers*, arXiv:quant-ph/0305025v1,
§5.4.1, eq. (5.33), p.78 (PDF p.95), recalled as eq. (6.16), p.90 (PDF p.107): `Υ_J` "transforms
an operator `X` on the full Hilbert space to an operator which acts only on the degeneracy of the
`J`th irrep".

For a system operator `X`, `upsilon n d J X` is the `n_J × n_J` matrix with entries
`(Υ_J X)_{λλ'} = Σ_{m < d_J} ⟨J,λ,m| X |J,λ',m⟩`: restrict `X` to the block `J` and take the
partial trace over the factor `m`.

**Formalization Note.** Written as `WildeQIT.partialTraceRight` (the partial trace over the second
Kronecker factor) of the restriction `X.submatrix (Sigma.mk J) (Sigma.mk J)` of `X` to the block
`J ≅ Fin (n J) × Fin (d J)`. -/
def upsilon {𝒥 : Type} (n d : 𝒥 → ℕ) (J : 𝒥)
    (X : Matrix (Σ K : 𝒥, Fin (n K) × Fin (d K)) (Σ K : 𝒥, Fin (n K) × Fin (d K)) ℂ) :
    Matrix (Fin (n J)) (Fin (n J)) ℂ :=
  WildeQIT.partialTraceRight
    (X.submatrix (fun x : Fin (n J) × Fin (d J) => (⟨J, x⟩ : Σ K : 𝒥, Fin (n K) × Fin (d K)))
      (fun x : Fin (n J) × Fin (d J) => (⟨J, x⟩ : Σ K : 𝒥, Fin (n K) × Fin (d K))))

end BaconThesis.Stability


