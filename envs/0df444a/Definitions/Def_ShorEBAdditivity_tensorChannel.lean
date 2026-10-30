-- Prove2me | Definitions.Def_ShorEBAdditivity_tensorChannel
-- name    : ShorEBAdditivity_tensorChannel
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:18:01.020811+00:00
-- url     : https://prove2.me/theorems/17ddd902-0e44-416b-af48-ddb2f043ab35
-- title:
--   Tensor product $\Psi\otimes\Phi$ of two superoperators
-- statement:
--   Let $\Psi : M_A \to M_{A'}$ and $\Phi : M_B \to M_{B'}$ be maps between spaces of complex matrices indexed by finite sets. Their **tensor product** $\Psi\otimes\Phi : M_{A\times B} \to M_{A'\times B'}$ is defined on every operator $X$ on $\mathbb C^A \otimes \mathbb C^B$ (entangled inputs included) by expanding $X$ in matrix units,
--
--   $$
--   (\Psi\otimes\Phi)(X) = \sum_{i,j\in A}\ \sum_{k,l\in B} X_{(i,k),(j,l)}\; \Psi(E_{ij}) \otimes \Phi(E_{kl}),
--   $$
--
--   where $E_{ij}$ is the matrix with a single entry $1$ in position $(i,j)$. The map $\Psi$ acts on the first factor and $\Phi$ on the second.
--
--   For linear $\Psi$ and $\Phi$ (in particular for quantum channels) this is the unique linear map with $(\Psi\otimes\Phi)(X\otimes Y) = \Psi(X)\otimes\Phi(Y)$, so it is the channel $\Psi\otimes\Phi$ whose Holevo capacity the paper studies.
--
--   **Formalization Note** The body is copied from the public platform definition `QAlgorithms.Papers.Independent.Information100.P62.tensorChannel`, which is stated only for index types in universe 0; this copy allows arbitrary universes, so the main theorem can be stated for arbitrary finite types.
-- source:
--   Shor, Additivity of the Classical Capacity of Entanglement-Breaking Quantum Channels, arXiv:quant-ph/0201149v3, eq. (4), p.1 and Theorem 2, eq. (16), p.4 (the channel Ψ ⊗ Φ)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel

open QAlgorithms

namespace ShorEBAdditivity

/-- Shor, arXiv:quant-ph/0201149v3, eqs. (4), (16), pp.1, 4: the tensor product `Ψ ⊗ Φ` of two
superoperators `Ψ : M_A → M_{A'}` and `Φ : M_B → M_{B'}`, acting on every operator on
`A ⊗ B` (entangled inputs included) by the matrix-unit expansion
`(Ψ ⊗ Φ)(X) = Σ_{i,j,k,l} X_{(i,k),(j,l)} Ψ(E_ij) ⊗ Φ(E_kl)`.

**Formalization Note.** `Ψ` acts on the **first** factor `A` and `Φ` on the second factor `B`,
as in the paper's `Ψ ⊗ Φ`. For linear `Ψ`, `Φ` (channels) this is the unique linear map with
`(Ψ ⊗ Φ)(X ⊗ Y) = Ψ(X) ⊗ Φ(Y)`. The body is copied verbatim from the public platform definition
`QAlgorithms.Papers.Independent.Information100.P62.tensorChannel` (5e296929-…), which is stated
only for types in universe 0; this copy allows arbitrary universes. -/
noncomputable def tensorChannel {A A' B B' : Type*} [Fintype A] [DecidableEq A] [Fintype B]
    [DecidableEq B] (Ψ : Superop A A') (Φ : Superop B B') : Superop (A × B) (A' × B') :=
  fun X a b => ∑ i, ∑ j, ∑ k, ∑ l,
    X (i, k) (j, l) * Ψ (Matrix.single i j 1) a.1 b.1 * Φ (Matrix.single k l 1) a.2 b.2

end ShorEBAdditivity


