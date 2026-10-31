-- Prove2me | Definitions.Def_MayersBC_bb84State
-- name    : MayersBC_bb84State
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T15:56:45.082346+00:00
-- url     : https://prove2.me/theorems/fbb1652b-2c68-4eba-a27d-f90015d06712
-- title:
--   Product BB84 state $|c\rangle_\theta$ of $n$ photons
-- statement:
--   For a basis string $\theta \in \{+,\times\}^n$ and a bit string $c \in \{0,1\}^n$, the $n$ photons sent by Alice are in the product state
--
--   $$
--   |c\rangle_\theta = |c_1\rangle_{\theta_1} \otimes \cdots \otimes |c_n\rangle_{\theta_n},
--   $$
--
--   a unit vector of the $2^n$-dimensional photon space with computational basis $\{|x\rangle : x \in \{0,1\}^n\}$; its amplitude at $|x\rangle$ is $\prod_i \langle x_i \mid c_i\rangle_{\theta_i}$.
--
--   This is the pure state of step 4 of the BCJL commitment, and the state on which Bob's side collapses when Alice's measurement returns $(\theta, c)$.
--
--   **Formalization Note** The photon space is indexed by functions $\{1,\dots,n\} \to \mathbb Z/2$.
-- source:
--   Mayers, The Trouble with Quantum Bit Commitment, arXiv:quant-ph/9603015v3, section b, p.3 (COMMIT step 4)

import Mathlib
import Definitions.Def_MayersBC_bb84Amp

namespace MayersBC

/-- Mayers, arXiv:quant-ph/9603015v3, section b, p.3, step 4 of COMMIT: the product state
`|c⟩_θ = |c_1⟩_{θ_1} ⊗ … ⊗ |c_n⟩_{θ_n}` of the `n` photons, as a vector indexed by the
computational basis `{0, 1}^n`: `⟨x | c⟩_θ = Π_i ⟨x_i | c_i⟩_{θ_i}`.

**Formalization Note.** The photon space is `EuclideanSpace ℂ (Fin n → ZMod 2)`; the amplitudes
are `bb84Amp`. -/
noncomputable def bb84State {n : ℕ} (θ : Fin n → Bool) (c : Fin n → ZMod 2) :
    EuclideanSpace ℂ (Fin n → ZMod 2) :=
  WithLp.toLp 2 (fun x => ∏ i, bb84Amp (θ i) (c i) (x i))

end MayersBC


