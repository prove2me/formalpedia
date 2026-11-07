-- Prove2me | Definitions.Def_SelfCorrect3D_Memory_encoding
-- name    : SelfCorrect3D_Memory_encoding
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:36:03.489815+00:00
-- url     : https://prove2.me/theorems/7f385099-97b8-4e67-a564-9eb0ca832910
-- title:
--   Thermal encoding $\mathrm{Enc}_\beta(\tau)=\tau\otimes e^{-\beta H'}/\mathrm{Tr}\,e^{-\beta H'}$
-- statement:
--   Given a memory frame and $\beta\in\mathbb R$, the **thermal encoding** of a single-qubit operator $\tau$ is
--
--   $$\mathrm{Enc}_\beta(\tau)=\sum_{\sigma}\frac{e^{-\beta|\sigma|}}{Z}\,\bigl(\mathcal O(\sigma)V\bigr)\,\tau\,\bigl(\mathcal O(\sigma)V\bigr)^\dagger,\qquad Z=\sum_\sigma e^{-\beta|\sigma|},$$
--
--   where $\sigma=(\sigma_Z,\sigma_X)$ runs over the achievable syndromes, $|\sigma|=|\sigma_Z|+|\sigma_X|$ is the Hamming weight and $\mathcal O(\sigma)=\mathcal O_X(\sigma_X)\mathcal O_Z(\sigma_Z)$. In the factorization $\mathcal H_S=\mathcal H_{\log}\otimes\mathcal H_{\mathrm{syn}}$ this is $\tau\otimes e^{-\beta H'}/\mathrm{Tr}\,e^{-\beta H'}$, eq. (49), with $H'$ the syndrome weight.
--
--   **Formalization Note** Defined on all $2\times2$ matrices (it is linear); the frame fixes the factorization.
-- source:
--   Balasubramanian, Davydova, Lin, A passive self-correcting quantum memory in three dimensions, arXiv:2605.10943, eq. (49), p. 21; p. 4

import Mathlib
import Definitions.Def_SelfCorrect3D_Memory_MemoryFrame
open Matrix

namespace SelfCorrect3D.Memory

/-- **Thermal encoding map** `Enc_β(τ) = τ ⊗ e^{−βH′}/Tr(e^{−βH′})`. Balasubramanian, Davydova, Lin, *A passive self-correcting quantum memory in three dimensions*, arXiv:2605.10943,
eq. (49), p. 21, and p. 4 ("The encoding that we choose is a thermal encoding"). In the
factorization `𝓗_S = 𝓗_log ⊗ 𝓗_syn`, `|a⟩ ⊗ |σ⟩ ↦ O(σ) V |a⟩` with
`O(σ) = O_X(σ_X) O_Z(σ_Z)`, and `H′` diagonal with entry `|σ| = |σ_Z| + |σ_X|` (p. 21):
`Enc_β(τ) = Σ_σ w_σ (O(σ)V) τ (O(σ)V)†`, `w_σ = e^{−β|σ|}/Z`, `Z = Σ_σ e^{−β|σ|}`,
the sums over achievable syndromes `σ_Z ∈ im H_x`, `σ_X ∈ im H_z`.

**Formalization Note.** `|·|` is the Hamming weight. Defined on all `2 × 2` matrices `τ`
(linear in `τ`). The frame (logicals, decoder, `V`) is a parameter: the factorization is the one
induced by the decoder's corrections. -/
noncomputable def encoding {n mX mZ : ℕ} (C : CSSCode n mX mZ) (F : MemoryFrame C) (β : ℝ)
    (τ : Matrix (ZMod 2) (ZMod 2) ℂ) : Op n :=
  ∑ σZ ∈ C.achX, ∑ σX ∈ C.achZ,
    ((Real.exp (-β * (hammingNorm σZ + hammingNorm σX)) /
        ∑ σZ' ∈ C.achX, ∑ σX' ∈ C.achZ, Real.exp (-β * (hammingNorm σZ' + hammingNorm σX')) : ℝ) : ℂ) •
      ((pauliX (F.fX σX) * pauliZ (F.fZ σZ) * F.V) * τ *
        (pauliX (F.fX σX) * pauliZ (F.fZ σZ) * F.V)ᴴ)

end SelfCorrect3D.Memory


