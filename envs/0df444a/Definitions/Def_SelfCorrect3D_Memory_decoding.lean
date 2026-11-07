-- Prove2me | Definitions.Def_SelfCorrect3D_Memory_decoding
-- name    : SelfCorrect3D_Memory_decoding
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:36:02.976264+00:00
-- url     : https://prove2.me/theorems/5894fd73-fe37-4ed4-8558-dd1101e6eca8
-- title:
--   Logical decoding $\mathrm{Dec}(\rho)=\mathrm{Tr}_{\mathcal H_{\mathrm{syn}}}\rho$
-- statement:
--   Given a memory frame, the **logical decoding map** is the partial trace over the syndrome register,
--
--   $$\mathrm{Dec}(\rho)=\sum_\sigma\bigl(\mathcal O(\sigma)V\bigr)^\dagger\,\rho\,\bigl(\mathcal O(\sigma)V\bigr),$$
--
--   the sum over achievable syndromes $\sigma=(\sigma_Z,\sigma_X)$. It "extracts the state of the encoded qubit".
-- source:
--   Balasubramanian, Davydova, Lin, A passive self-correcting quantum memory in three dimensions, arXiv:2605.10943, p. 21 (after eq. (49))

import Mathlib
import Definitions.Def_SelfCorrect3D_Memory_MemoryFrame
open Matrix

namespace SelfCorrect3D.Memory

/-- **Logical decoding map** `Dec(ρ) = Tr_{𝓗_syn}(ρ)`. Balasubramanian, Davydova, Lin, *A passive self-correcting quantum memory in three dimensions*, arXiv:2605.10943, p. 21
("The logical decoding map Dec(ρ) = Tr_{𝓗syn}(ρ) extracts the state of the encoded qubit"). In
the factorization `|a⟩ ⊗ |σ⟩ ↦ O(σ) V |a⟩`: `Dec(ρ) = Σ_σ (O(σ)V)† ρ (O(σ)V)`, the sum over
achievable syndromes.

**Formalization Note.** Defined on all operators `ρ` (linear). -/
noncomputable def decoding {n mX mZ : ℕ} (C : CSSCode n mX mZ) (F : MemoryFrame C) (ρ : Op n) :
    Matrix (ZMod 2) (ZMod 2) ℂ :=
  ∑ σZ ∈ C.achX, ∑ σX ∈ C.achZ,
    (pauliX (F.fX σX) * pauliZ (F.fZ σZ) * F.V)ᴴ * ρ * (pauliX (F.fX σX) * pauliZ (F.fZ σZ) * F.V)

end SelfCorrect3D.Memory


