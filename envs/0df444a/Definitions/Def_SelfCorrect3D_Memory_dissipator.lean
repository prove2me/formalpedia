-- Prove2me | Definitions.Def_SelfCorrect3D_Memory_dissipator
-- name    : SelfCorrect3D_Memory_dissipator
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:31:30.448602+00:00
-- url     : https://prove2.me/theorems/66fe814f-5ede-4487-8545-9196440643f8
-- title:
--   Lindbladian $\mathcal L(\rho)=\sum_i(S_i\rho S_i^\dagger-\tfrac12\{\rho,S_i^\dagger S_i\})$
-- statement:
--   For finitely many **jump operators** $S_1,\dots,S_m$ on $n$ qubits, the **Lindbladian** (dissipator) is
--
--   $$\mathcal L(\rho)=\sum_{i=1}^m\Bigl(S_i\rho S_i^\dagger-\tfrac12\{\rho,S_i^\dagger S_i\}\Bigr),$$
--
--   the dissipative part of the master equation (45).
--
--   **Formalization Note** Defined on all operators $\rho$ (it is linear). The Hamiltonian part $-i[H,\rho]$ is added separately in the generator.
-- source:
--   Balasubramanian, Davydova, Lin, A passive self-correcting quantum memory in three dimensions, arXiv:2605.10943, eq. (45), p. 19

import Mathlib
import Definitions.Def_SelfCorrect3D_Memory_Op
open Matrix

namespace SelfCorrect3D.Memory

/-- **The Lindbladian (dissipator) of a finite family of jump operators.** Balasubramanian, Davydova, Lin, *A passive self-correcting quantum memory in three dimensions*, arXiv:2605.10943,
eq. (45), p. 19: `𝓛(ρ) = Σ_i (S_i ρ S_i† − ½{ρ, S_i† S_i})`, "the last term is often called the
Lindbladian and written as 𝓛(ρ). The operators {S_i} are referred to as jump operators."

**Formalization Note.** Defined on all operators `ρ` (it is linear). The Hamiltonian part
`−i[H, ρ]` is not included; it is added in `generator`. -/
noncomputable def dissipator {n m : ℕ} (J : Fin m → Op n) (ρ : Op n) : Op n :=
  ∑ j, (J j * ρ * (J j)ᴴ - (1 / 2 : ℂ) • ((J j)ᴴ * J j * ρ + ρ * ((J j)ᴴ * J j)))

end SelfCorrect3D.Memory


