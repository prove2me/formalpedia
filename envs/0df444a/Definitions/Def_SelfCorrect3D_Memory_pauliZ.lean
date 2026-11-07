-- Prove2me | Definitions.Def_SelfCorrect3D_Memory_pauliZ
-- name    : SelfCorrect3D_Memory_pauliZ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:31:32.331323+00:00
-- url     : https://prove2.me/theorems/b507a83e-4dbb-4f43-a580-c573e03a64ce
-- title:
--   $Z$-type Pauli string $Z^w$
-- statement:
--   For $w\in\mathbb F_2^n$, the **$Z$-type Pauli string** $Z^w$ is the tensor product of Pauli $Z$ on the qubits where $w_i=1$:
--
--   $$Z^w|y\rangle=(-1)^{w\cdot y}|y\rangle,$$
--
--   with $w\cdot y=\sum_i w_iy_i\in\mathbb F_2$. The decoder's $Z$-type corrections $\mathcal O_Z(\sigma_Z)=Z^{f_Z(\sigma_Z)}$, the $Z$-type stabilizers and the logical $Z_L$ are of this form.
-- source:
--   Balasubramanian, Davydova, Lin, A passive self-correcting quantum memory in three dimensions, arXiv:2605.10943, §2.1, p. 10; Definition 2.3, p. 20

import Mathlib
import Definitions.Def_SelfCorrect3D_Memory_Op

namespace SelfCorrect3D.Memory

/-- **Z-type Pauli string `Z^w`.** Balasubramanian, Davydova, Lin, *A passive self-correcting quantum memory in three dimensions*, arXiv:2605.10943, §2.1, p. 10 and
Definition 2.3, p. 20 (`O_Z(σ_Z) = Z^{f_Z(σ_Z)}`): the tensor product of Pauli `Z` on the qubits
where `w` is `1`, so `Z^w |y⟩ = (−1)^{w·y} |y⟩`.

**Formalization Note.** A diagonal matrix with entries `(−1)^{(w ⬝ᵥ y).val}`, the 𝔽₂ inner product
read as a natural number in `{0, 1}`. -/
def pauliZ {n : ℕ} (w : Fin n → ZMod 2) : Op n :=
  Matrix.diagonal fun y => (-1 : ℂ) ^ (w ⬝ᵥ y).val

end SelfCorrect3D.Memory


