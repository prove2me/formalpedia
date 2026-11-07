-- Prove2me | Definitions.Def_SelfCorrect3D_Memory_pauliX
-- name    : SelfCorrect3D_Memory_pauliX
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:31:29.821316+00:00
-- url     : https://prove2.me/theorems/46d778b6-7450-48ef-b4be-db8e061f68fa
-- title:
--   $X$-type Pauli string $X^v$
-- statement:
--   For $v\in\mathbb F_2^n$, the **$X$-type Pauli string** $X^v$ is the tensor product of Pauli $X$ on the qubits where $v_i=1$ and the identity elsewhere:
--
--   $$X^v|y\rangle=|y+v\rangle\qquad(y\in\mathbb F_2^n).$$
--
--   The decoder's $X$-type corrections $\mathcal O_X(\sigma_X)=X^{f_X(\sigma_X)}$, the $X$-type stabilizers and the logical $X_L$ are of this form.
-- source:
--   Balasubramanian, Davydova, Lin, A passive self-correcting quantum memory in three dimensions, arXiv:2605.10943, §2.1, p. 10; Definition 2.3, p. 20

import Mathlib
import Definitions.Def_SelfCorrect3D_Memory_Op

namespace SelfCorrect3D.Memory

/-- **X-type Pauli string `X^v`.** Balasubramanian, Davydova, Lin, *A passive self-correcting quantum memory in three dimensions*, arXiv:2605.10943, §2.1, p. 10 and
Definition 2.3, p. 20 (`O_X(σ_X) = X^{f_X(σ_X)}`): the tensor product of Pauli `X` on the qubits
where `v` is `1`, so `X^v |y⟩ = |y + v⟩`.

**Formalization Note.** Entry `(x, y)` is `1` if `x = y + v` and `0` otherwise. -/
def pauliX {n : ℕ} (v : Fin n → ZMod 2) : Op n :=
  Matrix.of fun x y => if x = y + v then 1 else 0

end SelfCorrect3D.Memory


