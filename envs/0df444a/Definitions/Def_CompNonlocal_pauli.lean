-- Prove2me | Definitions.Def_CompNonlocal_pauli
-- name    : CompNonlocal_pauli
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:38:47.842327+00:00
-- url     : https://prove2.me/theorems/98cd0be1-13e6-48a7-9608-cc4912d5b79a
-- title:
--   The Pauli matrices $\sigma_x,\sigma_y,\sigma_z$
-- statement:
--   The Pauli matrices
--   $$\sigma_1=\sigma_x=\begin{pmatrix}0&1\\1&0\end{pmatrix},\quad \sigma_2=\sigma_y=\begin{pmatrix}0&-i\\ i&0\end{pmatrix},\quad \sigma_3=\sigma_z=\begin{pmatrix}1&0\\0&-1\end{pmatrix}$$
--   in the computational basis $(|0\rangle,|1\rangle)$ of a qubit.
--
--   **Formalization Note** A qubit basis is indexed by `Bool` with `false` $=|0\rangle$; the index $j\in\{1,2,3\}$ is $j\in\{0,1,2\}$.
-- source:
--   Głuch, Morimae, From Computational Nonlocality to Public-Key Encryption and Commitments, manuscript (STOC 2027 submission, sha256 e245edd7…), §4.1, p.18

import Mathlib

set_option autoImplicit false

namespace CompNonlocal

/-- The Pauli matrices `(σ₁, σ₂, σ₃) = (σ_x, σ_y, σ_z)`. Głuch, Morimae, *From Computational Nonlocality to Public-Key Encryption and Commitments*, manuscript (STOC 2027 submission, sha256 e245edd7…), §4.1, p.18:
"σx = (0 1; 1 0), σy = (0 −i; i 0), σz = (1 0; 0 −1)", and "(σ1, σ2, σ3) = (σx, σy, σz)".

**Formalization Note** A qubit is indexed by `Bool` with `false = |0⟩` and `true = |1⟩`, so the
row/column order is `(false, true)`; the paper's index `j ∈ {1, 2, 3}` is `j ∈ Fin 3 = {0, 1, 2}`. -/
def pauli : Fin 3 → Matrix Bool Bool ℂ :=
  ![Matrix.of fun a b => if a = b then 0 else 1,
    Matrix.of fun a b => if a = b then 0 else if a then Complex.I else -Complex.I,
    Matrix.of fun a b => if a = b then (if a then -1 else 1) else 0]

end CompNonlocal


