-- Prove2me | Definitions.Def_QThermalClassical_Supplement_thm37Coeff
-- name    : QThermalClassical_Supplement_thm37Coeff
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:38:47.985881+00:00
-- url     : https://prove2.me/theorems/c99a27cd-ed3c-41e1-81eb-f9d95ad0cdc8
-- title:
--   The Hamiltonian $-h\sum_iZ_i-(g/w(n))\prod_iX_i$ of Theorem 37
-- statement:
--   On $n$ qubits, the Pauli Hamiltonian (433)
--   $$
--   H_n=-h\sum_{i=1}^nZ_i-\frac{g}{w(n)}\prod_{i=1}^nX_i ,
--   $$
--   with coefficient $-h$ on each single-qubit $Z_i$ and $-g/w(n)$ on the all-$X$ string.
--
--   **Formalization Note** At $n=0$ the all-$X$ string is the empty (identity) word, a case Theorem 37 does not use.
-- source:
--   J. Cotler, H. Putterman, A. Zlokapa, When quantum thermal states look classical, arXiv:2607.28536 (held version, sha256 7491d0b2…), Theorem 37, eq. (433), p.88

import Mathlib
import Definitions.Def_QThermalClassical_pauliOp

set_option autoImplicit false

namespace QThermalClassical.Supplement

/-- The coefficient function of the Hamiltonian (433) of Theorem 37 on `n` qubits,
`H = −h Σ_i Z_i − (g / w(n)) Π_i X_i`: coefficient `−h` on each single-site word `Z_i` and
`−g / w(n)` on the all-`X` word `X^{⊗n}`.

Source: J. Cotler, H. Putterman, A. Zlokapa, *When quantum thermal states look classical*,
arXiv:2607.28536 (held version, sha256 7491d0b2…), Theorem 37, eq. (433), p.88.

**Formalization Note.** For `n ≥ 1` the words `Z_i` and `X^{⊗n}` are distinct and none is the
identity; at `n = 0` the all-`X` word is the empty (identity) word, a case Theorem 37 does not
use. -/
noncomputable def thm37Coeff (n : ℕ) (h g : ℝ) (w : ℕ → ℝ) : PauliWord (Fin n) → ℝ :=
  fun P => (∑ i : Fin n, if P = (fun j => if j = i then 3 else 0) then -h else 0) +
    if P = (fun _ => 1) then -(g / w n) else 0

end QThermalClassical.Supplement


