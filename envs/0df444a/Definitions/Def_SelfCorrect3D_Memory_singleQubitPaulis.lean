-- Prove2me | Definitions.Def_SelfCorrect3D_Memory_singleQubitPaulis
-- name    : SelfCorrect3D_Memory_singleQubitPaulis
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:32:36.717096+00:00
-- url     : https://prove2.me/theorems/3e177f54-0f2f-418d-a5cf-95ab10189a7e
-- title:
--   Single-qubit Pauli operators $\{X_q,Y_q,Z_q\}$
-- statement:
--   The set of **single-qubit Pauli operators** on $n$ qubits is
--
--   $$\mathcal E=\{X_q,\;Y_q,\;Z_q : q=1,\dots,n\},$$
--
--   where $X_q=X^{e_q}$, $Z_q=Z^{e_q}$ ($e_q$ the $q$-th unit vector) and $Y_q=iX_qZ_q$. This is the set of errors against which the paper's analysis protects the logical qubit (footnote 7: "We restrict our analysis to single-site Pauli jump operators").
-- source:
--   Balasubramanian, Davydova, Lin, A passive self-correcting quantum memory in three dimensions, arXiv:2605.10943, §2.5, p. 21 and footnote 7

import Mathlib
import Definitions.Def_SelfCorrect3D_Memory_pauliX
import Definitions.Def_SelfCorrect3D_Memory_pauliZ

namespace SelfCorrect3D.Memory

/-- **The single-qubit Pauli operators** `{X_q, Y_q, Z_q : q}`. Balasubramanian, Davydova, Lin, *A passive self-correcting quantum memory in three dimensions*, arXiv:2605.10943,
§2.5, p. 21 and footnote 7 ("We restrict our analysis to single-site Pauli jump operators"); this is
the error set `𝓔` of the paper's analysis.

**Formalization Note.** `X_q = X^{e_q}`, `Z_q = Z^{e_q}` with `e_q = Pi.single q 1`, and
`Y_q = i X_q Z_q` (the Hermitian Pauli `Y` on qubit `q`). -/
def singleQubitPaulis (n : ℕ) : Set (Op n) :=
  {P | ∃ q : Fin n, P = pauliX (Pi.single q 1) ∨ P = pauliZ (Pi.single q 1) ∨
    P = Complex.I • (pauliX (Pi.single q 1) * pauliZ (Pi.single q 1))}

end SelfCorrect3D.Memory


