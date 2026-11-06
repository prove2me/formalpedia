-- Prove2me | Definitions.Def_AutoQMem_Lindblad_pauliAt
-- name    : AutoQMem_Lindblad_pauliAt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:54:33.477213+00:00
-- url     : https://prove2.me/theorems/29873ce3-4334-49a8-b602-cf98a9d461cd
-- title:
--   Single-qubit Pauli $P_i$ on qubit $i$
-- statement:
--   For a label $P\in\{I,X,Y,Z\}$ and a qubit $i$, $P_i$ is the single-qubit Pauli $P$ acting on qubit $i$ (and the identity elsewhere):
--   $$I_i=I,\qquad X_i=X^{\hat e_i},\qquad Z_i=Z^{\hat e_i},\qquad Y_i=iX_iZ_i,$$
--   where $\hat e_i$ is the $i$-th standard basis vector of $\mathbb F_2^n$.
--
--   These are the Pauli factors of the jump operators in Definition 2.22.
-- source:
--   Drechsler, Oreg, Aharonov, Autonomous Quantum Memories from Classical Stochastic Processes, arXiv:2610.05589 (PDF of 2026-11-03), §2.2.1, p. 20 (PDF p. 22); Appendix B, p. 65 (PDF p. 67)

import Mathlib
import Definitions.Def_AutoQMem_Lindblad_pauliX
import Definitions.Def_AutoQMem_Lindblad_pauliZ
import Definitions.Def_AutoQMem_Lindblad_Pauli1
open Matrix

namespace AutoQMem.Lindblad

/-- **The single-qubit Pauli `P_i` acting on qubit i.** Drechsler, Oreg, Aharonov, *Autonomous Quantum Memories from Classical Stochastic Processes*,
arXiv:2610.05589 (PDF of 2026-11-03), §2.2.1, p. 20 (PDF 22): "We write
P_i for the single-qubit operator P ∈ {I, X, Y, Z} acting on qubit i, with I_i = I".

**Formalization Note.** `X_i = X^{ê_i}`, `Z_i = Z^{ê_i}` (`ê_i = Pi.single i 1`) and
`Y_i = i X_i Z_i`, the paper's convention (Appendix B, proof of Lemma 4.4, p. 65, PDF 67). -/
noncomputable def pauliAt {n : ℕ} : Pauli1 → Fin n → Op n
  | .I, _ => 1
  | .X, i => pauliX (Pi.single i 1)
  | .Y, i => Complex.I • (pauliX (Pi.single i 1) * pauliZ (Pi.single i 1))
  | .Z, i => pauliZ (Pi.single i 1)

end AutoQMem.Lindblad


