-- Prove2me | Definitions.Def_HeisenbergRep_Knill_cliffordImage
-- name    : HeisenbergRep_Knill_cliffordImage
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:59:26.410061+00:00
-- url     : https://prove2.me/theorems/bd3ba51d-c975-462e-b3ad-c9974b1838e0
-- title:
--   The Pauli operator $UPU^\dagger$ (Clifford image of a Pauli string)
-- statement:
--   Let $U$ be a $2^n\times 2^n$ complex matrix and $P$ an $n$-qubit Pauli operator $i^c P_1\otimes\cdots\otimes P_n$ (phase included). The **image** $\mathrm{img}_U(P)$ is the Pauli operator $Q$, phase included, whose matrix is
--
--   $$Q=UPU^\dagger ,$$
--
--   when such a $Q$ exists; otherwise it is $P$ itself.
--
--   Applying $U$ to the computer transforms every operator $N$ into $UNU^\dagger$ (Eq. (2)). When $U$ belongs to the Clifford group $N(\mathcal P)$, this image of a Pauli operator is again a Pauli operator, so the first case always applies and the fallback is never used. Distinct Pauli strings have distinct matrices, so $Q$ is unique.
--
--   **Formalization Note** The choice uses `Classical.choose`; uniqueness of the representing string is what makes the result well defined (checked for $n=1$ in the mission's verification file).
-- source:
--   Gottesman, The Heisenberg Representation of Quantum Computers, arXiv:quant-ph/9807006v1, §2, Eq. (2), p. 3; §3, p. 4 (the Clifford group transforms Pauli operators into Pauli operators)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Stabilizer

namespace HeisenbergRep.Knill

open QAlgorithms QAlgorithms.Stabilizer

/-- **The Pauli string `U P U†`.**
Gottesman, *The Heisenberg Representation of Quantum Computers*, arXiv:quant-ph/9807006v1, §2,
Eq. (2), p. 3: "applying `U` to the computer transforms an arbitrary operation `N` by
`N → U N U†`"; §3, p. 4: the Clifford group consists of "the gates which transform elements of the
Pauli group into other elements of the Pauli group".

`cliffordImage U P` is the Pauli string `Q` (phase included) whose matrix equals `U · P · U†`, when
such a `Q` exists, and `P` itself otherwise.

**Formalization Note.** Distinct Pauli strings have distinct matrices (the off-diagonal pattern
determines which wires carry `X` or `Y`, the diagonal signs then determine `Z`/`Y` versus `I`/`X`
and the overall phase), so the chosen `Q` is the unique one; this is proved for `n = 1` in the
mission's verification file. For `U` in the Clifford group `N(P)` the existential always holds,
so the fallback branch `P` is never used for a Clifford gate. -/
noncomputable def cliffordImage {n : ℕ} (U : Matrix (Qubits n) (Qubits n) ℂ) (P : PauliString n) :
    PauliString n :=
  open Classical in
  if h : ∃ Q : PauliString n, Q.toMatrix = U * P.toMatrix * U.conjTranspose then Classical.choose h
  else P

end HeisenbergRep.Knill


