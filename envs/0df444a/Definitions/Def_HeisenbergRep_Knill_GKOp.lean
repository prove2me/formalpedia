-- Prove2me | Definitions.Def_HeisenbergRep_Knill_GKOp
-- name    : HeisenbergRep_Knill_GKOp
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T16:01:09.225218+00:00
-- url     : https://prove2.me/theorems/d836246a-95a2-47ff-acee-87f76f9c9194
-- title:
--   Operations of a Knill computer: Clifford gates and signed Pauli measurements, with their bit code
-- statement:
--   An operation of an $n$-qubit computer in Knill's theorem is one of
--
--   1. **a Clifford gate** $U$: any unitary $U$ in the Clifford group $\mathcal C=N(\mathcal P)$, the normalizer of the Pauli group $\mathcal P$ in $U(2^n)$, i.e. $U\mathcal PU^\dagger=\mathcal P$;
--   2. **a Pauli measurement** of $A=\pm P_1\otimes\cdots\otimes P_n$, a Pauli operator with overall phase $+1$ or $-1$ (the Hermitian elements of $\mathcal P$). It performs $P_\pm=\tfrac12(I\pm A)$ according to the result $\pm1$ (Eq. (35)).
--
--   The **code** of a controller's answer is a bit string: halting is $0$; a Clifford gate $U$ is $10$ followed, for each qubit $q=0,\dots,n-1$, by the codes of the Pauli operators $UX_qU^\dagger$ and $UZ_qU^\dagger$ ($2n(2n+2)$ bits); a measurement of $A$ is $11$ followed by the code of $A$ ($2n+2$ bits, sign included).
--
--   The images of $X_1,\dots,X_n,Z_1,\dots,Z_n$ determine $N\mapsto UNU^\dagger$ on all operators (Eq. (6)), hence $U$ up to a global phase, which no measurement detects.
--
--   **Formalization Note** Gates are all elements of $N(\mathcal P)$ (`QAlgorithms.Clifford.normalizer n`), not only the generators $R$, $P$, CNOT. Measured operators have phase exponent $0$ or $2$: for phase $\pm i$ the operators $\tfrac12(I\pm A)$ are not projectors. The global phase of a gate is not part of its code.
-- source:
--   Gottesman, The Heisenberg Representation of Quantum Computers, arXiv:quant-ph/9807006v1, §3, p. 4 (Clifford group = normalizer of P in U(2^n)); §7, Eq. (35), p. 15; §8, Theorem 1, p. 19

import Mathlib
import Definitions.Def_QAlgorithms_Defs_ProjectiveCliffords
import Definitions.Def_HeisenbergRep_Knill_singlePauli
import Definitions.Def_HeisenbergRep_Knill_cliffordImage
import Definitions.Def_HeisenbergRep_Knill_encPauliString

namespace HeisenbergRep.Knill

open QAlgorithms QAlgorithms.Stabilizer QAlgorithms.Complexity

/-- **The operations of a Knill computer: a Clifford group gate, or the measurement of a Pauli
group operator.**
Gottesman, *The Heisenberg Representation of Quantum Computers*, arXiv:quant-ph/9807006v1, §8,
Theorem 1 (Knill's theorem), p. 19: "Any quantum computer performing only: a) Clifford group gates,
b) measurements of Pauli group operators, and c) Clifford group operations conditioned on classical
bits"; the Clifford group is "the normalizer of `P` in `U(2^n)`" (§3, p. 4), and a measurement of
`A ∈ P` "performs one of the operators `P± = ½(I ± A)`" (§7, Eq. (35), p. 15).

An operation on `n` qubits is
1. `clifford U hU`: the gate `U`, any unitary `U` in the Clifford group
   `N(P) = QAlgorithms.Clifford.normalizer n` (the normalizer of the Pauli group in `U(2^n)`); or
2. `measure A hA`: the measurement of the Pauli operator `A` (a Pauli string, with its sign),
   whose phase is `+1` or `−1`.

**Formalization Note.** (a) Gates are *all* elements of `N(P)`, not only the generators `R`, `P`,
`CNOT` of Table 1 (Reading R3). (b) Measured operators are the Hermitian elements `±P` of the Pauli
group (`A.phase = 0` or `2`, Reading R4): for phase `±i` the operators `½(I ± A)` are not
projectors and `A` has imaginary eigenvalues (p. 9), so there is no measurement of them. The sign is
kept: measuring `−X ⊗ X` is allowed. -/
inductive GKOp (n : ℕ) where
  /-- Apply a Clifford group gate `U ∈ N(P)`. -/
  | clifford (U : Matrix.unitaryGroup (Qubits n) ℂ) (hU : U ∈ Clifford.normalizer n)
  /-- Measure the Hermitian Pauli operator `A = ±P` (phase exponent `0` or `2`). -/
  | measure (A : PauliString n) (hA : A.phase = 0 ∨ A.phase = 2)

/-- The bit code of the controller's answer (an operation, or `none` = halt).

* `none` (halt) ↦ `0`;
* `clifford U` ↦ `10`, then for each wire `q = 0, …, n − 1` the codes (`encPauliString`) of the
  Pauli strings `U X_q U†` and `U Z_q U†` (`cliffordImage`): `2n` signed Pauli strings,
  `2n (2n + 2)` bits. These images determine the conjugation `N ↦ U N U†` on the whole Pauli group
  (Eq. (6), p. 4: "we can deduce the behavior of any element of the Pauli group by just following
  the evolution of a generating set … `{X_1, …, X_n, Z_1, …, Z_n}`"), hence `U` up to a global
  phase, which no measurement detects;
* `measure A` ↦ `11`, then `encPauliString A` (`2n + 2` bits, the sign included).

**Formalization Note.** The global phase of a Clifford gate is not encoded (Reading R3). -/
noncomputable def GKOp.code {n : ℕ} : Option (GKOp n) → Str
  | none => [false]
  | some (.clifford U _) => [true, false] ++ (List.ofFn fun q : Fin n =>
      encPauliString (cliffordImage (U : Matrix (Qubits n) (Qubits n) ℂ) (singlePauli q .X)) ++
        encPauliString (cliffordImage (U : Matrix (Qubits n) (Qubits n) ℂ) (singlePauli q .Z))).flatten
  | some (.measure A _) => [true, true] ++ encPauliString A

end HeisenbergRep.Knill


