-- Prove2me | Definitions.Def_QThermalClassical_pauliOp
-- name    : QThermalClassical_pauliOp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:10:56.800757+00:00
-- url     : https://prove2.me/theorems/41e441b4-2457-406f-b03c-a1fa776f7b0d
-- title:
--   Operators on qubits, Pauli words, tensor products and Pauli strings
-- statement:
--   A register of qubits is a finite set $Q$ (for $n$ qubits, $Q=[n]$); an operator on it is a complex matrix indexed by computational-basis strings $Q\to\{0,1\}$. A **Pauli word** assigns to each qubit one of $I, X, Y, Z$, and its **Pauli string** is the tensor product
--   $$
--   P=\bigotimes_{q\in Q}\sigma_{P(q)},\qquad \sigma_0=I,\ \sigma_1=X,\ \sigma_2=Y,\ \sigma_3=Z,
--   $$
--   with matrix entries $P_{a,b}=\prod_{q}(\sigma_{P(q)})_{a_q,b_q}$. The **support** $\mathrm{supp}(P)$ is the set of qubits where $P(q)\neq I$.
--
--   These objects carry every Hamiltonian, monomial and state of the mission.
--
--   **Formalization Note** The single-qubit matrices are the published `QAlgorithms.pauliX/Y/Z`; the tensor product of single-qubit operators is computed entrywise.
-- source:
--   J. Cotler, H. Putterman, A. Zlokapa, When quantum thermal states look classical, arXiv:2607.28536 (held version, sha256 7491d0b2…), §2.1, eq. (5), p.11

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Gates

set_option autoImplicit false

namespace QThermalClassical

/-- Operators on a finite register of qubits `Q`, as matrices indexed by computational-basis
strings `Q → Bool` (`false` is `|0⟩`).

Source: J. Cotler, H. Putterman, A. Zlokapa, *When quantum thermal states look classical*,
arXiv:2607.28536 (held version, sha256 7491d0b2…), §2.1, p.11.

**Formalization Note.** The qubits are any finite type `Q` (the paper's `[n]` is `Fin n`);
the Hilbert space `(ℂ²)^{⊗n}` is `(Q → Bool) → ℂ`. -/
abbrev Op (Q : Type) := Matrix (Q → Bool) (Q → Bool) ℂ

/-- A Pauli word on `Q`: at each qubit one of `0, 1, 2, 3`, standing for `I, X, Y, Z`
(arXiv:2607.28536, §2.1, p.11, "Pauli string"). -/
abbrev PauliWord (Q : Type) := Q → Fin 4

/-- The single-qubit Pauli matrix with index `0, 1, 2, 3 ↦ I, X, Y, Z`, using the published
matrices `QAlgorithms.pauliX/Y/Z`. -/
def pauli1 (a : Fin 4) : Matrix Bool Bool ℂ :=
  if a = 0 then 1 else if a = 1 then QAlgorithms.pauliX
  else if a = 2 then QAlgorithms.pauliY else QAlgorithms.pauliZ

/-- The tensor product `⊗_q M_q` of single-qubit operators, entrywise in the computational
basis: `(⊗_q M_q)_{a,b} = ∏_q (M_q)_{a_q, b_q}`. -/
def tensorOp {Q : Type} [Fintype Q] (M : Q → Matrix Bool Bool ℂ) : Op Q :=
  Matrix.of fun a b => ∏ q, M q (a q) (b q)

/-- The support `supp(P) ⊆ Q` of a Pauli word: the qubits on which it acts nontrivially
(arXiv:2607.28536, §2.1, p.11). -/
def pauliSupport {Q : Type} [Fintype Q] (P : PauliWord Q) : Finset Q :=
  Finset.univ.filter fun q => P q ≠ 0

/-- The Pauli string `P = ⊗_q σ_{P(q)}` of a Pauli word, as an operator on `Q`
(arXiv:2607.28536, §2.1, p.11). -/
def pauliOp {Q : Type} [Fintype Q] (P : PauliWord Q) : Op Q :=
  tensorOp fun q => pauli1 (P q)

end QThermalClassical


