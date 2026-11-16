-- Prove2me | Definitions.Def_QStateSearch_Supplement_QCircuit_ArityAt
-- name    : QStateSearch_Supplement_QCircuit_ArityAt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:09:03.31685+00:00
-- url     : https://prove2.me/theorems/94cc01f2-d1a6-4da4-a5b8-b3d9a9ee4b43
-- title:
--   Length-respecting oracle access at length $n$
-- statement:
--   A circuit is **length-respecting at length $n$** if every quantum-oracle call acts on exactly $n$ qubits, i.e. addresses only the component $U_n$ of a quantum oracle $U=(U_1,U_2,\dots)$.
--
--   This is the convention of Aaronson and Kuperberg adopted on p.10: on input $0^n$ a machine queries only $U_n$. The diagonalization in the proof of Theorem 5 relies on it.
-- source:
--   Barhoush, Quantum State Search with Classical Interactive Advice, arXiv:2610.25657 (held version, sha256 2a16939a…3408), Section 2.3, p.10

import Mathlib
import Definitions.Def_QStateSearch_Supplement_QCircuit

set_option autoImplicit false

namespace QStateSearch.Supplement

/-- **Length-respecting** oracle access at length `n`: every quantum oracle call of `C` acts on
exactly `n` qubits, i.e. addresses the component `U_n` of an oracle `U = (U_1, U_2, …)`.

Barhoush, *Quantum State Search with Classical Interactive Advice*, arXiv:2610.25657
(held version, sha256 2a16939a…3408), Section 2.3, p.10: "We use the length-respecting convention of Aaronson and Kuperberg: on
input 0^n, a machine queries only U_n." -/
def QCircuit.ArityAt (C : QCircuit) (n : ℕ) : Prop :=
  ∀ lab c ws, QGate.oracle lab c ws ∈ C.gates → ws.length = n

end QStateSearch.Supplement


