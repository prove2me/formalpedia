-- Prove2me | Definitions.Def_QStateSearch_Supplement_QCircuit
-- name    : QStateSearch_Supplement_QCircuit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:07:05.423196+00:00
-- url     : https://prove2.me/theorems/268d9b08-ea8c-4ee7-b351-b8a573c418da
-- title:
--   Explicit quantum oracle circuits
-- statement:
--   An explicit quantum circuit consists of a number of wires, a number of input wires (the first ones; all other wires start in $|0\rangle$), a list of gates applied in order, and an output wire measured in the computational basis at the end, outcome $1$ meaning accept.
--
--   Private measurements are deferred to the end, so a circuit is a gate sequence followed by one measurement; the classical oracle calls keep their measurement through fresh ancillas.
-- source:
--   Barhoush, Quantum State Search with Classical Interactive Advice, arXiv:2610.25657 (held version, sha256 2a16939a…3408), Section 2, p.8; Section 2.2, p.10; Section 6.1, p.16

import Mathlib
import Definitions.Def_QStateSearch_Supplement_QGate

set_option autoImplicit false

namespace QStateSearch.Supplement

/-- An explicit quantum circuit: `wires` qubits, of which the first `inputs` carry the input
(all others start in `|0⟩`), a list of gates applied in order, and the wire `output` measured in
the computational basis at the end (`1` = accept).

Barhoush, *Quantum State Search with Classical Interactive Advice*, arXiv:2610.25657
(held version, sha256 2a16939a…3408), Section 2, p.8 ("A QPT algorithm means a uniform polynomial-time quantum oracle
algorithm"); Section 6.1, p.16 ("explicit descriptions over a fixed finite universal gate set").

**Formalization Note.** Private measurements are deferred, so a circuit is a sequence of gates
followed by one measurement; the classical calls to a Boolean oracle keep their measurement
explicitly through fresh ancillas (`QGate.cquery`). Well-formedness is `QCircuit.Valid`. -/
structure QCircuit where
  inputs : ℕ
  wires : ℕ
  output : ℕ
  gates : List QGate
  deriving DecidableEq

end QStateSearch.Supplement


