-- Prove2me | Definitions.Def_QStateSearch_Supplement_QCircuit_NoCQuery
-- name    : QStateSearch_Supplement_QCircuit_NoCQuery
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:08:24.448487+00:00
-- url     : https://prove2.me/theorems/77fb2f7d-dc81-4c7b-9e2e-663cb166b058
-- title:
--   Circuits without classical-oracle calls
-- statement:
--   A circuit **makes no classical oracle calls** if it contains no classical-oracle gate. Verifiers, samplers and the QCIP[2] protocols inside oracle queries access only the quantum oracle; only the distinguisher of Definition 3 also has the Boolean oracle $O$.
-- source:
--   Barhoush, Quantum State Search with Classical Interactive Advice, arXiv:2610.25657 (held version, sha256 2a16939a…3408), Section 5, p.15; Section 6.1, p.16

import Mathlib
import Definitions.Def_QStateSearch_Supplement_QCircuit

set_option autoImplicit false

namespace QStateSearch.Supplement

/-- The circuit `C` makes no classical calls to a Boolean oracle (it has access to the quantum
oracle only).

Barhoush, *Quantum State Search with Classical Interactive Advice*, arXiv:2610.25657
(held version, sha256 2a16939a…3408), Section 5, p.15, and Section 6.1, p.16 (verifiers, samplers and the QCIP[2] protocols have
access to the quantum oracle only; only the distinguisher of Definition 3 has the classical
oracle `O`). -/
def QCircuit.NoCQuery (C : QCircuit) : Prop :=
  ∀ qs anc tgt, QGate.cquery qs anc tgt ∉ C.gates

end QStateSearch.Supplement


