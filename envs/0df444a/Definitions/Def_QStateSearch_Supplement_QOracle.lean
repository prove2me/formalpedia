-- Prove2me | Definitions.Def_QStateSearch_Supplement_QOracle
-- name    : QStateSearch_Supplement_QOracle
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:09:54.829016+00:00
-- url     : https://prove2.me/theorems/c07c3ae1-2d9b-4a44-8415-28848cd90efd
-- title:
--   Quantum oracles (labelled families of matrices)
-- statement:
--   A **quantum oracle** assigns to every classical label $\ell$ (a list of naturals) and every number $k$ of qubits a $2^k\times2^k$ matrix $U_\ell^{(k)}$, indexed by $\{0,1\}^k$, applied by an oracle gate with label $\ell$ on $k$ wires.
--
--   A sequence $U=(U_1,U_2,\dots)$ in the sense of Section 2.3 is the oracle that ignores the label and uses $U_k$ on $k$ qubits; the tagged block-diagonal oracle $T$ of Section 6 uses the label for the block and the tag.
--
--   **Formalization Note** Unitarity is not part of the type; the two oracles of the paper are unitary by construction.
-- source:
--   Barhoush, Quantum State Search with Classical Interactive Advice, arXiv:2610.25657 (held version, sha256 2a16939a…3408), Section 2.3, p.10; Section 6.2, p.17

import Mathlib

set_option autoImplicit false

namespace QStateSearch.Supplement

/-- A **quantum oracle**: for every classical label `lab` and every number `k` of qubits, a
`2^k × 2^k` matrix `U lab k` on `k` qubits (rows and columns indexed by `{0,1}^k`), applied by
the gate `QGate.oracle lab c ws` when `k = |ws|`.

Barhoush, *Quantum State Search with Classical Interactive Advice*, arXiv:2610.25657
(held version, sha256 2a16939a…3408), Section 2.3, p.10: "A quantum oracle is a sequence U = (U_1, U_2, …), where U_n is a unitary
on a specified polynomial number of qubits"; Section 6.2, p.17: "The integer t is a classical
tag. Equivalently, all these blocks form one tagged block-diagonal unitary."

**Formalization Note.** A sequence `(U_n)` is the oracle that ignores the label and uses `U_k`
on `k` qubits. Unitarity is not part of the type; the oracles of Sections 5 and 6 are unitary
by construction (for unit vectors). -/
abbrev QOracle : Type := List ℕ → (k : ℕ) → Matrix (Fin k → Bool) (Fin k → Bool) ℂ

end QStateSearch.Supplement


