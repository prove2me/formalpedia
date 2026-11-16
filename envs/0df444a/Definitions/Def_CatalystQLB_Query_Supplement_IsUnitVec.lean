-- Prove2me | Definitions.Def_CatalystQLB_Query_Supplement_IsUnitVec
-- name    : CatalystQLB_Query_Supplement_IsUnitVec
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T21:56:06.74213+00:00
-- url     : https://prove2.me/theorems/e25c34c7-4d57-480f-9ab3-2baefc97a09e
-- title:
--   Unit vectors (pure states) $|v\rangle$ with $\sum_i |v_i|^2 = 1$
-- statement:
--   A vector $|v\rangle\in\mathbb C^m$, written in a fixed orthonormal basis indexed by a finite set $m$, is a **unit vector** if
--   $$\sum_{i} |v_i|^2 = 1 .$$
--   Unit vectors are the pure states of the paper: every $|\phi\rangle$, $|\psi\rangle$, $|\eta\rangle$ in the catalytic conditions below is normalized.
--
--   **Formalization Note** Vectors are functions on the basis index type; for the registers of the paper the index type is the set of bit strings $\{0,1\}^n$ (`QAlgorithms.Qubits n`).
-- source:
--   Arora, Chakraborty, Cojocaru, Saminathan, Singh, Computational Work Extraction: The Complexity of Catalysts, arXiv:2609.40323 (version of 2026-11-03, sha256 44854b3a…), Notation 9, p.17 (PDF 20)

import Mathlib

namespace CatalystQLB.Query.Supplement

/-- A **unit vector** `|v⟩` of the finite-dimensional Hilbert space `ℂ^m`: `Σᵢ |vᵢ|² = 1`
(Arora, Chakraborty, Cojocaru, Saminathan, Singh, *Computational Work Extraction: The Complexity
of Catalysts*, arXiv:2609.40323 (version of 2026-11-03), Notation 9, p.17 (PDF 20): a pure state
`|ϕ⟩` is a normalized vector).

**Formalization Note** Vectors are functions `m → ℂ` on a finite basis index type `m`; for the
registers of the paper `m = QAlgorithms.Qubits n` (bit strings). -/
def IsUnitVec {m : Type} [Fintype m] (v : m → ℂ) : Prop :=
  ∑ i, Complex.normSq (v i) = 1

end CatalystQLB.Query.Supplement


