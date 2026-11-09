-- Prove2me | Definitions.Def_DepthOneQExp_xGate
-- name    : DepthOneQExp_xGate
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:45:31.313372+00:00
-- url     : https://prove2.me/theorems/92046d53-e496-4952-b8a6-81636cbead5a
-- title:
--   The single-qubit gate $X$
-- statement:
--   The Pauli $X$ gate $|b\rangle\mapsto|b\oplus1\rangle$ on one qubit, as a gate of arity 1 in the published gate model `MITMSynthesis.Gate` (a unitary on $\{0,1\}^{k}$ with $k\ge1$). It is one of the three gate types of which the sixteen unitaries of Theorem 2.2 are depth-1 circuits.
-- source:
--   Anshu–Balasubramanian–Haferkamp–Harrow–Tan, Depth-1 expanders on the unitary group and applications, arXiv:2609.01605 (held version, sha256 3c3f8513…aebfd87), Eq. (2.1), p.6

import Mathlib
import Definitions.Def_MITMSynthesis_Gate
import Definitions.Def_DepthOneQExp_permToMatrix
import Definitions.Def_DepthOneQExp_xPerm

namespace DepthOneQExp

/-- The single-qubit Pauli `X` gate `|b⟩ ↦ |b + 1⟩` as a gate of arity 1
(Anshu–Balasubramanian–Haferkamp–Harrow–Tan, *Depth-1 expanders on the unitary group and
applications*, arXiv:2609.01605, held version sha256 3c3f8513…aebfd87, Eq. (2.1), p.6). -/
noncomputable def xGate : MITMSynthesis.Gate :=
  ⟨1, one_pos, ⟨permToMatrix (xPerm 1 0), permToMatrix_mem_unitaryGroup _⟩⟩

end DepthOneQExp


