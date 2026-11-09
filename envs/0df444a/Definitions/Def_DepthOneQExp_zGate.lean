-- Prove2me | Definitions.Def_DepthOneQExp_zGate
-- name    : DepthOneQExp_zGate
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:47:47.851304+00:00
-- url     : https://prove2.me/theorems/420d9f8f-d7c3-4f38-bb1a-41f8b8127eb0
-- title:
--   The single-qubit gate $Z$
-- statement:
--   The Pauli $Z$ gate $\mathrm{diag}(1,-1)$ on one qubit, as a gate of arity 1 in the published gate model `MITMSynthesis.Gate`. It is one of the three gate types of which the sixteen unitaries of Theorem 2.2 are depth-1 circuits.
-- source:
--   Anshu–Balasubramanian–Haferkamp–Harrow–Tan, Depth-1 expanders on the unitary group and applications, arXiv:2609.01605 (held version, sha256 3c3f8513…aebfd87), Eq. (2.1), p.6

import Mathlib
import Definitions.Def_MITMSynthesis_Gate
import Definitions.Def_DepthOneQExp_zMat

namespace DepthOneQExp

/-- The single-qubit Pauli `Z` gate `diag(1, −1)` as a gate of arity 1
(Anshu–Balasubramanian–Haferkamp–Harrow–Tan, *Depth-1 expanders on the unitary group and
applications*, arXiv:2609.01605, held version sha256 3c3f8513…aebfd87, Eq. (2.1), p.6). -/
noncomputable def zGate : MITMSynthesis.Gate :=
  ⟨1, one_pos, ⟨zMat 1 0, zMat_mem_unitaryGroup 1 0⟩⟩

end DepthOneQExp


