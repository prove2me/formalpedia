-- Prove2me | Definitions.Def_PermInvCC_Qstar
-- name    : PermInvCC_Qstar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T20:23:59.189116+00:00
-- url     : https://prove2.me/theorems/74836415-51ad-4c56-97ed-5254080b6131
-- title:
--   Entanglement-assisted quantum communication complexity $Q^*(f)$
-- statement:
--   $Q^*(f)$ is the least number of qubits communicated by a quantum protocol with arbitrary prior entanglement whose output is wrong with probability at most $1/3$ on each promised input.
--
--   The main Theorem 1.1 bounds $R^{\mathrm{pub}}(f)$ in terms of $Q^*(f)^2$.
--
--   **Formalization Note** It is an infimum of natural numbers over the protocols of the model `EntQProtocol`; the defining set is nonempty on finite inputs (Alice can send her input in qubits).
-- source:
--   Huang and Ye, Quantum Advantage of Permutation-Invariant Functions in Communication Complexity, arXiv:2609.40116 (held version, sha256 fe1797dd…), Definition 2.1, p.9

import Mathlib
import Definitions.Def_PermInvCC_EntQProtocol

namespace PermInvCC

/-- The **entanglement-assisted quantum communication complexity** `Q*(f)` (Y. Huang and Z. Ye,
arXiv:2609.40116, held version sha256 fe1797dd…, Definition 2.1, p.9): the least number of qubits
communicated by a protocol with arbitrary prior entanglement whose output (Bob's) is wrong with
probability at most `1/3` on each promised input.

**Formalization Note.** `sInf ∅ = 0` for natural numbers; the set is nonempty on finite inputs
(Alice sends her input in qubits, Bob computes the answer). -/
noncomputable def Qstar {X Y : Type} (f : X → Y → Option Bool) : ℕ :=
  sInf {c : ℕ | ∃ P : EntQProtocol X Y, P.cost ≤ c ∧
    ∀ x y b, f x y = some b → P.errQ x y b ≤ 1 / 3}

end PermInvCC


