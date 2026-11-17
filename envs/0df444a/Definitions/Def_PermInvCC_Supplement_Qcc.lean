-- Prove2me | Definitions.Def_PermInvCC_Supplement_Qcc
-- name    : PermInvCC_Supplement_Qcc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:52:34.50021+00:00
-- url     : https://prove2.me/theorems/e10a440e-2fc6-4569-b76d-8658ec873ee8
-- title:
--   Quantum communication complexity $Q(f)$ without prior entanglement
-- statement:
--   Let $f : X \times Y \to \{-1,+1,*\}$ be a partial communication function. The **quantum communication complexity without prior entanglement** $Q(f)$ is the least number of qubits communicated by a quantum protocol that starts with every qubit in the state $|0\rangle$, so that Alice and Bob share neither entanglement nor randomness, and whose output, produced by Bob, differs from $f(x,y)$ with probability at most $1/3$ on every promised input $(x,y)$:
--
--   $$Q(f) = \min\{\,c : \text{some unassisted protocol of cost } c \text{ computes } f \text{ with error} \le 1/3\,\}.$$
--
--   The protocols are those of the base mission's entanglement-assisted model $Q^*$ (local unitaries on the qubits each party holds, messages that move qubits from sender to receiver, Bob measuring one qubit at the end, cost equal to the number of qubits moved), restricted to the all-zero start state. Hence every protocol admissible for $Q$ is admissible for $Q^*$, and $Q^*(f) \le Q(f)$ (p.9).
--
--   This is the model in which the paper's quantum upper bounds (Theorems 1.2, 1.3, 3.7, 5.3, 5.4) are stated.
--
--   **Formalization Note** The start state is the computational basis state $|0\cdots0\rangle$ on all qubits of the base `EntQProtocol`; private randomness and intermediate measurements are simulated unitarily on ancillas (deferred measurement). The minimum is `sInf` over natural numbers, which is attained because the set is nonempty on finite input sets.
-- source:
--   Huang and Ye, Quantum Advantage of Permutation-Invariant Functions in Communication Complexity, arXiv:2609.40116 (held version, sha256 fe1797dd…), §1.1, p.1 (PDF p.4), and Definition 2.1, p.9 (PDF p.12)

import Mathlib
import Definitions.Def_PermInvCC_EntQProtocol

namespace PermInvCC

namespace Supplement

/-- The **quantum communication complexity without prior entanglement** `Q(f)` (Y. Huang and Z. Ye, *Quantum Advantage of Permutation-Invariant Functions in Communication
Complexity*, arXiv:2609.40116, held version sha256 fe1797dd…, §1.1, p.1, and Definition 2.1, p.9): the least number of qubits communicated
by a quantum protocol with neither prior entanglement nor free shared randomness whose output
(Bob's) is wrong with probability at most `1/3` on each promised input.

**Formalization Note.** A protocol is the base mission's `EntQProtocol` whose start state is the
computational basis state with every qubit `0` (`ψ₀ σ = 1` exactly when `σ` is all-`false`):
a product state, so there is no prior entanglement and no shared randomness; each party's
workspace qubits start in `|0⟩`. Private randomness and intermediate measurements are simulated
unitarily (deferred measurement), as in `EntQProtocol`. Every such protocol is also admissible
for `Q*`, so `Q*(f) ≤ Q(f)` (p.9) holds by construction. `sInf ∅ = 0`; the set is nonempty on
finite input sets (Alice sends her input in qubits). -/
noncomputable def Qcc {X Y : Type} (f : X → Y → Option Bool) : ℕ :=
  sInf {c : ℕ | ∃ P : EntQProtocol X Y,
    (P.ψ₀ = fun σ => if σ = (fun _ => false) then 1 else 0) ∧ P.cost ≤ c ∧
    ∀ x y b, f x y = some b → P.errQ x y b ≤ 1 / 3}

end Supplement

end PermInvCC


