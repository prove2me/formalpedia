-- Prove2me | Definitions.Def_PermInvCC_EntQProtocol
-- name    : PermInvCC_EntQProtocol
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T20:23:04.354401+00:00
-- url     : https://prove2.me/theorems/92483ff1-bd62-45bb-afe6-f22e3cdd5648
-- title:
--   Quantum protocols with arbitrary prior entanglement
-- statement:
--   An **entanglement-assisted quantum protocol** acts on $W$ qubits and exchanges $r$ messages, alternately sent by Alice and Bob.
--
--   1. Before message $t$ each qubit is held by Alice or by Bob; message $t$ moves some qubits from its sender to the receiver, and its cost is the number of qubits moved.
--   2. The start state $\psi_0$ is an **arbitrary unit vector on all $W$ qubits, independent of the inputs**; this is the arbitrary prior entanglement.
--   3. Between messages each party applies a unitary, depending only on its own input, to the qubits it holds.
--   4. At the end Bob measures one qubit he holds in the computational basis; the outcome $1$ is the output $+1$ (acceptance).
--
--   The **acceptance probability** on $(x,y)$ is the probability of outcome $1$, and the **cost** is the total number of qubits moved.
--
--   This is the model of $Q^*$ in Definition 2.1: local computation is unrestricted, Bob produces the output.
--
--   **Formalization Note** Messages may move zero qubits, so alternation with Alice first loses nothing. Private randomness and intermediate measurements are simulated unitarily on ancillas. Prior entanglement uses finitely many qubits.
-- source:
--   Huang and Ye, Quantum Advantage of Permutation-Invariant Functions in Communication Complexity, arXiv:2609.40116 (held version, sha256 fe1797dd…), Definition 2.1, p.9

import Mathlib

open Matrix

namespace PermInvCC

/-- An **entanglement-assisted quantum communication protocol** (Y. Huang and Z. Ye,
arXiv:2609.40116, held version sha256 fe1797dd…, Definition 2.1, p.9: "`Q*(f)` … quantum
communication complexity with arbitrary prior entanglement … Local computation is unrestricted.
We take Bob to produce the output").

The protocol acts on `W` qubits, with computational basis states `σ : Fin W → Bool`, and has `r`
messages.
* `owner t j` says who holds qubit `j` (`true` = Alice) before message `t` (`t < r`), and
  `owner r j` after the last message.
* Message `t` is sent by Alice if `t` is even and by Bob if `t` is odd; it moves qubits from its
  sender to the receiver only (`transfer`); its cost is the number of qubits moved.
* The start state `ψ₀` is an **arbitrary unit vector on all `W` qubits, independent of the
  inputs**: this is the arbitrary prior entanglement (and any fresh workspace qubits).
* At each time `t ≤ r` Alice applies a unitary `uA t x`, depending only on her input `x`, to the
  qubits she holds at time `t`, and Bob a unitary `uB t y` to the qubits he holds.
* At the end Bob measures a qubit `out` that he holds in the computational basis and outputs the
  outcome (`true` = `+1`).

**Formalization Note.** A message may move zero qubits, so fixing Alice to send the even-numbered
messages loses nothing. Private randomness and intermediate measurements are simulated unitarily
on ancilla qubits (deferred measurement). Prior entanglement is finite-dimensional (finitely many
qubits). -/
structure EntQProtocol (X Y : Type) where
  /-- number of qubits -/
  W : ℕ
  /-- number of messages -/
  r : ℕ
  /-- `owner t j = true` iff Alice holds qubit `j` before message `t` (after the last if `t = r`) -/
  owner : Fin (r + 1) → Fin W → Bool
  /-- message `t` only moves qubits from its sender (Alice iff `t` is even) to the receiver -/
  transfer : ∀ (t : Fin r) (j : Fin W), owner t.castSucc j ≠ owner t.succ j →
    owner t.castSucc j = decide (t.val % 2 = 0)
  /-- the measured output qubit -/
  out : Fin W
  /-- Bob holds the output qubit at the end -/
  out_owner : owner (Fin.last r) out = false
  /-- the input-independent start state (prior entanglement) -/
  ψ₀ : (Fin W → Bool) → ℂ
  /-- the start state is a unit vector -/
  ψ₀_norm : ∑ σ, ‖ψ₀ σ‖ ^ 2 = 1
  /-- Alice's unitary at time `t` on the qubits she holds then -/
  uA : (t : Fin (r + 1)) → X → Matrix.unitaryGroup ({j : Fin W // owner t j = true} → Bool) ℂ
  /-- Bob's unitary at time `t` on the qubits he holds then -/
  uB : (t : Fin (r + 1)) → Y → Matrix.unitaryGroup ({j : Fin W // owner t j = false} → Bool) ℂ

namespace EntQProtocol

variable {X Y : Type}

/-- The joint local operation `uA t x ⊗ uB t y` at time `t`, as a matrix on the computational
basis of all `W` qubits. -/
noncomputable def stepOp (P : EntQProtocol X Y) (x : X) (y : Y) (t : Fin (P.r + 1)) :
    Matrix (Fin P.W → Bool) (Fin P.W → Bool) ℂ :=
  fun σ σ' =>
    (P.uA t x : Matrix ({j : Fin P.W // P.owner t j = true} → Bool)
        ({j : Fin P.W // P.owner t j = true} → Bool) ℂ) (fun j => σ j.1) (fun j => σ' j.1) *
      (P.uB t y : Matrix ({j : Fin P.W // P.owner t j = false} → Bool)
        ({j : Fin P.W // P.owner t j = false} → Bool) ℂ) (fun j => σ j.1) (fun j => σ' j.1)

/-- The final state on `(x, y)`: start from `ψ₀` and apply the local operations of times
`0, 1, …, r` in order (messages only change who holds which qubit). -/
noncomputable def finalState (P : EntQProtocol X Y) (x : X) (y : Y) : (Fin P.W → Bool) → ℂ :=
  (List.finRange (P.r + 1)).foldl (fun ψ t => P.stepOp x y t *ᵥ ψ) P.ψ₀

/-- The **acceptance probability** on `(x, y)`: the probability that Bob's measured qubit is `1`,
i.e. the squared norm of the part of the final state in which qubit `out` is `1`. -/
noncomputable def acceptProb (P : EntQProtocol X Y) (x : X) (y : Y) : ℝ :=
  ∑ σ : Fin P.W → Bool, if σ P.out then ‖P.finalState x y σ‖ ^ 2 else 0

/-- The probability that the output on `(x, y)` differs from `b` (`true` = `+1`). -/
noncomputable def errQ (P : EntQProtocol X Y) (x : X) (y : Y) (b : Bool) : ℝ :=
  if b then 1 - P.acceptProb x y else P.acceptProb x y

/-- The **cost**: the total number of qubits moved, over all `r` messages (the same on every
input). -/
def cost (P : EntQProtocol X Y) : ℕ :=
  ∑ t : Fin P.r, (Finset.univ.filter fun j => P.owner t.castSucc j ≠ P.owner t.succ j).card

end EntQProtocol

end PermInvCC


