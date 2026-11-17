-- Prove2me | Definitions.Def_CompNonlocal_Supplement_partyMem
-- name    : CompNonlocal_Supplement_partyMem
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:01:37.4633+00:00
-- url     : https://prove2.me/theorems/b48b87d3-6623-42d9-b6ab-27636a2324d2
-- title:
--   The private memory of an honest party in a multi-round QCCC protocol
-- statement:
--   In a protocol with **classical communication** between quantum parties (QCCC), an honest party keeps a private quantum memory between its rounds. Fix a circuit $C$ that the party runs in each of its rounds, a set of rounds in which it speaks, a private classical input $\mathrm{pre}$, and a transcript $t=(t_0,t_1,\dots)$ of messages.
--
--   The memory starts in $|0\cdots0\rangle$. In each of its rounds $j$ the party runs $C$ on the classical input $(j,\mathrm{pre},t_0\cdots t_{j-1})$ and on its memory, and keeps the branch in which its classical output equals the message $t_j$; the retained wires of $C$ become the new memory. In the other party's rounds the memory is unchanged. The result after $j$ rounds is an **unnormalized** state whose trace is the probability that the party sends its messages of $t$, given the other party's messages.
--
--   This is the execution model of honest parties ("may retain quantum states locally, and exchange only classical messages") used for the commitment protocols of Definition 6.
--
--   **Formalization Note** One circuit with the round number as classical input is run in every round; a uniform sequence of round circuits can be merged into such a circuit. Memory qubits that the circuit does not read are discarded.
-- source:
--   Głuch, Morimae, From Computational Nonlocality to Public-Key Encryption and Commitments, manuscript (STOC 2027 submission, sha256 e245edd7b7dd5f4c52119a37e0ee1d00eaf20185262775b8ab7d3067a9f2fcae), §4.4, p.20; Definition 6, p.22

import Mathlib
import Definitions.Def_CompNonlocal_ICirc_branchOn

set_option autoImplicit false

namespace CompNonlocal.Supplement

open QAlgorithms.Complexity

/-- The private quantum memory of an honest party in a multi-round QCCC protocol. Głuch, Morimae, *From Computational Nonlocality to Public-Key Encryption and Commitments*, manuscript (STOC 2027 submission, sha256 e245edd7…),
§4.4, p.20 ("Honest algorithms are uniform QPT, may retain quantum states locally, and exchange
only classical messages. The parties start with independent private workspaces") and Definition 6,
p.22 ("Com(1^κ, b) is a classical-communication protocol … It produces a public classical
transcript T and private registers C, R held by the committer and receiver").

The party runs the same circuit `C` in each of its rounds. Rounds are numbered `0, 1, 2, …`; the
party acts in round `j` when `mine j`. In its round `j` it reads, classically, `encNat j` (the
round number), its private classical input `pre`, and the transcript so far `(t.take j).flatten`,
and, quantumly, its memory (`C.outQ.length` qubits); its classical output is the message of round
`j` and its quantum output `outQ` is the new memory. `partyMem C mine pre t j` is the
unnormalized memory after rounds `0, …, j−1` of the transcript `t`, on the event that the party's
own messages are those of `t`: its trace is the probability of the party's messages given the
other party's messages.

**Formalization Note** The memory starts in `|0…0⟩`. Memory qubits beyond the circuit's `nq`
quantum-input wires are not read and are discarded (`branchOn`). Running one circuit with the round
number as input loses no generality: a uniform sequence of round circuits can be merged into one
uniform circuit that branches on the round number. -/
noncomputable def partyMem (C : ICirc) (mine : ℕ → Bool) (pre : Str) (t : List Str) :
    ℕ → Matrix (Bits C.outQ.length) (Bits C.outQ.length) ℂ
  | 0 => Matrix.of fun s s' => if (∀ i, s i = false) ∧ (∀ i, s' i = false) then 1 else 0
  | j + 1 =>
    if mine j then
      C.branchOn C.outQ.length (encNat j ++ pre ++ (t.take j).flatten) (partyMem C mine pre t j)
        (fun o => decide (o = t.getD j []))
    else partyMem C mine pre t j

end CompNonlocal.Supplement


