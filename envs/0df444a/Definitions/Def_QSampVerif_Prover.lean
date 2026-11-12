-- Prove2me | Definitions.Def_QSampVerif_Prover
-- name    : QSampVerif_Prover
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T08:32:41.833195+00:00
-- url     : https://prove2.me/theorems/8476d33b-e8c2-4511-81bf-c0ae71d735d3
-- title:
--   Quantum provers with classical advice: persistent core, $X$-flip message loading, measured replies
-- statement:
--   A **quantum prover** (also used for IND-CPA adversaries) has a core of $n$ qubits started in $|0\cdots0\rangle$ and one *round step* per round. In round $i$ the incoming classical message $m$ is written as $\mathrm{padEnc}(m)$ into the step's input wires by $X$ flips, the step's layered Clifford+T circuit is applied to the core, and the step's output wires are measured in the computational basis; the outcome is the prover's reply. The core persists between rounds. In a round without a step the prover replies with the empty string. Any classical advice is hard-wired into the circuits ("polynomial-size quantum circuits with nonuniform classical advice", §3.11).
--
--   The **size** of a prover is $n$ plus, summed over the rounds, the number of input wires, instructions and output wires. A prover is *well formed* when its wire lists are duplicate-free and its layers act on disjoint wires.
--
--   A family $P^*(\lambda,C)$ of provers is **QPT** (quantum polynomial time) when every member is well formed and some classical polynomial-time map computes the description of $P^*(\lambda,C)$ from the common input $\langle 1^\lambda,\langle C\rangle\rangle$.
--
--   **Formalization Note** The prover never sees the verifier's coins, only its messages. No quantum advice is allowed.
-- source:
--   Chung, Cojocaru, Lee, Lin, Classical Verification of Quantum Sampling with Negligible Error, STOC 2027 submission (held version, sha256 dbc19d8f…7ee7), §3.11, p.23 (PDF 24); Theorem 14.5, p.189 (PDF 190)

import Definitions.Def_QSampVerif_TargetCircuit

set_option autoImplicit false

namespace QSampVerif

open QAlgorithms QAlgorithms.Complexity

/-- One round of a quantum prover acting on its persistent core of `n` qubits: the incoming
message is written into the wires `inW` by `X` flips, the layered Clifford+T circuit `circ` is
applied, and the wires `outW` are measured in the computational basis; the outcome is the reply. -/
structure RoundStep (n : ℕ) where
  /-- Wires receiving the incoming message. -/
  inW : List (Fin n)
  /-- The circuit applied in this round. -/
  circ : Layered n
  /-- Wires measured to produce the reply. -/
  outW : List (Fin n)

/-- Chung, Cojocaru, Lee, Lin, STOC 2027 submission (held version, sha256 dbc19d8f…7ee7), §3.11,
p.23 (PDF 24): "We consider polynomial-size quantum circuits with nonuniform classical advice."

A quantum prover (or adversary): a core of `n` qubits started in `|0…0⟩` and one `RoundStep` per
round. The core persists between rounds; any classical advice is hard-wired into the circuits.
In a round without a step the prover replies with the empty string and leaves its core alone.

**Formalization Note.** The prover sees only the messages (loaded as `padEnc m`, so that the
message length is visible), never the verifier's coins. Measurements are projective in the
computational basis. No quantum advice is allowed (paper.md decision 6). -/
structure Prover where
  /-- Number of qubits of the core. -/
  n : ℕ
  /-- The round steps, in order. -/
  steps : List (RoundStep n)

namespace Prover

/-- The size of a prover: core qubits plus, for every round, the input wires, the instructions
and the measured wires. -/
def size (P : Prover) : ℕ :=
  P.n + (P.steps.map fun s => s.inW.length + numInstr s.circ + s.outW.length).sum

/-- A prover is well formed: distinct wires in each wire list, disjoint gates in each layer. -/
def Valid (P : Prover) : Prop :=
  ∀ s ∈ P.steps, s.inW.Nodup ∧ s.outW.Nodup ∧ ∀ l ∈ s.circ, LayerOk l

/-- The classical description of a prover. -/
def encode (P : Prover) : Str :=
  tup [unary P.n,
    tup (P.steps.map fun s => tup [wireList s.inW, encCirc s.circ, wireList s.outW])]

end Prover

/-- Theorem 14.5, p.189: "a QPT prover". A family of provers, one for each security parameter
`λ` and target circuit `C`, is quantum polynomial time when every member is well formed and the
descriptions are produced from the common input by one classical polynomial-time map
(uniformity). -/
def IsQPTProver (F : ℕ → TargetCircuit → Prover) : Prop :=
  (∀ lam C, (F lam C).Valid) ∧
    ∃ f : Str → Str, PolyTimeComputable f ∧ ∀ lam C, f (commonInput lam C) = (F lam C).encode

end QSampVerif


