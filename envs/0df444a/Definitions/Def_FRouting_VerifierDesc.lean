-- Prove2me | Definitions.Def_FRouting_VerifierDesc
-- name    : FRouting_VerifierDesc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:11:55.283311+00:00
-- url     : https://prove2.me/theorems/50d441bc-fc9a-4a02-8e13-ca951b0f7b6d
-- title:
--   Verifier protocols, provers, interactions and acceptance
-- statement:
--   A **verifier protocol** on qubits, with $m$ message qubits, consists of $v$ private qubits, a first circuit from the auxiliary input to the private and message qubits, a list of circuits on those qubits applied after each prover move, and a last circuit producing the output qubits. A **prover** has a finite memory, a basis state to start from, and arbitrary channels on the message qubits and the memory as its moves. The **interaction** alternates them and discards the memory, giving a channel from the auxiliary input to the output. For an honest verifier, with no auxiliary input and one output qubit, the **acceptance probability** is the probability that the output qubit is $|1\rangle$.
--
--   **Formalization Note** Definition 5.1 cites [Wat02; Wat09] for the model, so this is a reading. A cheating verifier is the same object with any auxiliary input and output. The prover's memory starting in a basis state loses nothing, since its first move is arbitrary.
-- source:
--   Renard, Computational Bounds for f-Routing, arXiv:2609.40278 (held copy, sha256 4a327f29…), Definition 5.1, p.20, citing [Wat02; Wat09]

import Definitions.Def_FRouting_RoutingStrategy
import Definitions.Def_FRouting_encCircuit

set_option autoImplicit false

open Matrix

namespace FRouting

open WildeQIT QAlgorithms.Complexity

/-- The basis of `k` qubits. -/
abbrev Qubits (k : ℕ) : Type := Fin k → Fin 2

/-- **A verifier's protocol on one input.** Renard, *Computational Bounds for f-Routing*,
arXiv:2609.40278 (held copy, sha256 4a327f29…), Definition 5.1, p.20, cites [Wat02; Wat09] for the proof
system without defining it. This is the reading: a verifier holds `priv` private qubits and shares `msg`
message qubits with the prover. `first` maps the auxiliary input to the private and message qubits;
after each prover move the verifier applies the next circuit of `rounds`; after the last prover move,
`last` produces the `out` output qubits. An honest verifier has `aux = 0` and `out = 1`.

**Formalization Note** A cheating verifier is the same object with any `aux` and `out`. The prover
moves `rounds.length + 1` times. A protocol in which the prover speaks first has a trivial `first`
on the message qubits. -/
structure VerifierDesc (aux out msg : ℕ) where
  /-- The number of private qubits. -/
  priv : ℕ
  /-- The verifier's first circuit. -/
  first : Circuit 2 aux (priv + msg)
  /-- The verifier's circuits between prover moves. -/
  rounds : List (Circuit 2 (priv + msg) (priv + msg))
  /-- The verifier's last circuit. -/
  last : Circuit 2 (priv + msg) out

/-- The description a verifier machine prints. -/
def encVerifier {aux out msg : ℕ} (V : VerifierDesc aux out msg) : Str :=
  encNat aux ++ encNat out ++ encNat msg ++ encNat V.priv ++ encCircuit V.first ++
    encBin V.rounds.length ++ V.rounds.flatMap (fun c => encCircuit c) ++ encCircuit V.last

/-- The verifier's quantum work is within `t`: at most `t` gates in total, at most `t` wires in each
circuit, at most `t` rounds. -/
def VerifierDesc.SizeBound {aux out msg : ℕ} (V : VerifierDesc aux out msg) (t : ℕ) : Prop :=
  V.first.size + (V.rounds.map Circuit.size).sum + V.last.size ≤ t ∧
    V.first.width ≤ t ∧ (∀ c ∈ V.rounds, c.width ≤ t) ∧ V.last.width ≤ t ∧ V.rounds.length ≤ t

/-- **A prover**: an unrestricted quantum party with a finite private memory, starting in a basis state
of it, whose `j`-th move is any channel on the message qubits and the memory.

**Formalization Note** The memory starting in a basis state loses nothing, since the first move is an
arbitrary channel. -/
structure Prover (msg : ℕ) where
  /-- The prover's private memory. -/
  Mem : Reg
  /-- The initial basis state of the memory. -/
  start : Mem
  /-- The prover's moves. -/
  move : ℕ → QChannel (Qubits msg × Mem) (Qubits msg × Mem)

variable {aux out msg : ℕ}

/-- The `j`-th prover move on all the qubits and the prover's memory, the private qubits untouched. -/
noncomputable def proverStep (V : VerifierDesc aux out msg) (P : Prover msg) (j : ℕ) :
    QChannel (Qubits (V.priv + msg) × P.Mem) (Qubits (V.priv + msg) × P.Mem) :=
  let e : (Qubits (V.priv + msg) × P.Mem) ≃ (Qubits V.priv × (Qubits msg × P.Mem)) :=
    (Equiv.prodCongr (Fin.appendEquiv V.priv msg).symm (Equiv.refl _)).trans
      (Equiv.prodAssoc _ _ _)
  chanReindex e.symm e.symm (chanTensorLeft (Qubits V.priv) (P.move j))

/-- The alternation of prover moves and verifier circuits: move `j`, then the first circuit of the
list, then move `j + 1`, and so on, ending with a prover move. -/
noncomputable def roundsChannel (V : VerifierDesc aux out msg) (P : Prover msg) :
    ℕ → List (Circuit 2 (V.priv + msg) (V.priv + msg)) →
      QChannel (Qubits (V.priv + msg) × P.Mem) (Qubits (V.priv + msg) × P.Mem)
  | j, [] => proverStep V P j
  | j, c :: cs =>
    chanComp (roundsChannel V P (j + 1) cs)
      (chanComp (chanTensorRight c.channel P.Mem) (proverStep V P j))

/-- **The channel of an interaction**: from the verifier's auxiliary input to the verifier's output,
the prover's memory being discarded at the end. -/
noncomputable def interaction (V : VerifierDesc aux out msg) (P : Prover msg) :
    QChannel (Qubits aux) (Qubits out) :=
  chanComp (chanDiscard P.Mem)
    (chanComp (chanTensorRight V.last.channel P.Mem)
      (chanComp (roundsChannel V P 0 V.rounds)
        (chanComp (chanAttach P.Mem P.start) V.first.channel)))

/-- **The acceptance probability** of an honest verifier with a prover: the probability that the
output qubit of the interaction is `|1⟩`.

**Formalization Note** A real number on an actual state, not a supremum over provers: the class
quantifies over provers with `∀` and `∃`. -/
noncomputable def acceptance (V : VerifierDesc 0 1 msg) (P : Prover msg) : ℝ :=
  ((interaction V P).apply (1 : Matrix (Qubits 0) (Qubits 0) ℂ) (fun _ => 1) (fun _ => 1)).re

end FRouting


