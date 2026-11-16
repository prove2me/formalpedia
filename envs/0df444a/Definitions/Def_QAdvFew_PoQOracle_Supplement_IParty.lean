-- Prove2me | Definitions.Def_QAdvFew_PoQOracle_Supplement_IParty
-- name    : QAdvFew_PoQOracle_Supplement_IParty
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:17:39.684117+00:00
-- url     : https://prove2.me/theorems/91a74e13-8819-45cc-9df4-a3e20daf4978
-- title:
--   Quantum parties of protocols with classical communication
-- statement:
--   A protocol with **classical communication** exchanges $M(n)$ messages of $\ell(n)$ bits that alternate between two parties. A **QPT party** holds a register with receiving wires, sending wires, one input/output qubit and work qubits; at each message it applies an oracle quantum circuit and then either measures its sending wires (if it sends this message) or XORs the received message onto its receiving wires; at the end it applies a final circuit. Its **likelihood** of a transcript with a final outcome $o$ is the squared norm of its state projected onto its own messages and onto $o$ when its input/output qubit is measured in the computational or the Hadamard basis.
--
--   Because communication is classical and each party's measurements are private, the probability of a transcript with given final outcomes is the product of the two parties' likelihoods. A party is uniform if its circuits are generated in polynomial time and polynomially bounded if its circuit sizes and work space are polynomial; without uniformity it is a nonuniform QPT party.
-- source:
--   Goldin, Lombardi, Morimae, Quantum Advantage has Few Complexity Implications, arXiv:2611.05303v1, Definitions 3.26, 3.28, B.1, pp. 19, 52–53 (PDF pp. 21, 54–55); §3.2.1, p. 12 (PDF p. 14)

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_Supplement_UCirc
import Definitions.Def_QAdvFew_PoQOracle_Protocol
import Definitions.Def_QAdvFew_PoQOracle_tup

open QAlgorithms.Complexity

namespace QAdvFew.PoQOracle.Supplement

open QAdvFew.PoQOracle

/-- A transcript of a protocol with classical communication of `M` messages of length `ℓ`
(Goldin, Lombardi, Morimae, *Quantum Advantage has Few Complexity Implications*, arXiv:2611.05303v1, Definitions 3.26, 3.28, B.1, pp. 19, 52–53 (PDF pp. 21, 54–55): "a protocol with classical
communication"): message `j` is `τ j`. Messages alternate between the two parties; who sends
message `0` is fixed by the protocol.

**Formalization Note** All messages have the same length `ℓ`, a polynomial in `n`; shorter messages
are zero-padded, as in the published `QAdvFew.PoQOracle.Transcript`. -/
abbrev ITranscript (M ℓ : ℕ) := Fin M → Msg ℓ

/-- A **QPT party** of a protocol with message length `ℓ(n)`, with access to a unitary oracle of
arity `ar` and a classical oracle (§3.2.1, p. 12; Definitions 3.28, B.1). At length `n` it holds a
register of `2ℓ(n) + 1 + W(n)` qubits: wires `0, …, ℓ − 1` receive messages, wires `ℓ, …, 2ℓ − 1`
carry outgoing messages, wire `2ℓ` is the party's input/output qubit, the rest is work space. At
message `j` it applies the circuit `circ n j`, then measures its outgoing wires (if it sends message
`j`) or XORs the received message onto its receiving wires; after the last message it applies
`circ n M`.

**Formalization Note** Fixed wire roles lose nothing (CNOTs move data). Since every message is
classical and each party's randomness and measurements are private, the probability of a transcript
with given final outcomes is the product of the two parties' likelihoods (`IParty.lik`), as in the
published `QAdvFew.PoQOracle.acceptProb`. -/
structure IParty (ar : ℕ → ℕ → ℕ) (ℓ : ℕ → ℕ) where
  W : ℕ → ℕ
  circ : (n j : ℕ) → UCirc ar (2 * ℓ n + 1 + W n)

namespace IParty

variable {ar : ℕ → ℕ → ℕ} {ℓ : ℕ → ℕ}

/-- The input/output wire `2ℓ`. -/
def io (P : IParty ar ℓ) (n : ℕ) : Fin (2 * ℓ n + 1 + P.W n) := ⟨2 * ℓ n, by omega⟩

/-- XOR a message onto the receiving wires `0, …, ℓ − 1`. -/
def xorIn (P : IParty ar ℓ) (n : ℕ) (m : Msg (ℓ n)) (ψ : QState (2 * ℓ n + 1 + P.W n)) :
    QState (2 * ℓ n + 1 + P.W n) :=
  fun y => ψ (fun k => if h : (k : ℕ) < ℓ n then xor (y k) (m ⟨k, h⟩) else y k)

/-- Project the sending wires `ℓ, …, 2ℓ − 1` onto the outcome `m`. -/
def projOut (P : IParty ar ℓ) (n : ℕ) (m : Msg (ℓ n)) (ψ : QState (2 * ℓ n + 1 + P.W n)) :
    QState (2 * ℓ n + 1 + P.W n) :=
  fun y => if ∀ i : Fin (ℓ n), y ⟨ℓ n + i, by omega⟩ = m i then ψ y else 0

/-- The unnormalized final state of a party that sends the even-numbered messages if `first` (else
the odd-numbered ones), starts with its input/output qubit in `|b⟩` and all other qubits `|0⟩`, and
whose measurements gave its own messages of `τ` while it received the other party's messages of
`τ`. -/
noncomputable def finalState (P : IParty ar ℓ) (O : UOracle ar) (C : Oracle) (n : ℕ)
    (first : Bool) {M : ℕ} (τ : ITranscript M (ℓ n)) (b : Bool) : QState (2 * ℓ n + 1 + P.W n) :=
  let ψ0 : QState (2 * ℓ n + 1 + P.W n) := basisState fun k => if k = P.io n then b else false
  let ψ := (List.finRange M).foldl
    (fun ψ (j : Fin M) =>
      let ψ' := (P.circ n (j : ℕ)).run O C ψ
      if decide ((j : ℕ) % 2 = 0) = first then P.projOut n (τ j) ψ' else P.xorIn n (τ j) ψ')
    ψ0
  (P.circ n M).run O C ψ

/-- The probability that measuring wire `w` of the unnormalized state `ψ` gives `o`:
`‖Π_{w=o} ψ‖²`. -/
noncomputable def probOutcome {m : ℕ} (ψ : QState m) (w : Fin m) (o : Bool) : ℝ :=
  ∑ y : Bits m, if y w = o then ‖ψ y‖ ^ 2 else 0

/-- The party's likelihood `w(τ, o)`: its measurements give its messages of `τ`, and measuring its
input/output qubit at the end in the computational basis (`had = false`) or the Hadamard basis
(`had = true`) gives `o`. -/
noncomputable def lik (P : IParty ar ℓ) (O : UOracle ar) (C : Oracle) (n : ℕ) (first : Bool)
    {M : ℕ} (τ : ITranscript M (ℓ n)) (b had o : Bool) : ℝ :=
  let ψ := P.finalState O C n first τ b
  probOutcome (if had then apply1 hMat (P.io n) ψ else ψ) (P.io n) o

/-- Uniformity (§3.2.1, p. 12): a polynomial-time computable map, with no oracle access, sends
`(1^n, 1^j)` to the work-qubit count and the description of the circuit for message `j`. -/
def Uniform (P : IParty ar ℓ) : Prop :=
  ∃ f : Str → Str, PolyTimeComputable f ∧
    ∀ n j : ℕ, f (tup [unary n, unary j]) = bnat (P.W n) ++ (P.circ n j).desc

/-- Polynomial size: the circuit for message `j` at length `n` has size at most `q(n + j)`
(`UCirc.size`) and there are at most `q(n)` work qubits. Without `Uniform` this is a nonuniform QPT
party (§3.2.1: "Nonuniform algorithms are polynomial-size circuit families"). -/
def PolyBounded (P : IParty ar ℓ) : Prop :=
  ∃ q : Polynomial ℕ, ∀ n j : ℕ, (P.circ n j).size ≤ q.eval (n + j) ∧ P.W n ≤ q.eval n

end IParty

end QAdvFew.PoQOracle.Supplement


