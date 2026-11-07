-- Prove2me | Definitions.Def_QAdvFew_PoQOracle_QParty
-- name    : QAdvFew_PoQOracle_QParty
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:50:54.134645+00:00
-- url     : https://prove2.me/theorems/b35af562-3287-4f25-bb16-4163420f2987
-- title:
--   QPT party of a protocol
-- statement:
--   A **QPT party** of a protocol with message length $\ell(n)$ holds a persistent register initially $|0\cdots0\rangle$. In its $j$-th turn it XORs the incoming message onto designated wires, applies an oracle quantum circuit, and measures the designated outgoing wires in the computational basis; a verifier's last turn measures an output wire instead.
--
--   The likelihood of a sequence of outcomes is the squared norm $\|\Pi_{a_k}U_k\cdots\Pi_{a_1}U_1|0\rangle\|^2$ of the projected state. The party is **uniform** if a deterministic polynomial-time computable map with no oracle access sends $(1^n,1^j)$ to the circuit of turn $j$, and **polynomially bounded** if a polynomial bounds the instructions and the work qubits.
--
--   **Formalization Note** Fixed wire roles lose nothing, since a circuit can move data with CNOT gates.
-- source:
--   Goldin, Lombardi, Morimae, Quantum Advantage has Few Complexity Implications, arXiv:2611.05303v1, Definition 3.26, p. 19 (PDF p. 21); §3.2.1, p. 12 (PDF p. 14)

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_OInstr
import Definitions.Def_QAdvFew_PoQOracle_Protocol
import Definitions.Def_QAdvFew_PoQOracle_tup

open QAlgorithms.Complexity

namespace QAdvFew.PoQOracle

/-- A **QPT party** of a protocol with classical communication and message length `ℓ(n)` (Goldin,
Lombardi, Morimae, *Quantum Advantage has Few Complexity Implications*, arXiv:2611.05303v1,
Definition 3.26, p. 19 (PDF p. 21): "a QPT prover `P^O`"; "Allowing `V^O` to be QPT"; §3.2.1, p. 12).
At length `n` it holds a persistent register of `2ℓ(n) + 1 + W(n)` qubits, initially `|0…0⟩`. Wires
`0, …, ℓ − 1` receive messages, wires `ℓ, …, 2ℓ − 1` carry outgoing messages, wire `2ℓ` carries a
verifier's output bit. In its `j`-th turn the party XORs the incoming message onto the receiving
wires, applies the oracle circuit `circ n j`, and measures the sending wires (or, at a verifier's
last turn, the output wire) in the computational basis.

**Formalization Note** Fixed wire roles lose nothing: the circuit can move data with CNOTs. The
measurement is sequential projective measurement on a state kept between turns, so the probability
of a sequence of outcomes is the squared norm of the projected state (`likP`, `likV`). -/
structure QParty (ℓ : ℕ → ℕ) where
  /-- work qubits beyond the message and output wires -/
  W : ℕ → ℕ
  /-- the oracle circuit of turn `j` at length `n` -/
  circ : (n j : ℕ) → OCirc (2 * ℓ n + 1 + W n)

namespace QParty

variable {ℓ : ℕ → ℕ}

/-- XOR a message onto the receiving wires `0, …, ℓ − 1`. -/
def xorIn (P : QParty ℓ) (n : ℕ) (m : Msg (ℓ n)) (ψ : QState (2 * ℓ n + 1 + P.W n)) :
    QState (2 * ℓ n + 1 + P.W n) :=
  fun y => ψ (fun k => if h : (k : ℕ) < ℓ n then xor (y k) (m ⟨k, h⟩) else y k)

/-- Project the sending wires `ℓ, …, 2ℓ − 1` onto the outcome `m`. -/
def projOut (P : QParty ℓ) (n : ℕ) (m : Msg (ℓ n)) (ψ : QState (2 * ℓ n + 1 + P.W n)) :
    QState (2 * ℓ n + 1 + P.W n) :=
  fun y => if ∀ i : Fin (ℓ n), y ⟨ℓ n + i, by omega⟩ = m i then ψ y else 0

/-- Project the output wire `2ℓ` onto the outcome `b`. -/
def projDec (P : QParty ℓ) (n : ℕ) (b : Bool) (ψ : QState (2 * ℓ n + 1 + P.W n)) :
    QState (2 * ℓ n + 1 + P.W n) :=
  fun y => if y ⟨2 * ℓ n, by omega⟩ = b then ψ y else 0

/-- The all-zero initial state. -/
def zero (P : QParty ℓ) (n : ℕ) : QState (2 * ℓ n + 1 + P.W n) := basisState fun _ => false

/-- The unnormalized state of a prover after it has received the verifier messages of `τ` and its
measurements gave its own messages of `τ`. -/
noncomputable def stateP (P : QParty ℓ) (O : Oracle) (n : ℕ) {R : ℕ}
    (τ : Transcript R (ℓ n)) : QState (2 * ℓ n + 1 + P.W n) :=
  (List.finRange R).foldl
    (fun ψ j => P.projOut n (τ j).2 ((P.circ n j).run O (P.xorIn n (τ j).1 ψ))) (P.zero n)

/-- The prover's likelihood `w_P(τ)`. -/
noncomputable def likP (P : QParty ℓ) (O : Oracle) (n : ℕ) {R : ℕ} (τ : Transcript R (ℓ n)) : ℝ :=
  ∑ y, ‖P.stateP O n τ y‖ ^ 2

/-- The message a verifier receives before its turn `j`: the prover's message of round `j − 1`
(nothing before turn `0`). -/
def incoming {R m : ℕ} (τ : Transcript R m) (j : ℕ) : Msg m :=
  if h : 0 < j ∧ j ≤ R then (τ ⟨j - 1, by omega⟩).2 else fun _ => false

/-- The unnormalized state of a verifier that has sent the messages of `τ` and output `b`: turns
`0, …, R − 1` produce its messages, turn `R` its output bit. -/
noncomputable def stateV (P : QParty ℓ) (O : Oracle) (n : ℕ) {R : ℕ}
    (τ : Transcript R (ℓ n)) (b : Bool) : QState (2 * ℓ n + 1 + P.W n) :=
  let ψ := (List.finRange R).foldl
    (fun ψ j => P.projOut n (τ j).1 ((P.circ n j).run O (P.xorIn n (incoming τ j) ψ))) (P.zero n)
  P.projDec n b ((P.circ n R).run O (P.xorIn n (incoming τ R) ψ))

/-- The verifier's likelihood `w_V(τ, b)`. -/
noncomputable def likV (P : QParty ℓ) (O : Oracle) (n : ℕ) {R : ℕ} (τ : Transcript R (ℓ n))
    (b : Bool) : ℝ :=
  ∑ y, ‖P.stateV O n τ b y‖ ^ 2

/-- Uniformity: a polynomial-time computable map, with no oracle access, sends `(1^n, 1^j)` to the
work-qubit count and the circuit of turn `j` at length `n` (§3.2.1, p. 12). -/
def Uniform (P : QParty ℓ) : Prop :=
  ∃ f : Str → Str, PolyTimeComputable f ∧
    ∀ n j : ℕ, f (tup [unary n, unary j]) = encNat (P.W n) ++ (P.circ n j).enc

/-- Polynomial size: the circuit of turn `j` at length `n` has at most `q(n + j)` instructions and
there are at most `q(n)` work qubits. -/
def PolyBounded (P : QParty ℓ) : Prop :=
  ∃ q : Polynomial ℕ, ∀ n j : ℕ, (P.circ n j).length ≤ q.eval (n + j) ∧ P.W n ≤ q.eval n

end QParty

end QAdvFew.PoQOracle


