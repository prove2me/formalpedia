-- Prove2me | Definitions.Def_RandomStreamCI_CodeIntersection_Quantum
-- name    : RandomStreamCI_CodeIntersection_Quantum
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T20:28:52.669296+00:00
-- url     : https://prove2.me/theorems/a6fbf63e-17fe-41da-ba3a-0300e7504bc7
-- title:
--   Quantum stream execution on charged finite memory
-- statement:
--   A quantum program has an input-independent density matrix, current-item-controlled normalized Kraus channels on $q$ persistent qubits, an input-independent final channel and a normalized measurement with word-or-failure outcomes. Kraus application and measurement use the referenced general quantum interfaces. Every persistent classical record is encoded inside the same memory.
--
--   $$\Pr[\text{success}\mid\pi]=\mathbb E_H\sum_{c\text{ valid for }H}\operatorname{Tr}(M_c\rho_{H,\pi}).$$
--
--   A conservative workspace charge includes $q$ persistent qubits, up to $2q$ dilation qubits and twice the output label length, plus one bit. Arbitrary finite-dimensional operations are allowed with unrestricted time. This includes preparation and final readout workspace and has no oracle access after the pass, postselection, or correctness hypothesis.
-- source:
--   Bouland–Ding–Jain, Exponential quantum space advantage in random data streams, STOC 2027 submission #71, preprint dated 2026-11-02, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/71.pdf, SHA256 3fe1835efedc1b9f29103379085d28d84ab1057dc30c3e3f05a8dce9f536a797, Appendix A, Theorem 28 and proof, p. 28; Problem 1, p. 6

import Definitions.Def_RandomStreamCI_CodeIntersection_Stream
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Defs_Channel

noncomputable section

namespace RandomStreamCI.CodeIntersection

open scoped BigOperators
open QAlgorithms

attribute [local instance] Classical.propDecidable

/-- Finite-dimensional CPTP operation, via a complete Kraus representation.
At most D² Kraus operators suffice on D-dimensional memory. Its environment
is charged in QuantumProgram.memoryBits. No success promise is present. -/
structure FiniteChannel (q : ℕ) where
  count : ℕ
  kraus : Fin count → Matrix (Qubits q) (Qubits q) ℂ
  complete : QAlgorithms.IsKrausFamily kraus
  count_bound : count ≤ (2 ^ q)^2

def FiniteChannel.apply {q : ℕ} (E : FiniteChannel q)
    (ρ : Matrix (Qubits q) (Qubits q) ℂ) : Matrix (Qubits q) (Qubits q) ℂ :=
  QAlgorithms.krausApply E.kraus ρ

/-- Appendix A operational model: all persistent quantum and classical
registers live in q qubits, with extra bounded dilation/output workspace
charged below. Initial state and final measurement cannot depend on H or π.
Transitions see only time and the arriving classical item. -/
structure QuantumProgram (n : ℕ) (Alphabet : Type*) [Fintype Alphabet] where
  q : ℕ
  initial : Matrix (Qubits q) (Qubits q) ℂ
  initial_valid : IsDensityMatrix initial
  step : Fin (Fintype.card (Address n Alphabet)) → Input n Alphabet → FiniteChannel q
  finish : FiniteChannel q
  measurement : Option (Word n Alphabet) → Matrix (Qubits q) (Qubits q) ℂ
  measurement_valid : IsPOVM measurement

namespace QuantumProgram

variable {n : ℕ} {Alphabet : Type*} [Fintype Alphabet]

def state (Q : QuantumProgram n Alphabet) (ω : Sample n Alphabet) :
    ℕ → Matrix (Qubits Q.q) (Qubits Q.q) ℂ
  | 0 => Q.initial
  | t+1 => if h : t < Fintype.card (Address n Alphabet) then
      (Q.step ⟨t, h⟩ (streamItem ω ⟨t, h⟩)).apply (Q.state ω t)
    else Q.state ω t

def outcomeProbability (Q : QuantumProgram n Alphabet) (ω : Sample n Alphabet)
    (out : Option (Word n Alphabet)) : ℝ :=
  effectProb (Q.measurement out)
    (Q.finish.apply (Q.state ω (Fintype.card (Address n Alphabet))))

/-- The explicit failure outcome remains in the normalized POVM. Only
successful outputs are summed; no conditioning or postselection is used. -/
def successAtOrder (Q : QuantumProgram n Alphabet) (C : Finset (Word n Alphabet))
    (π : Order n Alphabet) : ℝ :=
  (Fintype.card (Oracle n Alphabet) : ℝ)⁻¹ *
    ∑ H : Oracle n Alphabet, ∑ out : Option (Word n Alphabet),
      if ValidOutput C H out then Q.outcomeProbability (H, π) out else 0

/-- Conservative total workspace: q persistent qubits; at most 2q qubits for
the D²-outcome Kraus environment, recycled at each step; and twice the output
label length for final measurement/readout. An output tape is not memory.
Preparation, finish, intermediate records and scratch are charged. -/
def memoryBits (Q : QuantumProgram n Alphabet) : ℕ :=
  3 * Q.q + 2 * ⌈log₂ (Fintype.card (Option (Word n Alphabet)))⌉₊ + 1

end QuantumProgram

end RandomStreamCI.CodeIntersection


