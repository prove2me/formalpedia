-- Prove2me | Definitions.Def_RegularParity
-- name    : RegularParity
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:33:12.649988+00:00
-- url     : https://prove2.me/theorems/5fe5cca5-5d1d-4861-8558-00f3862a3729
-- statement:
--   This block sets up a model of quantum circuits on N qubits built from one-qubit unitaries and Toffoli gates of unbounded arity, together with a success measure for computing parity. A Bit is an element of Fin 2, a Word N is a function from the N qubit positions to bits, and an Operator N is a complex matrix indexed by pairs of words, that is, a 2^N by 2^N matrix in the computational basis. tensorMatrix takes one 2x2 complex matrix per qubit and returns the tensor product, whose (x,y) entry is the product over i of the (x_i,y_i) entry of the i-th factor. A Gate is either a local gate, a unitary 2x2 matrix applied to one qubit q, or a Toffoli gate with a finite set of control qubits and a target qubit not among the controls. The support of a local gate is its qubit, and the support of a Toffoli gate is its controls together with its target. A Toffoli gate maps a basis word to the word with the target bit flipped if every control bit equals 1, and otherwise leaves it unchanged. The matrix of a local gate is the tensor product with the unitary at position q and the identity elsewhere, and the matrix of a Toffoli gate has entry 1 at (x,y) exactly when x is this Toffoli image of y, and 0 otherwise. A PhysicalLayer is a list of gates whose supports are pairwise disjoint, and its matrix is the product of the gate matrices in list order. The matrix of a circuit given by a list of layers is the product of the layer matrices in reverse list order, so the first layer acts first. inputWord embeds an n-bit word into N bits by copying it into the first n positions and setting all remaining positions to 0. parity of an n-bit word is the sum of its bits in Fin 2, that is, modulo 2. Finally, successProbability for an operator W, an output qubit out and an input word x is the sum, over all N-bit words y whose out-th bit equals parity(x), of the squared modulus of the entry of W at row y and column inputWord(x). This is the Born probability that measuring the output qubit gives the parity, summed over all values of the other qubits, with no requirement that they be returned to a clean state. These are only definitions, with no theorem or bound stated about them.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/RegularParity.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/RegularParity.lean; bytes 16..2163
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator

namespace QAC

abbrev Bit := Fin 2
abbrev Word (N : ℕ) := Fin N → Bit
abbrev Operator (N : ℕ) := Matrix (Word N) (Word N) ℂ
abbrev QubitOperator := Matrix Bit Bit ℂ

/-- Tensor product in the computational basis. -/
def tensorMatrix {N : ℕ} (a : Fin N → QubitOperator) : Operator N :=
  fun x y => ∏ i, a i (x i) (y i)

/-- A one-qubit unitary or an unbounded-arity Toffoli gate. -/
inductive Gate (N : ℕ) where
  | local (q : Fin N) (u : Matrix.unitaryGroup Bit ℂ)
  | toffoli (controls : Finset (Fin N)) (target : Fin N) (hne : target ∉ controls)

namespace Gate

def support {N : ℕ} : Gate N → Finset (Fin N)
  | .local q _ => {q}
  | .toffoli c t _ => insert t c

/-- A Toffoli flips its target iff all controls are one. -/
def toffoliWord {N : ℕ} (c : Finset (Fin N)) (t : Fin N) (x : Word N) : Word N :=
  if ∀ i ∈ c, x i = 1 then Function.update x t (1 - x t) else x

def matrix {N : ℕ} : Gate N → Operator N
  | .local q u => tensorMatrix fun i => if i = q then (u : QubitOperator) else 1
  | .toffoli c t _ => fun x y => if x = toffoliWord c t y then 1 else 0

end Gate

structure PhysicalLayer (N : ℕ) where
  gates : List (Gate N)
  disjoint : gates.Pairwise (fun A B => Disjoint A.support B.support)

def physicalLayerMatrix {N : ℕ} (L : PhysicalLayer N) : Operator N :=
  (L.gates.map Gate.matrix).prod

/-- Chronological order: the rightmost matrix acts first. -/
def physicalCircuitMatrix {N : ℕ} (layers : List (PhysicalLayer N)) : Operator N :=
  ((layers.map physicalLayerMatrix).reverse).prod

/-- The computational-basis input with the remaining qubits initialized to zero. -/
def inputWord {n N : ℕ} (x : Word n) : Word N :=
  fun i => if h : i.val < n then x ⟨i.val, h⟩ else 0

def parity {n : ℕ} (x : Word n) : Bit := ∑ i, x i

/-- Born probability, summing all final garbage with no cleanliness assumption. -/
def successProbability {n N : ℕ} (W : Operator N) (out : Fin N) (x : Word n) : ℝ :=
  ∑ y : Word N, if y out = parity x then Complex.normSq (W y (inputWord x)) else 0



end QAC
end
end OAI


