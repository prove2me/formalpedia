-- Prove2me | Definitions.Def_QACParity
-- name    : QACParity
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:33:12.409426+00:00
-- url     : https://prove2.me/theorems/fbdd2a62-af5d-43f9-accb-70df4a5b2c23
-- statement:
--   This block sets up a model of quantum circuits of constant depth built from one-qubit unitaries and Toffoli gates of unbounded arity (QAC circuits), acting on N qubits whose computational basis states are bit strings Word N = Fin N → Fin 2. A gate is either a one-qubit 2×2 unitary applied at a qubit q, with matrix equal to the tensor product of that unitary at position q and the identity elsewhere, or a Toffoli gate with a finite control set and a target outside it, whose matrix maps y to the word that flips the target bit exactly when all controls are 1, and otherwise leaves y unchanged. A gate's support is its qubit, or the controls together with the target. A physical layer is a list of gates with pairwise disjoint supports, its matrix being the product of its gates; a circuit is a list of layers whose matrix is the product with the first layer acting first (rightmost). The input encoding inputWord places an n-bit string x in the first n positions and zeros in the remaining qubits, and parity x is the sum of its bits in Fin 2. successProbability(W, out, x) is the Born probability that measuring qubit out of the final state W applied to inputWord x yields parity x, summing over all values of the other qubits with no requirement that they be reset or clean. ParityStatement is a defined proposition, not an established theorem. It says that for every depth bound d, every real c ≥ 1 and every ε with 0 < ε ≤ 1/2, there is n₀ such that for all n ≥ n₀ and every total qubit count N with n ≤ N ≤ n^c, every circuit with at most d layers and every measured output qubit out fail to satisfy the following: success probability at least 1/2 + ε on every input x in Word n.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/QACParity.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/QACParity.lean; bytes 16..2639
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

/-- The literal measured-output, polynomial-total-qubit parity lower bound. -/
def ParityStatement : Prop :=
  ∀ (d : ℕ) (c ε : ℝ), 1 ≤ c → 0 < ε → ε ≤ 1 / 2 →
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ N : ℕ, n ≤ N → (N : ℝ) ≤ (n : ℝ) ^ c →
      ∀ layers : List (PhysicalLayer N), layers.length ≤ d →
        ∀ out : Fin N, ¬ (∀ x : Word n,
          1 / 2 + ε ≤ successProbability (physicalCircuitMatrix layers) out x)

end QAC



end
end OAI


