-- Prove2me | Definitions.Def_ExactQuantumFactoring
-- name    : ExactQuantumFactoring
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:10.96968+00:00
-- url     : https://prove2.me/theorems/08011f67-9372-4f8e-9f45-e90c1b34b1d2
-- statement:
--   The quantum circuit model has five primitive gates: NOT, controlled NOT, Toffoli, Hadamard, and the phase gate diag(1,i). Allowing each primitive its conjugate-transpose inverse and at most one additional control gives twenty gate names, each acting on at most four distinct wires. Hadamard has entries (−1)^(ab)/√2 for Boolean row and column indices a,b; controlled gates act as the identity when their added control is zero. Instructions act as the identity on unselected wires, and a circuit applies its finite instruction list in order to complex amplitudes on bit strings. An input integer N occupies the first ℓ wires, least significant bit first, with every other wire initially zero. Put n=max(128,ℓ). The output is a list of n integers, each read from n consecutive wires immediately after the input; reads beyond the available wires return zero. A correct encoding consists of all prime factors of N in nondecreasing order, including multiplicities, followed by zeros to reach length n: formally, the prime list has product N and length at most n. Correct-output probability is the sum of squared absolute amplitudes over basis outputs with this encoding. Circuit descriptions encode the width, instruction count, primitive codes, and wire addresses using unary natural numbers terminated by zero, together with the inverse and control bits. A circuit family is uniform when one polynomial-time classical Turing-machine generator produces this description from the unary input length alone, with every stack alphabet finite. Polynomial resources means that one polynomial with natural coefficients bounds both the number of qubits and instructions for every input length. MainTheorem is the defined proposition that there exists a uniform family with polynomial resources such that, for every integer N≥2 of binary length ℓ, its circuit has at least ℓ+n² qubits and correct-output probability exactly one.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/ExactQuantumFactoring.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/ExactQuantumFactoring.lean; bytes 16..5939
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI



namespace ExactQuantumFactoring

open scoped BigOperators

/-- The five primitive gates exactly as in Section 2. -/
inductive Primitive where
  | not | cnot | toffoli | hadamard | phase
  deriving DecidableEq

def Primitive.arity : Primitive → ℕ
  | .not | .hadamard | .phase => 1
  | .cnot => 2
  | .toffoli => 3

def Primitive.code : Primitive → ℕ
  | .not => 0 | .cnot => 1 | .toffoli => 2 | .hadamard => 3 | .phase => 4

/-- An inverse and/or one added control. This is a fixed set of 20 gate names,
not an unbounded-control or arbitrary-angle gate model. -/
structure Gate where
  primitive : Primitive
  inverse : Bool
  controlled : Bool
  deriving DecidableEq

def Gate.arity (g : Gate) : ℕ := g.primitive.arity + if g.controlled then 1 else 0

/-- Matrix entries are indexed by lists in wire order (row first, column second).
Entries on ill-sized lists are irrelevant and set to zero. -/
noncomputable def Primitive.matrix : Primitive → List Bool → List Bool → ℂ
  | .not, [a], [b] => if a = !b then 1 else 0
  | .cnot, [a,b], [c,d] => if a = c ∧ b = Bool.xor c d then 1 else 0
  | .toffoli, [a,b,c], [d,e,f] =>
      if a = d ∧ b = e ∧ c = Bool.xor f (d && e) then 1 else 0
  | .hadamard, [a], [b] =>
      (if a && b then -1 else 1) / (Real.sqrt 2 : ℂ)
  | .phase, [a], [b] => if a = b then (if b then Complex.I else 1) else 0
  | _, _, _ => 0

noncomputable def Gate.baseMatrix (g : Gate) (a b : List Bool) : ℂ :=
  if g.inverse then star (g.primitive.matrix b a) else g.primitive.matrix a b

noncomputable def Gate.matrix (g : Gate) (a b : List Bool) : ℂ :=
  if g.controlled then
    match a, b with
    | false :: a', false :: b' => if a' = b' then 1 else 0
    | true :: a', true :: b' => g.baseMatrix a' b'
    | _, _ => 0
  else g.baseMatrix a b

/-- A primitive is placed on distinct actual wires, with no operation of
unbounded arity hidden in a circuit instruction. -/
structure Instruction (q : ℕ) where
  gate : Gate
  wire : Fin gate.arity → Fin q
  distinct : Function.Injective wire

abbrev Basis (q : ℕ) := Fin q → Bool
abbrev State (q : ℕ) := Basis q → ℂ

noncomputable def Instruction.matrix {q : ℕ} (o : Instruction q) :
    Matrix (Basis q) (Basis q) ℂ := by
  classical
  exact fun a b =>
    if ∀ i : Fin q, (∀ j, o.wire j ≠ i) → a i = b i then
      o.gate.matrix (List.ofFn (a ∘ o.wire)) (List.ofFn (b ∘ o.wire))
    else 0

structure Circuit where
  qubits : ℕ
  instructions : List (Instruction qubits)

noncomputable def Circuit.apply (c : Circuit) (ψ : State c.qubits) : State c.qubits :=
  c.instructions.foldl (fun v o => o.matrix.mulVec v) ψ

/-- Input wires are first, least significant bit first; all other wires start zero. -/
def inputBasis (q ℓ N : ℕ) : Basis q :=
  fun i => if i.val < ℓ then N.testBit i.val else false

noncomputable def Circuit.outputState (c : Circuit) (ℓ N : ℕ) : State c.qubits := by
  classical
  exact c.apply (fun x => if x = inputBasis c.qubits ℓ N then 1 else 0)

/-- The cutoff and padding are the standing parameters in Section 2. -/
def paddedLength (ℓ : ℕ) : ℕ := max 128 ℓ

def readBit {q : ℕ} (x : Basis q) (i : ℕ) : Bool :=
  if h : i < q then x ⟨i,h⟩ else false

/-- n entries of n bits each, in the n² wires immediately after the input. -/
def outputList {q : ℕ} (ℓ : ℕ) (x : Basis q) : List ℕ :=
  let n := paddedLength ℓ
  List.ofFn (fun a : Fin n =>
    ∑ j ∈ Finset.range n, if readBit x (ℓ + a.val * n + j) then 2^j else 0)

/-- Complete nondecreasing prime factorization, multiplicities included,
padded by zeros, as in Section 6. There is no primality oracle in the circuit. -/
def CorrectEncoding (N n : ℕ) (xs : List ℕ) : Prop :=
  ∃ ps : List ℕ, (∀ p ∈ ps, Nat.Prime p) ∧ ps.Pairwise (· ≤ ·) ∧
    ps.prod = N ∧ ps.length ≤ n ∧ xs = ps ++ List.replicate (n - ps.length) 0

/-- Unnormalized Born sum on correct outputs; success is exactly one,
not positivity, postselection, or a limiting high probability. -/
noncomputable def Circuit.correctProbability (c : Circuit) (ℓ N : ℕ) : ℝ := by
  classical
  exact ∑ x : Basis c.qubits,
    if CorrectEncoding N (paddedLength ℓ) (outputList ℓ x) then
      Complex.normSq (c.outputState ℓ N x) else 0

/-- Unary natural words with delimiters make the circuit description explicit.
Unary wire addresses cause at most polynomial overhead when width is polynomial. -/
def natWord (k : ℕ) : List Bool := List.replicate k true ++ [false]

def Instruction.encode {q : ℕ} (o : Instruction q) : List Bool :=
  natWord o.gate.primitive.code ++ [o.gate.inverse, o.gate.controlled] ++
    (List.ofFn (fun i => o.wire i |>.val)).flatMap natWord

def Circuit.encode (c : Circuit) : List Bool :=
  natWord c.qubits ++ natWord c.instructions.length ++
    c.instructions.flatMap Instruction.encode

/-- A single finite-alphabet classical generator receives only the INPUT LENGTH.
All stack alphabets, states and labels are finite: no large-integer unit-cost
oracle is hidden in TM2 push/branch functions. -/
def Uniform (family : ℕ → Circuit) : Prop :=
  ∃ generator : Turing.TM2ComputableInPolyTime
      (fun ℓ => List.replicate ℓ true) Circuit.encode family,
    ∀ k, Finite (generator.tm.Γ k)

def PolynomialResources (family : ℕ → Circuit) : Prop :=
  ∃ bound : Polynomial ℕ, ∀ ℓ,
    (family ℓ).qubits ≤ bound.eval ℓ ∧
    (family ℓ).instructions.length ≤ bound.eval ℓ

/-- Literal main endpoint: one length-uniform family, exact output for EVERY
binary integer N≥2, and worst-case polynomial gates AND qubits. -/
def MainTheorem : Prop :=
  ∃ family : ℕ → Circuit, Uniform family ∧ PolynomialResources family ∧
    ∀ (ℓ N : ℕ), 2 ≤ N → N.size = ℓ →
      ℓ + (paddedLength ℓ)^2 ≤ (family ℓ).qubits ∧
      (family ℓ).correctProbability ℓ N = 1



end ExactQuantumFactoring
end OAI


