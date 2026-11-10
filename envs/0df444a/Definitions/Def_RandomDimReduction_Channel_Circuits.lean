-- Prove2me | Definitions.Def_RandomDimReduction_Channel_Circuits
-- name    : RandomDimReduction_Channel_Circuits
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T11:25:19.722057+00:00
-- url     : https://prove2.me/theorems/25267816-b73f-4f5b-b010-edbca40e3232
-- title:
--   Costed qubit circuits, channel semantics and fixed binary encodings
-- statement:
--   A circuit has a finite number of qubit wires, a list of unitary one- or two-qubit gates on named wires, ordered input wires and distinct designated output wires. All ancillary wires start at zero; non-output wires are traced out after applying the product of lifted gates. Its size is the number of gates plus the number of wires. Qudits are encoded in $\lceil\log_2d\rceil$ qubits per copy; dimension one uses zero qubits. The Schur encoding stores the partition row lengths and the Specht and Weyl basis indices in fixed binary fields. Neither encoding depends on the error tolerance. A polynomial bound is represented by
--   $$ c\bigl(n+\log d+\log(1/\varepsilon)+2\bigr)^K. $$
--   This gives actual mixed-output channel semantics and a counted elementary-gate implementation, rather than an asserted cost attached to a matrix.
-- source:
--   Angus Lowe, Xinyu Tan, Random dimension reduction and learning symmetric properties of quantum states, STOC 2027 submission #994 (October 2026), Theorems 1.1 and 5.1, pp.2,15–16; elementary-gate and encoding conventions. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/994.pdf

import Definitions.Def_RandomDimReduction_Channel_Schur
import Definitions.Def_RandomDimReduction_Channel_Diamond

set_option autoImplicit false

noncomputable section
open Matrix
open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise ENNReal

namespace RandomDimReduction.Channel
attribute [local instance] Classical.propDecidable Classical.decEq

abbrev Bits (q : ℕ) := Fin q → Bool

/-- Elementary gates act on one or two named qubits, never on a growing register. -/
inductive Gate (w : ℕ) where
  | one (i : Fin w) (U : Matrix.unitaryGroup Bool ℂ)
  | two (i j : Fin w) (distinct : i ≠ j) (U : Matrix.unitaryGroup (Bool × Bool) ℂ)

/-- Lift an elementary gate by identity on all other wires. -/
def gateMatrix {w : ℕ} : Gate w → Op (Bits w)
  | .one i U => fun x y =>
      if ∀ t, t ≠ i → x t = y t then (U : Op Bool) (x i) (y i) else 0
  | .two i j _ U => fun x y =>
      if ∀ t, t ≠ i → t ≠ j → x t = y t then
        (U : Op (Bool × Bool)) (x i, x j) (y i, y j) else 0

/-- An actual finite circuit, with input wires first and designated output wires.
Every remaining input wire is a fresh zero ancilla; all non-output wires are discarded. -/
structure Circuit (a b : ℕ) where
  wires : ℕ
  input_fits : a ≤ wires
  output : Fin b ↪ Fin wires
  gates : List (Gate wires)

/-- Both qubits and gates are charged, excluding unbounded free ancillas. -/
def circuitSize {a b : ℕ} (C : Circuit a b) : ℕ := C.wires + C.gates.length

def circuitUnitary {a b : ℕ} (C : Circuit a b) : Op (Bits C.wires) :=
  C.gates.foldl (fun U g => gateMatrix g * U) 1

/-- Adjoin ancillas in |0…0⟩, as a rectangular matrix. -/
def inputEmbedding {a b : ℕ} (C : Circuit a b) : Matrix (Bits C.wires) (Bits a) ℂ :=
  fun x y => if (∀ i : Fin a, x ⟨i.val, lt_of_lt_of_le i.isLt C.input_fits⟩ = y i) ∧
    (∀ i : Fin C.wires, a ≤ i.val → x i = false) then 1 else 0

/-- Partial trace onto the designated, ordered output wires. -/
def discard {a b : ℕ} (C : Circuit a b) (Y : Op (Bits C.wires)) : Op (Bits b) :=
  fun z z' => ∑ x : Bits C.wires, ∑ y : Bits C.wires,
    if (∀ i, x (C.output i) = z i) ∧ (∀ i, y (C.output i) = z' i) ∧
      (∀ t, (∀ i, C.output i ≠ t) → x t = y t) then Y x y else 0

/-- Mixed-output channel semantics, not a pure-vector circuit certificate. -/
def circuitChannel {a b : ℕ} (C : Circuit a b) (X : Op (Bits a)) : Op (Bits b) :=
  let V := circuitUnitary C * inputEmbedding C
  discard C (V * X * Vᴴ)

/-- Binary width, including width zero for a one-dimensional register. -/
def qubits (d : ℕ) : ℕ := Nat.clog 2 d

def inputQubits (n d : ℕ) : ℕ := n * qubits d

/-- Little-endian binary expansion within each tensor factor. -/
def encodedWord {n d : ℕ} (x : Word n d) : Bits (inputQubits n d) :=
  fun t => if h : qubits d = 0 then false else
    Nat.testBit (x ⟨t.val / qubits d, by
      have hq : 0 < qubits d := Nat.pos_of_ne_zero h
      exact (Nat.div_lt_iff_lt_mul hq).mpr t.isLt⟩).val (t.val % qubits d)

/-- |i₁,…,iₙ⟩ ↦ |bin(i₁),…,bin(iₙ)⟩. -/
def encodingMatrix (n d : ℕ) : Matrix (Bits (inputQubits n d)) (Word n d) ℂ :=
  fun z x => if z = encodedWord x then 1 else 0

def encode (n d : ℕ) (X : Op (Word n d)) : Op (Bits (inputQubits n d)) :=
  encodingMatrix n d * X * (encodingMatrix n d)ᴴ

/-- Fixed tuple encoding: n row lengths, a Specht basis index, a Weyl basis index.
The widths are chosen before ε; p < n!, q ≤ d^n. -/
def labelQubits (n : ℕ) : ℕ := n * qubits (n + 1)
def schurQubits (n d : ℕ) : ℕ :=
  labelQubits n + qubits n.factorial + inputQubits n d

def encodedSchur {n d : ℕ} (x : SchurIndex n d) : Bits (schurQubits n d) :=
  fun t => if t.val < labelQubits n then
    Nat.testBit (x.1.val.rowLen (t.val / qubits (n+1))) (t.val % qubits (n+1))
  else if t.val < labelQubits n + qubits n.factorial then
    Nat.testBit x.2.1.val (t.val - labelQubits n)
  else Nat.testBit x.2.2.val (t.val - (labelQubits n + qubits n.factorial))

def schurEncodingMatrix (n d : ℕ) :
    Matrix (Bits (schurQubits n d)) (SchurIndex n d) ℂ :=
  fun z x => if z = encodedSchur x then 1 else 0

def encodeSchur (n d : ℕ) (X : Op (SchurIndex n d)) : Op (Bits (schurQubits n d)) :=
  schurEncodingMatrix n d * X * (schurEncodingMatrix n d)ᴴ

/-- One global polynomial bound, with natural logarithms (base only changes constants). -/
def polyBound (c : ℝ) (K n d : ℕ) (eps : ℝ) : ℝ :=
  c * ((n : ℝ) + Real.log d + Real.log (1 / eps) + 2) ^ K

end RandomDimReduction.Channel


