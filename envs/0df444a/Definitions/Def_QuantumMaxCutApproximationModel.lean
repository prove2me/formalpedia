-- Prove2me | Definitions.Def_QuantumMaxCutApproximationModel
-- name    : QuantumMaxCutApproximationModel
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-31T22:00:41.473756+00:00
-- url     : https://prove2.me/theorems/5eb039e8-9f4d-49a3-b69b-42404c4602a1
-- title:
--   Uniform quantum algorithms and Quantum Max-Cut approximation
-- statement:
--   A finite Quantum Max-Cut input has $n$ vertices and nonnegative rational weights $w_{ij}$ on pairs $i<j$. Its Hamiltonian is $H_G=\sum_{i<j}w_{ij}(I-\mathrm{SWAP}_{ij})$. A uniform classical procedure maps a fixed finite input encoding to an explicitly listed H/T/CNOT circuit. Every wire starts in $|0\rangle$; the first $n$ wires are graph qubits and the rest are retained ancillas. Polynomial time is defined by an actual Mathlib Turing-machine certificate for this generator. The approximation predicate requires enough output wires and expected output energy at least $\alpha$ times the energy of every normalized complex state on the graph. The ratio is exact in this fixed gate model and is compared against unrestricted quantum states. The bundle contains definitions only, without an approximation axiom or proof. Rational numerators and denominators are encoded in binary; graph order, output-register width, and gate wire indices are encoded in unary. Unary wire indices add only polynomial overhead because register width is already unary.
-- source:
--   Reviewed campaign model; Hamiltonian convention agrees with Anshu, Gosset, and Morenz (2020), Eq. (5): https://arxiv.org/html/2003.14394#S2

import Mathlib.Data.Complex.Basic
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Order
import Mathlib.Data.Fin.Embedding
import Mathlib.Logic.Equiv.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Computability.TuringMachine.Computable

/-!
Statement: there exists a polynomial-time quantum algorithm whose expected
output energy is at least α times the quantum optimum on every input graph.

The model is a uniform classical polynomial-time generator of finite H/T/CNOT
circuits, followed by execution of that circuit. Every wire starts in |0>.
The graph occupies the first n output wires; other wires are retained ancillas.
Input weights are nonnegative rationals, encoded in binary. The graph order,
output-register width, and gate wire indices are encoded in unary. Unary wire
indices add only polynomial overhead because the register width is already unary.

The ratio α is exact in this fixed gate model. Approximate universality does
not establish independence from the gate set at an exact sharp threshold.
The claim concerns expected quantum energy, not classical simulation or a
per-run probability of attaining that energy.

Convention: h_ij = I - SWAP_ij = (I - XX - YY - ZZ) / 2.
-/

noncomputable section
open scoped BigOperators
namespace QuantumMaxCut

abbrev Basis (n : ℕ) := Fin n → Bool
abbrev Wave (n : ℕ) := Basis n → ℂ
abbrev Edge (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}
abbrev Weights (n : ℕ) := Edge n → ℚ≥0

structure Input where
  n : ℕ
  weights : Weights n

inductive Gate (n : ℕ) where
  | h : Fin n → Gate n
  | t : Fin n → Gate n
  | cx (control target : Fin n) (distinct : control ≠ target) : Gate n

structure Circuit where
  qubits : ℕ
  gates : List (Gate qubits)

/-- Squared Hilbert-space norm, expressed as a finite sum over bitstrings. -/
def squaredNorm {n : ℕ} (ψ : Wave n) : ℝ :=
  ∑ x, Complex.normSq (ψ x)

/-- QMC energy on distinct graph-qubit positions in an ambient register. -/
def energy {n m : ℕ} (w : Weights n) (sites : Fin n ↪ Fin m) (ψ : Wave m) : ℝ :=
  ∑ e, (w e : ℝ) / 2 * ∑ x,
    Complex.normSq (ψ x - ψ (x ∘ Equiv.swap (sites e.val.1) (sites e.val.2)))

def applyGate {n : ℕ} : Gate n → Wave n → Wave n
  | .h q, ψ => fun x =>
      (ψ (Function.update x q false) +
        (if x q then (-1 : ℂ) else 1) * ψ (Function.update x q true)) /
        (Real.sqrt 2 : ℂ)
  | .t q, ψ => fun x =>
      (if x q then (1 + Complex.I) / (Real.sqrt 2 : ℂ) else 1) * ψ x
  | .cx c t _, ψ => fun x =>
      ψ (Function.update x t (if x c then !(x t) else x t))

/-- All wires, including ancillas, start in the all-zero computational basis state. -/
def Circuit.state (C : Circuit) : Wave C.qubits :=
  C.gates.foldl (fun ψ gate => applyGate gate ψ)
    (fun x => if x = (fun _ => false) then 1 else 0)

/-- A binary natural prefixed by the unary length of its binary representation. -/
def encodeNumber (k : ℕ) : List Bool :=
  let bits := Computability.encodeNat k
  List.replicate bits.length true ++ [false] ++ bits

/-- Unary graph order followed by binary rational weights in endpoint order. -/
def encodeInput (G : Input) : List Bool :=
  List.replicate G.n true ++ [false] ++
    (List.finRange G.n).flatMap (fun i =>
      (List.finRange G.n).flatMap (fun j =>
        if hij : i < j then
          let q := G.weights ⟨(i, j), hij⟩
          encodeNumber q.num ++ encodeNumber q.den
        else []))

def encodeGate {n : ℕ} : Gate n → List Bool
  | .h i => [false, false] ++ (List.replicate i.val true ++ [false])
  | .t i => [false, true] ++ (List.replicate i.val true ++ [false])
  | .cx i j _ => [true, false] ++ (List.replicate i.val true ++ [false]) ++
      (List.replicate j.val true ++ [false])

/-- Unary width ensures that polynomial output size bounds the ancilla count. -/
def encodeCircuit (C : Circuit) : List Bool :=
  List.replicate C.qubits true ++ [false] ++ C.gates.flatMap encodeGate

/-- A classical circuit generator; the circuit's execution is the quantum part. -/
abbrev Algorithm := Input → Circuit

/-- The controller generates the circuit in polynomial time in the fixed
binary input encoding. Its output explicitly lists every gate and wire. -/
def PolynomialTime (A : Algorithm) : Prop :=
  Nonempty (Turing.TM2ComputableInPolyTime encodeInput encodeCircuit A)

/-- An at-least-α guarantee for every graph and every normalized comparison state.
Quantifying over all states avoids defining a maximum or selecting an optimizer.
The output-width witness is fixed before the comparison state is quantified. -/
def ApproximationRatio (A : Algorithm) (α : ℝ) : Prop :=
  ∀ G : Input, ∃ h : G.n ≤ (A G).qubits,
    ∀ ψ : Wave G.n, squaredNorm ψ = 1 →
      α * energy G.weights (Function.Embedding.refl _) ψ ≤
        energy G.weights (Fin.castLEEmb h) (A G).state

end QuantumMaxCut


