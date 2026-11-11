-- Prove2me | Definitions.Def_EFI1PRS_Uniform_Computation
-- name    : EFI1PRS_Uniform_Computation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:34:33.032223+00:00
-- url     : https://prove2.me/theorems/afa6fd65-bd0f-49a6-a559-4092144c044f
-- title:
--   Finite descriptions, circuit execution and quantum-advice security
-- statement:
--   A preparation is a circuit with designated classical input wires, zero workspace, and an ordered embedding of its output wires. Gate symbols come from the finite universal vocabulary $H,S,T,X,Z,\mathrm{CNOT}$; the published circuit carrier supplies their actual matrix denotation. A length-prefixed unary description charges all symbols, wire positions, workspace, inputs and outputs. Actual preparation applies the circuit and takes the partial trace of the complement.
--
--   Uniformity requires a single polynomial-time classical Turing machine, on unary security parameter $1^\lambda$, to return that complete description. Length functions are separately required to be polynomial-time computable and polynomially bounded. A non-uniform advised preparation instead permits arbitrary polynomial-size circuit families and arbitrary mixed, normalized polynomial-qubit advice depending only on $\lambda$.
--
--   Computational indistinguishability quantifies over every admissible one-bit test with its own nonnegative negligible error. The error may depend on the entire test, including advice. Security parameters are positive integers; arbitrary finite prefixes are permitted.
--
--   Encoding conventions: wires are zero-based, tensor order is most significant first, and a zero-qubit space has one basis vector. Intermediate measurement and classical control are represented by coherent simulation with retained workspace and final discarding; the model-equivalence/compilation bridge is a solver obligation, not an additional primitive hypothesis.
-- source:
--   Rishabh Batra, STOC 2027 submission #273 (October 2026), EFI ⇔ 1PRS, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/273.pdf, §§2.1–2.2, Definitions 2.1–2.3, pp.7–9

import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_QAlgorithms_ClassicalStringComputability

/-! Batra, EFI ⇔ 1PRS, pinned October 2026 submission, §§2.1–2.2, pp.7–9.
Finite gate descriptions, actual circuit execution, uniform classical description generation,
and non-uniform mixed quantum advice. No oracle gates are admitted.
This is a candidate operational layer; model-equivalence and serialization bridges still
need to be audited before any mission theorem is stated over it. -/
namespace EFI1PRS.Uniform
open QAlgorithms
open scoped BigOperators Matrix ComplexConjugate

/-- The finite vocabulary H, S, T, X, Z, CNOT; Clifford gates are exact. -/
noncomputable def elementary (s : Fin 6) : Gate :=
  match s.val with
  | 0 => Gate.ofMatrix1 hadamard
  | 1 => Gate.ofMatrix1 phaseS
  | 2 => Gate.ofMatrix1 gateT
  | 3 => Gate.ofMatrix1 pauliX
  | 4 => Gate.ofMatrix1 pauliZ
  | _ => Gate.ofMatrix2 cnot

def gateVocabulary : Set Gate := Set.range elementary

/-- A finite symbol with an ordered injective placement, using the shared circuit carrier. -/
structure Instruction (n : ℕ) where
  symbol : Fin 6
  wires : Fin (elementary symbol).arity ↪ Fin n

noncomputable def Instruction.application {n : ℕ} (g : Instruction n) :
    GateApp gateVocabulary n :=
  ⟨elementary g.symbol, ⟨g.symbol, rfl⟩, g.wires⟩

/-- Classical inputs occupy the first `input` wires. Every other input wire is initialized
to zero. The output embedding records the retained wires, in output order. -/
structure Preparation (input output : ℕ) where
  work : ℕ
  instructions : List (Instruction (input + work))
  outputs : Fin output ↪ Fin (input + work)

noncomputable def Preparation.circuit {a b : ℕ} (p : Preparation a b) :
    Circuit gateVocabulary (a + p.work) := p.instructions.map Instruction.application

/-- Length-prefixed unary code for a list of naturals. Length zero has the code `[false]`. -/
def encodeNaturals (xs : List ℕ) : List Bool :=
  QAlgorithms.Complexity.encNat xs.length ++ xs.flatMap QAlgorithms.Complexity.encNat

noncomputable def Instruction.description {n : ℕ} (g : Instruction n) : List ℕ :=
  g.symbol.val :: List.ofFn (fun i => (g.wires i).val)

/-- Complete syntax description: input/output/workspace widths, gate count, all gate
symbols and all wire locations, followed by the retained output-wire list. -/
noncomputable def Preparation.description {a b : ℕ} (p : Preparation a b) : List Bool :=
  encodeNaturals [a, b, p.work, p.instructions.length] ++
    (p.instructions.flatMap fun g => encodeNaturals g.description) ++
    encodeNaturals (List.ofFn fun i => (p.outputs i).val)

noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

/-- Trace out precisely the complement of an ordered wire embedding. Off-diagonal
entries of the retained system are preserved. -/
def marginal {n k : ℕ} (w : Fin k ↪ Fin n)
    (ρ : Matrix (Qubits n) (Qubits n) ℂ) : Matrix (Qubits k) (Qubits k) ℂ :=
  fun x y => ∑ u : Qubits n, ∑ v : Qubits n,
    if u ∘ w = x ∧ v ∘ w = y ∧
        (∀ j, j ∉ Set.range w → u j = v j)
    then ρ u v else 0

/-- Actual unitary circuit execution followed by discarding the unretained wires. -/
def Preparation.run {a b : ℕ} (p : Preparation a b)
    (ρ : Matrix (Qubits a) (Qubits a) ℂ) : Matrix (Qubits b) (Qubits b) ℂ :=
  let U := p.circuit.unitary
  marginal p.outputs (U * withZeroAncillas ρ p.work * Uᴴ)

def Preparation.onKey {a b : ℕ} (p : Preparation a b) (x : Qubits a) :=
  p.run (pureDensity (ket x))

/-- A polynomial bound has constants chosen before the security parameter. -/
def PolynomiallyBounded (f : ℕ → ℕ) : Prop :=
  ∃ C d : ℕ, ∀ sec, 1 ≤ sec → f sec ≤ C * (sec + 1)^d

/-- Unary input and unary output are fixed, explicit string encodings. -/
def PolynomialLength (f : ℕ → ℕ) : Prop :=
  PolynomiallyBounded f ∧ ∃ machine : List Bool → List Bool,
    QAlgorithms.Complexity.PolyTimeComputable machine ∧
    ∀ sec, 1 ≤ sec → machine (QAlgorithms.Complexity.encNat sec) =
      QAlgorithms.Complexity.encNat (f sec)

/-- One actual deterministic polynomial-time TM generates the complete circuit
description from unary sec; the family has no advice argument. -/
def UniformPreparation {a b : ℕ → ℕ} (p : (sec : ℕ) → Preparation (a sec) (b sec)) : Prop :=
  PolynomialLength a ∧ PolynomialLength b ∧
  PolynomiallyBounded (fun sec => (p sec).work) ∧
  ∃ machine : List Bool → List Bool,
    QAlgorithms.Complexity.PolyTimeComputable machine ∧
    ∀ sec, 1 ≤ sec → machine (QAlgorithms.Complexity.encNat sec) = (p sec).description

/-- The advice is arbitrary, possibly mixed, and depends only on sec. It is placed after
the challenge, before zero workspace. No computability condition is imposed on this data. -/
structure AdvisedPreparation (a b : ℕ → ℕ) where
  adviceWidth : ℕ → ℕ
  advice : (sec : ℕ) → Matrix (Qubits (adviceWidth sec)) (Qubits (adviceWidth sec)) ℂ
  program : (sec : ℕ) → Preparation (a sec + adviceWidth sec) (b sec)

def AdvisedPreparation.IsPolynomial {a b : ℕ → ℕ} (A : AdvisedPreparation a b) : Prop :=
  PolynomiallyBounded a ∧ PolynomiallyBounded b ∧
  PolynomiallyBounded A.adviceWidth ∧
  PolynomiallyBounded (fun sec => (A.program sec).work) ∧
  PolynomiallyBounded (fun sec => (A.program sec).instructions.length) ∧
  ∀ sec, 1 ≤ sec → IsDensityMatrix (A.advice sec)

def tensorQubits {a b : ℕ}
    (ρ : Matrix (Qubits a) (Qubits a) ℂ)
    (σ : Matrix (Qubits b) (Qubits b) ℂ) :
    Matrix (Qubits (a+b)) (Qubits (a+b)) ℂ :=
  (Matrix.kronecker ρ σ).submatrix (qubitsAppendEquiv a b) (qubitsAppendEquiv a b)

def AdvisedPreparation.run {a b : ℕ → ℕ} (A : AdvisedPreparation a b) (sec : ℕ)
    (ρ : Matrix (Qubits (a sec)) (Qubits (a sec)) ℂ) :=
  (A.program sec).run (tensorQubits ρ (A.advice sec))

def AdvisedPreparation.acceptance {a : ℕ → ℕ}
    (A : AdvisedPreparation a (fun _ => 1)) (sec : ℕ)
    (ρ : Matrix (Qubits (a sec)) (Qubits (a sec)) ℂ) : ℝ :=
  (A.run sec ρ (fun _ => true) (fun _ => true)).re

/-- Finite prefixes are unrestricted. The nonnegative negligible bound may depend on
the entire adversary, including its advice. sec=0 lies outside the security domain. -/
def Negligible (ν : ℕ → ℝ) : Prop :=
  (∀ sec, 1 ≤ sec → 0 ≤ ν sec) ∧
  ∀ c : ℕ, 1 ≤ c → ∃ N : ℕ, ∀ sec, N ≤ sec → 1 ≤ sec → ν sec ≤ (sec : ℝ)^(-(c : ℤ))

def ComputationallyIndistinguishable {w : ℕ → ℕ}
    (ρ σ : (sec : ℕ) → Matrix (Qubits (w sec)) (Qubits (w sec)) ℂ) : Prop :=
  PolynomiallyBounded w ∧
  ∀ A : AdvisedPreparation w (fun _ => 1), A.IsPolynomial →
    ∃ ν : ℕ → ℝ, Negligible ν ∧ ∀ sec, 1 ≤ sec →
      |A.acceptance sec (ρ sec) - A.acceptance sec (σ sec)| ≤ ν sec

end
end EFI1PRS.Uniform


