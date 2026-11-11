-- Prove2me | Definitions.Def_QuantumAdviceAmplification_Separation_classes
-- name    : QuantumAdviceAmplification_Separation_classes
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T06:01:54.211791+00:00
-- url     : https://prove2.me/theorems/66f1c483-0e67-4c37-b18a-639535807eab
-- title:
--   Exact-length randomized classical and mixed quantum advice classes
-- statement:
--   For positive lengths $n$, randomized classical advice is one distribution $D_n$ on exactly $m(n)$ bits. One fixed machine must have error at most $\varepsilon(n)$ on every length-$n$ input and halt in at most $Ct(n)$ transitions on every advice string in the support, with one $C$ for all lengths, inputs and sampled advice.
--
--   Quantum advice is one arbitrary density matrix $\rho_n$ on exactly $m(n)$ qubits. The gate alphabet is fixed and finite, its gates are unitary and universal, and it contains exact NOT and Toffoli. A finite machine, given $(1^n,\operatorname{bin}(m(n)))$, prints the complete structural description of the circuit, including binary wire addresses. Both generator time and the actual gate count are at most $Ct(n)$. Execution starts in $|x\rangle\langle x|\otimes\rho_n\otimes|0\cdots0\rangle\langle0\cdots0|$ and measures a designated output qubit.
--   $$\mathsf P_\varepsilon/r_m=\bigcup_{c\ge1}\mathsf{DTIME}(n^c)_\varepsilon/r_m,\qquad\mathsf{BQP}_\varepsilon/q_m=\bigcup_{c\ge1}\mathsf{BQTIME}(n^c)_\varepsilon/q_m.$$
--   The model makes no computability requirement on advice preparation, $m$, or the error function. It also defines $L_R^{(k)}$ using one-based lexicographic rank, ignoring the empty word in class obligations.
-- source:
--   Shih-Han Hung, Han-Hsuan Lin, STOC 2027 submission #1297 (October 2026), pp.6–7, Definition 2.6 and Eq. (45) on p.14

import Definitions.Def_QuantumAdviceAmplification_Separation_machine
import Definitions.Def_QAlgorithms_Defs_Circuit
set_option autoImplicit false
noncomputable section

namespace QuantumAdviceAmplification.Separation

open Classical
open scoped ComplexConjugate

/-- A fixed finite alphabet of unitary gates, containing exact NOT and Toffoli.
The gate matrices are fixed once, never selected by the input length or the generator. -/
def toffoliGate : QAlgorithms.Gate :=
  ⟨3, fun y x => if y 0 = x 0 ∧ y 1 = x 1 ∧
    y 2 = xor (x 2) (x 0 && x 1) then 1 else 0⟩

structure GateAlphabet where
  size : ℕ
  gates : Fin size → QAlgorithms.Gate
  unitary : ∀ i, (gates i).IsUnitary
  universal : QAlgorithms.IsUniversal (Set.range gates)
  notIndex : Fin size
  notGate : gates notIndex = QAlgorithms.Gate.ofMatrix1 QAlgorithms.pauliX
  toffoliIndex : Fin size
  toffoli : gates toffoliIndex = toffoliGate

structure Instruction (G : GateAlphabet) (w : ℕ) where
  name : Fin G.size
  wires : Fin (G.gates name).arity ↪ Fin w

structure CircuitDescription (G : GateAlphabet) (n m : ℕ) where
  ancillas : ℕ
  output : Fin (n + m + ancillas)
  operations : List (Instruction G (n + m + ancillas))

/-- Binary, self-delimiting integer code: a unary width, then the binary value.
It has O(log(v+2)) bits; large advice-wire counts are not printed in unary. -/
def encodeNat (v : ℕ) : List Bool :=
  List.replicate (Nat.log 2 v + 1) false ++ [true] ++ bin v

def encodeInstruction {G : GateAlphabet} {w : ℕ} (i : Instruction G w) : List Bool :=
  encodeNat i.name.val ++ (List.ofFn fun j => encodeNat (i.wires j).val).flatten

/-- Complete structural serialization. The known n,m determine the wire range;
the gate name determines its arity. No matrix entries or hidden circuit data are free. -/
def encodeCircuit {G : GateAlphabet} {n m : ℕ} (C : CircuitDescription G n m) : List Bool :=
  encodeNat C.ancillas ++ encodeNat C.output.val ++ encodeNat C.operations.length ++
    (C.operations.map encodeInstruction).flatten

def circuit {G : GateAlphabet} {n m : ℕ} (C : CircuitDescription G n m) :
    QAlgorithms.Circuit (Set.range G.gates) (n + m + C.ancillas) :=
  C.operations.map fun i => ⟨G.gates i.name, ⟨i.name, rfl⟩, i.wires⟩

abbrev Density (m : ℕ) :=
  {ρ : Matrix (Bits m) (Bits m) ℂ // QAlgorithms.IsDensityMatrix ρ}

/-- |x><x| tensor rho tensor |0...0><0...0|, in input/advice/ancilla wire order. -/
def initialDensity {n m : ℕ} (x : Bits n) (ρ : Density m) (a : ℕ) :
    Matrix (Bits (n + m + a)) (Bits (n + m + a)) ℂ :=
  fun y z =>
    if (∀ i : Fin n, y ⟨i.val, by omega⟩ = x i ∧ z ⟨i.val, by omega⟩ = x i) ∧
       (∀ i : Fin a, y ⟨n + m + i.val, by omega⟩ = false ∧
         z ⟨n + m + i.val, by omega⟩ = false) then
      ρ.val (fun i => y ⟨n + i.val, by omega⟩) (fun i => z ⟨n + i.val, by omega⟩)
    else 0

def outputProbability {G : GateAlphabet} {n m : ℕ} (C : CircuitDescription G n m)
    (x : Bits n) (ρ : Density m) (b : Bool) : ℝ :=
  let U := (circuit C).unitary
  let σ := U * initialDensity x ρ C.ancillas * U.conjTranspose
  ∑ y : Bits (n + m + C.ancillas), if y C.output = b then (σ y y).re else 0

/-- Finite probability over actual halting traces; a separate support time condition
excludes nontermination on every sampled advice string. -/
def classicalError (M : Machine) {n m : ℕ} (x : Bits n) (D : PMF (Bits m)) (b : Bool) : ℝ :=
  ∑ a : Bits m, (D a).toReal * if Outputs M (vectorList x) (vectorList a) (!b) then 1 else 0

def DTIME (t m : Length → ℕ) (ε : Length → ℝ) : Set Language :=
  {L | ∃ (M : Machine) (D : ∀ n : Length, PMF (Bits (m n))) (C : ℕ), 0 < C ∧
    ∀ (n : Length) (x : Bits n.val),
      classicalError M x (D n) (L (vectorList x)) ≤ ε n ∧
      ∀ a : Bits (m n), D n a ≠ 0 →
        ∃ (s : ℕ) (b : Bool), s ≤ C * t n ∧
          (run M (vectorList x) (vectorList a) s).answer = some b}

/-- Generator input contains unary n and the supplied binary value of m(n).
The one generator M has no access to the state family or to the input string x. -/
def BQTIME (G : GateAlphabet) (t m : Length → ℕ) (ε : Length → ℝ) : Set Language :=
  {L | ∃ (M : Machine) (Q : ∀ n : Length, CircuitDescription G n.val (m n))
      (ρ : ∀ n : Length, Density (m n)) (C : ℕ), 0 < C ∧
    ∀ n : Length,
      PrintsWithin M (List.replicate n.val true ++ [false] ++ bin (m n))
        (encodeCircuit (Q n)) (C * t n) ∧
      (Q n).operations.length ≤ C * t n ∧
      ∀ x : Bits n.val, outputProbability (Q n) x (ρ n) (!(L (vectorList x))) ≤ ε n}

def PAdvice (m : Length → ℕ) (ε : Length → ℝ) : Set Language :=
  {L | ∃ c : ℕ, 0 < c ∧ L ∈ DTIME (fun n => n.val ^ c) m ε}

def BQPAdvice (G : GateAlphabet) (m : Length → ℕ) (ε : Length → ℝ) : Set Language :=
  {L | ∃ c : ℕ, 0 < c ∧ L ∈ BQTIME G (fun n => n.val ^ c) m ε}

/-- Source equation (45); length zero is outside all class obligations. -/
def restrictedLanguage (k : Length → ℕ) (R : Language) (x : List Bool) : Bool :=
  if h : 0 < x.length then decide (rank x ≤ k ⟨x.length, h⟩) && R x else false

end QuantumAdviceAmplification.Separation


