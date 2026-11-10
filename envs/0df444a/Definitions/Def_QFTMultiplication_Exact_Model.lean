-- Prove2me | Definitions.Def_QFTMultiplication_Exact_Model
-- name    : QFTMultiplication_Exact_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T14:55:07.200667+00:00
-- url     : https://prove2.me/theorems/4d6cda7d-7288-408b-ae55-532930540498
-- title:
--   Restricted quantum gates, clean implementations, and multiplication families
-- statement:
--   The paper-specific interface builds on the published finite complex Euclidean states, Boolean DAGs, gate-list circuits, and positive-sign cyclic Fourier matrices. Registers are most significant bit first. Write $M(n)$ for the actual number of AND, OR, and NOT gates of a fixed family computing the full $2n$-bit product of two unsigned $n$-bit inputs. The multiplication hypothesis is an eventual family bound $M(n)\le Cn(\log_2 n)^\alpha$.
--
--   The basic quantum gates are $H$, CNOT, and $P(2\pi a/2^d)$ for integers $a$ and $d\ge1$. The extended set adds just one rotation $B(\theta)$. A clean implementation is a finite primitive-gate list whose matrix is unitary and satisfies
--   $$
--   U_c(\psi\otimes|0^a\rangle)=(T\psi)\otimes|0^a\rangle
--   $$
--   for every input vector $\psi$. The gate count is the list length and the auxiliary count is the number of physical wires beyond the designated registers.
--
--   The remaining definitions give the product phase, the Fourier-state answer-test inputs and sign, the zero-state reflection, the four-call Grover word, and the average success probability $p=2^{-q}\sum_x|\langle x|V|\phi_x\rangle|^2$ with $\theta_q=\arcsin(1/(2\sqrt p))$. These definitions share the source's signs, register order, and literal phase convention across all seven results.
-- source:
--   Chandrima Kayal, Rajat Mittal, Manaswi Paraashar, Nitin Saurabh, STOC 2027 submission #1075 (October 2026), pp. 2–3, 6–9, Equations (2)–(4), (7)–(8)

import Definitions.Def_QAlgorithms_Defs_Classical
import Definitions.Def_QAlgorithms_Defs_Fourier

set_option autoImplicit false

namespace QFTMultiplication.Exact

open QAlgorithms

noncomputable section

/-- Equation (3), p.3: integer-numerator dyadic phases; d is restricted in baseGates. -/
def dyadicPhase (a : ℤ) (d : ℕ) : Matrix Bool Bool ℂ :=
  Matrix.diagonal fun b =>
    if b then Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) / (2 : ℂ)^d) else 1

/-- Only H, CNOT, and the phases of Equation (3); neither SWAP nor Toffoli is primitive. -/
def baseGates : Set Gate :=
  {g | g = Gate.ofMatrix1 hadamard ∨ g = Gate.ofMatrix2 cnot ∨
    ∃ (a : ℤ) (d : ℕ), 1 ≤ d ∧ g = Gate.ofMatrix1 (dyadicPhase a d)}

/-- Equation (4), p.4. Rows/columns false,true; the upper-right entry has a minus sign. -/
def rotation (θ : ℝ) : Matrix Bool Bool ℂ :=
  fun i j => if i = j then (Real.cos θ : ℂ)
    else if i then (Real.sin θ : ℂ) else -(Real.sin θ : ℂ)

/-- One additional angle, fixed before input states. Its adjoint is not a new primitive. -/
def exactGates (θ : ℝ) : Set Gate :=
  baseGates ∪ {Gate.ofMatrix1 (rotation θ)}

abbrev Op (q : ℕ) := Matrix (Qubits q) (Qubits q) ℂ
abbrev Vec (q : ℕ) := EuclideanSpace ℂ (Qubits q)

/-- First n wires followed by m wires, in the published most-significant-bit-first order. -/
def joinVec {n m : ℕ} (u : Vec n) (v : Vec m) : Vec (n + m) :=
  WithLp.toLp 2 fun z =>
    u (fun i => z (Fin.castAdd m i)) * v (fun j => z (Fin.natAdd n j))

/-- ψ tensor |0^a⟩. No quotient by a scalar phase. -/
def cleanState {q : ℕ} (a : ℕ) (ψ : Vec q) : Vec (q + a) :=
  joinVec ψ (zeroKet a)

/-- Literal clean action on a specified input/output pair, including every temporary wire. -/
def CleanMaps {S : Set Gate} {q a : ℕ} (c : Circuit S (q + a))
    (u v : Vec q) : Prop :=
  act c.unitary (cleanState a u) = cleanState a v

/-- Physical circuit, distinct from its effective q-wire operator. Unitarity is asserted,
not inferred from the function name Circuit.unitary. All-vector equality follows the source
state equality by linearity and also covers the zero vector. -/
def CleanImplements {S : Set Gate} {q a : ℕ} (c : Circuit S (q + a))
    (U : Op q) : Prop :=
  c.unitary ∈ Matrix.unitaryGroup (Qubits (q + a)) ℂ ∧
    ∀ ψ : Vec q, CleanMaps c ψ (act U ψ)

/-- Equation (2): full 2n-bit unsigned multiplication, not the low n bits. -/
def MultCorrect (F : (n : ℕ) → BoolCircuit (n + n) (2 * n)) : Prop :=
  ∀ n : ℕ, (F n).WellFormed ∧
    ∀ A B : Qubits n,
      bitsToNat ((F n).eval (Fin.append A B)) = bitsToNat A * bitsToNat B

/-- Actual gate count of the fixed AND/OR/NOT DAG family. -/
def multSize (F : (n : ℕ) → BoolCircuit (n + n) (2 * n)) (n : ℕ) : ℕ :=
  (F n).size

/-- All logarithms in the source are binary. -/
def logTwo (x : ℝ) : ℝ := Real.log x / Real.log 2

/-- q (log₂ q)^α, with real α, including 0 < α < 1. -/
def exactBudget (α : ℝ) (q : ℕ) : ℝ :=
  q * (logTwo q) ^ α

/-- q (log₂ log₂ q)^(α+1), used only for q ≥ 64. -/
def halfBudget (α : ℝ) (q : ℕ) : ℝ :=
  q * (logTwo (logTwo q)) ^ (α + 1)

/-- Eventual multiplication bound; no uniform generation and no artificial linear lower
bound are premises. Finite exceptional lengths may be absorbed in later constants. -/
def MultBound (α : ℝ) (F : (n : ℕ) → BoolCircuit (n + n) (2 * n)) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
    (multSize F n : ℝ) ≤ C * exactBudget α n

/-- |ϕ_x⟩, using the cyclic positive-sign normalized QFT, p.2. -/
def fourierState (q : ℕ) (x : Qubits q) : Vec q :=
  act (qftQubits q) (ket x)

/-- Lemma 2.1's diagonal product phase. neg=false gives + and neg=true gives −. -/
def productPhase (q d : ℕ) (neg : Bool) : Op (q + q) :=
  Matrix.diagonal fun z =>
    Complex.exp ((if neg then (-1 : ℂ) else 1) * 2 * Real.pi * Complex.I *
      (bitsToNat (fun i : Fin q => z (Fin.castAdd q i)) : ℂ) *
      (bitsToNat (fun i : Fin q => z (Fin.natAdd q i)) : ℂ) / (2 : ℂ)^d)

/-- Input of Lemma 2.3 in register order I,O,E. -/
def answerInput (q : ℕ) (x y : Qubits q) (b : Bool) : Vec ((q + q) + 1) :=
  joinVec (joinVec (fourierState q x) (ket y)) (ket (fun _ : Fin 1 => b))

/-- Exact sign of Lemma 2.3, for both flag values. -/
def answerSign {q : ℕ} (x y : Qubits q) (b : Bool) : ℂ :=
  if x = y ∧ b = true then -1 else 1

/-- R₀=2|0⟩⟨0|−I, with +1 on zero and −1 on all other basis states. -/
def zeroReflection (m : ℕ) : Op m := reflAt (fun _ : Fin m => false)

/-- Calls in temporal order: D, U†, R₀, U. Each label occurs once. -/
def groverCalls : List (Fin 4) := [0, 1, 2, 3]

/-- Evaluation of the actual four-call word, with the first call rightmost. -/
def groverOperator {m : ℕ} (U D : Op m) : Op m :=
  (groverCalls.map (fun j => (![D, star U, zeroReflection m, U] : Fin 4 → Op m) j)).reverse.prod

/-- Equation (7): average success probability computed from V, not a free hypothesis. -/
def averageSuccess (q : ℕ) (V : Op q) : ℝ :=
  (1 / (2 : ℝ)^q) * ∑ x : Qubits q, prob (act V (fourierState q x)) x

/-- Equation (8). Half-error unitarity proves p≥3/4; it is not assumed separately. -/
def exactAngle (q : ℕ) (V : Op q) : ℝ :=
  Real.arcsin (1 / (2 * Real.sqrt (averageSuccess q V)))

end

end QFTMultiplication.Exact


