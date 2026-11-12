-- Prove2me | Definitions.Def_QuantumScalingMWPM_QLiquidationist_Machine
-- name    : QuantumScalingMWPM_QLiquidationist_Machine
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T07:11:41.163628+00:00
-- url     : https://prove2.me/theorems/82888f58-103b-4732-a3dc-92915ded1c21
-- title:
--   The QRAM model: a word RAM with quantum subroutine calls, Born-rule runs and cost
-- statement:
--   This definition fixes the model of computation of §1.1 (pp. 2–3): a classical controller with a shared memory that it reads and writes in one step, and quantum subroutine calls that may read that memory coherently through the access oracle $O_A:|i\rangle|0\rangle\mapsto|i\rangle|A[i]\rangle$.
--
--   1. **Controller.** A program is a finite list of instructions fixed before the input. The registers $R[0],R[1],\dots$ hold integers and form the shared memory. Loading a constant, copying, $+,-,\times$, integer division and remainder, a conditional jump, indirect load and store, and halting each cost one unit.
--   2. **Word length.** A run records the largest absolute value $\mathrm{peak}$ ever held by a register. Algorithmic statements require $\mathrm{peak}<2^{\beta}$ with $\beta=\mathrm{width}\cdot(1+\lfloor\log_2(2+|I|+\sum_j|I_j|)\rfloor)$, where the constant $\mathrm{width}$ is fixed with the program. Words therefore have $O(\log(n+m+W))$ bits, and unit-cost arithmetic on huge integers is excluded.
--   3. **Quantum calls.** The instruction `qcall a` runs the circuit whose description the controller has written in its registers: $q$ qubits and $L$ operations, each a Hadamard or $T$ gate, a CNOT, a QRAM query $|j\rangle|d\rangle\mapsto|j\rangle|d\oplus(R[u+j]\bmod 2^b)\rangle$ on $b$-qubit words that reads the controller's *current* registers, or a reversible word operation on $b\le\beta$ qubits (addition, subtraction, equality and comparison tests, and product, quotient and remainder XORed into a third word). The circuit starts in $|0^q\rangle$ and all qubits are measured in the computational basis. The outcome is written back into the registers. The call costs $1+5L+2q$.
--   4. **Runs.** $\mathrm{succProb}(P,\beta,t,s,E)$ is the probability, under the Born rule at every quantum call, that the run from $s$ halts within $t$ steps in a state satisfying $E$. Every step costs at least one unit.
--   5. **Input and output.** The input list $I$ is stored as $R[0]=|I|$, $R[i+1]=I[i]$. The output is the list $R[1],\dots,R[R[0]]$.
--
--   The module also defines straight-line *predicate programs*. Their instructions are constant, copy, $+,-,\times,\div,\bmod$, a memory load, equality, comparison, and, and not. A predicate program computes a predicate $f(x)$ on a memory list. These are the predicates "computable in constant time" of Lemma 1.
--
--   This model is shared by Theorem 4 and Lemma 1. Every classical update to memory is charged, and so is every gate, query and qubit of a quantum call.
--
--   **Formalization Note** Gates, the embedding of a one-qubit gate and Born-rule probabilities come from the published `QAlgorithms_Defs_Circuit`. The published `CongruencyTU_Machine` is not imported: its oracle is a deterministic function, so it cannot express a quantum call. A malformed operation acts as the identity.
-- source:
--   Kourosh Mirsohi, Sandy Irani, Michael Goodrich, STOC 2027 submission #842 (October 2026), §1.1, pp. 2–3 (QRAM model); abstract p. 1; Lemma 1, p. 11 (constant-time predicates); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/842.pdf

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Circuit

/-!
# The QRAM model of §1.1 (pp. 2–3): a unit-cost word RAM with quantum subroutine calls

Kourosh Mirsohi, Sandy Irani, Michael Goodrich, *A Quantum Scaling Algorithm for Maximum-Weight
Perfect Matching in General Graphs*, STOC 2027 submission #842 (October 2026), §1.1, pp. 2–3.

The paper's model: a shared memory `A[0], A[1], …` that the classical controller reads and writes
"in one step", a unitary access oracle `O_A : |i⟩|0⟩ ↦ |i⟩|A[i]⟩` usable on address registers in
superposition, and "updates to A … performed sequentially with classical control between quantum
subroutine calls". Every classical step and every update is charged (abstract, p. 1).

**Formalization Note.**
* *Classical controller.* A program is a finite list of instructions fixed before the input.
  Registers are indexed by `ℕ` and hold integers; this register file is the shared memory. Each
  instruction costs one unit: constant, copy, `+ − × ÷ mod` (Lean's `Int.ediv`/`Int.emod`), branch
  on `≤`, indirect load and store (a negative address reads/writes register `0`), and `halt`.
* *Word size.* A run records `peak`, the largest absolute value ever held by a register. Statements
  require `peak < 2 ^ wordBits width I` with
  `wordBits width I = width · (1 + log₂(2 + |I| + Σ|I_j|))`, `width` fixed with the program: words of
  `O(log(n + m + W))` bits, so unit-cost arithmetic cannot exploit huge integers.
* *Quantum call.* `qcall a` reads a circuit description from the registers: `R[a] = q` qubits,
  `R[a+1] = L` operations, operation `j` in the five registers `R[a+2+5j], …, R[a+6+5j]`
  `(code, x, y, b, u)`. Codes: `0` Hadamard on wire `x`; `1` the `T` gate on wire `x`; `2` CNOT,
  control `x`, target `y`; `3` QRAM query `|j⟩_x |d⟩_y ↦ |j⟩_x |d ⊕ (R[u + j] mod 2^b)⟩_y` on the
  `b`-wire words starting at wires `x` and `y`, reading the controller's *current* registers (the
  XOR form is the unitary extension of the paper's `|i⟩|0⟩ ↦ |i⟩|A[i]⟩`); `4` word addition
  `|s⟩_x|t⟩_y ↦ |s⟩_x|t + s mod 2^b⟩_y`; `5` word subtraction; `6` and `7` flip wire `u` when the
  `b`-bit words at `x` and `y` are equal, resp. when the first is smaller (unsigned); `8`, `9`, `10`
  XOR the product, quotient, remainder (unsigned, `Nat` conventions `s / 0 = 0`, `s % 0 = s`) of the
  words at `x` and `y`, reduced mod `2^b`, into the word at `u`. Words are
  little-endian (wire `x + i` is bit `i`). Word operations and queries need `1 ≤ b ≤ wordBits`, words
  inside the register, pairwise disjoint and disjoint from the target wire; any other operation is
  the identity. The gate set is fixed and finite with algebraic entries; the word operations make
  "a predicate computable in constant time" (Lemma 1, p. 11) evaluable at unit cost per word
  operation, as in the paper. The circuit acts on `|0^q⟩`; all `q` qubits are measured in the
  computational basis (Born rule), and outcome bit `i` is written to `R[a + 2 + 5L + i]`.
  The call costs `1 + 5L + 2q`: every operation (gate, word operation, query), the description and
  every qubit are charged.
* *Semantics.* `succProb P wb t s E` is the probability that the run from `s`, within `t` steps,
  reaches a halted state satisfying `E`, branching at each quantum call with the Born
  probabilities. Every instruction costs at least one unit, so a run that halts with cost at most
  `B` halts within `⌊B⌋₊` steps.
* *Input/output.* The input list `I` is stored as `R[0] = |I|`, `R[i+1] = I[i]`; the output of a
  halted state is the list `R[1], …, R[R[0]]` (the convention of `CongruencyTU_Machine`). Building
  any data structure from the input is the program's work and is charged.
* The published `CongruencyTU_Machine` is not imported: its oracle is a deterministic function and
  its coins are a fixed string, so it cannot express a quantum call; gates, `embedOp`, `ket`,
  `act` and `prob` are reused from `QAlgorithms_Defs_Circuit`.
-/

namespace QuantumScalingMWPM.QLiquidationist

open QAlgorithms
open scoped Classical

/-- Instructions of the classical controller. -/
inductive Instr where
  | const (d : ℕ) (c : ℤ)
  | copy (d s : ℕ)
  | add (d a b : ℕ)
  | sub (d a b : ℕ)
  | mul (d a b : ℕ)
  | div (d a b : ℕ)
  | mod (d a b : ℕ)
  | jle (a b target : ℕ)
  | load (d a : ℕ)
  | store (a s : ℕ)
  | qcall (a : ℕ)
  | halt

/-- A program: a finite list of instructions, fixed before the input. -/
abbrev Program := List Instr

/-- Machine state: program counter, registers (the shared memory), accumulated cost, and the
largest absolute value held by any register so far. -/
structure State where
  pc : ℕ
  reg : ℕ → ℤ
  cost : ℕ
  peak : ℕ

/-- Initial state on input `I`: `R[0] = |I|`, `R[i+1] = I[i]`, all other registers `0`. -/
def initState (I : List ℤ) : State where
  pc := 0
  reg := fun j => if j = 0 then (I.length : ℤ) else I.getD (j - 1) 0
  cost := 0
  peak := ((I.length : ℤ) :: I).foldr (fun z acc => max z.natAbs acc) 0

/-- The word length allowed for a program of width constant `width` on input `I`:
`width · (1 + log₂(2 + |I| + Σ |I_j|))`. -/
def wordBits (width : ℕ) (I : List ℤ) : ℕ :=
  width * (1 + Nat.log 2 (2 + I.length + (I.map Int.natAbs).sum))

/-- The machine has halted: the program counter is on `halt` or outside the program. -/
def Halted (P : Program) (s : State) : Prop :=
  match P[s.pc]? with
  | none => True
  | some .halt => True
  | some _ => False

/-- Write `v` into register `d`, advance, pay one unit. -/
def State.write (s : State) (d : ℕ) (v : ℤ) : State :=
  { s with reg := Function.update s.reg d v, pc := s.pc + 1, cost := s.cost + 1,
           peak := max s.peak v.natAbs }

/-- One classical step (for every instruction except `qcall`; a halted state is fixed). -/
def detStep (P : Program) (s : State) : State :=
  match P[s.pc]? with
  | some (.const d v) => s.write d v
  | some (.copy d a) => s.write d (s.reg a)
  | some (.add d a b) => s.write d (s.reg a + s.reg b)
  | some (.sub d a b) => s.write d (s.reg a - s.reg b)
  | some (.mul d a b) => s.write d (s.reg a * s.reg b)
  | some (.div d a b) => s.write d (s.reg a / s.reg b)
  | some (.mod d a b) => s.write d (s.reg a % s.reg b)
  | some (.jle a b t) =>
      { s with pc := if s.reg a ≤ s.reg b then t else s.pc + 1, cost := s.cost + 1 }
  | some (.load d a) => s.write d (s.reg (s.reg a).toNat)
  | some (.store a v) => s.write (s.reg a).toNat (s.reg v)
  | _ => s

/-! ### Quantum calls -/

/-- The `b`-bit little-endian word of the basis string `z` starting at wire `x`. -/
def wordVal {q : ℕ} (z : Qubits q) (x b : ℕ) : ℕ :=
  ∑ i ∈ Finset.range b, if h : x + i < q then (if z ⟨x + i, h⟩ then 2 ^ i else 0) else 0

/-- Overwrite the `b`-bit word starting at wire `x` with (the low `b` bits of) `v`. -/
def setWord {q : ℕ} (z : Qubits q) (x b v : ℕ) : Qubits q :=
  fun i => if x ≤ i.val ∧ i.val < x + b then v.testBit (i.val - x) else z i

/-- The permutation matrix of a map on basis strings (used only for bijections). -/
noncomputable def permMat {q : ℕ} (f : Qubits q → Qubits q) : Matrix (Qubits q) (Qubits q) ℂ :=
  Matrix.of fun y x => if y = f x then 1 else 0

/-- A single-qubit matrix on wire `i` of a `q`-qubit register (identity if `i ≥ q`). -/
noncomputable def oneQubit {q : ℕ} (M : Matrix Bool Bool ℂ) (i : ℕ) :
    Matrix (Qubits q) (Qubits q) ℂ :=
  if h : i < q then
    embedOp (k := 1) (M.submatrix (fun b => b 0) (fun b => b 0))
      ⟨fun _ => ⟨i, h⟩, fun a b _ => Subsingleton.elim a b⟩
  else 1

/-- The two `b`-wire words at `x` and `y` are valid operands: `1 ≤ b ≤ wb`, inside the register,
disjoint. -/
def WordsOK (q wb x y b : ℕ) : Prop :=
  1 ≤ b ∧ b ≤ wb ∧ x + b ≤ q ∧ y + b ≤ q ∧ (x + b ≤ y ∨ y + b ≤ x)

/-- The matrix of one decoded operation `(code, x, y, b, u)`; `reg` is the controller's current
register file, read by QRAM queries; `wb` the word length. -/
noncomputable def opMat (q wb : ℕ) (reg : ℕ → ℤ) (code x y b u : ℕ) :
    Matrix (Qubits q) (Qubits q) ℂ :=
  match code with
  | 0 => oneQubit hadamard x
  | 1 => oneQubit gateT x
  | 2 => if h : x < q ∧ y < q ∧ x ≠ y then
            permMat fun z => Function.update z ⟨y, h.2.1⟩ (xor (z ⟨y, h.2.1⟩) (z ⟨x, h.1⟩))
          else 1
  | 3 => if WordsOK q wb x y b then
            permMat fun z => setWord z y b
              (Nat.xor (wordVal z y b) ((reg (u + wordVal z x b)) % (2 ^ b : ℤ)).toNat)
          else 1
  | 4 => if WordsOK q wb x y b then
            permMat fun z => setWord z y b ((wordVal z y b + wordVal z x b) % 2 ^ b)
          else 1
  | 5 => if WordsOK q wb x y b then
            permMat fun z => setWord z y b ((wordVal z y b + 2 ^ b - wordVal z x b) % 2 ^ b)
          else 1
  | 6 => if h : WordsOK q wb x y b ∧ u < q ∧ ¬ (x ≤ u ∧ u < x + b) ∧ ¬ (y ≤ u ∧ u < y + b) then
            permMat fun z => if wordVal z x b = wordVal z y b then
              Function.update z ⟨u, h.2.1⟩ (!(z ⟨u, h.2.1⟩)) else z
          else 1
  | 7 => if h : WordsOK q wb x y b ∧ u < q ∧ ¬ (x ≤ u ∧ u < x + b) ∧ ¬ (y ≤ u ∧ u < y + b) then
            permMat fun z => if wordVal z x b < wordVal z y b then
              Function.update z ⟨u, h.2.1⟩ (!(z ⟨u, h.2.1⟩)) else z
          else 1
  | 8 => if WordsOK q wb x y b ∧ WordsOK q wb x u b ∧ WordsOK q wb y u b then
            permMat fun z => setWord z u b (Nat.xor (wordVal z u b) ((wordVal z x b * wordVal z y b) % 2 ^ b))
          else 1
  | 9 => if WordsOK q wb x y b ∧ WordsOK q wb x u b ∧ WordsOK q wb y u b then
            permMat fun z => setWord z u b (Nat.xor (wordVal z u b) ((wordVal z x b / wordVal z y b) % 2 ^ b))
          else 1
  | 10 => if WordsOK q wb x y b ∧ WordsOK q wb x u b ∧ WordsOK q wb y u b then
            permMat fun z => setWord z u b (Nat.xor (wordVal z u b) ((wordVal z x b % wordVal z y b) % 2 ^ b))
          else 1
  | _ => 1

/-- Number of qubits of the circuit described at block `a`. -/
def qubitsAt (s : State) (a : ℕ) : ℕ := (s.reg a).toNat

/-- Number of operations of the circuit described at block `a`. -/
def opsAt (s : State) (a : ℕ) : ℕ := (s.reg (a + 1)).toNat

/-- Field `i` (`0 ≤ i ≤ 4`) of operation `j` of the circuit described at block `a`. -/
def opField (s : State) (a j i : ℕ) : ℕ := (s.reg (a + 2 + 5 * j + i)).toNat

/-- The unitary of the circuit described at block `a`: operation `0` is applied first. -/
noncomputable def circuitMat (wb : ℕ) (s : State) (a : ℕ) :
    Matrix (Qubits (qubitsAt s a)) (Qubits (qubitsAt s a)) ℂ :=
  (List.range (opsAt s a)).foldl
    (fun U j => opMat (qubitsAt s a) wb s.reg (opField s a j 0) (opField s a j 1)
      (opField s a j 2) (opField s a j 3) (opField s a j 4) * U) 1

/-- The state before measurement: the circuit applied to `|0^q⟩`. -/
noncomputable def circuitState (wb : ℕ) (s : State) (a : ℕ) :
    EuclideanSpace ℂ (Qubits (qubitsAt s a)) :=
  act (circuitMat wb s a) (zeroKet (qubitsAt s a))

/-- The state after the call at block `a` returned the measurement outcome `z`. -/
def afterCall (s : State) (a : ℕ) (z : Qubits (qubitsAt s a)) : State where
  pc := s.pc + 1
  reg := fun j =>
    if h : a + 2 + 5 * opsAt s a ≤ j ∧ j < a + 2 + 5 * opsAt s a + qubitsAt s a then
      (if z ⟨j - (a + 2 + 5 * opsAt s a), by omega⟩ then 1 else 0)
    else s.reg j
  cost := s.cost + 1 + 5 * opsAt s a + 2 * qubitsAt s a
  peak := max s.peak 1

/-- `succProb P wb t s E`: the probability that the run of `P` from `s` (word length `wb`) reaches,
within `t` steps, a halted state satisfying `E`. Quantum calls branch on every measurement outcome
with its Born probability. -/
noncomputable def succProb (P : Program) (wb : ℕ) : ℕ → State → (State → Prop) → ℝ
  | 0, s, E => if Halted P s ∧ E s then 1 else 0
  | t + 1, s, E =>
      if Halted P s then (if E s then 1 else 0) else
      match P[s.pc]? with
      | some (.qcall a) =>
          ∑ z : Qubits (qubitsAt s a),
            prob (circuitState wb s a) z * succProb P wb t (afterCall s a z) E
      | _ => succProb P wb t (detStep P s) E

/-- The output list `R[1], …, R[R[0]]` of a state. -/
def outputOf (s : State) : List ℤ :=
  (List.range (s.reg 0).toNat).map fun i => s.reg (i + 1)

/-! ### Predicates computable in constant time (Lemma 1, p. 11) -/

/-- Straight-line word-RAM instructions of a constant-time predicate over local registers, reading a
memory list: constant, copy, `+`, `−`, `×`, `÷`, `mod`, memory load, equality, comparison, and,
not. A branch of a constant-time program is expressible without jumps (`c·a + (1 − c)·b`), so these
straight-line programs compute exactly the predicates computable in constant time on the word RAM. -/
inductive PInstr where
  | const (d : ℕ) (c : ℤ)
  | copy (d s : ℕ)
  | add (d a b : ℕ)
  | sub (d a b : ℕ)
  | mul (d a b : ℕ)
  | div (d a b : ℕ)
  | mod (d a b : ℕ)
  | load (d a : ℕ)
  | eq (d a b : ℕ)
  | lt (d a b : ℕ)
  | band (d a b : ℕ)
  | bnot (d a : ℕ)

/-- One predicate instruction; `load` reads `I[r a]` (`0` outside `I` or at a negative address). -/
def PInstr.exec (I : List ℤ) (r : ℕ → ℤ) : PInstr → ℕ → ℤ
  | .const d c => Function.update r d c
  | .copy d a => Function.update r d (r a)
  | .add d a b => Function.update r d (r a + r b)
  | .sub d a b => Function.update r d (r a - r b)
  | .mul d a b => Function.update r d (r a * r b)
  | .div d a b => Function.update r d (r a / r b)
  | .mod d a b => Function.update r d (r a % r b)
  | .load d a => Function.update r d (if 0 ≤ r a then I.getD (r a).toNat 0 else 0)
  | .eq d a b => Function.update r d (if r a = r b then 1 else 0)
  | .lt d a b => Function.update r d (if r a < r b then 1 else 0)
  | .band d a b => Function.update r d (if r a ≠ 0 ∧ r b ≠ 0 then 1 else 0)
  | .bnot d a => Function.update r d (if r a = 0 then 1 else 0)

/-- The predicate computed by the straight-line program `F` on memory `I`: start with local
register `0` holding `x` (all others `0`), run `F`, accept iff local register `0` is nonzero. -/
def evalPred (F : List PInstr) (I : List ℤ) (x : ℕ) : Prop :=
  (F.foldl (fun r i => i.exec I r) (fun j => if j = 0 then (x : ℤ) else 0)) 0 ≠ 0

/-! ### Sanity checks -/

example : outputOf (initState [5, 7]) = [5, 7] := by
  simp [outputOf, initState, List.range_succ]

example : wordBits 1 [] = 2 := by decide

example : evalPred [.load 0 0] [0, 3] 1 := by
  simp [evalPred, PInstr.exec]

end QuantumScalingMWPM.QLiquidationist


