-- Prove2me | Definitions.Def_HypercliqueCircuits_Circuits_Machine
-- name    : HypercliqueCircuits_Circuits_Machine
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T00:34:51.644908+00:00
-- url     : https://prove2.me/theorems/9bc1948a-9b88-4d79-9a6d-0279828d85b7
-- title:
--   Finite operational generators, charged execution and the saving sequence
-- statement:
--   A program is a finite list of instructions for natural-word registers and random-access memory: literals, copies, arithmetic, load, store, input read, output write, branches and halt. Every register and memory cell starts at zero. Execution is defined one instruction at a time; after halting the state is fixed. No instruction takes an arbitrary function, polynomial evaluator or correctness certificate.
--
--   For the final generator all cells are binary natural-number words. Each transition costs one plus the square of the sum of the lengths of its accessed words and addresses, including output serialization. A separate unit transition count is used for Lemma 3's record operations. That transformation can copy literal input coefficient atoms; the final generator has no atoms or advice.
--
--   Circuit encodings contain source records, actual signed dyadic numerators and denominator exponents, gate pointers and output pointers. The input is unary $(1^n,1^k)$. A correct generated output requires a halted execution, equality to the complete circuit encoding and formal equality to $\Delta_n^{(k)}$.
--
--   The saving sequence is defined, rather than assumed:
--
--   $$\epsilon_3=1/8,\quad L_j=\log_2(1/\epsilon_j),\quad B_j=\lceil8L_j/\epsilon_j\rceil,\quad \epsilon_{j+1}=\epsilon_j/(4B_j).$$
--
--   Values below $k=3$ are unused. These mathematical logarithms and ceilings are not machine instructions.
-- source:
--   Josh Alman, Baitian Li, Neha Pant, Kevin Pratt, Ryan Williams, Finding Hypercliques Faster Than Brute Force, STOC 2027 submission #1224 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1224.pdf, Theorem 1, p.2 (PDF 3), Lemma 3, p.16 (PDF 17), proof of Theorem 1, p.24 (PDF 25).

import Definitions.Def_HypercliqueCircuits_Circuits_Polynomials

set_option autoImplicit false

namespace HypercliqueCircuits.Circuits

/-- Natural-number words, with optional opaque coefficient atoms for circuit transformations.
The final generator has A = Empty and therefore only binary integer words. -/
abbrev Cell (A : Type) := ℕ ⊕ A

inductive Instruction (A : Type) where
  | literal (dst value : ℕ)
  | atom (dst : ℕ) (a : A)
  | copy (dst src : ℕ)
  | add (dst x y : ℕ)
  | sub (dst x y : ℕ)
  | mul (dst x y : ℕ)
  | div (dst x y : ℕ)
  | mod (dst x y : ℕ)
  | load (dst addr : ℕ)
  | store (addr src : ℕ)
  | readInput (dst index : ℕ)
  | emit (src : ℕ)
  | jump (target : ℕ)
  | ifZero (src target : ℕ)
  | halt

abbrev Program (A : Type) := List (Instruction A)

structure MachineState (A : Type) where
  pc : ℕ
  registers : ℕ → Cell A
  memory : ℕ → Cell A
  output : List (Cell A)
  halted : Bool

def wordNat {A : Type} : Cell A → ℕ
  | .inl n => n
  | .inr _ => 0

def initialState (A : Type) : MachineState A :=
  ⟨0, fun _ => .inl 0, fun _ => .inl 0, [], false⟩

def machineStep {A : Type} (prog : Program A) (input : List (Cell A))
    (s : MachineState A) : MachineState A := Id.run do
  if s.halted then return s
  let ins := prog.getD s.pc .halt
  let r := s.registers
  let n := fun j => wordNat (r j)
  let next := {s with pc := s.pc+1}
  match ins with
  | .literal d v => return {next with registers := Function.update r d (.inl v)}
  | .atom d a => return {next with registers := Function.update r d (.inr a)}
  | .copy d a => return {next with registers := Function.update r d (r a)}
  | .add d a b => return {next with registers := Function.update r d (.inl (n a+n b))}
  | .sub d a b => return {next with registers := Function.update r d (.inl (n a-n b))}
  | .mul d a b => return {next with registers := Function.update r d (.inl (n a*n b))}
  | .div d a b => return {next with registers := Function.update r d (.inl (n a/n b))}
  | .mod d a b => return {next with registers := Function.update r d (.inl (n a%n b))}
  | .load d a => return {next with registers := Function.update r d (s.memory (n a))}
  | .store a b => return {next with memory := Function.update s.memory (n a) (r b)}
  | .readInput d a => return {next with registers := Function.update r d (input.getD (n a) (.inl 0))}
  | .emit a => return {next with output := s.output ++ [r a]}
  | .jump p => return {s with pc := p}
  | .ifZero a p => return {next with pc := if n a = 0 then p else s.pc+1}
  | .halt => return {s with halted := true}

/-- Every accessed word, value and address, including input/output and instruction operands.
A unit word operation is one transition. Bit cost below charges lengths of these words. -/
def footprint {A : Type} (prog : Program A) (input : List (Cell A))
    (s : MachineState A) : List (Cell A) :=
  let r := s.registers
  let n := fun j => wordNat (r j)
  let N := fun xs : List ℕ => xs.map (Sum.inl : ℕ → Cell A)
  .inl s.pc :: (match prog.getD s.pc .halt with
  | .literal d v => N [d,v]
  | .atom d a => [.inl d,.inr a]
  | .copy d a => N [d,a] ++ [r a]
  | .add d a b | .sub d a b | .mul d a b | .div d a b | .mod d a b =>
      N [d,a,b] ++ [r a,r b]
  | .load d a => N [d,a,n a] ++ [r a,s.memory (n a)]
  | .store a b => N [a,b,n a] ++ [r a,r b]
  | .readInput d a => N [d,a,n a] ++ [r a,input.getD (n a) (.inl 0)]
  | .emit a => [.inl a,r a]
  | .jump p => N [p]
  | .ifZero a p => [.inl a,.inl p,r a]
  | .halt => [])

/-- A conventional quadratic bignum charge, sufficient for schoolbook arithmetic.
It also charges serialization of every emitted word; no output operation is free. -/
def transitionBits {A : Type} (weight : A → ℕ) (prog : Program A)
    (input : List (Cell A)) (s : MachineState A) : ℕ :=
  if s.halted then 0 else
    1 + ((footprint prog input s).map (fun w => match w with
      | .inl n => 1 + Nat.log2 (n+1)
      | .inr a => weight a)).sum ^ 2

def execute {A : Type} (prog : Program A) (input : List (Cell A)) : ℕ → MachineState A
  | 0 => initialState A
  | t+1 => machineStep prog input (execute prog input t)

def executionBits {A : Type} (weight : A → ℕ) (prog : Program A)
    (input : List (Cell A)) (t : ℕ) : ℕ :=
  ∑ h ∈ Finset.range t, transitionBits weight prog input (execute prog input h)

/-- Length-prefixed source records, gate pointers, and output pointers. -/
def circuitWords {A σ R : Type} {o : ℕ} (encodeVar : σ → List (Cell A))
    (coefficient : R → List (Cell A)) (c : Circuit R σ o) : List (Cell A) :=
  let N := fun xs : List ℕ => xs.map (Sum.inl : ℕ → Cell A)
  N [c.size] ++ c.code.flatMap (fun g => match g with
    | .input x => N [0,(encodeVar x).length] ++ encodeVar x
    | .constant a => N [1,(coefficient a).length] ++ coefficient a
    | .add i j => N [2,i,j]
    | .sub i j => N [3,i,j]
    | .mul i j => N [4,i,j]) ++
    N [o] ++ (List.finRange o).map (fun j => .inl (c.outputs j).val)

/-- Finite atoms are the literal coefficients of this input circuit, not an external table. -/
def derivativeInput {R : Type} {n : ℕ} (c : Circuit R (Fin n) 1) : List (Cell R) :=
  .inl n :: circuitWords (fun i => [.inl i.val]) (fun a => [.inr a]) c

def derivativeOutput {R : Type} {n : ℕ} (c : Circuit R (Fin n) n) : List (Cell R) :=
  circuitWords (fun i => [.inl i.val]) (fun a => [.inr a]) c

def signedWord (a : ℤ) : ℕ := if 0 ≤ a then 2*a.natAbs else 2*a.natAbs+1

def variableWords {k n : ℕ} (x : UniformVar k n) : List (Cell Empty) :=
  .inl x.1.val :: (List.finRange k).filterMap (fun i =>
    if h : i ≠ x.1 then some (.inl (x.2 ⟨i,h⟩).val) else none)

def dyadicWords (a : Dyadic) : List (Cell Empty) := [.inl (signedWord a.1),.inl a.2]

def unaryInput (k n : ℕ) : List (Cell Empty) :=
  List.replicate n (.inl 1) ++ [.inl 0] ++ List.replicate k (.inl 1) ++ [.inl 0]

def generatorOutput {k n : ℕ} (c : Circuit Dyadic (UniformVar k n) 1) : List (Cell Empty) :=
  circuitWords variableWords dyadicWords c

/-- Correctness includes actual execution, a completely serialized circuit, and polynomial equality. -/
def Generates (prog : Program Empty) (k n t : ℕ)
    (c : Circuit Dyadic (UniformVar k n) 1) : Prop :=
  (execute prog (unaryInput k n) t).halted = true ∧
  (execute prog (unaryInput k n) t).output = generatorOutput c ∧
  c.polynomial dyadicValue 0 = uniformHyperclique k n

/-- The exact real recurrence from printed p.24; Nat.ceil is the mathematical ceiling.
Values at k<3 are unused. No efficient-logarithm oracle is a machine instruction. -/
noncomputable def savingAux : ℕ → ℝ
  | 0 => 1/8
  | j+1 =>
      let ε := savingAux j
      let B : ℕ := ⌈8 * Real.logb 2 (1/ε) / ε⌉₊
      ε / (4 * B)

noncomputable def saving (k : ℕ) : ℝ := savingAux (k-3)

end HypercliqueCircuits.Circuits


