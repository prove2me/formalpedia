-- Prove2me | Definitions.Def_SubspaceEvasion312_Explicit_machine
-- name    : SubspaceEvasion312_Explicit_machine
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T03:58:01.256591+00:00
-- url     : https://prove2.me/theorems/4e400993-af2c-40c6-a80d-b58ec71439e4
-- title:
--   Finite field-register programs and charged execution
-- statement:
--   A program is a finite list of instructions acting on natural registers, field registers, indexed memory, read-only input arrays, and output streams. Its instructions are field constants, arithmetic, inversion, equality tests, natural word arithmetic, coordinate reads and writes, branches, jumps, individual output symbols, and halt. It has no instruction for an arbitrary function or a mathematical oracle.
--
--   Each transition costs one step. Every invocation starts with zero registers and empty work memory. Code loading costs the number of instructions, with the binary length of every natural literal additionally charged. Natural registers must stay below a specified bound $B$. Thus a single natural literal cannot supply a free table of a global set. A successful computation satisfies
--
--   $$\operatorname{size}(P)+t\le T,$$
--
--   halts explicitly, and emits exactly the specified field and natural output lists. Preprocessing and all emitted symbols belong to this same charged execution. For global families $B$ is polynomial in the ambient dimension, giving logarithmic bookkeeping words. Field symbols and field operations cost one, as in the source footnote. This definition supplies an operational meaning of time rather than an asserted runtime label.
-- source:
--   Brakensiek, Chen, Cheraghchi, Goyal, Guruswami, Putterman, Zhang, STOC 2027 submission #312 (October 2026), complexity conventions and footnote 4, printed p. 7 (PDF p. 8); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/312.pdf; PDF SHA256 a6946cb436bf453cfc53c1547fdd79e55134761b2192ee39f145dfc45490f6bc

import Mathlib

namespace SubspaceEvasion312.Explicit

/-- A finite register program. Natural arithmetic is word-RAM bookkeeping;
field arithmetic, tests, indexed memory and input/output each take one step.
No instruction can call an arbitrary function or a semantic oracle. -/
inductive Instruction (F : Type) where
  | halt
  | literal (dst value : ℕ)
  | inputNat (dst index : ℕ)
  | addNat (dst a b : ℕ)
  | subNat (dst a b : ℕ)
  | mulNat (dst a b : ℕ)
  | divNat (dst a b : ℕ)
  | modNat (dst a b : ℕ)
  | branchNat (a b yes no : ℕ)
  | constant (dst : ℕ) (value : F)
  | add (dst a b : ℕ)
  | sub (dst a b : ℕ)
  | mul (dst a b : ℕ)
  | inv (dst a : ℕ)
  | load (dst address : ℕ)
  | store (address src : ℕ)
  | input (dst address : ℕ)
  | branch (a b yes no : ℕ)
  | jump (target : ℕ)
  | output (src : ℕ)
  | outputNat (src : ℕ)

abbrev Program (F : Type) := List (Instruction F)

/-- Natural literal bits are charged: one huge integer cannot encode a free table.
Field constants are single field symbols, as in the source's field-operation model. -/
def instructionSize {F : Type} : Instruction F → ℕ
  | .literal _ v => 2 + v.log2
  | _ => 1

def programSize {F : Type} (P : Program F) : ℕ := (P.map instructionSize).sum

structure MachineState (F : Type) where
  pc : ℕ
  natReg : ℕ → ℕ
  fieldReg : ℕ → F
  out : List F
  natOut : List ℕ

def initialState {F : Type} [Zero F] : MachineState F :=
  ⟨0, fun _ => 0, fun _ => 0, [], []⟩

noncomputable def step {F : Type} [Field F] (P : Program F)
    (ns : List ℕ) (xs : List F) (z : MachineState F) : Option (MachineState F) := by
  classical
  let next := {z with pc := z.pc + 1}
  let putN := fun d v => {next with natReg := Function.update z.natReg d v}
  let putF := fun d v => {next with fieldReg := Function.update z.fieldReg d v}
  exact match P[z.pc]? with
  | none | some .halt => none
  | some (.literal d v) => some (putN d v)
  | some (.inputNat d i) => some (putN d (ns.getD i 0))
  | some (.addNat d a b) => some (putN d (z.natReg a + z.natReg b))
  | some (.subNat d a b) => some (putN d (z.natReg a - z.natReg b))
  | some (.mulNat d a b) => some (putN d (z.natReg a * z.natReg b))
  | some (.divNat d a b) => some (putN d (z.natReg a / z.natReg b))
  | some (.modNat d a b) => some (putN d (z.natReg a % z.natReg b))
  | some (.branchNat a b y n) => some {z with pc := if z.natReg a = z.natReg b then y else n}
  | some (.constant d v) => some (putF d v)
  | some (.add d a b) => some (putF d (z.fieldReg a + z.fieldReg b))
  | some (.sub d a b) => some (putF d (z.fieldReg a - z.fieldReg b))
  | some (.mul d a b) => some (putF d (z.fieldReg a * z.fieldReg b))
  | some (.inv d a) => some (putF d (z.fieldReg a)⁻¹)
  | some (.load d a) => some (putF d (z.fieldReg (z.natReg a)))
  | some (.store a s) => some (putF (z.natReg a) (z.fieldReg s))
  | some (.input d a) => some (putF d (xs.getD (z.natReg a) 0))
  | some (.branch a b y n) => some {z with pc := if z.fieldReg a = z.fieldReg b then y else n}
  | some (.jump p) => some {z with pc := p}
  | some (.output s) => some {next with out := z.fieldReg s :: z.out}
  | some (.outputNat s) => some {next with natOut := z.natReg s :: z.natOut}

/-- Execution counts every transition; only an explicit halt terminates.
The bound B prevents unbounded-word arithmetic from hiding global advice. -/
noncomputable def runFrom {F : Type} [Field F] (P : Program F) (ns : List ℕ)
    (xs : List F) (B : ℕ) : ℕ → MachineState F → Option (MachineState F)
  | 0, _ => none
  | t + 1, z => by
      classical
      exact if (∀ i, z.natReg i ≤ B) then
        match P[z.pc]? with
        | some .halt => some z
        | _ => (step P ns xs z).bind (runFrom P ns xs B t)
      else none

/-- Code loading is charged, and each query starts with empty work memory.
The list outputs have a charged instruction for every symbol. -/
def RunsWithin {F : Type} [Field F] (P : Program F) (ns : List ℕ) (xs : List F)
    (T B : ℕ) (ys : List F) (outN : List ℕ := []) : Prop :=
  ∃ t z, programSize P + t ≤ T ∧ runFrom P ns xs B t initialState = some z ∧
    z.out.reverse = ys ∧ z.natOut.reverse = outN

end SubspaceEvasion312.Explicit


