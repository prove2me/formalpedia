-- Prove2me | Definitions.Def_EllipticRootFinding_Online_Machine
-- name    : EllipticRootFinding_Online_Machine
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T19:02:03.418785+00:00
-- url     : https://prove2.me/theorems/b6208ffb-0a63-4a85-bbce-ccd22317c170
-- title:
--   A uniform algebraic machine over a field, with its count of field operations
-- statement:
--   A **program** is a finite list of instructions that mentions no field, so the same program runs over every field $F$. A state consists of a program counter, field registers $\mathrm{fr} : \mathbb N \to F$ and integer registers $\mathrm{ir} : \mathbb N \to \mathbb Z$. The instructions are: field addition, subtraction, multiplication and inversion (with $0^{-1} = 0$) between field registers, and a branch on whether a field register is zero, each costing **one** operation; loading the constants $0$ and $1$ into a field register, copying a field register (directly, or through an address held in an integer register), every integer instruction (constants, $+$, $-$, $\times$, Euclidean division and remainder, comparison branch, indirect load and store), and `halt`, each costing **nothing**. There is no instruction that turns an integer into a field element and no other field constant: any other element of the prime field must be built from $1$ by counted additions.
--
--   Running a program for $t$ steps from a state stops at `halt` (or past the end of the list) and returns the state reached and the number of counted operations performed.
--
--   Inputs and outputs are **values**: integers, field elements, and finite lists of values. A value is written to the machine by a fixed self-delimiting layout: its integer stream (a tagged prefix code) goes to integer registers $0, 1, \dots$ and its field elements, in order, to field registers $0, 1, \dots$. The output of a halted state is read back as follows: integer register $0$ holds a length $a$ and integer register $1$ a length $b$; the output integer stream is integer registers $2, \dots, a+1$ and the output field stream is field registers $0, \dots, b-1$.
--
--   For a program $P$, an input value $v$, a property $\mathrm{Spec}$ of values and a real bound $B$, $\mathrm{Computes}(P, v, \mathrm{Spec}, B)$ means: for some $t$ the run of $P$ on $v$ has halted after $t$ steps, its output is the layout of a value satisfying $\mathrm{Spec}$, and the number of counted operations is at most $B$:
--   $$\exists t,\ \text{halted} \;\wedge\; \exists\, w,\ \mathrm{layout}(w) = \mathrm{output} \wedge \mathrm{Spec}(w) \;\wedge\; \mathrm{cost}_t \le B.$$
--   A polynomial is input as its coefficients $0, \dots, \deg g$ and read from an output as any finite coefficient list (trailing zeros allowed).
--
--   **Formalization Note.** This is the model in which the paper's phrase "arithmetic operations in $\mathbb F_q$" is made precise for every item of the mission: one program for all fields, counted field arithmetic and zero tests, free integer bookkeeping.
-- source:
--   Spaenlehauer, Deterministic Root-Finding over Finite Fields with Elliptic Curves, arXiv:2610.32508 (version held, sha256 c72ee273…), p. 2, Theorem 1.3 ('arithmetic operations in Fq') and p. 12, §3

import Mathlib

namespace EllipticRootFinding.Online

/-!
# A uniform algebraic machine over a field, with its count of field operations

Spaenlehauer, *Deterministic Root-Finding over Finite Fields with Elliptic Curves*,
arXiv:2610.32508 (version held), p. 2 (Theorem 1.3, "arithmetic operations in Fq") and p. 12 (§3).

A program is a finite list of instructions. It mentions no field: the same program runs over every
field `F`. The machine has field registers `fr : ℕ → F` and integer registers `ir : ℕ → ℤ`.

* Cost 1: field addition, subtraction, multiplication, inversion (`0⁻¹ = 0`) and the zero test.
* Cost 0: loading the field constants `0` and `1`, copying field registers (directly or through an
  integer register), every integer instruction, and `halt`.
* There is no instruction that turns an integer into a field element, and no other field constant.

Input and output are values of `Val F` (integers, field elements, and finite lists of values),
written to the registers by a fixed self-delimiting layout (`Val.ints`, `Val.flds`).
-/

/-- Instructions. `i j k` name registers, `l` a position in the program. -/
inductive Instr where
  | fadd (i j k : ℕ)          -- fr i := fr j + fr k            (cost 1)
  | fsub (i j k : ℕ)          -- fr i := fr j - fr k            (cost 1)
  | fmul (i j k : ℕ)          -- fr i := fr j * fr k            (cost 1)
  | finv (i j : ℕ)            -- fr i := (fr j)⁻¹, 0⁻¹ = 0      (cost 1)
  | fbz (i l : ℕ)             -- if fr i = 0 then go to l       (cost 1)
  | fzero (i : ℕ)             -- fr i := 0
  | fone (i : ℕ)              -- fr i := 1
  | fcopy (i j : ℕ)           -- fr i := fr j
  | fload (i j : ℕ)           -- fr i := fr (ir j)
  | fstore (i j : ℕ)          -- fr (ir i) := fr j
  | iconst (i : ℕ) (c : ℤ)    -- ir i := c
  | iadd (i j k : ℕ)          -- ir i := ir j + ir k
  | isub (i j k : ℕ)          -- ir i := ir j - ir k
  | imul (i j k : ℕ)          -- ir i := ir j * ir k
  | idiv (i j k : ℕ)          -- ir i := ir j / ir k  (Euclidean division, `x / 0 = 0`)
  | imod (i j k : ℕ)          -- ir i := ir j % ir k
  | iload (i j : ℕ)           -- ir i := ir (ir j)
  | istore (i j : ℕ)          -- ir (ir i) := ir j
  | iblt (i j l : ℕ)          -- if ir i < ir j then go to l
  | halt

/-- A program: a finite list of instructions, independent of the field. Fetching past the end
reads `halt`. -/
abbrev Program := List Instr

/-- Whether an instruction is `halt`. -/
def Instr.isHalt : Instr → Bool
  | .halt => true
  | _ => false

/-- A machine state over the field `F`. Addresses held in integer registers are read with
`Int.toNat` (negative addresses read register `0`). -/
structure State (F : Type) where
  pc : ℕ
  fr : ℕ → F
  ir : ℕ → ℤ

/-- The instruction at the program counter (`halt` past the end). -/
def State.instr {F : Type} (P : Program) (s : State F) : Instr :=
  P.getD s.pc .halt

/-- One step: the next state and the number of counted field operations (0 or 1). -/
noncomputable def step {F : Type} [Field F] (P : Program) (s : State F) : State F × ℕ :=
  open Classical in
  let fw (i : ℕ) (x : F) : State F := { s with pc := s.pc + 1, fr := Function.update s.fr i x }
  let iw (i : ℕ) (z : ℤ) : State F := { s with pc := s.pc + 1, ir := Function.update s.ir i z }
  match s.instr P with
  | .fadd i j k => (fw i (s.fr j + s.fr k), 1)
  | .fsub i j k => (fw i (s.fr j - s.fr k), 1)
  | .fmul i j k => (fw i (s.fr j * s.fr k), 1)
  | .finv i j => (fw i (s.fr j)⁻¹, 1)
  | .fbz i l => ({ s with pc := if s.fr i = 0 then l else s.pc + 1 }, 1)
  | .fzero i => (fw i 0, 0)
  | .fone i => (fw i 1, 0)
  | .fcopy i j => (fw i (s.fr j), 0)
  | .fload i j => (fw i (s.fr (s.ir j).toNat), 0)
  | .fstore i j => (fw (s.ir i).toNat (s.fr j), 0)
  | .iconst i c => (iw i c, 0)
  | .iadd i j k => (iw i (s.ir j + s.ir k), 0)
  | .isub i j k => (iw i (s.ir j - s.ir k), 0)
  | .imul i j k => (iw i (s.ir j * s.ir k), 0)
  | .idiv i j k => (iw i (s.ir j / s.ir k), 0)
  | .imod i j k => (iw i (s.ir j % s.ir k), 0)
  | .iload i j => (iw i (s.ir (s.ir j).toNat), 0)
  | .istore i j => (iw (s.ir i).toNat (s.ir j), 0)
  | .iblt i j l => ({ s with pc := if s.ir i < s.ir j then l else s.pc + 1 }, 0)
  | .halt => (s, 0)

/-- Run for at most `t` steps, stopping at `halt`: the state reached and the number of counted
field operations performed. -/
noncomputable def exec {F : Type} [Field F] (P : Program) : ℕ → State F → State F × ℕ
  | 0, s => (s, 0)
  | t + 1, s =>
    if (s.instr P).isHalt then (s, 0)
    else
      let r := step P s
      let r' := exec P t r.1
      (r'.1, r.2 + r'.2)

/-- Values exchanged with the machine: integers, field elements and finite lists of values
(`nil`, `cons`). -/
inductive Val (F : Type) where
  | int : ℤ → Val F
  | fld : F → Val F
  | nil : Val F
  | cons : Val F → Val F → Val F

/-- The integer stream of a value: a prefix code with tags `0` (integer, followed by it),
`1` (field element), `2` (`nil`), `3` (`cons`). -/
def Val.ints {F : Type} : Val F → List ℤ
  | .int z => [0, z]
  | .fld _ => [1]
  | .nil => [2]
  | .cons a b => 3 :: (a.ints ++ b.ints)

/-- The field stream of a value: its field elements in order. -/
def Val.flds {F : Type} : Val F → List F
  | .int _ => []
  | .fld x => [x]
  | .nil => []
  | .cons a b => a.flds ++ b.flds

/-- A finite list of values as one value. -/
def Val.ofList {F : Type} : List (Val F) → Val F
  | [] => .nil
  | a :: as => .cons a (Val.ofList as)

/-- The initial state on input `v`: the integer stream in integer registers `0, 1, …`, the field
stream in field registers `0, 1, …`, every other register `0`, program counter `0`. -/
def initState {F : Type} [Field F] (v : Val F) : State F where
  pc := 0
  fr := fun i => v.flds.getD i 0
  ir := fun i => v.ints.getD i 0

/-- The integer output of a state: integer register `0` holds a length `a`, and the output is
integer registers `2, …, a + 1`. -/
def outInts {F : Type} (s : State F) : List ℤ :=
  (List.range (s.ir 0).toNat).map fun k => s.ir (k + 2)

/-- The field output of a state: integer register `1` holds a length `b`, and the output is
field registers `0, …, b - 1`. -/
def outFlds {F : Type} (s : State F) : List F :=
  (List.range (s.ir 1).toNat).map fun k => s.fr k

/-- `P` run on input `v` halts, its output is the layout of a value satisfying `Spec`, and it has
performed at most `bound` counted field operations. -/
def Computes {F : Type} [Field F] (P : Program) (v : Val F) (Spec : Val F → Prop)
    (bound : ℝ) : Prop :=
  ∃ t : ℕ,
    (((exec P t (initState v)).1.instr P).isHalt = true) ∧
    (∃ out : Val F, out.ints = outInts (exec P t (initState v)).1 ∧
      out.flds = outFlds (exec P t (initState v)).1 ∧ Spec out) ∧
    (((exec P t (initState v)).2 : ℕ) : ℝ) ≤ bound

/-- Input encoding of a polynomial: its coefficients `0, …, natDegree` (so `0 ↦ [0]`). -/
noncomputable def polyVal {F : Type} [Field F] (g : Polynomial F) : Val F :=
  Val.ofList ((List.range (g.natDegree + 1)).map fun i => Val.fld (g.coeff i))

/-- Output reading of a polynomial: any finite coefficient list (trailing zeros allowed). -/
def IsPolyVal {F : Type} [Field F] (w : Val F) (g : Polynomial F) : Prop :=
  ∃ cs : List F, w = Val.ofList (cs.map Val.fld) ∧
    g = ∑ i ∈ Finset.range cs.length, Polynomial.C (cs.getD i 0) * Polynomial.X ^ i

/-- A finite list of field elements as a value. -/
def fieldListVal {F : Type} (L : List F) : Val F :=
  Val.ofList (L.map Val.fld)

end EllipticRootFinding.Online


