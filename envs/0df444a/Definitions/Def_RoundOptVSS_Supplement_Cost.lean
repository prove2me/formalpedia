-- Prove2me | Definitions.Def_RoundOptVSS_Supplement_Cost
-- name    : RoundOptVSS_Supplement_Cost
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T12:10:22.233348+00:00
-- url     : https://prove2.me/theorems/172d7336-a1b4-4770-b51d-e332880d92b2
-- title:
--   The field-operation cost model: an algebraic RAM over $\mathbb F\subseteq\mathbb E$, layouts, polynomial computation and communication
-- statement:
--   The paper measures the costs of §7 and §8 in field elements and field operations: "M IC instances of width $h$ plus $O(n^2)$ vectors of width $h$ and $n$ vectors of length $m_{\mathrm{WS}}$, and all computation is polynomial" (proof of Theorem 7.1) and "$O(n^{11})$ operations in $\mathbb E$" (proof of Lemma 7.8). This definition makes that cost model precise.
--
--   **The machine.** A program is a finite list of instructions that mentions no field and no parameter, so one program runs over every pair of finite fields $\mathbb F\subseteq\mathbb E$. Field registers hold elements of $\mathbb E$ (an element of $\mathbb F$ is held as its image, where the operations of $\mathbb F$ are those of $\mathbb E$); integer registers hold integers. The instructions are: addition, subtraction, multiplication and inversion ($0^{-1}=0$) of field registers; a branch on whether a field register is $0$; a branch on whether a field register lies in $\mathbb F$; loading the constants $0,1$; copying field registers, directly or through an address held in an integer register; integer constants, addition, subtraction, comparison branches and indirect loads and stores; and halt. There is no integer multiplication or division and no instruction turning an integer into a field element. Every executed instruction costs one step.
--
--   **Data and layouts.** Values are integers, field elements and finite lists of values; a value is written to the machine as an integer stream (a prefix code) and a field stream, and its *size* is the total length of the two streams. A *layout* of a protocol fixes how its public parameters (including any field constants the protocol is defined with), its states, its messages and the coins of a round (each coin drawn uniformly from a finite domain is written as the element drawn) are written as values.
--
--   **Polynomial computation and communication.** For a protocol in the execution model, a layout, a size measure $N(P)$ of the parameters and a polynomial $p$:
--
--   1. *Computation* holds for programs $c=(c_{\mathrm{init}},c_{\mathrm{send}},c_{\mathrm{recv}},c_{\mathrm{out}})$ when, for every valid admissible parameter set $P$, each program computes its honest map (initial state; the private messages to all parties and the broadcast of a round; the state update; the output) on **every** input within $p(N(P)+\text{input size})$ steps, each round requests at most $p(N(P))$ coins, and the parameter layout has size at most $p(N(P))$.
--   2. *Communication* holds when, for every valid admissible $P$, the protocol's message cap and, on every execution in the support against every static rushing adversary, every honest state and every honest message have size at most $p(N(P))$.
--
--   This is the cost model of the supplement's Theorems 7.1 and 8.7, and it can be reused for any protocol over a finite field.
--
--   **Formalization Note** The published uniform algebraic machine `EllipticRootFinding_Online_Machine` is not reused: it has a single field and no test of membership in a subfield, and recognising a valid key of the packed IC needs to test whether an element of $\mathbb E$ lies in $\mathcal A\subseteq\mathbb F$ (in any representation of $\mathbb E$ over $\mathbb F$, such as the basis $1,\lambda,\lambda^2,\dots$ of §8.4, this test reads coordinates). The step count includes every instruction, so a polynomial bound is a bound on running time.
-- source:
--   Liu-Zhang, Masserova, Round-Optimal Statistical Verifiable Secret Sharing with Polynomial Complexity, manuscript (2026; STOC 2027 submission, sha256 3a45d95d…), proof of Theorem 7.1 (p.25), Definition 6.1 (p.19, "Out is a public deterministic polynomial-time function"), Definition 7.7 (p.26), Theorem 8.7 (p.30), proof of Lemma 7.8 (p.39)

import Mathlib
import Definitions.Def_RoundOptVSS_Model

namespace RoundOptVSS

namespace Supplement

/-!
# The field-operation cost model: layouts, programs, polynomial computation and communication

Liu-Zhang, Masserova, *Round-Optimal Statistical Verifiable Secret Sharing with Polynomial
Complexity*, manuscript (STOC 2027 submission, sha256 3a45d95d…): the cost statements
"polynomial communication and computation" of Theorem 7.1 (p.24), "Out is a public deterministic
polynomial-time function" (Definition 6.1, p.19), "deterministic polynomial-time algorithm Search"
(Definition 7.7, p.26) and "its local computation is polynomial" (Theorem 8.7, p.30). The paper counts
these costs in field elements and field operations (proof of Theorem 7.1, p.25: "M IC instances of
width h plus O(n²) vectors of width h and n vectors of length mWS, and all computation is
polynomial"; Lemma 7.8's proof, p.39: "O(n¹¹) operations in 𝔼").

**Formalization Note.**
* The machine (`Instr`, `mstep`, `mrun`) is a uniform algebraic RAM over the pair `𝔽 ⊆ 𝔼`: field
  registers hold elements of `𝔼` (an element of `𝔽` is held as its image, where `𝔽`'s operations
  are `𝔼`'s), with `+, −, ×`, inversion (`0⁻¹ = 0`), a zero test, and a test "lies in `𝔽`" (needed
  to recognise a valid key, whose point must lie in `A ⊆ 𝔽` (§5.1); in any representation of `𝔼`
  over `𝔽`, such as the basis `1, λ, λ², …` of §8.4, it reads coordinates); integer registers
  with constants, `+`, `−`, comparison and indirect addressing; no integer multiplication or
  division (a unit-cost machine with them is not polynomially related to Turing machines) and no
  map from integers to field elements. One program serves every parameter and every field.
* Cost is the number of executed instructions (`RunsWithin`).
* Data are values of `MVal 𝔼` (integers, field elements, finite lists); the size of a value is the
  number of entries of its integer and field streams (`valSize`). A protocol is measured through a
  `Layout`: the layout of the public parameters, of states, of messages, and of the coins as they
  are drawn (a coin drawn as a uniform element of a finite domain is laid out as that element; one
  draw is one step, as in the cost model of the paper).
* `Computation L prot N p c`: the programs `c` compute the protocol's initial state, its messages
  (all private messages and the broadcast of a round), its state update and its output, each within
  `p(N(P) + size of the input)` steps on **every** input, for all valid parameters satisfying the
  scheme's admissibility predicate `Adm` (its standing assumptions); the number of
  coins requested in a round is at most `p(N(P))`, and so is the size of the parameter layout.
  `Communication L prot N p`: the message cap and, on every execution in the support against every
  adversary, every honest state and every honest message have size at most `p(N(P))`. The
  polynomial is chosen before the parameters (and, where a statement says so, before the fields).
-/

/-- Instructions of the algebraic RAM over `𝔽 ⊆ 𝔼`. `i j k` name registers, `l` a program position.
Field registers hold elements of `𝔼` (elements of `𝔽` as their images). -/
inductive Instr where
  | fadd (i j k : ℕ)
  | fsub (i j k : ℕ)
  | fmul (i j k : ℕ)
  | finv (i j : ℕ)
  | fbz (i l : ℕ)
  | fbsub (i l : ℕ)
  | fzero (i : ℕ)
  | fone (i : ℕ)
  | fcopy (i j : ℕ)
  | fload (i j : ℕ)
  | fstore (i j : ℕ)
  | iconst (i : ℕ) (c : ℤ)
  | iadd (i j k : ℕ)
  | isub (i j k : ℕ)
  | iload (i j : ℕ)
  | istore (i j : ℕ)
  | iblt (i j l : ℕ)
  | halt

/-- A program: a finite list of instructions, independent of the parameters and of the fields.
Fetching past the end reads `halt`. -/
abbrev Program := List Instr

/-- A machine state: program counter, field registers and integer registers. -/
structure MState (𝔼 : Type) where
  pc : ℕ
  fr : ℕ → 𝔼
  ir : ℕ → ℤ

/-- The instruction at the program counter. -/
def MState.instr {𝔼 : Type} (prog : Program) (s : MState 𝔼) : Instr := prog.getD s.pc .halt

/-- Whether an instruction is `halt`. -/
def Instr.isHalt : Instr → Bool
  | .halt => true
  | _ => false

/-- One step. `fr i := fr j ∘ fr k` for `+, −, ×`; `finv` with `0⁻¹ = 0`; `fbz i l` jumps to `l` if
`fr i = 0`; `fbsub i l` jumps to `l` if `fr i` lies in (the image of) `𝔽`; `fzero`, `fone` load
`0`, `1`; `fcopy`, `fload`, `fstore` copy (directly or through an address in an integer register,
read with `Int.toNat`); integer constants, `+`, `−`, indirect load and store, and the branch `iblt i j
l` (jump if `ir i < ir j`). There is no integer multiplication or division and no instruction
turning an integer into a field element. -/
noncomputable def mstep (𝔽 : Type) {𝔼 : Type} [Field 𝔽] [Field 𝔼] [Algebra 𝔽 𝔼]
    (prog : Program) (s : MState 𝔼) : MState 𝔼 :=
  open Classical in
  let fw (i : ℕ) (x : 𝔼) : MState 𝔼 := { s with pc := s.pc + 1, fr := Function.update s.fr i x }
  let iw (i : ℕ) (z : ℤ) : MState 𝔼 := { s with pc := s.pc + 1, ir := Function.update s.ir i z }
  match s.instr prog with
  | .fadd i j k => fw i (s.fr j + s.fr k)
  | .fsub i j k => fw i (s.fr j - s.fr k)
  | .fmul i j k => fw i (s.fr j * s.fr k)
  | .finv i j => fw i (s.fr j)⁻¹
  | .fbz i l => { s with pc := if s.fr i = 0 then l else s.pc + 1 }
  | .fbsub i l => { s with pc := if s.fr i ∈ Set.range (algebraMap 𝔽 𝔼) then l else s.pc + 1 }
  | .fzero i => fw i 0
  | .fone i => fw i 1
  | .fcopy i j => fw i (s.fr j)
  | .fload i j => fw i (s.fr (s.ir j).toNat)
  | .fstore i j => fw (s.ir i).toNat (s.fr j)
  | .iconst i c => iw i c
  | .iadd i j k => iw i (s.ir j + s.ir k)
  | .isub i j k => iw i (s.ir j - s.ir k)
  | .iload i j => iw i (s.ir (s.ir j).toNat)
  | .istore i j => iw (s.ir i).toNat (s.ir j)
  | .iblt i j l => { s with pc := if s.ir i < s.ir j then l else s.pc + 1 }
  | .halt => s

/-- Run for at most `t` steps, stopping at `halt`. -/
noncomputable def mrun (𝔽 : Type) {𝔼 : Type} [Field 𝔽] [Field 𝔼] [Algebra 𝔽 𝔼]
    (prog : Program) : ℕ → MState 𝔼 → MState 𝔼
  | 0, s => s
  | t + 1, s => if (s.instr prog).isHalt then s else mrun 𝔽 prog t (mstep 𝔽 prog s)

/-- Values exchanged with the machine: integers, field elements and finite lists. -/
inductive MVal (𝔼 : Type) where
  | int : ℤ → MVal 𝔼
  | fld : 𝔼 → MVal 𝔼
  | nil : MVal 𝔼
  | cons : MVal 𝔼 → MVal 𝔼 → MVal 𝔼

/-- The integer stream of a value (a prefix code: tag `0` integer, `1` field element, `2` nil,
`3` cons). -/
def MVal.ints {𝔼 : Type} : MVal 𝔼 → List ℤ
  | .int z => [0, z]
  | .fld _ => [1]
  | .nil => [2]
  | .cons a b => 3 :: (a.ints ++ b.ints)

/-- The field stream of a value: its field elements in order. -/
def MVal.flds {𝔼 : Type} : MVal 𝔼 → List 𝔼
  | .int _ => []
  | .fld x => [x]
  | .nil => []
  | .cons a b => a.flds ++ b.flds

/-- A finite list of values as one value. -/
def MVal.ofList {𝔼 : Type} : List (MVal 𝔼) → MVal 𝔼
  | [] => .nil
  | a :: as => .cons a (MVal.ofList as)

/-- The initial state on input `v`: the integer stream in integer registers `0, 1, …`, the field
stream in field registers `0, 1, …`, every other register `0`. -/
def minit {𝔼 : Type} [Zero 𝔼] (v : MVal 𝔼) : MState 𝔼 where
  pc := 0
  fr := fun i => v.flds.getD i 0
  ir := fun i => v.ints.getD i 0

/-- Output integer stream: integer register `0` holds a length `a`, output = registers `2, …, a+1`. -/
def moutInts {𝔼 : Type} (s : MState 𝔼) : List ℤ := (List.range (s.ir 0).toNat).map fun k => s.ir (k + 2)

/-- Output field stream: integer register `1` holds a length `b`, output = field registers
`0, …, b−1`. -/
def moutFlds {𝔼 : Type} (s : MState 𝔼) : List 𝔼 := (List.range (s.ir 1).toNat).map fun k => s.fr k

/-- The size of a value: the number of entries of its integer and field streams. -/
def valSize {𝔼 : Type} (v : MVal 𝔼) : ℕ := v.ints.length + v.flds.length

/-- `prog`, started on the layout of `v`, halts within `B` executed instructions and its output is
the layout of `w`. -/
def RunsWithin (𝔽 : Type) {𝔼 : Type} [Field 𝔽] [Field 𝔼] [Algebra 𝔽 𝔼] (prog : Program)
    (v w : MVal 𝔼) (B : ℕ) : Prop :=
  ∃ s : ℕ, s ≤ B ∧ ((mrun 𝔽 prog s (minit v)).instr prog).isHalt = true ∧
    w.ints = moutInts (mrun 𝔽 prog s (minit v)) ∧ w.flds = moutFlds (mrun 𝔽 prog s (minit v))

variable {𝔼 : Type}

/-- A natural number as an integer value. -/
def layNat (k : ℕ) : MVal 𝔼 := .int (k : ℤ)

/-- A bit. -/
def layBool (b : Bool) : MVal 𝔼 := .int (if b then 1 else 0)

/-- An optional value: `none ↦ 0`, `some a ↦ (1, a)`. -/
def layOpt {α : Type} (f : α → MVal 𝔼) : Option α → MVal 𝔼
  | none => .int 0
  | some a => .cons (.int 1) (f a)

/-- A list of values. -/
def layList {α : Type} (f : α → MVal 𝔼) (l : List α) : MVal 𝔼 := MVal.ofList (l.map f)

/-- A finite family, in index order. -/
def layFin {k : ℕ} {α : Type} (f : α → MVal 𝔼) (v : Fin k → α) : MVal 𝔼 :=
  MVal.ofList (List.ofFn fun r => f (v r))

/-- A vector of field elements. -/
def layVec {k : ℕ} (x : Fin k → 𝔼) : MVal 𝔼 := layFin MVal.fld x

/-- The numeric parameters `(n, t, κ, h, dealer)`. -/
def layParams (P : Params) : MVal 𝔼 :=
  MVal.ofList [layNat P.n, layNat P.t, layNat P.κ, layNat P.h, layNat (P.dealer : ℕ)]

/-- A layout of a protocol's data: the public parameters (including any field constants the
protocol is defined with), the states, the messages, and the coins of a round as drawn. -/
structure Layout (𝔼 Msg St : Type) where
  par : Params → MVal 𝔼
  st : St → MVal 𝔼
  msg : Msg → MVal 𝔼
  coin : (P : Params) → Fin P.n → Fin 4 → St → List ℕ → MVal 𝔼

/-- One program for each honest map of a protocol. -/
structure Codes where
  init : Program
  send : Program
  recv : Program
  output : Program

section Maps

variable {Msg St : Type} (L : Layout 𝔼 Msg St)

/-- Input of the initial-state map. -/
def initIn (P : Params) (i : Fin P.n) (x : Option (Fin P.h → 𝔼)) : MVal 𝔼 :=
  MVal.ofList [L.par P, layNat (i : ℕ), layOpt layVec x]

/-- Input of the message map of round `r`. -/
def sendIn (P : Params) (i : Fin P.n) (r : Fin 4) (st : St) (c : List ℕ) : MVal 𝔼 :=
  MVal.ofList [L.par P, layNat (i : ℕ), layNat (r : ℕ), L.st st, L.coin P i r st c]

/-- Output of the message map: the private message to each party and the broadcast. -/
def sendOut (P : Params) (pm : (Fin P.n → Msg) × Msg) : MVal 𝔼 :=
  MVal.ofList [layFin L.msg pm.1, L.msg pm.2]

/-- Input of the state update of round `r` (inboxes indexed by sender, `none` = missing). -/
def recvIn (P : Params) (i : Fin P.n) (r : Fin 4) (st : St) (c : List ℕ)
    (pr bc : Fin P.n → Option Msg) : MVal 𝔼 :=
  MVal.ofList [L.par P, layNat (i : ℕ), layNat (r : ℕ), L.st st, L.coin P i r st c,
    layFin (layOpt L.msg) pr, layFin (layOpt L.msg) bc]

/-- Input of the output map. -/
def outputIn (P : Params) (i : Fin P.n) (st : St) : MVal 𝔼 :=
  MVal.ofList [L.par P, layNat (i : ℕ), L.st st]

end Maps

variable (𝔽 : Type) [Field 𝔽] [Field 𝔼] [Algebra 𝔽 𝔼] {Msg St : Type}

/-- **Polynomial computation**: the programs `c` compute every honest map of `prot` within
`p(N(P) + input size)` executed instructions on every input, for all valid parameters with `Adm P`; each round's
coin request has at most `p(N(P))` coins and the parameter layout has size at most `p(N(P))`. -/
def Computation (Adm : Params → Prop) (L : Layout 𝔼 Msg St) (prot : Protocol Msg St 𝔼)
    (N : Params → ℕ) (p : Polynomial ℕ) (c : Codes) : Prop :=
  ∀ P : Params, P.Valid → Adm P →
    valSize (L.par P) ≤ p.eval (N P) ∧
    (∀ i r st, (prot.coins P i r st).length ≤ p.eval (N P)) ∧
    (∀ i x, RunsWithin 𝔽 c.init (initIn L P i x) (L.st (prot.init P i x))
      (p.eval (N P + valSize (initIn L P i x)))) ∧
    (∀ i r st cs, RunsWithin 𝔽 c.send (sendIn L P i r st cs) (sendOut L P (prot.send P i r st cs))
      (p.eval (N P + valSize (sendIn L P i r st cs)))) ∧
    (∀ i r st cs pr bc, RunsWithin 𝔽 c.recv (recvIn L P i r st cs pr bc)
      (L.st (prot.recv P i r st cs pr bc)) (p.eval (N P + valSize (recvIn L P i r st cs pr bc)))) ∧
    (∀ i st, RunsWithin 𝔽 c.output (outputIn L P i st) (layOpt layVec (prot.output P i st))
      (p.eval (N P + valSize (outputIn L P i st))))

/-- **Polynomial communication**: for all valid parameters with `Adm P` the message cap and, on every execution
in the support against every static rushing adversary, every honest state and every honest message
(private or broadcast, every round) have size at most `p(N(P))`. -/
def Communication (Adm : Params → Prop) (L : Layout 𝔼 Msg St) (prot : Protocol Msg St 𝔼)
    (N : Params → ℕ) (p : Polynomial ℕ) : Prop :=
  ∀ P : Params, P.Valid → Adm P → prot.msgCap P ≤ p.eval (N P) ∧
    ∀ C : Finset (Fin P.n), C.card ≤ P.t →
      ∀ (x : Fin P.h → 𝔼) (A : ShareAdv P Msg 𝔼) (B : RecAdv A),
        ∀ o ∈ (exec prot P C x A B).support, ∀ i, i ∉ C →
          (∀ r : Fin 5, valSize (L.st ((o.stateAt r) i)) ≤ p.eval (N P)) ∧
          ∀ r : Fin 4, (∀ j, valSize (L.msg ((o.roundAt r).sent i j)) ≤ p.eval (N P)) ∧
            valSize (L.msg ((o.roundAt r).sentB i)) ≤ p.eval (N P)

end Supplement

end RoundOptVSS


