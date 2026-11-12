-- Prove2me | Definitions.Def_ITPIRPreproc_MatchVec_Machine
-- name    : ITPIRPreproc_MatchVec_Machine
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T07:08:04.285592+00:00
-- url     : https://prove2.me/theorems/29d069d7-e612-4f45-8870-64b1725f2fd1
-- title:
--   Cost model: randomized word RAM with work and bit-measured storage
-- statement:
--   The paper measures client and server work "in the RAM model" (§3) and, in its accounting, counts work "in bit operations, including random-bit generation" and storage "in bits" (§4.2). This definition fixes that cost model as a **randomized word RAM**.
--
--   A program is a finite list of instructions over natural-number registers $r_0,r_1,\dots$ and a natural-number memory $M$ (finitely many nonzero cells): constants, $+$, truncated $-$, $\times$, integer division and remainder (with $x/0=0$, $x \bmod 0=x$), bitwise AND and XOR, indexed load and store $M[r_a]$, the conditional jump "if $r_a<r_b$", `coin` (the next bit of an infinite tape of independent fair coins), `inBit` (the next input bit, read **sequentially**), `inBitAt` (the input bit at position $r_a$, **random access**), `outBit` (append a bit to the output) and `halt`. Outside the input the read value is $2$.
--
--   **Work.** At each step the word size is
--   $$w=\max\{1,\ \lceil\log_2(|\text{input}|+\text{storage in use}+1)\rceil\},$$
--   the bit length of the input length plus the current storage. An instruction costs $1$ plus, for each operand it touches, the number of $w$-bit words of that operand, $\lceil \mathrm{size}(x)/w\rceil$. So arithmetic on numbers that fit a machine word costs $O(1)$ and longer numbers are charged word by word; `coin`, `inBit`, `outBit` and `halt` cost $1$. The work of a halting run is the total charge.
--
--   **Storage.** The working bits of a state are the bit lengths of all nonzero registers, the bit lengths of the address **and** of the value of every nonzero memory cell, and the length of the output written so far; the storage of a run is the maximum over its states. The input tape and the coin tape are not included; wherever the input is client storage, the mission adds the input length explicitly.
--
--   The module also fixes the bit-string codes used by all statements: the self-delimiting codes of natural numbers and of bit strings (each bit preceded by a $1$, a final $0$), fixed-width binary, and the reading of a one-bit output as a bit and of every other output as $\bot$. The coin tape is the product of uniform laws on $\{0,1\}$. A program is *deterministic* if it has no `coin`, and *streaming* if it has no `inBitAt`.
--
--   **Formalization Note** Charging per word of the operands (rather than per bit, as a log-cost RAM does) is what lets a contiguous scan of the input cost $O(1)$ per bit, as the paper's $O(\sqrt n)$ server-work and offline terms assume; letting the word size grow with the storage in use is the usual transdichotomous convention and makes running a subprogram inside a larger program cost no more than running it alone.
-- source:
--   Jesko Dujmovic, Zhengnan Lai, Daniel Wichs, Nearly Optimal Information-Theoretic PIR with Client Preprocessing, STOC 2027 submission #572 (October 2026), §3 "Efficiency", printed p.10 (PDF p.12), footnote 6; §4.2 "Guarantees and costs", printed p.14 (PDF p.16)

import Mathlib

open MeasureTheory

namespace ITPIRPreproc.MatchVec

/-!
# The cost model: a randomized word RAM with bit-measured storage

Dujmovic, Lai, Wichs, STOC 2027 submission #572, §3 p.10 ("Efficiency": client and server work
are run times "measured in the RAM model"; client storage counts the evolving state and all
temporary values) and §4.2 p.14 ("Work is measured in bit operations, including random-bit
generation, and storage is measured in bits").

* Registers `r : ℕ →₀ ℕ` and memory `M : ℕ →₀ ℕ` hold natural numbers (finitely many nonzero).
* Instructions: `const`, `add`, `sub` (truncated), `mul`, `div` (`x / 0 = 0`), `mod`
  (`x % 0 = x`), bitwise `land`, `lxor`, indexed `load`/`store` at address `r[a]`, the jump
  `jlt a b t` (to `t` if `r[a] < r[b]`), `coin` (next fair coin), `inBit` (next input bit, read
  sequentially; `2` past the end), `inBitAt` (input bit at position `r[a]`; `2` outside),
  `outBit` (append a bit to the output) and `halt`.
* **Word size** at a step: `w = max 1 (Nat.size (|input| + working bits of the current state))`,
  the bit length of the input length plus the storage in use (the transdichotomous convention: a
  word can address the input and the memory). An instruction costs `1 +` the number of `w`-bit
  words of every operand it touches (`words w x = ⌈size x / w⌉`): operations on numbers of
  `O(log(input + storage))` bits cost `O(1)`, and longer numbers are charged word by word. `coin`,
  `inBit`, `outBit`, `halt` cost `1`. An instruction counter outside the program is stuck at cost
  `1` per step and never halts.
* **Working bits** of a state: total bit length of all nonzero registers, plus, for every nonzero
  memory cell, the bit length of its address and of its value, plus the length of the output
  written so far. The input tape and the coin tape are not counted; callers add the input length
  explicitly where the input is client storage.
-/

namespace WordRAM

/-- An instruction of the word RAM. -/
inductive Instr where
  /-- `r[dst] := k`. -/
  | const (dst k : ℕ)
  /-- `r[dst] := r[a] + r[b]`. -/
  | add (dst a b : ℕ)
  /-- `r[dst] := r[a] - r[b]` (truncated at `0`). -/
  | sub (dst a b : ℕ)
  /-- `r[dst] := r[a] * r[b]`. -/
  | mul (dst a b : ℕ)
  /-- `r[dst] := r[a] / r[b]` (`0` if `r[b] = 0`). -/
  | div (dst a b : ℕ)
  /-- `r[dst] := r[a] % r[b]` (`r[a]` if `r[b] = 0`). -/
  | mod (dst a b : ℕ)
  /-- `r[dst] := r[a] AND r[b]` (bitwise). -/
  | land (dst a b : ℕ)
  /-- `r[dst] := r[a] XOR r[b]` (bitwise). -/
  | lxor (dst a b : ℕ)
  /-- `r[dst] := M[r[a]]`. -/
  | load (dst a : ℕ)
  /-- `M[r[a]] := r[src]`. -/
  | store (a src : ℕ)
  /-- If `r[a] < r[b]` jump to `target`, else fall through. -/
  | jlt (a b target : ℕ)
  /-- `r[dst] :=` the next fair-coin bit (`1` or `0`). -/
  | coin (dst : ℕ)
  /-- `r[dst] :=` the next input bit, read sequentially (`2` past the end). -/
  | inBit (dst : ℕ)
  /-- `r[dst] :=` the input bit at position `r[a]` (`2` past the end): random access. -/
  | inBitAt (dst a : ℕ)
  /-- Append the bit `r[src] ≠ 0` to the output. -/
  | outBit (src : ℕ)
  /-- Halt. -/
  | halt

/-- A program: a finite list of instructions, executed from position `0`. -/
abbrev Program := List Instr

/-- The program uses no coins. -/
def Deterministic (P : Program) : Prop :=
  ∀ op ∈ P, ∀ d : ℕ, op ≠ .coin d

/-- The program reads its input only sequentially (no `inBitAt`): a streaming algorithm that
receives its input one bit at a time, in order, in a single pass. -/
def Streaming (P : Program) : Prop :=
  ∀ op ∈ P, ∀ d a : ℕ, op ≠ .inBitAt d a

/-- A machine state. -/
structure State where
  /-- Program counter. -/
  pc : ℕ
  /-- Registers. -/
  regs : ℕ →₀ ℕ
  /-- Memory. -/
  mem : ℕ →₀ ℕ
  /-- Position of the next sequentially read input bit. -/
  inPos : ℕ
  /-- Output written so far. -/
  out : List Bool
  /-- Number of coins used (position of the next unread coin). -/
  coins : ℕ
  /-- Halted flag. -/
  halted : Bool
  /-- Work charged so far. -/
  cost : ℕ

/-- Number of `w`-bit words of the natural number `x`: `⌈size x / w⌉`. -/
def words (w x : ℕ) : ℕ :=
  (Nat.size x + w - 1) / w

/-- `1` for `true`, `0` for `false`; `2` for a position outside the input. -/
def inputVal : Option Bool → ℕ
  | some true => 1
  | some false => 0
  | none => 2

/-- The working bits of a state: bit lengths of all nonzero registers, of the address and the
value of every nonzero memory cell, and the output written so far. -/
noncomputable def space (s : State) : ℕ :=
  (s.regs.sum fun _ x => Nat.size x) + (s.mem.sum fun a x => Nat.size a + Nat.size x) +
    s.out.length

/-- The word size at state `s` on input `inp`: the bit length of `|inp| + space s` (at least
`1`). -/
noncomputable def wordSize (inp : List Bool) (s : State) : ℕ :=
  max 1 (Nat.size (inp.length + space s))

/-- One step of `P` on input `inp` with coin tape `ω`. A halted state does not change. -/
noncomputable def step (P : Program) (inp : List Bool) (ω : ℕ → Bool) (s : State) : State :=
  if s.halted then s else
    let w := wordSize inp s
    let r := s.regs
    let c : ℕ → ℕ := fun i => words w (r i)
    let nx : State := { s with pc := s.pc + 1 }
    match P[s.pc]? with
    | none => { s with cost := s.cost + 1 }
    | some (.const d k) =>
        { nx with regs := r.update d k, cost := s.cost + 1 + words w k }
    | some (.add d a b) =>
        { nx with regs := r.update d (r a + r b), cost := s.cost + 1 + c a + c b }
    | some (.sub d a b) =>
        { nx with regs := r.update d (r a - r b), cost := s.cost + 1 + c a + c b }
    | some (.mul d a b) =>
        { nx with regs := r.update d (r a * r b), cost := s.cost + 1 + c a + c b }
    | some (.div d a b) =>
        { nx with regs := r.update d (r a / r b), cost := s.cost + 1 + c a + c b }
    | some (.mod d a b) =>
        { nx with regs := r.update d (r a % r b), cost := s.cost + 1 + c a + c b }
    | some (.land d a b) =>
        { nx with regs := r.update d (r a &&& r b), cost := s.cost + 1 + c a + c b }
    | some (.lxor d a b) =>
        { nx with regs := r.update d (r a ^^^ r b), cost := s.cost + 1 + c a + c b }
    | some (.load d a) =>
        { nx with regs := r.update d (s.mem (r a)),
                  cost := s.cost + 1 + c a + words w (s.mem (r a)) }
    | some (.store a src) =>
        { nx with mem := s.mem.update (r a) (r src), cost := s.cost + 1 + c a + c src }
    | some (.jlt a b target) =>
        { s with pc := if r a < r b then target else s.pc + 1, cost := s.cost + 1 + c a + c b }
    | some (.coin d) =>
        { nx with regs := r.update d (if ω s.coins then 1 else 0), coins := s.coins + 1,
                  cost := s.cost + 1 }
    | some (.inBit d) =>
        { nx with regs := r.update d (inputVal inp[s.inPos]?), inPos := s.inPos + 1,
                  cost := s.cost + 1 }
    | some (.inBitAt d a) =>
        { nx with regs := r.update d (inputVal inp[r a]?), cost := s.cost + 1 + c a }
    | some (.outBit src) =>
        { nx with out := s.out ++ [decide (r src ≠ 0)], cost := s.cost + 1 }
    | some .halt => { nx with halted := true, cost := s.cost + 1 }

/-- The initial state: everything zero, no output. -/
def initState : State :=
  ⟨0, 0, 0, 0, [], 0, false, 0⟩

/-- The state after `k` steps on input `inp` and coin tape `ω`. -/
noncomputable def run (P : Program) (inp : List Bool) (ω : ℕ → Bool) (k : ℕ) : State :=
  (step P inp ω)^[k] initState

/-- The run halts. -/
def Halts (P : Program) (inp : List Bool) (ω : ℕ → Bool) : Prop :=
  ∃ k : ℕ, (run P inp ω k).halted = true

open Classical in
/-- The number of steps to the first halted state (`0` if the run never halts; only used under
`Halts`). -/
noncomputable def haltStep (P : Program) (inp : List Bool) (ω : ℕ → Bool) : ℕ :=
  if h : ∃ k, (run P inp ω k).halted = true then Nat.find h else 0

/-- The first halted state (meaningful under `Halts`). -/
noncomputable def finalState (P : Program) (inp : List Bool) (ω : ℕ → Bool) : State :=
  run P inp ω (haltStep P inp ω)

/-- Work charged by a halting run. -/
noncomputable def cost (P : Program) (inp : List Bool) (ω : ℕ → Bool) : ℕ :=
  (finalState P inp ω).cost

/-- Working bits of a halting run: the maximum of `space` over its states. -/
noncomputable def workingBits (P : Program) (inp : List Bool) (ω : ℕ → Bool) : ℕ :=
  (Finset.range (haltStep P inp ω + 1)).sup fun k => space (run P inp ω k)

/-- The output string of a halting run. -/
noncomputable def output (P : Program) (inp : List Bool) (ω : ℕ → Bool) : List Bool :=
  (finalState P inp ω).out

/-- The coin tape fed to a deterministic program (never read). -/
def zeroTape : ℕ → Bool := fun _ => false

/-- The fair-coin tape: independent fair bits (each cell uniform on `Bool`). -/
noncomputable def coinTape : Measure (ℕ → Bool) :=
  Measure.infinitePi fun _ : ℕ => (PMF.uniformOfFintype Bool).toMeasure

end WordRAM

/-! ## Bit-string encodings -/

/-- Self-delimiting code of a natural number: each binary digit (least significant first) is
preceded by `true`; a final `false` ends the number. -/
def encNat (k : ℕ) : List Bool :=
  (k.bits.flatMap fun bit => [true, bit]) ++ [false]

/-- Self-delimiting code of a bit string: each bit preceded by `true`, then a final `false`. -/
def encBits (bs : List Bool) : List Bool :=
  (bs.flatMap fun b => [true, b]) ++ [false]

/-- Split a string `encBits x ++ y` back into `(x, y)` (a malformed string gives `([], [])` at
the point of failure). -/
def unpair : List Bool → List Bool × List Bool
  | true :: b :: rest => (b :: (unpair rest).1, (unpair rest).2)
  | false :: rest => ([], rest)
  | _ => ([], [])

/-- The `w`-bit little-endian binary representation of `k` (higher bits dropped). -/
def natBits (w k : ℕ) : List Bool :=
  List.ofFn fun t : Fin w => k.testBit t

/-- A one-bit output string is read as that bit; every other string means `⊥` (`none`). -/
def decodeBit : List Bool → Option Bool
  | [b] => some b
  | _ => none

end ITPIRPreproc.MatchVec


