-- Prove2me | Definitions.Def_TargetedSamplers_Machine
-- name    : TargetedSamplers_Machine
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T04:03:59.702614+00:00
-- url     : https://prove2.me/theorems/b8704ecb-fd54-4c7b-ae28-e94e87a07a19
-- title:
--   The log-cost random access machine with coins, read-once witness and oracle
-- statement:
--   The paper states that "the machine model used throughout this paper is the Random Access Machines (RAM) model" and fixes nothing else. This definition pins one such model.
--
--   A **program** is a finite list of instructions over work cells holding natural numbers: constants, addition, truncated subtraction, indirect load and store, a conditional jump, reading the input length, random access to bit $a$ of the input $x$ and of the coin string $r$, reading the **next** bit of the witness $w$ (a cursor that only moves forward, so the witness is read once), an **oracle query** on the bit string held in a range of cells, appending a bit to the output, answering $\bot$, and halting. Reading past the end of a tape returns a sentinel value.
--
--   Every executed instruction costs $1$ plus the bit lengths of the addresses and values it touches; a query also pays the length of the queried string. The **space** of a run is the sum, over the work cells ever written, of the bit length of the address plus the largest bit length the cell ever held; input, coins, witness and output tapes are not counted. A run halts in a unique state, whose cost, space, result ($\bot$ or an output string) and list of oracle queries are the run's totals.
--
--   The helper $\mathrm{budget}(K,k,t,n)=K\,(t+1)\,(\lfloor\log_2(n+t+2)\rfloor+1)^k$ is the reading of "time $t$" used for every complexity class of the mission.
--
--   **Formalization Note** The log-cost RAM is polylog-equivalent to a word RAM with $\Theta(\log T)$-bit words, and the paper's bounds carry factors $T^{O(\epsilon)}$ that absorb this gap. Unit-cost arithmetic on unbounded words is excluded on purpose, since it makes circuit evaluation too cheap and the paper's hardness assumptions false. There is no multiplication instruction; it is programmable at polylogarithmic cost.
-- source:
--   Chen, Doron, Ebtehaj, Tell, Targeted Samplers, STOC 2027 submission (manuscript sha256 599d0a59…), §3, p.19 (pdf p.21)

import Mathlib

namespace TargetedSamplers

/-- An instruction of the log-cost random access machine (RAM). No constructor carries a function:
a program is a finite syntactic object. Work cells hold natural numbers; `load` and `store` are
indirect. `readInput`, `readCoin` give random access to the input and to the coins, `readWitness`
reads the witness once, left to right, `query` asks the oracle about the bit string held in a range
of cells. -/
inductive Instr
  | const (d c : ℕ)
  | add (d a b : ℕ)
  | monus (d a b : ℕ)
  | load (d a : ℕ)
  | store (a b : ℕ)
  | jle (a b target : ℕ)
  | inputLength (d : ℕ)
  | readInput (d a : ℕ)
  | readCoin (d a : ℕ)
  | readWitness (d : ℕ)
  | query (d a b : ℕ)
  | output (a : ℕ)
  | outputBot
  | halt

/-- A program of the RAM (Chen, Doron, Ebtehaj, Tell, Targeted Samplers, STOC 2027 submission,
manuscript sha256 599d0a59…, §3, p.19: "The machine model used throughout this paper is the Random
Access Machines (RAM) model").

**Formalization Note** The paper fixes no word size or cost model. Each executed instruction costs 1
plus the bit lengths (`Nat.size`) of every address used and every value read or written; a query
also pays the length of the queried string. There is no multiplication: it is programmable at
polylogarithmic overhead. The model is polylog-equivalent to a word RAM with `Θ(log T)`-bit words,
and the paper's time bounds are read up to polylogarithmic factors (`budget`). Unit-cost
arithmetic on unbounded words is excluded on purpose: it would make circuit evaluation too cheap
and the paper's hardness hypotheses false. -/
abbrev Program := List Instr

/-- The read-only tapes of one run: the input `x`, the coins `r` (random access), the witness `w`
(read once, left to right) and the oracle, which maps a bit string to a natural number (a Boolean
oracle answers `0` or `1`). -/
structure Tapes where
  input : List Bool
  coins : List Bool
  witness : List Bool
  oracle : List Bool → ℕ

/-- The oracle used by machines that have no oracle: it answers `0` to everything. -/
def noOracle : List Bool → ℕ := fun _ => 0

/-- Tapes of a deterministic run on input `x`: no coins, no witness, no oracle. -/
def Tapes.ofInput (x : List Bool) : Tapes := ⟨x, [], [], noOracle⟩

/-- Machine state: program counter, memory, the largest bit length ever stored in each cell, the
set of cells ever written, the witness cursor, the output written so far, the `⊥` flag, the halted
flag, the accumulated cost, and the list of oracle queries asked so far. -/
structure State where
  pc : ℕ
  mem : ℕ → ℕ
  peak : ℕ → ℕ
  touched : Finset ℕ
  wcursor : ℕ
  out : List Bool
  bot : Bool
  halted : Bool
  work : ℕ
  asked : List (List Bool)

/-- The start state: all cells zero, nothing written, nothing output. -/
def State.init : State := ⟨0, fun _ => 0, fun _ => 0, ∅, 0, [], false, false, 0, []⟩

/-- The value read from a tape cell: the bit, or the sentinel `2` past the end of the tape. -/
def bitVal : Option Bool → ℕ
  | some b => b.toNat
  | none => 2

/-- Write `v` into work cell `d`, recording the cell and its peak bit length. -/
def State.write (st : State) (d v : ℕ) : State :=
  { st with
    mem := Function.update st.mem d v
    peak := Function.update st.peak d (max (st.peak d) v.size)
    touched := insert d st.touched }

/-- Space used so far: over every work cell ever written, the bit length of its address plus the
largest bit length it ever held. Input, coins, witness and output are not counted. -/
def State.space (st : State) : ℕ := ∑ i ∈ st.touched, (i.size + st.peak i)

/-- The result of a halted state: `none` is the answer `⊥`, `some y` is the output string `y`. -/
def State.result (st : State) : Option (List Bool) := if st.bot then none else some st.out

/-- The bit string held in cells `lo, …, hi - 1` (a cell holds bit `1` iff it is nonzero). -/
def queryString (mem : ℕ → ℕ) (lo hi : ℕ) : List Bool :=
  (List.range' lo (hi - lo)).map (fun i => mem i != 0)

/-- One step. A halted state stays; an invalid program counter is stuck and never halts. -/
def Program.step (p : Program) (τ : Tapes) (st : State) : State :=
  if st.halted then st
  else
    match p[st.pc]? with
    | none => st
    | some (.const d c) =>
        { st.write d c with pc := st.pc + 1, work := st.work + 1 + d.size + c.size }
    | some (.add d a b) =>
        let u := st.mem a
        let v := st.mem b
        { st.write d (u + v) with
          pc := st.pc + 1
          work := st.work + 1 + d.size + a.size + b.size + u.size + v.size + (u + v).size }
    | some (.monus d a b) =>
        let u := st.mem a
        let v := st.mem b
        { st.write d (u - v) with
          pc := st.pc + 1
          work := st.work + 1 + d.size + a.size + b.size + u.size + v.size + (u - v).size }
    | some (.load d a) =>
        let u := st.mem a
        let v := st.mem u
        { st.write d v with
          pc := st.pc + 1
          work := st.work + 1 + d.size + a.size + u.size + v.size }
    | some (.store a b) =>
        let u := st.mem a
        let v := st.mem b
        { st.write u v with
          pc := st.pc + 1
          work := st.work + 1 + a.size + b.size + u.size + v.size }
    | some (.jle a b target) =>
        let u := st.mem a
        let v := st.mem b
        { st with
          pc := if u ≤ v then target else st.pc + 1
          work := st.work + 1 + a.size + b.size + u.size + v.size + target.size }
    | some (.inputLength d) =>
        let v := τ.input.length
        { st.write d v with pc := st.pc + 1, work := st.work + 1 + d.size + v.size }
    | some (.readInput d a) =>
        let u := st.mem a
        let v := bitVal τ.input[u]?
        { st.write d v with
          pc := st.pc + 1
          work := st.work + 1 + d.size + a.size + u.size + v.size }
    | some (.readCoin d a) =>
        let u := st.mem a
        let v := bitVal τ.coins[u]?
        { st.write d v with
          pc := st.pc + 1
          work := st.work + 1 + d.size + a.size + u.size + v.size }
    | some (.readWitness d) =>
        let v := bitVal τ.witness[st.wcursor]?
        { st.write d v with
          pc := st.pc + 1
          wcursor := st.wcursor + 1
          work := st.work + 1 + d.size + v.size }
    | some (.query d a b) =>
        let lo := st.mem a
        let hi := st.mem b
        let q := queryString st.mem lo hi
        let v := τ.oracle q
        { st.write d v with
          pc := st.pc + 1
          asked := st.asked ++ [q]
          work := st.work + 1 + d.size + a.size + b.size + lo.size + hi.size + q.length + v.size }
    | some (.output a) =>
        let u := st.mem a
        { st with
          pc := st.pc + 1
          out := st.out ++ [u != 0]
          work := st.work + 1 + a.size + u.size }
    | some .outputBot =>
        { st with halted := true, bot := true, work := st.work + 1 }
    | some .halt =>
        { st with halted := true, work := st.work + 1 }

/-- The state after `k` steps. -/
def Program.config (p : Program) (τ : Tapes) (k : ℕ) : State :=
  (p.step τ)^[k] State.init

open Classical in
/-- The halting state of the run, if the run halts. A halted state is a fixed point of the step,
so it is unique; cost, space and queries only grow along a run, so the halting state carries the
totals of the run. -/
noncomputable def Program.final (p : Program) (τ : Tapes) : Option State :=
  if h : ∃ k, (p.config τ k).halted = true then some (p.config τ (Nat.find h)) else none

/-- The run on `τ` halts with total cost at most `t`, space at most `s`, and result `v`
(`v = none` is the answer `⊥`). -/
def Program.Runs (p : Program) (τ : Tapes) (t s : ℕ) (v : Option (List Bool)) : Prop :=
  ∃ st, p.final τ = some st ∧ st.work ≤ t ∧ st.space ≤ s ∧ st.result = v

/-- The run on `τ` halts with total cost at most `t` and result `v` (space unrestricted). -/
def Program.RunsIn (p : Program) (τ : Tapes) (t : ℕ) (v : Option (List Bool)) : Prop :=
  ∃ st, p.final τ = some st ∧ st.work ≤ t ∧ st.result = v

/-- The run on `τ` halts with result `v`. -/
def Program.Outputs (p : Program) (τ : Tapes) (v : Option (List Bool)) : Prop :=
  ∃ st, p.final τ = some st ∧ st.result = v

/-- The oracle queries asked during the run (empty if the run does not halt). -/
noncomputable def Program.queriesAsked (p : Program) (τ : Tapes) : List (List Bool) :=
  match p.final τ with
  | some st => st.asked
  | none => []

/-- The run on `τ` halts with cost at most `t` and writes, as its output, the strings of some list
whose multiset is `S`, one after another. Used for "the multiset of strings … is computable". -/
def Program.OutputsMultisetIn (p : Program) (τ : Tapes) (t : ℕ) (S : Multiset (List Bool)) :
    Prop :=
  ∃ L : List (List Bool), (L : Multiset (List Bool)) = S ∧ p.RunsIn τ t (some L.flatten)

/-- The running-time budget "time `t`" on inputs of length `n`: `K · (t + 1) · (log₂(n + t + 2) + 1)^k`.

**Formalization Note** The paper's RAM has no fixed cost model. A time bound `t` of the paper is
read as `t` up to a constant factor and a polylogarithmic factor, which is the gap between the
log-cost RAM and a word RAM; the `+ 1` keeps the budget positive when `t = 0`. -/
def budget (K k t n : ℕ) : ℕ := K * (t + 1) * (Nat.log 2 (n + t + 2) + 1) ^ k

end TargetedSamplers


