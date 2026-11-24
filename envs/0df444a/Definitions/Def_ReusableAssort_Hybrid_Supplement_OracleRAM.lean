-- Prove2me | Definitions.Def_ReusableAssort_Hybrid_Supplement_OracleRAM
-- name    : ReusableAssort_Hybrid_Supplement_OracleRAM
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T00:18:18.36897+00:00
-- url     : https://prove2.me/theorems/600b82e9-fa3a-42ec-aa56-981a3a745c0f
-- title:
--   Logarithmic-cost randomized oracle RAM with rational cells (computation model for the running-time clause of Theorem EC.2)
-- statement:
--   This definition fixes the machine model in which the running-time clause of Theorem EC.2 is stated. The paper says that Algorithm 4 "runs in time Poly$(n, T, \sum_t|\mathcal Z_t|)$ given oracle access to an offline algorithm for assortment optimization" without naming a machine; this is a standard logarithmic-cost random access machine (Cook and Reckhow 1973) extended by calls to a world and by uniform random sampling.
--
--   1. **Memory and programs.** Memory is an infinite array of cells $M[0], M[1], \dots$ holding rational numbers, all initially $0$. A **program** is a finite list of instructions: loading a constant, the four rational operations ($x/0 = 0$), the floor, indirect load and store (the address is $\lfloor M[a]\rfloor$, truncated at $0$), a conditional jump on $M[a] > 0$, `rand` (a uniform sample from $\{0, \dots, k-1\}$, where $k = \lfloor M[a] \rfloor$), `call` and `halt`.
--   2. **World calls.** `call d a` sends the code $M[a]$ and the argument list $M[a+2], \dots, M[a+1+k]$, $k = \lfloor M[a+1]\rfloor$, to a **world**. The world answers with a weighted list of rational answers that may depend on the history of earlier calls; deterministic answers model oracles, random answers model the online environment. The answer is stored in $M[d]$ and the call is appended to the history.
--   3. **Cost.** The non-halting instructions charge $1$ plus the binary lengths of their operands, results and explicit addresses as specified by `step`, where a rational $p/q$ in lowest terms has length $\lceil\log_2(|p|+1)\rceil + \lceil\log_2(q+1)\rceil + 1$. A call also pays for its code, all its arguments and its answer; `rand` pays for the range.
--   4. **Runs.** A run from the all-zero configuration for at most $f$ instructions is a weighted list of outcomes. A branch that halts within $f$ instructions yields its final configuration (memory, history of calls and accumulated cost); a branch that does not halt yields "none".
--
--   Uniform sampling from an arbitrary finite integer range is an explicit primitive. The bound is a bit cost for arithmetic and oracle communication with that sampling primitive; it does not assert bounded-time exact sampling from a fair-bit tape.
--
--   **Formalization Note** Weighted lists are used as finite distributions, so no measure theory is needed. A world that is not a probability law (negative or non-normalized weights) is allowed by the type; the world of Theorem EC.2's companion is a probability law on the instances it is applied to.
-- source:
--   Feng, Niazadeh & Saberi, arXiv:2512.06997v1, p. ec7 (PDF 33), Theorem EC.2 (running-time clause) and p. 9, Assumption 3; machine model: Cook & Reckhow, Time bounded random access machines, J. Comput. System Sci. 7 (1973) 354–375; oracle-polynomial time as in Grötschel, Lovász & Schrijver (1981), cited on PDF 34

import Mathlib

namespace ReusableAssort.Hybrid.Supplement

/-- Encoding length of a rational number in binary: the bit lengths of its numerator's
absolute value and of its denominator, plus one (sign). -/
def qsize (q : ℚ) : ℕ := Nat.size q.num.natAbs + Nat.size q.den + 1

/-- The cell address denoted by a rational value: `⌊q⌋` truncated at `0`. -/
def addrOf (q : ℚ) : ℕ := (Int.floor q).toNat

/-- Instructions of the oracle log-cost random access machine. Cells hold rationals and are
indexed by naturals; `d`, `a`, `b`, `s` are cell addresses and `l` an instruction label.
* `const d q`: `M[d] := q`;
* `add`/`sub`/`mul`/`div d a b`: `M[d] := M[a] ∘ M[b]` (`div` by `0` gives `0`);
* `floor d a`: `M[d] := ⌊M[a]⌋`;
* `load d a`: `M[d] := M[addr M[a]]`; `store a s`: `M[addr M[a]] := M[s]` (indirect addressing);
* `jpos a l`: jump to `l` if `M[a] > 0`;
* `rand d a`: `M[d] :=` a uniform sample from `{0, …, k − 1}`, `k = addr M[a]` (`0` if `k = 0`);
* `call d a`: interaction with the world: code `M[a]`, argument list
  `M[a+2], …, M[a+1+k]` with `k = addr M[a+1]`; the answer is written to `M[d]`;
* `halt`. -/
inductive Instr where
  | const (d : ℕ) (q : ℚ)
  | add (d a b : ℕ)
  | sub (d a b : ℕ)
  | mul (d a b : ℕ)
  | div (d a b : ℕ)
  | floor (d a : ℕ)
  | load (d a : ℕ)
  | store (a s : ℕ)
  | jpos (a l : ℕ)
  | rand (d a : ℕ)
  | call (d a : ℕ)
  | halt

/-- One interaction with the world: its code, its argument list and the answer received. -/
abbrev Event := ℚ × List ℚ × ℚ

/-- A finite weighted list of outcomes (a finitely supported distribution when the weights are
nonnegative and sum to `1`). -/
abbrev Dist (α : Type) := List (ℝ × α)

/-- The point mass. -/
def Dist.pure {α : Type} (a : α) : Dist α := [(1, a)]

/-- Sequential composition: weights multiply along each branch. -/
noncomputable def Dist.bind {α β : Type} (d : Dist α) (f : α → Dist β) : Dist β :=
  d.flatMap fun pa => (f pa.2).map fun qb => (pa.1 * qb.1, qb.2)

/-- Total weight of the outcomes satisfying a Boolean test. -/
noncomputable def Dist.prob {α : Type} (d : Dist α) (P : α → Bool) : ℝ :=
  (d.map fun pa => if P pa.2 then pa.1 else 0).sum

/-- A world answers a call, given the history of earlier calls (oldest first), its code and its
arguments, with a weighted list of answers. It models both the oracles (deterministic answers)
and the online environment (random answers). -/
abbrev World := List Event → ℚ → List ℚ → Dist ℚ

/-- A machine configuration: program counter, memory, history of world calls (oldest first) and
the cost charged so far. -/
structure Config where
  pc : ℕ
  mem : ℕ → ℚ
  hist : List Event
  cost : ℕ

/-- The initial configuration: all cells `0`, no history, no cost. -/
def Config.init : Config := ⟨0, fun _ => 0, [], 0⟩

/-- A configuration has halted when its program counter is past the program or at `halt`. -/
def halted (P : List Instr) (c : Config) : Bool :=
  match P[c.pc]? with
  | none => true
  | some Instr.halt => true
  | some _ => false

/-- Result of a binary arithmetic instruction, with its log cost: `1` plus the bit lengths of the
three addresses, of the two operands and of the result. -/
def arith (c : Config) (d a b : ℕ) (x : ℚ) : Config :=
  { c with pc := c.pc + 1, mem := Function.update c.mem d x,
           cost := c.cost + 1 + Nat.size d + Nat.size a + Nat.size b
             + qsize (c.mem a) + qsize (c.mem b) + qsize x }

/-- One step of the machine, as a weighted list of successor configurations. Every executed
instruction costs `1` plus the bit lengths of every address and value it touches; `rand` also
pays the bit length of the range, and `call` the bit lengths of its code, of all arguments and
of the answer. -/
noncomputable def step (w : World) (P : List Instr) (c : Config) : Dist Config :=
  match P[c.pc]? with
  | none => Dist.pure c
  | some Instr.halt => Dist.pure c
  | some (Instr.const d q) =>
      Dist.pure { c with pc := c.pc + 1, mem := Function.update c.mem d q,
                         cost := c.cost + 1 + Nat.size d + qsize q }
  | some (Instr.add d a b) => Dist.pure (arith c d a b (c.mem a + c.mem b))
  | some (Instr.sub d a b) => Dist.pure (arith c d a b (c.mem a - c.mem b))
  | some (Instr.mul d a b) => Dist.pure (arith c d a b (c.mem a * c.mem b))
  | some (Instr.div d a b) => Dist.pure (arith c d a b (c.mem a / c.mem b))
  | some (Instr.floor d a) =>
      let x : ℚ := (Int.floor (c.mem a) : ℚ)
      Dist.pure { c with pc := c.pc + 1, mem := Function.update c.mem d x,
                         cost := c.cost + 1 + Nat.size d + Nat.size a + qsize (c.mem a) + qsize x }
  | some (Instr.load d a) =>
      let p := addrOf (c.mem a)
      let x := c.mem p
      Dist.pure { c with pc := c.pc + 1, mem := Function.update c.mem d x,
                         cost := c.cost + 1 + Nat.size d + Nat.size a + qsize (c.mem a)
                           + Nat.size p + qsize x }
  | some (Instr.store a s) =>
      let p := addrOf (c.mem a)
      Dist.pure { c with pc := c.pc + 1, mem := Function.update c.mem p (c.mem s),
                         cost := c.cost + 1 + Nat.size a + Nat.size s + qsize (c.mem a)
                           + Nat.size p + qsize (c.mem s) }
  | some (Instr.jpos a l) =>
      Dist.pure { c with pc := if 0 < c.mem a then l else c.pc + 1,
                         cost := c.cost + 1 + Nat.size a + Nat.size l + qsize (c.mem a) }
  | some (Instr.rand d a) =>
      let k := addrOf (c.mem a)
      let base := c.cost + 1 + Nat.size d + Nat.size a + qsize (c.mem a)
      if k = 0 then
        Dist.pure { c with pc := c.pc + 1, mem := Function.update c.mem d 0, cost := base + 1 }
      else
        (List.range k).map fun j =>
          ((1 : ℝ) / k, { c with pc := c.pc + 1, mem := Function.update c.mem d (j : ℚ),
                                 cost := base + qsize (j : ℚ) })
  | some (Instr.call d a) =>
      let code := c.mem a
      let k := addrOf (c.mem (a + 1))
      let args := (List.range k).map fun j => c.mem (a + 2 + j)
      (w c.hist code args).map fun pq =>
        (pq.1, { pc := c.pc + 1, mem := Function.update c.mem d pq.2,
                 hist := c.hist ++ [(code, args, pq.2)],
                 cost := c.cost + 1 + Nat.size d + Nat.size a + qsize code + qsize (c.mem (a + 1))
                   + (args.map qsize).sum + qsize pq.2 })

/-- Run the program for at most `fuel` instructions from configuration `c`. A branch that halts
returns its final configuration; a branch still running when the fuel is exhausted returns
`none`. -/
noncomputable def run (w : World) (P : List Instr) : ℕ → Config → Dist (Option Config)
  | 0, c => if halted P c then Dist.pure (some c) else Dist.pure none
  | f + 1, c => if halted P c then Dist.pure (some c) else (step w P c).bind (run w P f)

end ReusableAssort.Hybrid.Supplement


