-- Prove2me | Definitions.Def_MinrankTW_RAM
-- name    : MinrankTW_RAM
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:31:48.503612+00:00
-- url     : https://prove2.me/theorems/daaa09fe-1c88-466c-bc83-3571adb68f80
-- title:
--   Logarithmic-cost random access machine
-- statement:
--   The machine model in which the running times of Theorems 1 and 2 ("deterministic time", with every quantity of "polynomial bit cost") are stated.
--
--   A program is a finite list of instructions acting on registers $[0],[1],\dots$ holding natural numbers, with a program counter starting at $0$:
--
--   1. $\mathtt{const}\ i\ c$: $[i]:=c$; $\mathtt{add}\ i\ j\ k$: $[i]:=[j]+[k]$; $\mathtt{sub}\ i\ j\ k$: $[i]:=\max([j]-[k],0)$; $\mathtt{half}\ i\ j$: $[i]:=\lfloor [j]/2\rfloor$;
--   2. $\mathtt{load}\ i\ j$: $[i]:=[[j]]$; $\mathtt{store}\ i\ j$: $[[i]]:=[j]$;
--   3. $\mathtt{jz}\ i\ l$: jump to $l$ if $[i]=0$, else continue; $\mathtt{halt}$. A program counter past the end acts as $\mathtt{halt}$.
--
--   There is no multiplication or division instruction. The cost of a step is the **logarithmic cost** of Cook and Reckhow: $1$ plus $\ell(v)=\mathrm{size}(v)+1$ summed over every address and value the instruction reads or writes ($\mathrm{size}(v)$ is the binary length of $v$); $\mathtt{halt}$ costs $1$. A program **halts within** cost $B$ on an input memory with output property $Q$ if after some number of steps it is at a halt, the summed cost of those steps is at most $B$, and the final memory satisfies $Q$.
--
--   **Formalization Note** A unit-cost RAM on unbounded integers would be stronger than the source's model, and a Turing machine or an $O(\log n)$-bit word RAM loses polynomial factors that change the exponent $(w+1)^2$. Every value the algorithm handles has polynomially many bits (§A.3), so its word-RAM time and its logarithmic cost agree up to a polynomial factor.
-- source:
--   Perles–Weinstein, Efficient Algorithms for Minrank and Index Coding for Low-Treewidth Graphs, STOC 2027 submission (manuscript sha256 32a91384…), Theorems 1–2, p.3 ("deterministic time") and Section A.3, p.17 ("polynomial bit cost")

import Mathlib

namespace MinrankTW

/-!
# The logarithmic-cost random access machine

The machine in which the running times of Perles–Weinstein, *Efficient Algorithms for Minrank and Index Coding for Low-Treewidth Graphs*, STOC 2027 submission manuscript (sha256 32a91384…c57991) are stated: "deterministic time" (Theorems 1
and 2, p.3) with every quantity of "polynomial bit cost" (§A.3, p.17).

**Formalization Note**
* Memory: registers `ℕ → ℕ` (unbounded natural numbers, all `0` except the input), a program
  `List Instr` and a program counter starting at `0`.
* Instructions: `const i c` (`[i] := c`), `add i j k` (`[i] := [j] + [k]`), `sub i j k`
  (`[i] := [j] − [k]`, truncated at `0`), `half i j` (`[i] := ⌊[j]/2⌋`), `load i j`
  (`[i] := [[j]]`), `store i j` (`[[i]] := [j]`), `jz i l` (jump to `l` if `[i] = 0`,
  otherwise go to the next instruction), `halt`. A program counter past the end of the program
  reads as `halt`. There is no multiplication or division instruction.
* Cost (Cook–Reckhow logarithmic cost): one step costs `1` plus `ℓ(v) = size(v) + 1` summed over
  every address and every value the instruction reads or writes (`size v` is the binary length
  of `v`). `halt` costs `1`. Every step costs at least `1`.
* Why this machine: a unit-cost RAM on unbounded integers is stronger than the paper's model and a
  Turing machine or an `O(log n)`-bit word RAM loses polynomial factors that would change the
  exponent. Every value the paper's algorithm handles has polynomially many bits, so its word-RAM
  time and its logarithmic cost agree up to a polynomial factor.
-/

/-- An instruction of the logarithmic-cost RAM. -/
inductive Instr where
  | const (i c : ℕ)
  | add (i j k : ℕ)
  | sub (i j k : ℕ)
  | half (i j : ℕ)
  | load (i j : ℕ)
  | store (i j : ℕ)
  | jz (i l : ℕ)
  | halt
  deriving DecidableEq

/-- A configuration: program counter and memory. -/
structure Config where
  pc : ℕ
  mem : ℕ → ℕ

/-- The logarithmic length `ℓ(v) = size(v) + 1` of a register address or value. -/
def logLen (v : ℕ) : ℕ := Nat.size v + 1

/-- One step of program `P`. A halted configuration (at `halt` or past the end) is fixed. -/
def step (P : List Instr) (c : Config) : Config :=
  match P[c.pc]? with
  | none => c
  | some .halt => c
  | some (.const i v) => ⟨c.pc + 1, Function.update c.mem i v⟩
  | some (.add i j k) => ⟨c.pc + 1, Function.update c.mem i (c.mem j + c.mem k)⟩
  | some (.sub i j k) => ⟨c.pc + 1, Function.update c.mem i (c.mem j - c.mem k)⟩
  | some (.half i j) => ⟨c.pc + 1, Function.update c.mem i (c.mem j / 2)⟩
  | some (.load i j) => ⟨c.pc + 1, Function.update c.mem i (c.mem (c.mem j))⟩
  | some (.store i j) => ⟨c.pc + 1, Function.update c.mem (c.mem i) (c.mem j)⟩
  | some (.jz i l) => if c.mem i = 0 then ⟨l, c.mem⟩ else ⟨c.pc + 1, c.mem⟩

/-- The logarithmic cost of the step taken from configuration `c`. -/
def stepCost (P : List Instr) (c : Config) : ℕ :=
  match P[c.pc]? with
  | none => 1
  | some .halt => 1
  | some (.const i v) => 1 + logLen i + logLen v
  | some (.add i j k) => 1 + logLen i + logLen j + logLen k + logLen (c.mem j) +
      logLen (c.mem k) + logLen (c.mem j + c.mem k)
  | some (.sub i j k) => 1 + logLen i + logLen j + logLen k + logLen (c.mem j) +
      logLen (c.mem k) + logLen (c.mem j - c.mem k)
  | some (.half i j) => 1 + logLen i + logLen j + logLen (c.mem j) + logLen (c.mem j / 2)
  | some (.load i j) => 1 + logLen i + logLen j + logLen (c.mem j) + logLen (c.mem (c.mem j))
  | some (.store i j) => 1 + logLen i + logLen j + logLen (c.mem i) + logLen (c.mem j)
  | some (.jz i l) => 1 + logLen i + logLen l + logLen (c.mem i)

/-- The configuration after `t` steps. -/
def run (P : List Instr) : Config → ℕ → Config
  | c, 0 => c
  | c, t + 1 => run P (step P c) t

/-- The total logarithmic cost of the first `t` steps. -/
def runCost (P : List Instr) : Config → ℕ → ℕ
  | _, 0 => 0
  | c, t + 1 => stepCost P c + runCost P (step P c) t

/-- The configuration is halted: its program counter is at a `halt` or past the end. -/
def IsHalted (P : List Instr) (c : Config) : Prop :=
  P[c.pc]? = some .halt ∨ P[c.pc]? = none

/-- `HaltsWithin P mem B Q`: started at program counter `0` on memory `mem`, the program
`P` reaches a halted configuration after some number `t` of steps of total logarithmic cost at
most `B`, and the final memory satisfies `Q`. -/
def HaltsWithin (P : List Instr) (mem : ℕ → ℕ) (B : ℕ) (Q : (ℕ → ℕ) → Prop) : Prop :=
  ∃ t : ℕ, IsHalted P (run P ⟨0, mem⟩ t) ∧ runCost P ⟨0, mem⟩ t ≤ B ∧
    Q (run P ⟨0, mem⟩ t).mem

end MinrankTW


