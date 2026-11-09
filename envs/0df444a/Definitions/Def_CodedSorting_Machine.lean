-- Prove2me | Definitions.Def_CodedSorting_Machine
-- name    : CodedSorting_Machine
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T23:04:48.315366+00:00
-- url     : https://prove2.me/theorems/0c47750a-693c-4bb3-b0ad-85b29ca0b5bf
-- title:
--   The external-memory machine: words, memory, disk, block transfers and runs
-- statement:
--   This is the deterministic external-memory machine of §3.1 and Appendix D.
--
--   Fix positive integers $M$ (memory size in words), $B$ (block size in words) and $w$ (word length in bits). A **word** is an integer in $[0,2^w)$. The **memory** consists of exactly $M$ words; the **disk** is an unbounded sequence of words $d_0,d_1,\dots$, and disk **block** $b$ is the $B$ consecutive words $d_{bB},\dots,d_{bB+B-1}$.
--
--   A **program** is a map that, given the current step index $t$ and the current memory contents, returns new memory contents (an arbitrary computation, not charged) and one action:
--
--   1. *read* block $b$ into memory words $[o,o+B)$;
--   2. *write* memory words $[o,o+B)$ onto block $b$;
--   3. do nothing;
--   4. halt.
--
--   Offsets satisfy $o+B\le M$. A **configuration** records the step index, memory, disk, the number of block transfers performed so far (each read or write counts one), the end $bB+B$ of the highest block touched so far, and whether the machine has halted; a halted configuration no longer changes. The run of a program for $T$ steps iterates this step map. The **trace** of a run lists the actions taken at each step until the halt.
--
--   For the sorting problem the input $x_0,\dots,x_{N-1}$ is placed in disk words $0,\dots,N-1$, all other disk words and all memory words are $0$, and the output condition is that disk words $0,\dots,N-1$ hold a nondecreasing permutation of the input.
--
--   This machine is shared by every machine statement of the mission (Theorem 3.1, Lemma 6.1, Lemma 7.2, Proposition 8.2, Lemma 8.3).
--
--   **Formalization Note** The step index $t$ is the "predetermined execution-step index" that Appendix D stores outside the $M$ words; it is the number of steps already taken and carries no information about the input. All other control state must be in memory or on disk. The $M$-word memory bound is the type of the memory.
-- source:
--   B. Li, Z. Li, S. Liu, Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting, arXiv:2610.20079 (held version, sha256 6e149d97…8850b), §3.1, p.4 (PDF 5), and Appendix D, p.39 (PDF 40)

import Mathlib

namespace CodedSorting

/-! # The external-memory machine

B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory
Integer Sorting*, arXiv:2610.20079 (held version, sha256 6e149d97…8850b), §3.1, p.4, and
Appendix D, p.39. -/

/-- A machine word of `w` bits: an unsigned integer in `[0, 2^w)` (§3.1, p.4: "A storage unit of
`w` bits is called a machine word"). -/
abbrev Word (w : ℕ) := Fin (2 ^ w)

/-- The memory: exactly `M` words. The `M`-word memory bound of §3.1 is in the type. -/
abbrev Mem (M w : ℕ) := Fin M → Word w

/-- The disk: an unbounded sequence of words, indexed from `0`. Disk block `b` is the `B`
consecutive words `[b·B, b·B + B)`. -/
abbrev Disk (w : ℕ) := ℕ → Word w

/-- One I/O action of a machine step.
* `read blk off`: copy disk block `blk` (disk words `[blk·B, blk·B + B)`) into memory words
  `[off, off + B)`;
* `write off blk`: copy memory words `[off, off + B)` onto disk block `blk`;
* `none`: no transfer;
* `halt`: stop.

The offset has type `Fin (M - B + 1)`, so `off + B ≤ M` whenever `B ≤ M`: a transfer that does not
fit in memory cannot be issued. -/
inductive IOAct (M B : ℕ) where
  | read (blk : ℕ) (off : Fin (M - B + 1))
  | write (off : Fin (M - B + 1)) (blk : ℕ)
  | none
  | halt

/-- A program for fixed size parameters `(M, B, w)`. At step index `t` it maps the current memory
to a new memory (arbitrary computation, not charged) and chooses one I/O action.

**Formalization Note.** The step index `t` is the number of steps already taken; it is the
"predetermined execution-step index" that Appendix D (p.39) stores outside the `M` words. It
carries no information about the input, since every run is at step `t` at time `t`. All other
control state (counters, pointers, recursion state) must live in the memory or on the disk. -/
structure Program (M B w : ℕ) where
  step : ℕ → Mem M w → Mem M w × IOAct M B

/-- A machine configuration: step index, memory, disk, number of block transfers so far, the end
`maxEnd` of the highest disk block touched by a transfer so far, and whether the machine halted. -/
structure Config (M w : ℕ) where
  t : ℕ
  mem : Mem M w
  disk : Disk w
  ios : ℕ
  maxEnd : ℕ
  halted : Bool

/-- One machine step of program `P` with block size `B`. A halted configuration does not change.
Otherwise the program computes `(mem', a) := P.step t mem` and then performs `a`:
* `read blk off` overwrites memory words `off ≤ i < off + B` with disk word `blk·B + (i − off)`;
  one block transfer;
* `write off blk` overwrites disk words `blk·B ≤ d < blk·B + B` with memory word
  `off + (d − blk·B)`; one block transfer;
* `none` keeps `mem'`; `halt` keeps `mem'` and sets `halted`.
Each read or write raises `maxEnd` to at least `blk·B + B`. -/
def Config.step {M B w : ℕ} (P : Program M B w) (c : Config M w) : Config M w :=
  if c.halted then c else
  match P.step c.t c.mem with
  | (mem', IOAct.read blk off) =>
      { t := c.t + 1
        mem := fun i => if (off : ℕ) ≤ i ∧ (i : ℕ) < off + B then c.disk (blk * B + (i - off))
          else mem' i
        disk := c.disk
        ios := c.ios + 1
        maxEnd := max c.maxEnd (blk * B + B)
        halted := false }
  | (mem', IOAct.write off blk) =>
      { t := c.t + 1
        mem := mem'
        disk := fun d => if blk * B ≤ d ∧ d < blk * B + B then
            (if h : (off : ℕ) + (d - blk * B) < M then mem' ⟨off + (d - blk * B), h⟩ else 0)
          else c.disk d
        ios := c.ios + 1
        maxEnd := max c.maxEnd (blk * B + B)
        halted := false }
  | (mem', IOAct.none) =>
      { c with t := c.t + 1, mem := mem' }
  | (mem', IOAct.halt) =>
      { c with t := c.t + 1, mem := mem', halted := true }

/-- The configuration after `T` machine steps. -/
def run {M B w : ℕ} (P : Program M B w) (T : ℕ) (c : Config M w) : Config M w :=
  (Config.step P)^[T] c

/-- The initial configuration on disk contents `d`: step index `0`, memory all zero, no transfers
yet. -/
def initCfgOf {M w : ℕ} (d : Disk w) : Config M w :=
  { t := 0, mem := fun _ => 0, disk := d, ios := 0, maxEnd := 0, halted := false }

/-- The input disk of the sorting problem: words `0, …, N−1` hold `x`, all other words are `0`. -/
def inputDisk {N w : ℕ} (x : Fin N → Word w) : Disk w :=
  fun i => if h : i < N then x ⟨i, h⟩ else 0

/-- The initial configuration of the sorting problem on input `x`. -/
def initCfg {M N w : ℕ} (x : Fin N → Word w) : Config M w :=
  initCfgOf (inputDisk x)

/-- The action trace of `P` from `c`: at time `n`, `some a` if the machine has not halted and takes
action `a`, and `none` once it has halted. Two runs are *oblivious* to each other when their traces
agree. -/
def trace {M B w : ℕ} (P : Program M B w) (c : Config M w) (n : ℕ) : Option (IOAct M B) :=
  let cn := run P n c
  if cn.halted then none else some (P.step cn.t cn.mem).2

/-- The disk `d` holds the sorted input in words `0, …, N−1`: the list of those words is a
permutation of the input list and is nondecreasing (repeated values allowed). -/
def IsSortedOutput {N w : ℕ} (x : Fin N → Word w) (d : Disk w) : Prop :=
  (List.ofFn (fun i : Fin N => d i)).Perm (List.ofFn x) ∧
    (List.ofFn (fun i : Fin N => d i)).Pairwise (· ≤ ·)

end CodedSorting


