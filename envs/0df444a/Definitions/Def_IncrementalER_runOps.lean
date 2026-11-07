-- Prove2me | Definitions.Def_IncrementalER_runOps
-- name    : IncrementalER_runOps
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:06:04.735207+00:00
-- url     : https://prove2.me/theorems/ad443ac7-981c-453b-8c3e-79e89e6a529a
-- title:
--   Feeding operations online to one program of the randomized real RAM
-- statement:
--   The data structure of Theorem 1.1 is a single program $P$ of the randomized exact-arithmetic real RAM (`PNormReg.Machine`). The operations are given to it one at a time. Operation $j$ is written into the memory left by operation $j-1$:
--
--   1. $\mathrm{InsertEdge}(u,v,c)$ writes the integer words $[0,n,u,v]$ and the real words $[\varepsilon,c]$; $\mathrm{Query}(d)$ with nonzero entries $(v_1,x_1),\dots,(v_s,x_s)$ writes the integer words $[1,n,s,v_1,\dots,v_s]$ and the real words $[\varepsilon,x_1,\dots,x_s]$. Integer word $i$ is stored in integer cell $-1-i$, real word $i$ in real cell $-2-i$.
--   2. The program counter, the registers and the pointers are reset to $0$; both memories, the position on the coin tape and the work counter are kept.
--   3. The program runs until it halts (at most $F$ steps). The answer of a query is real cell $-1$ after its run.
--
--   The final work counter is the total time over all operations. The time bound of Theorem 1.1 is
--
--   $$T(C,n,\varepsilon,M)=C\,M\,(1/\varepsilon)^{C\sqrt{\log n\cdot\log\log n}}$$
--
--   for $M$ operations.
--
--   **Formalization Note** The paper names no machine; the real RAM with rational literals, $+,-,\times,\div,\sqrt{\cdot}$, $|r|^s$, integer pointers, fair coins and no floor is a reading. Operation $j$ never sees a later operation, so the adversary is oblivious and the time bound online. $n$ and $\varepsilon$ come with every operation, so there is no free initialization. Natural logarithms; $\sqrt{\cdot}$ of a negative number is $0$, so for $n\le15$ the bound is $CM$.
-- source:
--   Goranci, Kyng, Probst Gutenberg, Zhao, Zöcklein, Incremental All-Pairs Effective Resistance in Almost-Linear Time, STOC 2027 submission (manuscript sha256 a0415fd5…), Theorem 1.1, p.4 (reading of "there is a data structure … total time")

import Mathlib
import Definitions.Def_PNormReg_Machine
import Definitions.Def_IncrementalER_Op

namespace IncrementalER

/-!
# Feeding the operations online to one program of the real RAM

Goranci, Kyng, Probst Gutenberg, Zhao, Zöcklein, *Incremental All-Pairs Effective Resistance in
Almost-Linear Time*, STOC 2027 submission (manuscript sha256 a0415fd5…), Theorem 1.1, p.4
("There is a data structure that supports the following operations … total time …").

The paper names no machine. The machine is the published randomized exact real RAM
`PNormReg.Machine` (rational literals, `+ − × ÷`, `√`, `|r|^s`, integer pointers and memory, fair
coins, `halt`; no floor and no real-to-integer cast; one finite program for every `n`).

**Formalization Note.**
* *Online feeding.* Operations are given one at a time. Operation `j` is written into the memory
  of the state left by operation `j − 1`, and the program is run on it until it halts. The run
  of operation `j` never sees a later operation, so the adversary is oblivious and the time bound
  is an online one.
* *Cell layout.* `InsertEdge(u, v, c)` writes integer words `[0, n, u, v]` and real words
  `[ε, c]`; `Query(d)` with sparse list `[(v₁, x₁), …, (v_s, x_s)]` writes integer words
  `[1, n, s, v₁, …, v_s]` and real words `[ε, x₁, …, x_s]`. Integer word `i` goes to integer cell
  `−1 − i`, real word `i` to real cell `−2 − i`; other cells are unchanged. The answer of a query
  is real cell `−1` of the state after its run.
* *What is kept.* `load` resets the program counter, all real registers and all pointers to `0`
  and clears the halted flag. It keeps both memories, the coin-tape cursor (the tape continues and
  no coin is reused) and the work counter, so the final `work` is the total time over all
  operations. `n` and `ε` come with every operation, so there is no free initialization run: zero
  operations cost zero time.
* *Fuel.* Each operation is run for `F` steps. A halted state stutters at no cost, so any fuel
  beyond the halting time gives the same state; the theorem takes `F` equal to its time bound and
  asserts that every run has halted.
-/

/-- The integer words of an operation. -/
def opInts {n : ℕ} : Op n → List ℤ
  | .insertEdge u v _ => [0, (n : ℤ), ((u : ℕ) : ℤ), ((v : ℕ) : ℤ)]
  | .query l => [1, (n : ℤ), (l.length : ℤ)] ++ l.map fun p => ((p.1 : ℕ) : ℤ)

/-- The real words of an operation, with `ε` first. -/
def opReals {n : ℕ} (ε : ℝ) : Op n → List ℝ
  | .insertEdge _ _ c => [ε, c]
  | .query l => ε :: l.map Prod.snd

/-- Write an operation into the state `s` left by the previous one: integer word `i` at integer
cell `−1 − i`, real word `i` at real cell `−2 − i`, all other cells unchanged; program counter,
registers and pointers reset to `0`, halted flag cleared; cursor and work kept. -/
noncomputable def load {n : ℕ} (ε : ℝ) (s : PNormReg.State) (op : Op n) : PNormReg.State :=
  let ints := opInts op
  let reals := opReals ε op
  { core :=
      { pc := 0
        regs := fun _ => 0
        ptrs := fun _ => 0
        mem := fun z =>
          if -((reals.length : ℤ) + 1) ≤ z ∧ z ≤ -2 then reals.getD (-2 - z).toNat 0
          else s.core.mem z }
    integerMemory := fun z =>
      if -(ints.length : ℤ) ≤ z ∧ z ≤ -1 then ints.getD (-1 - z).toNat 0
      else s.integerMemory z
    cursor := s.cursor
    halted := false
    work := s.work }

/-- The state after the first `k` operations of `ops`, each run for `F` steps on coin tape `ω`,
starting from the all-zero state `PNormReg.initState [] []`. -/
noncomputable def runOps (P : PNormReg.Program) {n : ℕ} (ε : ℝ) (ops : List (Op n)) (F : ℕ)
    (ω : ℕ → Bool) (k : ℕ) : PNormReg.State :=
  (ops.take k).foldl (fun s op => PNormReg.run P (load ε s op) ω F) (PNormReg.initState [] [])

/-- The answer to operation `j` (0-indexed): real cell `−1` after its run. -/
noncomputable def answer (P : PNormReg.Program) {n : ℕ} (ε : ℝ) (ops : List (Op n)) (F : ℕ)
    (ω : ℕ → Bool) (j : ℕ) : ℝ :=
  (runOps P ε ops F ω (j + 1)).core.mem (-1)

/-- The time bound `C · M · (1/ε)^{C √(log n · log log n)}` of Theorem 1.1 for `M` operations
(natural logarithms; `Real.sqrt` of a negative number is `0`). -/
noncomputable def timeBound (C : ℝ) (n : ℕ) (ε : ℝ) (M : ℕ) : ℝ :=
  C * M * (1 / ε) ^ (C * Real.sqrt (Real.log n * Real.log (Real.log n)))

end IncrementalER


