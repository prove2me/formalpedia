-- Prove2me | Definitions.Def_OnlineBinCover_Online
-- name    : OnlineBinCover_Online
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:48:39.263321+00:00
-- url     : https://prove2.me/theorems/a3244202-19a6-4870-9e5d-a3391a5b70ee
-- title:
--   Deterministic online programs on the real RAM and the online feed of item sizes
-- statement:
--   The paper's online algorithms are read as programs of the published exact real RAM `PNormReg.Machine` (rational literals; exact $+,-,\times,\div$ with $x/0=0$; $\sqrt{\cdot}$; integer pointers and integer memory; a pointer-to-real cast; comparison jumps; halt; unit cost per instruction; no floor and no real-to-integer cast).
--
--   1. A **deterministic program** is the published `DetANN.DetProgram`: an admissible program containing neither the coin instruction nor the power instruction; its runs are taken on the published all-false coin tape, which it never reads.
--   2. **Online feed.** The sizes arrive one at a time. Size number $t$ is written into real cell $-2$ of the state left by the run on item $t-1$; program counter, registers and pointers are reset, and both memories and the work counter are kept. The program then runs for at most $F$ steps. Nothing else is ever written, so the program is never told $n$, $\mathrm{OPT}(I)$, an end marker or a later item.
--   3. **Bins.** The bin of item $t$ is the integer in integer cell $-1$ after its run, so each item is assigned irrevocably before the next one is revealed.
--   4. $A_P(s)$ is the number of covered bins of this labelling when the sizes arrive in the order $s_0,s_1,\dots$.
--
--   This makes "a deterministic polynomial-time online algorithm told neither $n$ nor an estimate of $\mathrm{OPT}(I)$" a finite syntactic object whose running time is counted.
--
--   **Formalization Note** The final work counter is the total time over all items; halted runs stutter at no cost, so any fuel beyond the halting time gives the same state.
-- source:
--   Ayyadevara, Khan, Kumar, Sreenivas, Optimal Online Bin Covering across Stochastic Models, STOC 2027 submission (manuscript sha256 e77e556c…), §1, p.2 (PDF p.3); Theorem 1.3, p.5 (PDF p.6); reading of "deterministic polynomial-time online algorithm"

import Mathlib
import Definitions.Def_PNormReg_Machine
import Definitions.Def_DetANN_DataStructure
import Definitions.Def_OnlineBinCover_Basic

namespace OnlineBinCover

/-!
# Deterministic online programs on the real RAM and the online feed of item sizes

Ayyadevara, Khan, Kumar, Sreenivas, *Optimal Online Bin Covering across Stochastic Models*,
STOC 2027 submission (manuscript sha256 e77e556c…), §1 p.2 ("items arrive one at a time, and each
item must be assigned irrevocably to a bin before the next item is revealed") and Theorem 1.3, p.5
("deterministic polynomial-time online algorithm … given neither n nor an estimate of OPT(I)").

The paper names no machine. The machine is the published exact real RAM `PNormReg.Machine`
(rational literals, `+ − × ÷` with `x / 0 = 0`, `√`, integer pointers and integer memory, a
pointer-to-real cast, comparison jumps, `halt`; no floor and no real-to-integer cast; one finite
program for every input; unit cost per executed instruction).

**Formalization Note.**
* *Deterministic.* Programs are the published `DetANN.DetProgram` (admissible, with no `coin` and
  no `rpow` instruction); their runs are taken on the published all-false tape `DetANN.detTape`,
  which such a program never reads.
* *Online feed.* Item `t`'s size is written into real cell `−2` of the state left by item
  `t − 1`; nothing else is written, so the program never sees `n`, `OPT`, an end marker or a later
  item. `feedLoad` resets the program counter, all real registers and all pointers to `0` and
  clears the halted flag; both memories, the tape cursor and the work counter are kept, so the final
  `work` is the total time over all items. The first item's run starts from
  `PNormReg.initState [] []` (all cells `0`).
* *Fuel.* Each item is run for `F` steps. Halted states stutter at no cost, so fuel beyond the
  halting time gives the same state; theorems take `F` equal to their time bound and assert that
  every run has halted.
* *Labels.* The bin of item `t` is integer cell `−1` after its run; bins are labelled by integers.
  `alg P F s` is the number of covered bins of that labelling when the sizes arrive in the order
  `s 0, s 1, …, s (n − 1)`. Every covered bin counts.
-/

/-- Write the next item size `x` into real cell `−2` of the state left by the previous item, reset
program counter, registers and pointers, clear the halted flag; keep both memories otherwise, the
cursor and the work counter. -/
noncomputable def feedLoad (st : PNormReg.State) (x : ℝ) : PNormReg.State :=
  { core :=
      { pc := 0
        regs := fun _ => 0
        ptrs := fun _ => 0
        mem := Function.update st.core.mem (-2) x }
    integerMemory := st.integerMemory
    cursor := st.cursor
    halted := false
    work := st.work }

/-- The state after the first `t` items of the size list `x`, each fed by `feedLoad` and run for
`F` steps, starting from the all-zero state. -/
noncomputable def feedState (P : PNormReg.Program) (F : ℕ) (x : List ℝ) (t : ℕ) :
    PNormReg.State :=
  (x.take t).foldl (fun st y => PNormReg.run P (feedLoad st y) DetANN.detTape F)
    (PNormReg.initState [] [])

/-- The bin label of item `t` (`0`-based): integer cell `−1` after its run. -/
noncomputable def label (P : PNormReg.Program) (F : ℕ) (x : List ℝ) (t : ℕ) : ℤ :=
  (feedState P F x (t + 1)).integerMemory (-1)

/-- The number of bins covered by program `P` (fuel `F` per item) on the arrival sequence `s`. -/
noncomputable def alg (P : PNormReg.Program) (F : ℕ) {n : ℕ} (s : Fin n → ℝ) : ℕ :=
  covered s (fun t : Fin n => label P F (List.ofFn s) t)

end OnlineBinCover


