-- Prove2me | Definitions.Def_MinKCutII_Main_Runs
-- name    : MinKCutII_Main_Runs
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T03:38:10.33826+00:00
-- url     : https://prove2.me/theorems/5470d9d8-410f-42df-8417-3c47a24d0cd2
-- title:
--   Runs of a randomized word-RAM program: halting, time, output, space, the random-tape law, word size
-- statement:
--   Running times are read on the published randomized word RAM `DynConnWC.Program`: memory cells hold $W$-bit words; instructions are unit-cost addition, subtraction, multiplication, unsigned division and remainder, bitwise and/or/xor and shifts (modulo $2^W$), indirect load and store, a branch and a jump, `read` (the next input word), `write` (append a word to the output), `rand` (the next word of the random tape $\omega:\mathbb N\to\{0,\dots,2^W-1\}$) and `halt`. Each executed instruction is one step.
--
--   A run **halts within $T$ steps** if the configuration after some $t\le T$ steps is halted (program counter at `halt` or outside the program); from then on nothing changes, and the **output** is the list of words written. **Space** is the number of distinct memory cells touched; the input is read once and occupies memory only when stored. A program is **deterministic** if it has no `rand` instruction. The random tape has the law of independent uniform $W$-bit words; a failure probability is the measure of the set of failing tapes. On input words $\mathrm{inp}$ with time bound $T$ the word size is
--   $$W=C\cdot\big\lceil\log_2\big(|\mathrm{inp}|+\textstyle\sum\mathrm{inp}+2+\lceil T\rceil\big)\big\rceil$$
--   with the constant $C$ of the statement: every input word fits in a word and every address up to the running time is addressable.
--
--   **Formalization Note.** The paper names no machine. `tapeLaw` restates the published `DynConnWC.tapeLaw` (product of uniform words) to avoid importing that paper's operation type. For fixed $k$ the word size is $\Theta(\log n)$ bits on the paper's inputs.
-- source:
--   Vaughn, Faster Minimum k-Cut II: Improved Randomized and Deterministic Algorithms for Weighted Graphs, arXiv:2609.27797 (version of November 1, 2026, sha256 b01b5a6f…), pp. 3, 5 (running times, 'with high probability'); machine model is the mission's reading

import Mathlib
import Definitions.Def_DynConnWC_Program

set_option autoImplicit false

open DynConnWC MeasureTheory

namespace MinKCutII.Main

/-!
# Runs of a randomized word-RAM program: halting, time, output, space, the tape law, word size

Vaughn, *Faster Minimum k-Cut II*, arXiv:2609.27797 (version of November 1, 2026, sha256
b01b5a6f…). The paper names no machine model. Its running times are read on the published
randomized word RAM `DynConnWC.Program` (Prove2Me `DynConnWC_Program`): `W`-bit words; unit-cost
`+, −, ×`, unsigned division and remainder, bitwise and/or/xor, shifts (all modulo `2^W`);
indirect load and store; a branch and a jump; `read` (the next input word, so the input is read
once, in order); `write` (append a word to the output); `rand` (the next word `ω c` of the random
tape `ω : ℕ → Fin (2^W)`); `halt`. Every executed instruction is one step.

* `Halted P c`: the program counter is at `halt` or outside the program. `DynConnWC.step` leaves
  such a configuration unchanged, so output and memory are frozen from then on.
* `HaltsWithin W P inp ω T`: some configuration reached after `t ≤ T` steps is halted.
* `finalOutput W P inp ω`: the output list at the first halted configuration (`[]` if the run
  never halts; every statement asserts halting, so this value is never used).
* `SpaceWithin W P inp ω S`: for every `t`, the number of distinct memory cells touched by the
  first `t` steps (`DynConnWC.touchedBetween`) is at most `S`. Input words are not in memory;
  they occupy a cell only once read, so this is working space.
* `IsDeterministic P`: `P` contains no `rand` instruction.
* `tapeLaw W`: the law of the random tape, independent uniform `W`-bit words (the same measure as
  the published `DynConnWC.tapeLaw`, restated here so as not to import that paper's operations).
  A failure probability is the measure of the failure set (an outer measure if the set were not
  measurable).
* Word size. On input words `inp` and a time bound `T`, the word size is
  `wordSize C inp T = C · ⌈log₂(|inp| + Σ inp + 2 + ⌈T⌉)⌉` with the constant `C` of the statement:
  every input word fits in one word, and every cell address up to the time bound is addressable.
  For a fixed `k` this is `Θ(log n)` bits on the paper's inputs (capacities polynomial in `n`).
-/

/-- The law of the random tape: independent uniform `W`-bit words. -/
noncomputable def tapeLaw (W : ℕ) : Measure (ℕ → Fin (2 ^ W)) :=
  Measure.infinitePi (fun _ => (PMF.uniformOfFintype (Fin (2 ^ W))).toMeasure)

/-- Configuration `c` is halted for program `P`. -/
def Halted {W : ℕ} (P : Program) (c : Config W) : Prop :=
  P[c.pc]? = none ∨ P[c.pc]? = some Instr.halt

/-- The run of `P` on input words `inp` and tape `ω` halts within `T` steps. -/
def HaltsWithin (W : ℕ) (P : Program) (inp : List ℕ) (ω : ℕ → Fin (2 ^ W)) (T : ℝ) : Prop :=
  ∃ t : ℕ, (t : ℝ) ≤ T ∧ Halted P (conf W P inp ω t)

open Classical in
/-- The output of the run at its first halted configuration (`[]` if it never halts). -/
noncomputable def finalOutput (W : ℕ) (P : Program) (inp : List ℕ) (ω : ℕ → Fin (2 ^ W)) :
    List ℕ :=
  if h : ∃ t, Halted P (conf W P inp ω t) then (conf W P inp ω (Nat.find h)).output else []

/-- Every prefix of the run touches at most `S` distinct memory cells. -/
def SpaceWithin (W : ℕ) (P : Program) (inp : List ℕ) (ω : ℕ → Fin (2 ^ W)) (S : ℝ) : Prop :=
  ∀ t : ℕ, ((touchedBetween W P inp ω 0 t).ncard : ℝ) ≤ S

/-- `P` is deterministic: it has no `rand` instruction. -/
def IsDeterministic (P : Program) : Prop :=
  ∀ i : ℕ, Instr.rand i ∉ P

/-- `|inp| + Σ inp + 2`, an upper bound on the length and on every entry of the input. -/
def inputMag (inp : List ℕ) : ℕ :=
  inp.length + inp.sum + 2

/-- The word size `C · ⌈log₂(inputMag inp + ⌈T⌉)⌉`. -/
noncomputable def wordSize (C : ℕ) (inp : List ℕ) (T : ℝ) : ℕ :=
  C * Nat.clog 2 (inputMag inp + ⌈T⌉₊)

end MinKCutII.Main


