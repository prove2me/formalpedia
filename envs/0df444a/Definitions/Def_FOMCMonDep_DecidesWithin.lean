-- Prove2me | Definitions.Def_FOMCMonDep_DecidesWithin
-- name    : FOMCMonDep_DecidesWithin
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:22:37.943486+00:00
-- url     : https://prove2.me/theorems/30b7309a-4a82-4909-8cce-d57eaca9991f
-- title:
--   Word size threshold, deciding within $t$ steps, outputs, rational inputs
-- statement:
--   The machine is the published deterministic word RAM `TrulySubcubicAPSP`: a finite instruction list over integer-addressed memory of $W$-bit words, each instruction costing one step. This item fixes the conventions of every algorithmic statement of the mission.
--
--   1. **Word size.** A program comes with a factor $b$ and must be correct at every word size $W\ge b\,(\lfloor\log_2(N+2)\rfloor+1)$, where $N$ is the length of the input word list plus the largest absolute value of its entries: the RAM with words of logarithmic length.
--   2. **Deciding.** A program decides a property $p$ within $t$ steps on an input if, started on the memory holding the input in cells $0,1,2,\dots$, it halts within $t$ steps and accepts if $p$ holds and rejects otherwise.
--   3. **Outputs.** An output begins with a given word list if the cells after the input hold it.
--   4. **Rationals.** A rational $\varepsilon$ is input as its numerator and positive denominator.
--
--   **Formalization Note** The word-size threshold is taken on the input size rather than on the vertex count, since sentences, construction sequences and type trees are part of the input, and the largest entry is counted so that every input number fits in a word.
-- source:
--   Dreier, Mählmann, Toruńczyk, First-Order Model Checking on Monadically Dependent Graph Classes, STOC 2027 submission (held manuscript, sha256 98040ab52fa9eeb6577af7e100d83ff2a156142fed0a0178723cec8569510454), §1, p.2 (PDF 4); Part III, p.38 (PDF 40)

import Mathlib
import Definitions.Def_TrulySubcubicAPSP_WordRAM

set_option autoImplicit false

open TrulySubcubicAPSP

namespace FOMCMonDep

/-- The largest absolute value of an entry of a word list (`0` for the empty list). -/
def maxAbs (ws : List ℤ) : ℕ := (ws.map Int.natAbs).foldr max 0

/-- **The word-size threshold.** The machine is the published `TrulySubcubicAPSP` word RAM, whose word size `W` is a
parameter of the run. Dreier, Mählmann, Toruńczyk, *First-Order Model Checking on Monadically Dependent Graph Classes*, STOC 2027 submission (held manuscript, sha256 98040ab5…), Part III, p.38 (PDF 40): "Type trees are represented in the
standard RAM model"; the companion paper [Dre+26] (App. C) uses "the RAM model with words of length O(log n)".
`WordSizeOK b ws W` says that `W` is at least `b · (⌊log₂(N + 2)⌋ + 1)`, where `N` is the length of the input word
list `ws` plus the largest absolute value of its entries.

**Formalization Note.** Every algorithmic statement of this mission fixes `b` together with the program and asks for
correctness at **every** word size above the threshold. The threshold is taken on the input size, not on the vertex
count `n`, because the sentence `φ`, a construction sequence or type trees are part of the input; counting the
largest entry makes sure that every input number (a radius `r`, the numerator of `ε`, a color name) fits in a word.
On the inputs of the goal theorem the largest entry is at most the length plus `4`. -/
def WordSizeOK (b : ℕ) (ws : List ℤ) (W : ℕ) : Prop :=
  b * (Nat.log 2 (ws.length + maxAbs ws + 2) + 1) ≤ W

open Classical in
/-- **Deciding a property within `t` steps.** The program `P`, started at position `0` on the memory holding the word
list `ws` in cells `0, 1, 2, …` (published `loadWords`), halts within `t` steps (the halting step counted) with the
verdict `true` (accept) if `p` holds and `false` (reject) otherwise. `exec P t` is `some` exactly when `P` halts
within `t` steps, so this is a correctness and a running-time statement at once. -/
def DecidesWithin (P : List Instr) (W t : ℕ) (ws : List ℤ) (p : Prop) : Prop :=
  ∃ m, exec P t 0 (loadWords W ws) = some (decide p, m)

/-- **An output that begins with a given word list.** `out a` is the signed word in the `a`-th cell after the input
(the argument of the `spec` of the published `MonDepMW.RunsWithin`); `Emits out ws` says that the output cells
`0, …, |ws| − 1` hold `ws`. Every code written in this mission starts with its own length or is otherwise prefix-free,
so the output object is determined by the output cells. -/
def Emits (out : ℕ → ℤ) (ws : List ℤ) : Prop :=
  ∀ (i : ℕ) (h : i < ws.length), out i = ws[i]

/-- **A rational number as an input**: its numerator and its (positive) denominator. -/
def ratCode (ε : ℚ) : List ℤ := [ε.num, (ε.den : ℤ)]

end FOMCMonDep


