-- Prove2me | Definitions.Def_APSPSource_ThreeSumApsp_Machine_Steps
-- name    : APSPSource_ThreeSumApsp_Machine_Steps
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-06T07:24:38.583319+00:00
-- url     : https://prove2.me/theorems/e8df92cc-a967-4f2c-a8b4-2c1837de7c02
-- title:
--   Word-RAM configurations, steps, and code fragments
-- statement:
--   For a word length $W\in\mathbb N$, a machine configuration consists of a natural-number program counter and memory $\mu:\mathbb Z\to\{0,1\}^{W}$. The word corresponding to an integer is its $W$-bit encoding. The predicate that an integer $v$ lies in the signed range is
--
--   $$-2^W\le 2v<2^W.$$
--
--   One machine step either produces the next configuration or returns an accept/reject verdict. It follows the source instruction set: writing one, word arithmetic, indirect load and store, branching on a negative signed word, and the two verdicts. Reading beyond the program gives a reject instruction. Arithmetic is word arithmetic, and indirect addresses are interpreted as signed integers.
--
--   Writing $\operatorname{step}_P(c)=\operatorname{next}(c_1)$ for a step that continues, the relation of $t$ nonhalting steps is defined recursively by
--
--   $$\operatorname{Steps}_P(0,c,c')\iff c=c',\qquad
--   \operatorname{Steps}_P(t+1,c,c')\iff\exists c_1,\ \operatorname{step}_P(c)=\operatorname{next}(c_1)\land\operatorname{Steps}_P(t,c_1,c').$$
--
--   A code fragment occurs at position $q$ when it is a prefix of the program after dropping its first $q$ instructions. The bundle includes immediate rules for locating the two parts of concatenated code, memory effects of straight-line instructions and their lists, and agreement outside a set of cells. A conservative write-set predicate requires explicit destination addresses to belong to the set and excludes indirect stores.
--
--   These interfaces support proofs that generated code implements a routine and preserves memory outside its workspace.
--
--   References:
--
--   1. [Source formalization: signed range and execution steps](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Machine/Steps.lean#L52-L119).
--   2. [Source formalization: code fragments and memory effects](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Machine/Steps.lean#L188-L243).
--   3. [Source formalization: memory agreement](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Machine/Steps.lean#L364-L365).
--   4. [Source formalization: write-set predicate](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Machine/Steps.lean#L394-L398).
-- source:
--   https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Machine/Steps.lean#L52-L56; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Machine/Steps.lean#L93-L112; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Machine/Steps.lean#L116-L119; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Machine/Steps.lean#L188-L204; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Machine/Steps.lean#L220-L222; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Machine/Steps.lean#L226-L243; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Machine/Steps.lean#L364-L365; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Machine/Steps.lean#L394-L398

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Set.Function
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false


/-!
# Running the word RAM: words, steps, pieces of code, straight-line code, branches

What the proofs about compiled code need to know about the word RAM in which the paper's claims are
stated.

* **Words.**  `wd W v` is the word of the integer v.  If v is in the range of signed words
  (`InRange`), the word gives back v (`toInt_wd`).
* **Steps.**  The end statement defines only whole runs (`exec`).  A configuration (`Cfg`) and a
  single step (`step`) are defined here; `exec_succ_of_step` and `exec_succ_of_verdict` say that
  `exec` takes one step at a time.
* **Runs.**  `Steps P n c c'`: exactly n steps lead from c to c', none of them a verdict.
  Runs are composed by `Steps.trans`; a run that ends before a verdict gives the value of `exec`
  (`exec_of_steps`), and more time does not change that value (`exec_mono`).
* **Code.**  `CodeAt P pos l`: the program P has the instructions of the list l from position pos
  on.
* **Straight-line code.**  Six instructions only change the memory (`Straight`, `effect`); a list
  of them runs through in its length (`steps_straight`).
* **Known numbers.**  On cells that hold the words of known numbers, an instruction writes the word
  of a known number: `effect_add`, …, `effect_store` for the memory; `steps_add`, `steps_sub`,
  `steps_load`, `steps_store` for the step.
* **Branches and verdicts.**  A branch on a cell that holds a known number is `steps_bltz`;
  `Steps.branch` turns its two outcomes into the two outcomes of a test.  The verdicts are
  `step_accept` and `step_reject`.
* **Framing.**  `AgreeOutside s m m'`: the memories m and m' are equal outside the set s of cells.
  For code without stores such a set can be read off the text (`WritesIn`, `agreeOutside_effects`).
-/

@[expose] public section

namespace ThreeSumApsp.WordRam

open EndStatement (Instr exec loadWords)

variable {W : ℕ} {P : List Instr}

/-! ## Words -/

/-- The integer v is the signed value of a W-bit word. -/
def InRange (W : ℕ) (v : ℤ) : Prop := -(2 : ℤ) ^ W ≤ 2 * v ∧ 2 * v < (2 : ℤ) ^ W

/-- The word of an integer. -/
abbrev wd (W : ℕ) (v : ℤ) : BitVec W := BitVec.ofInt W v


































/-! ## Configurations and single steps -/

/-- A configuration of the machine: the position of the next instruction and the memory. -/
structure Cfg (W : ℕ) where
  pc : ℕ
  mem : ℤ → BitVec W

/-- One step: the next configuration, or the verdict. -/
def step (P : List Instr) (c : Cfg W) : Cfg W ⊕ Bool :=
  let m := c.mem
  let write (i : ℤ) (v : BitVec W) : Cfg W ⊕ Bool :=
    .inl ⟨c.pc + 1, fun x => if x = i then v else m x⟩
  match P.getD c.pc .reject with
  | .one i => write i 1
  | .add i j k => write i (m j + m k)
  | .sub i j k => write i (m j - m k)
  | .mul i j k => write i (m j * m k)
  | .load i j => write i (m (m j).toInt)
  | .store i j => write (m i).toInt (m j)
  | .bltz i l => .inl ⟨if (m i).toInt < 0 then l else c.pc + 1, m⟩
  | .accept => .inr true
  | .reject => .inr false

/-! ## Runs -/

/-- n steps of the machine, none of which gives a verdict, lead from c to c'. -/
def Steps (P : List Instr) : ℕ → Cfg W → Cfg W → Prop
  | 0, c, c' => c = c'
  | n + 1, c, c' => ∃ c₁, step P c = .inl c₁ ∧ Steps P n c₁ c'


































































/-! ## Pieces of code -/

/-- The program P has the instructions of the list l from position pos on. -/
def CodeAt (P : List Instr) (pos : ℕ) (l : List Instr) : Prop := l <+: P.drop pos

/-- The whole program, from position 0 on. -/
theorem codeAt_self (l : List Instr) : CodeAt l 0 l := List.prefix_refl l

/-- The first part of a piece of code. -/
theorem CodeAt.left {pos : ℕ} {l₁ l₂ : List Instr} (h : CodeAt P pos (l₁ ++ l₂)) :
    CodeAt P pos l₁ :=
  (List.prefix_append l₁ l₂).trans h

/-- The second part of a piece of code follows the first. -/
theorem CodeAt.right {pos : ℕ} {l₁ l₂ : List Instr} (h : CodeAt P pos (l₁ ++ l₂)) :
    CodeAt P (pos + l₁.length) l₂ := by
  obtain ⟨r, hr⟩ := h
  refine ⟨r, ?_⟩
  rw [← List.drop_drop, ← hr, List.append_assoc, List.drop_left]















/-- A piece of code, with its position written differently. -/
theorem CodeAt.cast_pos {pos pos' : ℕ} {l : List Instr} (h : CodeAt P pos l) (hp : pos = pos') :
    CodeAt P pos' l := hp ▸ h

/-! ## Straight-line code -/

/-- The instructions that only change the memory and go on to the next position. -/
def Straight : Instr → Prop
  | .one _ | .add _ _ _ | .sub _ _ _ | .mul _ _ _ | .load _ _ | .store _ _ => True
  | _ => False

/-- What an instruction that only changes the memory does to it. -/
def effect (i : Instr) (m : ℤ → BitVec W) : ℤ → BitVec W :=
  match i with
  | .one i => Function.update m i (wd W 1)
  | .add i j k => Function.update m i (m j + m k)
  | .sub i j k => Function.update m i (m j - m k)
  | .mul i j k => Function.update m i (m j * m k)
  | .load i j => Function.update m i (m (m j).toInt)
  | .store i j => Function.update m (m i).toInt (m j)
  | _ => m

/-- What a list of instructions that only change the memory does to it. -/
def effects (l : List Instr) (m : ℤ → BitVec W) : ℤ → BitVec W := l.foldl (fun m i => effect i m) m


































/-! ## Single instructions on cells that hold known numbers -/

section known

variable {m : ℤ → BitVec W} {i j k a b : ℤ}

















































end known

/-! ## Branches and verdicts -/























/-! ## Framing -/

section framing

variable {s t : Set ℤ} {m m' m₁ m₂ m₃ : ℤ → BitVec W} {a : ℤ}

/-- The memory m' differs from m only in cells of the set s. -/
def AgreeOutside (s : Set ℤ) (m m' : ℤ → BitVec W) : Prop := Set.EqOn m' m sᶜ




























/-- The instruction writes no cell outside s, whatever the memory holds. -/
def WritesIn (s : Set ℤ) : Instr → Prop
  | .one i | .add i _ _ | .sub i _ _ | .mul i _ _ | .load i _ => i ∈ s
  | .store _ _ => False
  | _ => True


















end framing

end ThreeSumApsp.WordRam


