-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Run
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Run
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:36:21.845204+00:00
-- url     : https://prove2.me/theorems/48da690b-9029-4a4c-92d7-1b4923e2d6c5
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Run — Facts about runs of multi-tape machines
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Run` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   Small facts about configurations and runs that are not specific to any construction: the input
--   symbol under the head as a list lookup, the input head move on natural-number positions, the
--   contents of a work tape after an action as a case distinction, the distance a work head can
--   travel, and the initial configuration as a configuration of words.
--
--   ### Main definitions
--
--   * `Turing.inputAt`: the symbol at a position of the input tape.
--   * `Turing.moveInputPosNat`: `Turing.moveInputPos` on positions as natural numbers.
--
--   ### Main results
--
--   * `Turing.Cfg.inputSymbol_eq_inputAt`, `Turing.val_moveInputPos_eq_moveInputPosNat`.
--   * `Turing.Action.apply_workTapes_eq_ite`.
--   * `Turing.MultiTapeTM.abs_workTapePos_runFrom_le`: after `t` steps a work head is within `t` cells
--     of the origin.
--   * `Turing.MultiTapeTM.initCfg_eq_wordsCfg`: the initial configuration has blank work tapes.
--   * `Turing.MultiTapeTM.runFrom_eq_of_runPath`: a path to a halted configuration, read as a run.
--   * `Turing.MultiTapeTM.runsInSpace_iff`: the shared space bound, read on the run of a deterministic
--     machine.
--   * `Turing.MultiTapeTM.ComputesInTimeAndSpace.runFrom_of_le`: a machine that computes within time
--     `t` has halted with its output after any number of steps from `t` on.
--
--   **Contents.** The module is published as a whole: 14 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Run`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Run.lean

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (additions to `Configuration`, `Deterministic` and `TapeLemmas`)

public import Definitions.Def_Cslib_254e30e_Computability_Machines_Turing_MultiTape_Plumbing_WordsCfg
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_TapeLemmas

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Run` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Facts about runs of multi-tape machines

Small facts about configurations and runs that are not specific to any construction: the input
symbol under the head as a list lookup, the input head move on natural-number positions, the
contents of a work tape after an action as a case distinction, the distance a work head can
travel, and the initial configuration as a configuration of words.

## Main definitions

* `Turing.inputAt`: the symbol at a position of the input tape.
* `Turing.moveInputPosNat`: `Turing.moveInputPos` on positions as natural numbers.

## Main results

* `Turing.Cfg.inputSymbol_eq_inputAt`, `Turing.val_moveInputPos_eq_moveInputPosNat`.
* `Turing.Action.apply_workTapes_eq_ite`.
* `Turing.MultiTapeTM.abs_workTapePos_runFrom_le`: after `t` steps a work head is within `t` cells
  of the origin.
* `Turing.MultiTapeTM.initCfg_eq_wordsCfg`: the initial configuration has blank work tapes.
* `Turing.MultiTapeTM.runFrom_eq_of_runPath`: a path to a halted configuration, read as a run.
* `Turing.MultiTapeTM.runsInSpace_iff`: the shared space bound, read on the run of a deterministic
  machine.
* `Turing.MultiTapeTM.ComputesInTimeAndSpace.runFrom_of_le`: a machine that computes within time
  `t` has halted with its output after any number of steps from `t` on.
-/

@[expose] public section

namespace Turing

variable {k : ℕ} {Symbol State : Type*}

/-! ### The input tape -/

/-- The symbol at position `j` of an input tape holding `x`: positions `0` and `x.length + 1` are
the blank end cells, and position `j + 1` holds `x[j]`. -/
def inputAt (x : List Symbol) (j : ℕ) : Option Symbol := if j = 0 then none else x[j - 1]?

theorem Cfg.inputSymbol_eq_inputAt {input : List Symbol} (cfg : Cfg k Symbol State input) :
    cfg.inputSymbol = inputAt input cfg.inputPos.val := by
  have hlt := cfg.inputPos.isLt
  by_cases h : cfg.inputPos.val = 0 ∨ cfg.inputPos.val = input.length + 1
  · rw [inputSymbol_eq_none_of_boundary h]
    rcases h with h | h <;> simp [inputAt, h]
  · push Not at h
    have hlt' : cfg.inputPos.val - 1 < input.length := by omega
    rw [inputSymbolInner (cfg.inputPos.val - 1) (by omega) hlt']
    simp [inputAt, h.1, List.getElem?_eq_getElem hlt']

/-- The input head position after a move `d` from position `j`, on an input of length `n`: the
head is clamped to `0, …, n + 1`. This is `Turing.moveInputPos` on positions as natural numbers. -/
def moveInputPosNat (n j : ℕ) (d : SignType) : ℕ :=
  (min ((n : ℤ) + 1) (max 0 ((j : ℤ) + (d : ℤ)))).toNat

theorem val_moveInputPos_eq_moveInputPosNat {n : ℕ} (pos : Fin (n + 2)) (d : SignType) :
    (moveInputPos pos d).val = moveInputPosNat n pos.val d := by
  have h := val_moveInputPos_eq pos d
  simp only [moveInputPosNat]
  omega

/-- A position on the input tape is reached by one move only from a neighbouring position. -/
theorem le_add_one_of_moveInputPosNat_eq {n j j' : ℕ} {d : SignType} (hj' : j' < n + 2)
    (h : moveInputPosNat n j' d = j) : j - 1 ≤ j' ∧ j' ≤ j + 1 := by
  subst h
  rcases d with _ | _ | _ <;>
    simp only [moveInputPosNat, SignType.zero_eq_zero, SignType.neg_eq_neg_one,
      SignType.pos_eq_one, SignType.coe_zero, SignType.coe_neg_one, SignType.coe_one] <;> omega

/-! ### Work tapes -/

/-- The contents of a work tape after applying an action: the written symbol under the head, if
the action writes one, and the old contents elsewhere. -/
theorem Action.apply_workTapes_eq_ite (a : Action k Symbol State) {input : List Symbol}
    (cfg : Cfg k Symbol State input) (i : Fin k) (z : ℤ) :
    (a.apply cfg).workTapes i z =
      if z = cfg.workTapePos i then ((a.workTapes i).1).getD (cfg.workTapes i z)
      else cfg.workTapes i z := by
  simp only [Action.apply_workTapes]
  rcases (a.workTapes i).1 with _ | s <;> split_ifs with hz <;> simp [hz]

namespace MultiTapeTM

variable {tm : MultiTapeTM k Symbol State}

/-- After `t` steps from the initial configuration, a work head is within `t` cells of the
origin. -/
theorem abs_workTapePos_runFrom_le (x : List Symbol) (t : ℕ) (i : Fin k) :
    |(tm.runFrom (tm.initCfg x) t).workTapePos i| ≤ t := by
  induction t with
  | zero => simp [runFrom]
  | succ t ih =>
    have h := MultiTapeNTM.Step.workTapePos_le
      (step_iff.mpr rfl : tm.Step (tm.runFrom (tm.initCfg x) t) _) i
    rw [runFrom_succ]
    rw [abs_le] at h ih ⊢
    push_cast
    omega

/-- The initial configuration is the configuration with the input and blank work tapes. -/
theorem initCfg_eq_wordsCfg (input : List Symbol) :
    tm.initCfg input = wordsCfg input (some tm.q₀) (fun _ => []) [] :=
  Cfg.init_eq_wordsCfg _ _

/-- A path of a deterministic machine ends where the run from its head does. -/
theorem runPath_last_eq_runFrom {input : List Symbol} (p : tm.RunPath input) :
    p.last = tm.runFrom p.head p.time :=
  runPath_apply_eq_runFrom p (Fin.last _)

/-- A path of a deterministic machine to a halted configuration gives the run from its head at
any later step. -/
theorem runFrom_eq_of_runPath {input : List Symbol} {p : tm.RunPath input} (hp : p.last.Halted)
    {t : ℕ} (ht : p.time ≤ t) : tm.runFrom p.head t = p.last := by
  rw [runPath_last_eq_runFrom] at hp ⊢
  exact runFrom_eq_of_halt tm _ ht hp

/-- A deterministic machine satisfying the shared space bound `s` uses at most `s` cells in every
prefix of its run. -/
theorem space_le_of_runsInSpace {input : List Symbol} {s : ℕ} (h : tm.RunsInSpace input s)
    (t : ℕ) : (MultiTapeNTM.RunPath.ofDeterministic tm (tm.initCfg input) t).space ≤ s :=
  h (MultiTapeNTM.ComputationPath.ofDeterministic tm input t)

/-- A deterministic machine satisfies the shared space bound `s` exactly when every prefix of its
run uses at most `s` cells. -/
theorem runsInSpace_iff {input : List Symbol} {s : ℕ} :
    tm.RunsInSpace input s ↔
      ∀ t, (MultiTapeNTM.RunPath.ofDeterministic tm (tm.initCfg input) t).space ≤ s := by
  refine ⟨space_le_of_runsInSpace, fun h p => ?_⟩
  rw [p.eq_ofDeterministic]
  exact h _

/-- A machine that computes `out` within time `t` has halted with output `out` after any number of
steps from `t` on. -/
theorem ComputesInTimeAndSpace.runFrom_of_le {x out : List Symbol} {t s J : ℕ}
    (h : tm.ComputesInTimeAndSpace x out t s) (hJ : t ≤ J) :
    (tm.runFrom (tm.initCfg x) J).Halted ∧ (tm.runFrom (tm.initCfg x) J).output = out := by
  obtain ⟨⟨u, hu, hout⟩, htime, -⟩ := h
  have hhalt := MultiTapeTM.runsInTime_iff_halted.mp htime
  rw [MultiTapeTM.runFrom_eq_of_halt tm _ hJ hhalt]
  refine ⟨hhalt, ?_⟩
  rcases le_total u t with hut | htu
  · exact (congrArg Cfg.output (MultiTapeTM.runFrom_eq_of_halt tm _ hut hu)).trans hout
  · exact (congrArg Cfg.output (MultiTapeTM.runFrom_eq_of_halt tm _ htu hhalt)).symm.trans hout

end MultiTapeTM

/-- The path of the first `t` steps from `cfg` ends where the run does. -/
@[simp]
theorem MultiTapeNTM.RunPath.last_ofDeterministic (tm : MultiTapeTM k Symbol State)
    {input : List Symbol} (cfg : Cfg k Symbol State input) (t : ℕ) :
    (RunPath.ofDeterministic tm cfg t).last = tm.runFrom cfg t :=
  rfl

end Turing


