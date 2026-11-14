-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Plumbing_WhileInput
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Plumbing_WhileInput
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:38:01.920768+00:00
-- url     : https://prove2.me/theorems/0846c2f2-09ab-4f0a-8bb1-793e1f404eec
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Plumbing.WhileInput — Repeating a machine while the input head reads a symbol
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Plumbing.WhileInput` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   `whileInput tm` reads the symbol under the input head and halts if it is blank; otherwise it runs
--   `tm` and repeats. A body that consumes the input from left to right, leaving the input head after
--   what it read (`Turing.MultiTapeTM.TransformsTapesAt`), is thus run until the input is used up.
--
--   ### Main definitions
--
--   * `Turing.MultiTapeTM.inputSymbolAt`: the symbol at a position of the input.
--   * `Turing.MultiTapeTM.whileInput`: the loop.
--
--   ### Main results
--
--   * `Turing.MultiTapeTM.transformsTapesAt_whileInput`: a loop invariant preserved by every round
--     gives a specification of `whileInput tm`, with the times of the rounds adding up.
--
--   **Contents.** The module is published as a whole: 11 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Plumbing_WhileInput`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Plumbing/WhileInput.lean

/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: vendored crei:crei/tidy-universal @7f7c0696 (unsubmitted)
-- vendored: `spaceUsed` is the space of a run path since cslib #1133 and #1122

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Plumbing_Cursor
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Plumbing_RepeatUntilBlank

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Plumbing.WhileInput` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Repeating a machine while the input head reads a symbol

`whileInput tm` reads the symbol under the input head and halts if it is blank; otherwise it runs
`tm` and repeats. A body that consumes the input from left to right, leaving the input head after
what it read (`Turing.MultiTapeTM.TransformsTapesAt`), is thus run until the input is used up.

## Main definitions

* `Turing.MultiTapeTM.inputSymbolAt`: the symbol at a position of the input.
* `Turing.MultiTapeTM.whileInput`: the loop.

## Main results

* `Turing.MultiTapeTM.transformsTapesAt_whileInput`: a loop invariant preserved by every round
  gives a specification of `whileInput tm`, with the times of the rounds adding up.
-/

namespace Turing.MultiTapeTM

variable {k : ℕ} {Symbol State : Type*} {input : List Symbol}

/-- The symbol at position `p` of the input tape holding `input`: blank at both ends. -/
@[expose] public def inputSymbolAt (input : List Symbol) (p : Fin (input.length + 2)) :
    Option Symbol :=
  if p.val = 0 then none else input[p.val - 1]?

public lemma inputSymbol_eq_inputSymbolAt (c : Cfg k Symbol State input) :
    c.inputSymbol = inputSymbolAt input c.inputPos := by
  unfold Cfg.inputSymbol inputSymbolAt
  have := c.inputPos.isLt
  split_ifs <;> grind

/-- From `check`, the machine halts if the input head reads a blank and otherwise starts `tm`,
moving no head. Each round of `tm` returns to `check`. -/
public noncomputable def whileInput (tm : MultiTapeTM k Symbol State) :
    MultiTapeTM k Symbol (RepeatUntilBlankState State) :=
  ofTr .check fun q inp work =>
    match q with
    | .run q =>
      let a := tm.tr q inp work
      { a with state := some (a.state.elim .check .run) }
    | .check =>
      { inputTape := 0, workTapes := fun _ => (none, 0), output := none,
        state := inp.map fun _ => .run tm.q₀ }

-- upstream: vendored crei:crei/tidy-universal @9cce4cc7 (unsubmitted)
-- vendored: the two input-head lemmas below, from that revision's `Plumbing/WhileInput`

/-- A move to the left stops at the blank before the input. -/
@[simp] public lemma val_moveInputPos_neg {n : ℕ} (p : Fin (n + 2)) :
    (moveInputPos p (-1)).val = p.val - 1 := by
  have := val_moveInputPos_eq p (-1)
  simp only [SignType.coe_neg, SignType.coe_one] at this
  omega

/-- A move to the right stops at the blank after the input. -/
@[simp] public lemma val_moveInputPos_pos {n : ℕ} (p : Fin (n + 2)) :
    (moveInputPos p 1).val = min (p.val + 1) (n + 1) := by
  have := val_moveInputPos_eq p 1
  simp only [SignType.coe_one] at this
  omega

namespace WhileInput

variable {tm : MultiTapeTM k Symbol State}

/-- A configuration of `tm` as one of `whileInput tm`: a live state `q` becomes `run q` and the
halted state becomes `check`. -/
def runCfg (cfg : Cfg k Symbol State input) : Cfg k Symbol (RepeatUntilBlankState State) input :=
  cfg.mapState (fun st => some (st.elim .check .run))

lemma step_runCfg (cfg : Cfg k Symbol State input) (h : ¬ cfg.Halted) :
    (whileInput tm).step (runCfg cfg) = runCfg (tm.step cfg) := by
  obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp h
  have hstate : (runCfg cfg).state = some (RepeatUntilBlankState.run q) := by
    simp [runCfg, Cfg.mapState, hq]
  rw [step_of_state hstate, step_of_state hq]
  simp only [whileInput, tr_ofTr]
  rfl

lemma runFrom_runCfg {cfg : Cfg k Symbol State input} {u n : ℕ} (hhalt : tm.HaltsAt cfg u)
    (hn : n ≤ u) :
    (whileInput tm).runFrom (runCfg cfg) n = runCfg (tm.runFrom cfg n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [runFrom_succ, runFrom_succ, ih (by lia), step_runCfg _ (hhalt.not_halted (by lia))]

/-- From `check`, the machine halts on a blank and otherwise starts `tm`. -/
lemma step_check (p : Fin (input.length + 2)) (ws : Fin k → List Symbol) (out : List Symbol) :
    (whileInput tm).step (wordsCfgAt input p (some .check) ws out) =
      wordsCfgAt input p ((inputSymbolAt input p).map fun _ => .run tm.q₀) ws out := by
  rw [step_of_state rfl, inputSymbol_eq_inputSymbolAt]
  refine Cfg.ext ?_ ?_ ?_ ?_ ?_ <;> (try simp [whileInput, Action.apply, moveInputPos_zero]) <;>
    rfl

/-- One round: from `check` with the input head on a symbol, the loop runs `tm` once and is back
in `check`, after at most `τ + 1` steps and with its heads within `[-σ, σ]`. -/
lemma exists_runFrom_round {c : Cfg k Symbol (RepeatUntilBlankState State) input} {t : ℕ}
    {p p' : Fin (input.length + 2)} {w w' : Fin k → List Symbol} {out out' : List Symbol}
    {τ σ : ℕ} (hc : ConfinedRun (whileInput tm) c (wordsCfgAt input p (some .check) w out) t σ)
    (hsym : inputSymbolAt input p ≠ none)
    (hrun : tm.runFrom (wordsCfgAt input p (some tm.q₀) w out) τ = wordsCfgAt input p' none w' out')
    (hsp : (MultiTapeNTM.RunPath.ofDeterministic tm (wordsCfgAt input p (some tm.q₀) w out)
      τ).space ≤ σ) :
    ∃ u ≤ τ, ConfinedRun (whileInput tm) c (wordsCfgAt input p' (some .check) w' out')
      (t + (u + 1)) σ := by
  obtain ⟨u, hu, hhalt⟩ := exists_haltsAt (show (tm.runFrom _ τ).Halted by rw [hrun]; rfl)
  obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.mp hsym
  have hstart : (whileInput tm).step (wordsCfgAt input p (some .check) w out) =
      runCfg (wordsCfgAt input p (some tm.q₀) w out) := by
    rw [step_check, ha]
    rfl
  have hround : (whileInput tm).runFrom (wordsCfgAt input p (some .check) w out) (u + 1) =
      wordsCfgAt input p' (some .check) w' out' := by
    rw [Nat.add_comm, runFrom_add, runFrom_one, hstart, runFrom_runCfg hhalt le_rfl,
      ← hhalt.runFrom_eq hu, hrun]
    rfl
  refine ⟨u, hu, by rw [runFrom_add, hc.reaches, hround], fun l => ?_⟩
  rw [visitedByTapeHead_add, hc.reaches]
  refine Finset.union_subset (hc.confined l) (visitedByTapeHead_subset _ fun m hm => ?_)
  rcases m with _ | m
  · simp [runFrom]
  · rw [Nat.add_comm, runFrom_add, runFrom_one, hstart]
    obtain hlt | rfl := (Nat.lt_succ_iff.mp hm).lt_or_eq
    · rw [runFrom_runCfg hhalt hlt.le]
      exact visitedByTapeHead_subset_Icc _ rfl ((space_mono tm _ hu).trans hsp)
        (MultiTapeNTM.RunPath.mem_visitedByTapeHead_ofDeterministic.mpr ⟨m, by lia, rfl⟩)
    · rw [runFrom_runCfg hhalt le_rfl, ← hhalt.runFrom_eq hu, hrun]
      simp [runCfg]

end WhileInput

open WhileInput in
/-- Let `P n` be a loop invariant after `n` rounds, on the input position, the words on the tapes
and the word emitted so far. If each round `n < rounds` starts on a symbol of the input and takes
`P n` to `P (n + 1)` within `t n` steps and `s` cells, and `P rounds` implies that the input head
is on a blank and that `R` holds, then `whileInput tm` takes `P 0` to `R`. -/
public theorem transformsTapesAt_whileInput {tm : MultiTapeTM k Symbol State}
    {P : ℕ → (input : List Symbol) → Fin (input.length + 2) → (Fin k → List Symbol) →
      List Symbol → Prop}
    {R : (input : List Symbol) → Fin (input.length + 2) → (Fin k → List Symbol) → List Symbol →
      Prop} {rounds : ℕ} {t : ℕ → ℕ} {s : ℕ}
    (hround : ∀ n < rounds, ∀ emitted, TransformsTapesAt tm
      (fun input p ws => P n input p ws emitted)
      (fun input _ _ p' ws' e => P (n + 1) input p' ws' (emitted ++ e)) (t n) s)
    (hmore : ∀ n < rounds, ∀ input p ws emitted, P n input p ws emitted →
      inputSymbolAt input p ≠ none)
    (hend : ∀ input p ws emitted, P rounds input p ws emitted →
      inputSymbolAt input p = none ∧ R input p ws emitted) :
    TransformsTapesAt (whileInput tm) (fun input p ws => P 0 input p ws [])
      (fun input _ _ p' ws' emitted => R input p' ws' emitted)
      (∑ n ∈ Finset.range rounds, (t n + 1) + 1) (2 * k * s + k) := by
  intro input p ws out hP0
  rw [show (whileInput tm).q₀ = .check from rfl]
  set start := wordsCfgAt (State := RepeatUntilBlankState State) input p (some .check) ws out
    with hstart
  -- after `n ≤ rounds` rounds the loop is back in `check` with `P n` holding
  have hrec : ∀ n ≤ rounds, ∃ m ≤ ∑ j ∈ Finset.range n, (t j + 1),
      ∃ (pn : Fin (input.length + 2)) (wsn : Fin k → List Symbol) (acc : List Symbol),
      ConfinedRun (whileInput tm) start (wordsCfgAt input pn (some .check) wsn (out ++ acc)) m s ∧
        P n input pn wsn acc := by
    intro n hn
    induction n with
    | zero =>
      exact ⟨0, by simp, p, ws, [], ⟨by simp [runFrom, hstart], fun l => by
        simp [MultiTapeNTM.RunPath.visitedByTapeHead, MultiTapeNTM.RunPath.ofDeterministic,
          hstart, Finset.subset_iff]⟩, hP0⟩
    | succ n ih =>
      obtain ⟨m, hm, pn, wsn, acc, hc, hPn⟩ := ih (by lia)
      obtain ⟨pn', wsn', e, hrunTm, hQ, hsp⟩ := hround n (by lia) acc input pn wsn (out ++ acc) hPn
      obtain ⟨u, hu, hc'⟩ :=
        exists_runFrom_round hc (hmore n (by lia) input pn wsn acc hPn) hrunTm hsp
      rw [List.append_assoc] at hc'
      exact ⟨m + (u + 1), by rw [Finset.sum_range_succ]; lia, pn', wsn', acc ++ e, hc', hQ⟩
  obtain ⟨m, hm, pLast, wsLast, acc, hc, hPlast⟩ := hrec rounds le_rfl
  obtain ⟨hblank, hR⟩ := hend input pLast wsLast acc hPlast
  have hfinal : (whileInput tm).runFrom start (m + 1) =
      wordsCfgAt input pLast none wsLast (out ++ acc) := by
    rw [runFrom_succ, hc.reaches, step_check, hblank]
    rfl
  have hhalt : ((whileInput tm).runFrom start (m + 1)).Halted := by rw [hfinal]; rfl
  refine ⟨pLast, wsLast, acc, ?_, hR, ?_⟩
  · rw [runFrom_eq_of_halt _ _ (by lia) hhalt, hfinal]
  · rw [space_eq_of_halt _ (by lia) hhalt]
    refine space_le_of_visited_subset_Icc _ _ fun l => ?_
    rw [visitedByTapeHead_add, hc.reaches]
    refine Finset.union_subset (hc.confined l) (visitedByTapeHead_subset _ fun j hj => ?_)
    rcases j with _ | j
    · simp [runFrom]
    · rw [runFrom_eq_of_halt (τ := 1) _ _ (by lia) (by rw [runFrom_one, step_check, hblank]; rfl),
        runFrom_one, step_check, hblank]
      simp

end Turing.MultiTapeTM


