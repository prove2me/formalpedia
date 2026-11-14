-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Plumbing_Branch
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Plumbing_Branch
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:36:09.805207+00:00
-- url     : https://prove2.me/theorems/64c3812e-ff2a-4636-9f80-3a9af8c2bc7c
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Plumbing.Branch — Branching on a work tape
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Plumbing.Branch` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   `branch i tm₁ tm₂` reads the cell under the head of work tape `i` and then runs `tm₁` if that cell
--   is not blank and `tm₂` if it is. On a `Turing.wordsCfg` configuration the head of tape
--   `i` is on the first cell of its word, so the machine runs `tm₂` exactly when the word on tape `i`
--   is empty.
--
--   ### Main definitions
--
--   * `Turing.MultiTapeTM.branch`: the branching machine.
--
--   ### Main results
--
--   * `Turing.MultiTapeTM.transformsTapes_branch`: a specification of `branch i tm₁ tm₂` from
--     specifications of `tm₁` for a non-empty word on tape `i` and of `tm₂` for an empty one.
--
--   **Contents.** The module is published as a whole: 5 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with library lemmas renamed back to their names in this Mathlib and a few proof steps adjusted; no statement is changed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Plumbing_Branch`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Plumbing/Branch.lean

/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: vendored crei:crei/tidy-universal @7f7c0696 (unsubmitted)
-- vendored: `spaceUsed` is `space` since cslib #1133

public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Plumbing_TransformsTapes

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Plumbing.Branch` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Branching on a work tape

`branch i tm₁ tm₂` reads the cell under the head of work tape `i` and then runs `tm₁` if that cell
is not blank and `tm₂` if it is. On a `Turing.wordsCfg` configuration the head of tape
`i` is on the first cell of its word, so the machine runs `tm₂` exactly when the word on tape `i`
is empty.

## Main definitions

* `Turing.MultiTapeTM.branch`: the branching machine.

## Main results

* `Turing.MultiTapeTM.transformsTapes_branch`: a specification of `branch i tm₁ tm₂` from
  specifications of `tm₁` for a non-empty word on tape `i` and of `tm₂` for an empty one.
-/

namespace Turing.MultiTapeTM

variable {k : ℕ} {Symbol S₁ S₂ : Type*} {input : List Symbol}

/-- Reads the cell under the head of work tape `i`, moving no head and writing nothing, then runs
`tm₁` if the cell is not blank and `tm₂` if it is. -/
public noncomputable def branch (i : Fin k) (tm₁ : MultiTapeTM k Symbol S₁)
    (tm₂ : MultiTapeTM k Symbol S₂) : MultiTapeTM k Symbol (Option (S₁ ⊕ S₂)) :=
  ofTr none fun q inp work =>
    match q with
    | none =>
      { inputTape := 0, workTapes := fun _ => (none, 0), output := none,
        state := some (some ((work i).elim (.inr tm₂.q₀) fun _ => .inl tm₁.q₀)) }
    | some (.inl q) =>
      let a := tm₁.tr q inp work
      { a with state := a.state.map (some ∘ .inl) }
    | some (.inr q) =>
      let a := tm₂.tr q inp work
      { a with state := a.state.map (some ∘ .inr) }

namespace Branch

variable {i : Fin k} {tm₁ : MultiTapeTM k Symbol S₁} {tm₂ : MultiTapeTM k Symbol S₂}

/-- If `branch i tm₁ tm₂` acts in the state `f q` as `tm` acts in `q`, its runs from such states
follow the runs of `tm`. -/
lemma runFrom_mapState {S : Type*} {tm : MultiTapeTM k Symbol S} {f : S → Option (S₁ ⊕ S₂)}
    (htr : ∀ q inp work, (branch i tm₁ tm₂).tr (f q) inp work =
      { tm.tr q inp work with state := (tm.tr q inp work).state.map f })
    (cfg : Cfg k Symbol S input) (n : ℕ) :
    (branch i tm₁ tm₂).runFrom (cfg.mapState (Option.map f)) n =
      (tm.runFrom cfg n).mapState (Option.map f) := by
  refine (Function.Semiconj.iterate_right (fun c => ?_) n cfg).symm
  cases hq : c.state with
  | none => rw [step_of_halt hq, step_of_halt (by simp [hq])]
  | some q => rw [step_of_state hq, step_of_state (q := f q) (by simp [hq]), htr]; rfl

/-- The first step reads tape `i` and starts `tm₁` or `tm₂`. -/
lemma step_check (ws : Fin k → List Symbol) (out : List Symbol) :
    (branch i tm₁ tm₂).step (wordsCfg input (some none) ws out) =
      if ws i = [] then (wordsCfg input (some tm₂.q₀) ws out).mapState (Option.map (some ∘ .inr))
      else (wordsCfg input (some tm₁.q₀) ws out).mapState (Option.map (some ∘ .inl)) := by
  have hsym : (wordsCfg input (some (none : Option (S₁ ⊕ S₂))) ws out).workTapeSymbols i =
      (ws i).head? := by
    simp [Cfg.workTapeSymbols, wordsCfg, tapeOfList_zero]
  rw [step_of_state rfl]
  simp only [branch, tr_ofTr, hsym]
  split_ifs with h
  · rw [h]
    refine Cfg.ext ?_ ?_ ?_ ?_ ?_ <;> simp [Action.apply, Cfg.mapState, wordsCfg]
  · obtain ⟨a, l, hl⟩ := List.exists_cons_of_ne_nil h
    rw [hl]
    refine Cfg.ext ?_ ?_ ?_ ?_ ?_ <;> simp [Action.apply, Cfg.mapState, wordsCfg]

/-- If the first step starts `tm`, with its states mapped by `f`, then a specification of `tm`
gives one of `branch i tm₁ tm₂`, with one more step and at most `k` more cells. -/
lemma transformsTapes_of_step {S : Type*} {tm : MultiTapeTM k Symbol S}
    {f : S → Option (S₁ ⊕ S₂)}
    (htr : ∀ q inp work, (branch i tm₁ tm₂).tr (f q) inp work =
      { tm.tr q inp work with state := (tm.tr q inp work).state.map f })
    {P : (input : List Symbol) → (Fin k → List Symbol) → Prop}
    {Q : (input : List Symbol) → (Fin k → List Symbol) → (Fin k → List Symbol) →
      List Symbol → Prop} {t s : ℕ}
    (hstep : ∀ input ws out, P input ws →
      (branch i tm₁ tm₂).step (wordsCfg input (some none) ws out) =
        (wordsCfg input (some tm.q₀) ws out).mapState (Option.map f))
    (h : TransformsTapes tm P Q t s) :
    TransformsTapes (branch i tm₁ tm₂) P Q (1 + t) (k + s) := by
  -- vendored: `TransformsTapes` is stated with run paths since cslib #1117
  refine transformsTapes_iff_runFrom.mpr fun input ws out hP => ?_
  obtain ⟨ws', e, hrun', hQ, hsp⟩ := transformsTapes_iff_runFrom.mp h input ws out hP
  rw [show (branch i tm₁ tm₂).q₀ = none from rfl]
  refine ⟨ws', e, ?_, hQ, (space_add_le _ _ _).trans (Nat.add_le_add ?_ ?_)⟩
  · rw [runFrom_add, runFrom_one, hstep _ _ _ hP, runFrom_mapState htr, hrun']; rfl
  · -- the first step does not move any head
    refine space_le_of_workTapePos_const _ _ fun m hm => ?_
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hm with rfl | rfl
    · rfl
    · rw [runFrom_one, hstep _ _ _ hP]; rfl
  · rw [runFrom_one, hstep _ _ _ hP, space_eq_of_workTapePos (tm' := tm) _
      (wordsCfg input (some tm.q₀) ws out) t fun m _ => by rw [runFrom_mapState htr]; rfl]
    exact hsp

end Branch

open Branch in
/-- If `tm₁` performs the transformation `Q` within `t₁` steps and `s₁` cells whenever the word on
tape `i` is non-empty, and `tm₂` within `t₂` steps and `s₂` cells whenever it is empty, then
`branch i tm₁ tm₂` performs `Q` with one more step and at most `k` more cells. -/
public theorem transformsTapes_branch (i : Fin k)
    -- vendored: `tm₁` and `tm₂` are bound here, as `autoImplicit` is off
    {tm₁ : MultiTapeTM k Symbol S₁} {tm₂ : MultiTapeTM k Symbol S₂}
    {P : (input : List Symbol) → (Fin k → List Symbol) → Prop}
    {Q : (input : List Symbol) → (Fin k → List Symbol) → (Fin k → List Symbol) →
      List Symbol → Prop} {t₁ s₁ t₂ s₂ : ℕ}
    (h₁ : TransformsTapes tm₁ (fun inp ws => P inp ws ∧ ws i ≠ []) Q t₁ s₁)
    (h₂ : TransformsTapes tm₂ (fun inp ws => P inp ws ∧ ws i = []) Q t₂ s₂) :
    TransformsTapes (branch i tm₁ tm₂) P Q (max t₁ t₂ + 1) (max s₁ s₂ + k) := by
  intro input ws out hP
  by_cases hi : ws i = []
  · exact ((transformsTapes_of_step (f := some ∘ .inr) (fun _ _ _ => by simp [branch])
      (fun _ _ _ h => by rw [step_check, if_pos h.2]) h₂).mono (by omega) (by omega))
      input ws out ⟨hP, hi⟩
  · exact ((transformsTapes_of_step (f := some ∘ .inl) (fun _ _ _ => by simp [branch])
      (fun _ _ _ h => by rw [step_check, if_neg h.2]) h₁).mono (by omega) (by omega))
      input ws out ⟨hP, hi⟩

end Turing.MultiTapeTM


