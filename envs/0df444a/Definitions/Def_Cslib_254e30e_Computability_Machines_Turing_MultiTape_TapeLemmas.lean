-- Prove2me | Definitions.Def_Cslib_254e30e_Computability_Machines_Turing_MultiTape_TapeLemmas
-- name    : Cslib_254e30e_Computability_Machines_Turing_MultiTape_TapeLemmas
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:34:41.284805+00:00
-- url     : https://prove2.me/theorems/d469490c-65dd-425d-8b73-11ca50f82e4e
-- title:
--   Cslib.Computability.Machines.Turing.MultiTape.TapeLemmas — Head movement along run paths
-- statement:
--   This is module `Cslib.Computability.Machines.Turing.MultiTape.TapeLemmas` of [CSLib](https://github.com/leanprover/cslib) (Apache-2.0), at commit `254e30e`: part of its development of multi-tape Turing machines. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states its running-time bounds on these machines.
--
--   This file collects how a step moves the work-tape heads and changes the work tapes, and what this
--   implies for the cells visited along a run path: a head moves by at most one cell per step, so it
--   visits every cell between its first and last positions, and a cell changes only under its head.
--
--   **Contents.** The module is published as a whole: 6 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Cslib_254e30e_Computability_Machines_Turing_MultiTape_TapeLemmas`.
-- source:
--   https://github.com/leanprover/cslib/blob/254e30e6d4299c51323aaeaf5f51a4763b375d4a/Cslib/Computability/Machines/Turing/MultiTape/TapeLemmas.lean

/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Definitions.Def_Cslib_254e30e_Computability_Machines_Turing_MultiTape_Deterministic
public import Mathlib.Data.Int.Interval
public import Mathlib.Order.Lattice.Nat

set_option autoImplicit true
set_option relaxedAutoImplicit true

/- Prove2me definition bundle for `Cslib.Computability.Machines.Turing.MultiTape.TapeLemmas` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Head movement along run paths

This file collects how a step moves the work-tape heads and changes the work tapes, and what this
implies for the cells visited along a run path: a head moves by at most one cell per step, so it
visits every cell between its first and last positions, and a cell changes only under its head.

-/

@[expose] public section

namespace Turing.MultiTapeNTM

variable {k k' : ℕ} {State State' Symbol : Type*} {input input' : List Symbol}
variable {ntm : MultiTapeNTM k Symbol State} {ntm' : MultiTapeNTM k' Symbol State'}

/-- A work-tape head moves by at most one cell in a single step. -/
lemma Step.workTapePos_le {c c' : Cfg k Symbol State input} (h : ntm.Step c c') (i : Fin k) :
    |c'.workTapePos i - c.workTapePos i| ≤ 1 := by
  unfold Step at h
  split at h
  · simp [h]
  · obtain ⟨a, _, rfl⟩ := h
    exact workTapePos_apply_le a c i

/-- A step does not change a work-tape cell away from its head. -/
lemma Step.workTapes_eq_of_ne {c c' : Cfg k Symbol State input} (h : ntm.Step c c') {i : Fin k}
    {z : ℤ} (hz : z ≠ c.workTapePos i) : c'.workTapes i z = c.workTapes i z := by
  unfold Step at h
  split at h
  · simp [h]
  · obtain ⟨a, _, rfl⟩ := h
    rw [Action.apply_workTapes]
    cases ha : (a.workTapes i).1 <;> simp [ha, hz]

namespace RunPath

/-- Every position between the first and the last position of a head along a path is visited,
since the head moves by at most one cell per step. -/
lemma uIcc_workTapePos_subset_visitedByTapeHead (p : ntm.RunPath input) (i : Fin k) :
    Finset.uIcc (p.head.workTapePos i) (p.last.workTapePos i) ⊆ p.visitedByTapeHead i := by
  induction p using RelSeries.inductionOn' with
  | singleton c =>
    simp +instances [visitedByTapeHead, RelSeries.singleton, RelSeries.head, RelSeries.last]
  | snoc p c h ih =>
    have hm := abs_le.mp (Step.workTapePos_le h i)
    rw [RelSeries.head_snoc, RelSeries.last_snoc, visitedByTapeHead_snoc]
    intro z hz
    by_cases he : z = c.workTapePos i
    · exact he ▸ Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (ih (by rw [Finset.mem_uIcc] at hz ⊢; omega))

/-- A work-tape cell that differs between the first and the last configuration of a path was
visited by its head. -/
lemma mem_visitedByTapeHead_of_workTapes_ne (p : ntm.RunPath input) {i : Fin k} {z : ℤ}
    (h : p.last.workTapes i z ≠ p.head.workTapes i z) : z ∈ p.visitedByTapeHead i := by
  induction p using RelSeries.inductionOn' with
  | singleton c => exact absurd rfl h
  | snoc p c hs ih =>
    rw [visitedByTapeHead_snoc]
    refine Finset.mem_insert_of_mem ?_
    by_cases hz : z = p.last.workTapePos i
    · exact hz ▸ Finset.mem_image_of_mem _ (Finset.mem_univ (Fin.last _))
    · rw [RelSeries.last_snoc, RelSeries.head_snoc, Step.workTapes_eq_of_ne hs hz] at h
      exact ih h

/-- Every position visited by a head lies within the space of its tape from its first position. -/
lemma natAbs_le_spaceUsedByTape_of_mem_visited (p : ntm.RunPath input) {i : Fin k} {z : ℤ}
    (hz : z ∈ p.visitedByTapeHead i) :
    (z - p.head.workTapePos i).natAbs ≤ p.spaceUsedByTape i := by
  obtain ⟨n, -, rfl⟩ := Finset.mem_image.mp hz
  -- the prefix up to `n` visits every position between the first position and the one at `n`
  have h := Finset.card_le_card
    ((uIcc_workTapePos_subset_visitedByTapeHead (p.take n) i).trans
      (p.visitedByTapeHead_take_subset n i))
  rw [RelSeries.head_take, RelSeries.last_take, Int.card_uIcc] at h
  change _ ≤ (p.visitedByTapeHead i).card
  omega

/-- A path that starts with every head at cell `0` and visits at most `s` cells keeps its heads
within `[-s, s]`. -/
lemma inWindow_of_space_le {p : ntm.RunPath input} {s : ℕ} (h0 : ∀ i, p.head.workTapePos i = 0)
    (hs : p.space ≤ s) : p.InWindow s := fun c hc i => by
  have hz := p.natAbs_le_spaceUsedByTape_of_mem_visited
    ((p.mem_visitedByTapeHead (i := i)).mpr ⟨c, hc, rfl⟩)
  rw [h0, sub_zero] at hz
  exact mem_window.mpr <| hz.trans <|
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans hs

end RunPath

end Turing.MultiTapeNTM


