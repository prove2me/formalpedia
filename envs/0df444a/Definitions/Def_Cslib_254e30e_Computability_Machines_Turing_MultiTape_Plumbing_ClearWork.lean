-- Prove2me | Definitions.Def_Cslib_254e30e_Computability_Machines_Turing_MultiTape_Plumbing_ClearWork
-- name    : Cslib_254e30e_Computability_Machines_Turing_MultiTape_Plumbing_ClearWork
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:36:58.245225+00:00
-- url     : https://prove2.me/theorems/f6e2a342-2dfd-429f-bc60-cd45e5a54a24
-- title:
--   Cslib.Computability.Machines.Turing.MultiTape.Plumbing.ClearWork — A machine that clears a work tape
-- statement:
--   This is module `Cslib.Computability.Machines.Turing.MultiTape.Plumbing.ClearWork` of [CSLib](https://github.com/leanprover/cslib) (Apache-2.0), at commit `254e30e`: part of its development of multi-tape Turing machines. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states its running-time bounds on these machines.
--
--   `clearWork Symbol` erases the word on its work tape and returns the head to the start. It never
--   moves the input head and never outputs. It is the sequential composition of two one-tape machines:
--
--   * `forwardWork Symbol` moves the head right over the word until it reads the first blank, the
--     frontier just past the word, and halts there (see `Plumbing.ForwardWork`).
--   * `rewindWork Symbol (some none)` rewinds the head to the start, erasing every symbol it walks
--     over.
--
--   On a word of length `l` the forward pass takes `l + 1` steps and the erasing rewind `l + 2` steps.
--   The head stays within the cells `-1, …, l`, so the machine runs in time `3 * (l + 1)` and space
--   `l + 2`; placed on tape `i` of `k` tapes, the remaining tapes contribute one cell each.
--
--   ### Main results
--
--   * `Turing.MultiTapeTM.clearWork`: the one-tape machine that clears its tape.
--   * `Turing.MultiTapeTM.transformsTapes_clearWork`: `clearWork` replaces the word on its tape by the
--     empty word.
--   * `Turing.MultiTapeTM.transformsTapes_clearWork_tapeEmb`: placed on tape `i` of a `k`-tape machine
--     it does so on that tape and leaves every other tape unchanged.
--
--   **Contents.** The module is published as a whole: 3 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Cslib_254e30e_Computability_Machines_Turing_MultiTape_Plumbing_ClearWork`.
-- source:
--   https://github.com/leanprover/cslib/blob/254e30e6d4299c51323aaeaf5f51a4763b375d4a/Cslib/Computability/Machines/Turing/MultiTape/Plumbing/ClearWork.lean

/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Mathlib.Algebra.BigOperators.Fin
public import Definitions.Def_Cslib_254e30e_Computability_Machines_Turing_MultiTape_Plumbing_ExtendTapes
public import Definitions.Def_Cslib_254e30e_Computability_Machines_Turing_MultiTape_Plumbing_ForwardWork
public import Definitions.Def_Cslib_254e30e_Computability_Machines_Turing_MultiTape_Plumbing_RewindWork
public import Definitions.Def_Cslib_254e30e_Computability_Machines_Turing_MultiTape_Plumbing_Sequential

set_option autoImplicit true
set_option relaxedAutoImplicit true

/- Prove2me definition bundle for `Cslib.Computability.Machines.Turing.MultiTape.Plumbing.ClearWork` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# A machine that clears a work tape

`clearWork Symbol` erases the word on its work tape and returns the head to the start. It never
moves the input head and never outputs. It is the sequential composition of two one-tape machines:

* `forwardWork Symbol` moves the head right over the word until it reads the first blank, the
  frontier just past the word, and halts there (see `Plumbing.ForwardWork`).
* `rewindWork Symbol (some none)` rewinds the head to the start, erasing every symbol it walks
  over.

On a word of length `l` the forward pass takes `l + 1` steps and the erasing rewind `l + 2` steps.
The head stays within the cells `-1, …, l`, so the machine runs in time `3 * (l + 1)` and space
`l + 2`; placed on tape `i` of `k` tapes, the remaining tapes contribute one cell each.

## Main results

* `Turing.MultiTapeTM.clearWork`: the one-tape machine that clears its tape.
* `Turing.MultiTapeTM.transformsTapes_clearWork`: `clearWork` replaces the word on its tape by the
  empty word.
* `Turing.MultiTapeTM.transformsTapes_clearWork_tapeEmb`: placed on tape `i` of a `k`-tape machine
  it does so on that tape and leaves every other tape unchanged.
-/

namespace Turing.MultiTapeTM

variable {k : ℕ} {Symbol : Type*} {input : List Symbol}

/-- The one-tape machine that clears its tape: it moves to the end of the word and erases it on
the way back. -/
public noncomputable def clearWork (Symbol : Type*) :
    MultiTapeTM 1 Symbol (Unit ⊕ RewindWorkState) :=
  (forwardWork Symbol).seq (rewindWork Symbol (some none))

open Sequential in
/-- **The machine that clears its work tape** replaces the word on it by the empty word, in at most
`3 * (w.length + 1)` steps and `w.length + 2` cells. -/
public theorem transformsTapes_clearWork (w : List Symbol) :
    TransformsTapes (clearWork Symbol) (fun _ ws => ws 0 = w)
      (fun _ _ ws' emitted => ws' = (fun _ => []) ∧ emitted = [])
      (3 * (w.length + 1)) (w.length + 2) := by
  intro input ws out hws
  obtain rfl : ws = fun _ => w := funext fun x => Fin.fin_one_eq_zero x ▸ hws
  unfold clearWork
  -- the forward pass takes `w.length + 1` steps, the erasing rewind `w.length + 2`
  let p₀ := MultiTapeNTM.RunPath.ofDeterministic (forwardWork Symbol)
    (wordsCfg input (some ()) (fun _ => w) out) (w.length + 1)
  let p₁ := MultiTapeNTM.RunPath.ofDeterministic (rewindWork Symbol (some none))
    (⟨some (rewindWork Symbol (some none)).q₀, 1, fun _ => tapeOfList w, fun _ => w.length, out⟩ :
      Cfg 1 Symbol RewindWorkState input) (w.length + 2)
  have h₀ : p₀.last = _ := runFrom_forwardWork (input := input) 1 w out (zero_add _)
  have h₁ : p₁.last = _ := runFrom_rewindWork_erase (input := input) 1 (tapeOfList w) out rfl
  obtain ⟨p, hh, hl, ht, hmem⟩ := exists_runPath_seq (p₀ := p₀) (p₁ := p₁) (by rw [h₀])
    (by rw [h₀]; rfl) (by rw [h₁])
  refine ⟨fun _ => [], [], ⟨rfl, rfl⟩, p, hh,
    by rw [hl, h₁]; simp [rightCfg, Cfg.mapState, wordsCfg],
    (show p.length ≤ w.length + 1 + (w.length + 2) from ht).trans (by lia), ?_⟩
  -- every head position of the two passes is in `[-1, w.length]`
  rw [MultiTapeNTM.RunPath.space, Fin.sum_univ_one]
  refine (p.spaceUsedByTape_le_card (S := .Icc (-1) (w.length : ℤ)) fun c hc => ?_).trans
    (by simp; lia)
  rcases hmem c hc with ⟨_, ⟨m, rfl⟩, he⟩ | ⟨_, ⟨m, rfl⟩, he⟩ <;>
    rw [show c.workTapePos 0 = _ from congrArg (·.workTapePos 0) he]
  · exact Finset.mem_Icc.2 (Set.Icc_subset_Icc_left (by lia)
      (workTapePos_runFrom_forwardWork (input := input) 1 w out (Nat.zero_le w.length) m))
  · exact Finset.mem_Icc.2
      (workTapePos_runFrom_rewindWork (some none) (input := input) 1 (tapeOfList w) out rfl
        le_rfl m)

/-! ### Clearing one of several work tapes -/

/-- **The machine that clears a work tape**, placed on tape `i` of a `k`-tape machine, replaces the
word on that tape by the empty word and leaves every other tape unchanged, in at most
`3 * (w.length + 1)` steps and `w.length + 1 + k` cells. -/
public theorem transformsTapes_clearWork_tapeEmb (i : Fin k) (w : List Symbol) :
    TransformsTapes ((clearWork Symbol).extendTapes (tapeEmb i)) (fun _ ws => ws i = w)
      (fun _ ws ws' emitted => ws' = Function.update ws i [] ∧ emitted = [])
      (3 * (w.length + 1)) (w.length + 1 + k) :=
  ((transformsTapes_clearWork (Symbol := Symbol) w).tapeEmb i).imp (fun _ _ h => h)
    (fun _ ws ws' _ _ ⟨v, ⟨hv, he⟩, hws'⟩ => ⟨by rw [hws', hv], he⟩) le_rfl
    (by have := i.pos; lia)

end Turing.MultiTapeTM


