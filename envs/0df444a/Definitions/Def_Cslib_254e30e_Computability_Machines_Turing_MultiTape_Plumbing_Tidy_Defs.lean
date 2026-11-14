-- Prove2me | Definitions.Def_Cslib_254e30e_Computability_Machines_Turing_MultiTape_Plumbing_Tidy_Defs
-- name    : Cslib_254e30e_Computability_Machines_Turing_MultiTape_Plumbing_Tidy_Defs
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:35:37.792329+00:00
-- url     : https://prove2.me/theorems/01a43613-701c-4580-90b8-56cc24783632
-- title:
--   Cslib.Computability.Machines.Turing.MultiTape.Plumbing.Tidy.Defs — Tidy computations
-- statement:
--   This is module `Cslib.Computability.Machines.Turing.MultiTape.Plumbing.Tidy.Defs` of [CSLib](https://github.com/leanprover/cslib) (Apache-2.0), at commit `254e30e`: part of its development of multi-tape Turing machines. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states its running-time bounds on these machines.
--
--   A machine computes *tidily* if it clears its work tapes before halting and moves all tape heads
--   to their initial position.
--   This means tidy computations can easily be iterated and when applied to a subset of work tapes,
--   a combinator can run a tidy machine as a subroutine and rely on nothing but the word it emits.
--
--   A tidy computation is defined as a `Turing.MultiTapeTM.TransformsTapes` from blank work tapes to
--   blank work tapes, so the lemmas about tape transformations apply to it directly. The three
--   notions below add tidiness to `Turing.MultiTapeTM.ComputesInTimeAndSpace`,
--   `Turing.MultiTapeTM.ComputesFunInTimeAndSpace` and `Turing.MultiTapeTM.ComputableInTimeAndSpace`.
--
--   ### Main definitions
--
--   * `Turing.MultiTapeTM.ComputesTidilyInTimeAndSpace`: a machine computes an output tidily.
--   * `Turing.MultiTapeTM.ComputesFunTidilyInTimeAndSpace`: a machine computes a function tidily.
--   * `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace`: some machine with binary alphabet and
--     finitely many states computes a function tidily.
--   * `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpaceOfLength`: the same, with bounds on the length
--     of the encoded input.
--
--   ### Main results
--
--   * `Turing.MultiTapeTM.computesTidily_iff`: a tidy computation is a single run path between
--     `Turing.MultiTapeTM.wordsCfg` configurations within the time and space bounds.
--
--   **Contents.** The module is published as a whole: 8 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Cslib_254e30e_Computability_Machines_Turing_MultiTape_Plumbing_Tidy_Defs`.
-- source:
--   https://github.com/leanprover/cslib/blob/254e30e6d4299c51323aaeaf5f51a4763b375d4a/Cslib/Computability/Machines/Turing/MultiTape/Plumbing/Tidy/Defs.lean

/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Definitions.Def_Cslib_254e30e_Computability_Machines_Turing_MultiTape_Plumbing_TransformsTapes

set_option autoImplicit true
set_option relaxedAutoImplicit true

/- Prove2me definition bundle for `Cslib.Computability.Machines.Turing.MultiTape.Plumbing.Tidy.Defs` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Tidy computations

A machine computes *tidily* if it clears its work tapes before halting and moves all tape heads
to their initial position.
This means tidy computations can easily be iterated and when applied to a subset of work tapes,
a combinator can run a tidy machine as a subroutine and rely on nothing but the word it emits.

A tidy computation is defined as a `Turing.MultiTapeTM.TransformsTapes` from blank work tapes to
blank work tapes, so the lemmas about tape transformations apply to it directly. The three
notions below add tidiness to `Turing.MultiTapeTM.ComputesInTimeAndSpace`,
`Turing.MultiTapeTM.ComputesFunInTimeAndSpace` and `Turing.MultiTapeTM.ComputableInTimeAndSpace`.

## Main definitions

* `Turing.MultiTapeTM.ComputesTidilyInTimeAndSpace`: a machine computes an output tidily.
* `Turing.MultiTapeTM.ComputesFunTidilyInTimeAndSpace`: a machine computes a function tidily.
* `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace`: some machine with binary alphabet and
  finitely many states computes a function tidily.
* `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpaceOfLength`: the same, with bounds on the length
  of the encoded input.

## Main results

* `Turing.MultiTapeTM.computesTidily_iff`: a tidy computation is a single run path between
  `Turing.MultiTapeTM.wordsCfg` configurations within the time and space bounds.
-/

@[expose] public section

namespace Turing.MultiTapeTM

variable {k : ℕ} {Symbol State : Type*} {tm : MultiTapeTM k Symbol State} {t s : ℕ}

/-! ### Tidy computations -/

/-- `ComputesTidilyInTimeAndSpace tm input output t s`: started on `input` with blank work tapes,
`tm` halts within `t` steps and `s` work-tape cells, having emitted `output`, with every work tape
blank and every head back at its starting cell. -/
abbrev ComputesTidilyInTimeAndSpace (tm : MultiTapeTM k Symbol State)
    (input output : List Symbol) (t s : ℕ) : Prop :=
  TransformsTapes tm (fun inp ws => inp = input ∧ ws = fun _ => [])
    (fun _ _ ws' emitted => ws' = (fun _ => []) ∧ emitted = output) t s

/-- A tidy computation is a single run path between `Turing.MultiTapeTM.wordsCfg` configurations
with blank work tapes, which emits the output, within the time and space bounds. -/
theorem computesTidily_iff {input output : List Symbol} :
    tm.ComputesTidilyInTimeAndSpace input output t s ↔
      ∃ p : tm.RunPath input, p.head = wordsCfg input (some tm.q₀) (fun _ => []) [] ∧
        p.last = wordsCfg input none (fun _ => []) output ∧ p.time ≤ t ∧ p.space ≤ s := by
  rw [ComputesTidilyInTimeAndSpace, transformsTapes_iff_nil_output]
  refine ⟨fun h => ?_, fun hp inp ws ⟨hinp, hws⟩ => ?_⟩
  · obtain ⟨_, _, ⟨rfl, rfl⟩, hp⟩ := h input (fun _ => []) ⟨rfl, rfl⟩
    exact hp
  · subst hinp hws
    exact ⟨fun _ => [], output, ⟨rfl, rfl⟩, hp⟩

/-- Resource bounds can be weakened. -/
theorem ComputesTidilyInTimeAndSpace.mono {input output : List Symbol} {t' s' : ℕ}
    (h : tm.ComputesTidilyInTimeAndSpace input output t s) (ht : t ≤ t') (hs : s ≤ s') :
    tm.ComputesTidilyInTimeAndSpace input output t' s' :=
  TransformsTapes.mono h ht hs

/-! ### Tidily computing a function -/

variable {α β : Type*}

/-- `ComputesFunTidilyInTimeAndSpace tm encIn encOut f t s`: for every `a`, the machine computes
`encOut (f a)` from `encIn a` tidily, within `t a` steps and `s a` cells. -/
def ComputesFunTidilyInTimeAndSpace (tm : MultiTapeTM k Symbol State)
    (encIn : α ↪ List Symbol) (encOut : β ↪ List Symbol) (f : α → β) (t s : α → ℕ) : Prop :=
  ∀ a, tm.ComputesTidilyInTimeAndSpace (encIn a) (encOut (f a)) (t a) (s a)

/-- Resource bounds can be weakened independently on every input. -/
theorem ComputesFunTidilyInTimeAndSpace.mono {encIn : α ↪ List Symbol} {encOut : β ↪ List Symbol}
    {f : α → β} {t s t' s' : α → ℕ} (h : ComputesFunTidilyInTimeAndSpace tm encIn encOut f t s)
    (ht : ∀ a, t a ≤ t' a) (hs : ∀ a, s a ≤ s' a) :
    ComputesFunTidilyInTimeAndSpace tm encIn encOut f t' s' :=
  fun a => (h a).mono (ht a) (hs a)

/-! ### Tidy computability -/

/-- Some machine with binary alphabet and finitely many states computes `f` tidily within the
bounds `t` and `s`. The bounds include the cost of restoring the tapes. -/
def ComputableTidilyInTimeAndSpace (f : α → β) (encIn : α ↪ List Bool) (encOut : β ↪ List Bool)
    (t s : α → ℕ) : Prop :=
  ∃ (k : ℕ) (State : Type) (_ : Finite State) (tm : MultiTapeTM k Bool State),
    ComputesFunTidilyInTimeAndSpace tm encIn encOut f t s

/-- `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace` with the bounds `t` and `s` evaluated at the
length of the encoded input: the tidy analog of
`Turing.MultiTapeTM.ComputableInTimeAndSpaceOfLength`. -/
abbrev ComputableTidilyInTimeAndSpaceOfLength (f : α → β) (encIn : α ↪ List Bool)
    (encOut : β ↪ List Bool) (t s : ℕ → ℕ) : Prop :=
  ComputableTidilyInTimeAndSpace f encIn encOut
    (fun a => t (encIn a).length) (fun a => s (encIn a).length)

/-- Tidy computability is monotone in the resource bounds. -/
theorem ComputableTidilyInTimeAndSpace.mono {f : α → β} {encIn : α ↪ List Bool}
    {encOut : β ↪ List Bool} {t s t' s' : α → ℕ}
    (h : ComputableTidilyInTimeAndSpace f encIn encOut t s)
    (ht : ∀ a, t a ≤ t' a) (hs : ∀ a, s a ≤ s' a) :
    ComputableTidilyInTimeAndSpace f encIn encOut t' s' :=
  let ⟨k, State, hfinite, tm, htm⟩ := h
  ⟨k, State, hfinite, tm, htm.mono ht hs⟩

end Turing.MultiTapeTM


