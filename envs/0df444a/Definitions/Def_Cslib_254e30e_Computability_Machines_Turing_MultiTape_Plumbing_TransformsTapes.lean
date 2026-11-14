-- Prove2me | Definitions.Def_Cslib_254e30e_Computability_Machines_Turing_MultiTape_Plumbing_TransformsTapes
-- name    : Cslib_254e30e_Computability_Machines_Turing_MultiTape_Plumbing_TransformsTapes
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:35:08.668116+00:00
-- url     : https://prove2.me/theorems/e243bac3-673c-4019-820e-9f54d3378eb1
-- title:
--   Cslib.Computability.Machines.Turing.MultiTape.Plumbing.TransformsTapes — Machines as transformers of tape words
-- statement:
--   This is module `Cslib.Computability.Machines.Turing.MultiTape.Plumbing.TransformsTapes` of [CSLib](https://github.com/leanprover/cslib) (Apache-2.0), at commit `254e30e`: part of its development of multi-tape Turing machines. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states its running-time bounds on these machines.
--
--   The interface through which combinators use machines: a machine reads words from its work tapes
--   and leaves words on them. A combinator composing such machines talks about words only, never about
--   individual cells, head positions or the set of tapes a machine has touched.
--
--   Configurations are described by *equalities*: `wordsCfg input q ws out` is the configuration whose
--   work tape `i` holds exactly the word `ws i` (contents `tapeOfList (ws i)`, head at the start), with
--   the input head at the start of the input and output `out`. A specification
--   `TransformsTapes tm P Q t s` says: started on word-holding tapes satisfying `P`, the machine has a
--   run path to the halted *normal form* `wordsCfg input none ws' (out ++ emitted)` (every head reset
--   to its initial position, tapes blank outside their words, the word `emitted` appended to the
--   output it was handed), with the new words related to the old ones by `Q`, taking at most `t` steps
--   and visiting at most `s` work-tape cells. The time and space are those of the path, so
--   specifications compose by joining their paths.
--   Requiring this normal form is what lets specifications compose by rewriting: the halting
--   configuration of one machine is already a valid start for the next, so which words survived a step
--   is read off the equation, not re-established cell by cell.
--
--   The output is described as the word the machine *appends*, never as an absolute value, so that a
--   specification is insensitive to the output it is handed — which is what lets specifications
--   compose: along a sequence the emitted words concatenate.
--
--   ### Main definitions
--
--   * `Turing.MultiTapeTM.TransformsTapes`: the specification format described above.
--   * `Turing.MultiTapeTM.nop`: the machine that does nothing.
--
--   ### Main results
--
--   * `Turing.MultiTapeTM.TransformsTapes.imp`: strengthen the precondition, weaken the postcondition
--     and raise the bounds.
--   * `Turing.MultiTapeTM.transformsTapes_iff_nil_output`: the generality in the ambient output is
--     free, so a concrete machine need only be run with no prior output.
--   * `Turing.MultiTapeTM.transformsTapes_nop`: `nop` leaves every word as it was, the first machine of
--     the interface and the check that the format is inhabited as intended.
--
--   **Contents.** The module is published as a whole: 8 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Cslib_254e30e_Computability_Machines_Turing_MultiTape_Plumbing_TransformsTapes`.
-- source:
--   https://github.com/leanprover/cslib/blob/254e30e6d4299c51323aaeaf5f51a4763b375d4a/Cslib/Computability/Machines/Turing/MultiTape/Plumbing/TransformsTapes.lean

/-
Copyright (c) 2026 Christian Reitwiessner and Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module

public import Definitions.Def_Cslib_254e30e_Computability_Machines_Turing_MultiTape_Plumbing_WordsCfg
public import Definitions.Def_Cslib_254e30e_Computability_Machines_Turing_MultiTape_TapeLemmas

set_option autoImplicit true
set_option relaxedAutoImplicit true

/- Prove2me definition bundle for `Cslib.Computability.Machines.Turing.MultiTape.Plumbing.TransformsTapes` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Machines as transformers of tape words

The interface through which combinators use machines: a machine reads words from its work tapes
and leaves words on them. A combinator composing such machines talks about words only, never about
individual cells, head positions or the set of tapes a machine has touched.

Configurations are described by *equalities*: `wordsCfg input q ws out` is the configuration whose
work tape `i` holds exactly the word `ws i` (contents `tapeOfList (ws i)`, head at the start), with
the input head at the start of the input and output `out`. A specification
`TransformsTapes tm P Q t s` says: started on word-holding tapes satisfying `P`, the machine has a
run path to the halted *normal form* `wordsCfg input none ws' (out ++ emitted)` (every head reset
to its initial position, tapes blank outside their words, the word `emitted` appended to the
output it was handed), with the new words related to the old ones by `Q`, taking at most `t` steps
and visiting at most `s` work-tape cells. The time and space are those of the path, so
specifications compose by joining their paths.
Requiring this normal form is what lets specifications compose by rewriting: the halting
configuration of one machine is already a valid start for the next, so which words survived a step
is read off the equation, not re-established cell by cell.

The output is described as the word the machine *appends*, never as an absolute value, so that a
specification is insensitive to the output it is handed — which is what lets specifications
compose: along a sequence the emitted words concatenate.

## Main definitions

* `Turing.MultiTapeTM.TransformsTapes`: the specification format described above.
* `Turing.MultiTapeTM.nop`: the machine that does nothing.

## Main results

* `Turing.MultiTapeTM.TransformsTapes.imp`: strengthen the precondition, weaken the postcondition
  and raise the bounds.
* `Turing.MultiTapeTM.transformsTapes_iff_nil_output`: the generality in the ambient output is
  free, so a concrete machine need only be run with no prior output.
* `Turing.MultiTapeTM.transformsTapes_nop`: `nop` leaves every word as it was, the first machine of
  the interface and the check that the format is inhabited as intended.
-/

@[expose] public section

namespace Turing.MultiTapeTM

open MultiTapeNTM

variable {k : ℕ} {Symbol State : Type*} {input : List Symbol}

/-- `TransformsTapes tm P Q t s`: started in its initial state on tapes holding words `ws` that
satisfy the precondition `P`, the machine has a run path of at most `t` steps, visiting at most `s`
work-tape cells, to the halted configuration whose tapes hold words `ws'` and which has appended
`emitted` to the output it was handed, with `Q input ws ws' emitted`.

The bounds are numbers; a specification whose bounds depend on the data is a *family*
`∀ j, TransformsTapes tm (P j) (Q j) (t j) (s j)` over one fixed machine. -/
def TransformsTapes (tm : MultiTapeTM k Symbol State)
    (P : (input : List Symbol) → (Fin k → List Symbol) → Prop)
    (Q : (input : List Symbol) → (Fin k → List Symbol) → (Fin k → List Symbol) →
      List Symbol → Prop)
    (t s : ℕ) : Prop :=
  ∀ (input : List Symbol) (ws : Fin k → List Symbol) (out : List Symbol), P input ws →
    ∃ ws' emitted, Q input ws ws' emitted ∧ ∃ p : tm.RunPath input,
      p.head = wordsCfg input (some tm.q₀) ws out ∧
      p.last = wordsCfg input none ws' (out ++ emitted) ∧ p.time ≤ t ∧ p.space ≤ s

/-- A `TransformsTapes` statement can be read with a stronger precondition, a weaker postcondition
and larger bounds. -/
theorem TransformsTapes.imp {tm : MultiTapeTM k Symbol State}
    {P P' : (input : List Symbol) → (Fin k → List Symbol) → Prop}
    {Q Q' : (input : List Symbol) → (Fin k → List Symbol) → (Fin k → List Symbol) →
      List Symbol → Prop}
    {t s t' s' : ℕ} (h : TransformsTapes tm P Q t s)
    (hP : ∀ input ws, P' input ws → P input ws)
    (hQ : ∀ input ws ws' emitted, P' input ws → Q input ws ws' emitted → Q' input ws ws' emitted)
    (ht : t ≤ t') (hs : s ≤ s') :
    TransformsTapes tm P' Q' t' s' := by
  intro input ws out hP'
  obtain ⟨ws', emitted, hQ'', p, hhead, hlast, htime, hspace⟩ := h input ws out (hP input ws hP')
  exact ⟨ws', emitted, hQ input ws ws' emitted hP' hQ'', p, hhead, hlast, htime.trans ht,
    hspace.trans hs⟩

/-- A `TransformsTapes` statement can be read with larger bounds. -/
theorem TransformsTapes.mono {tm : MultiTapeTM k Symbol State}
    {P : (input : List Symbol) → (Fin k → List Symbol) → Prop}
    {Q : (input : List Symbol) → (Fin k → List Symbol) → (Fin k → List Symbol) →
      List Symbol → Prop}
    {t s t' s' : ℕ} (h : TransformsTapes tm P Q t s) (ht : t ≤ t') (hs : s ≤ s') :
    TransformsTapes tm P Q t' s' :=
  h.imp (fun _ _ => id) (fun _ _ _ _ _ => id) ht hs

/-- **The ambient output is a concern of sequencing, not of machines.** A specification holds for
every prior output as soon as it holds for none, because a machine never reads what it has already
written. This is where that generality is discharged, once, rather than by every caller: a concrete
machine enters the interface by proving the right-hand side.

The only consumer of the generality is `Turing.MultiTapeTM.transformsTapes_seq`, which runs the
second machine after the first has emitted. -/
theorem transformsTapes_iff_nil_output {tm : MultiTapeTM k Symbol State}
    {P : (input : List Symbol) → (Fin k → List Symbol) → Prop}
    {Q : (input : List Symbol) → (Fin k → List Symbol) → (Fin k → List Symbol) →
      List Symbol → Prop} {t s : ℕ} :
    TransformsTapes tm P Q t s ↔ ∀ input ws, P input ws → ∃ ws' emitted, Q input ws ws' emitted ∧
      ∃ p : tm.RunPath input, p.head = wordsCfg input (some tm.q₀) ws [] ∧
        p.last = wordsCfg input none ws' emitted ∧ p.time ≤ t ∧ p.space ≤ s := by
  constructor
  · intro h input ws hP
    simpa using h input ws [] hP
  · rintro h input ws out hP
    obtain ⟨ws', emitted, hQ, p, hhead, hlast, htime, hspace⟩ := h input ws hP
    -- the run with output `out` is the run without it, mapped by prepending `out`
    exact ⟨ws', emitted, hQ, p.map (tm.prependOutputHom out), by simp [hhead], by simp [hlast],
      htime, hspace⟩

section Nop

/-- The machine that does nothing: it halts on its first step, leaving the configuration
unchanged. -/
def nop (k : ℕ) (Symbol : Type*) : MultiTapeTM k Symbol Unit :=
  ofTr () fun _ _ _ =>
    { inputTape := 0, workTapes := fun _ => (none, 0), output := none, state := none }

/-- A single step of `nop` halts and leaves the words alone. -/
@[simp]
lemma step_nop (ws : Fin k → List Symbol) (out : List Symbol) :
    (nop k Symbol).step (wordsCfg input (some ()) ws out) = wordsCfg input none ws out := by
  rw [step_of_state (by rfl)]
  simp [nop, Action.apply, wordsCfg, SignType.cast]

/-- `nop` reaches its halting configuration after exactly one step. -/
@[simp]
lemma runFrom_nop_one (ws : Fin k → List Symbol) (out : List Symbol) :
    (nop k Symbol).runFrom (wordsCfg input (some ()) ws out) 1 = wordsCfg input none ws out := by
  simpa only [runFrom, Function.iterate_one] using step_nop ws out

/-- **The machine that does nothing** halts in one step, leaving every word as it was and emitting
nothing. Its heads never move, so it visits one cell per tape. This is the first machine of the
interface: it checks that the specification format is inhabited exactly as intended. -/
theorem transformsTapes_nop (k : ℕ) (Symbol : Type*) :
    TransformsTapes (nop k Symbol) (fun _ _ => True)
      (fun _ ws ws' emitted => ws' = ws ∧ emitted = []) 1 k := by
  intro input ws out _
  -- the heads never move, so each head visits only the single cell `0`
  refine ⟨ws, [], ⟨rfl, rfl⟩, .ofDeterministic _ (wordsCfg input (some ()) ws out) 1, rfl,
    by rw [List.append_nil]; exact runFrom_nop_one ws out, le_rfl,
    (RunPath.space_le_sum_card _ (S := fun _ => {0}) ?_).trans_eq (by simp)⟩
  rintro _ ⟨⟨m, hm⟩, rfl⟩ i
  change m < 2 at hm
  rcases (by omega : m = 0 ∨ m = 1) with rfl | rfl <;>
    simp [RunPath.ofDeterministic]

end Nop

end Turing.MultiTapeTM


