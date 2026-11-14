-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Plumbing_TransformsWords
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Plumbing_TransformsWords
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:37:01.230677+00:00
-- url     : https://prove2.me/theorems/779dc0b9-afbf-4d80-98f9-0bc3ae6ac95b
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Plumbing.TransformsWords — Tape transformations given by equations
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Plumbing.TransformsWords` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   `TransformsWords tm ws ws' e t s`: started on the words `ws`, the machine `tm` leaves the words
--   `ws'` and emits `e`, within `t` steps and `s` work-tape cells. Most specifications of the parts of a
--   composed machine are of this form; for them, sequential composition is a plain chain of words, and
--   adapting a specification to other spellings of the words is rewriting.
--
--   ### Main definitions
--
--   * `Turing.MultiTapeTM.TransformsWords`: tape transformations given by equations.
--
--   ### Main results
--
--   * `Turing.MultiTapeTM.TransformsTapes.words`: a specification read on given words.
--   * `Turing.MultiTapeTM.TransformsWords.seq`: sequential composition.
--
--   **Contents.** The module is published as a whole: 5 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Plumbing_TransformsWords`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Plumbing/TransformsWords.lean

/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: vendored crei:crei/tidy-universal @9cce4cc7 (unsubmitted)

public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Plumbing_Sequential

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Plumbing.TransformsWords` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Tape transformations given by equations

`TransformsWords tm ws ws' e t s`: started on the words `ws`, the machine `tm` leaves the words
`ws'` and emits `e`, within `t` steps and `s` work-tape cells. Most specifications of the parts of a
composed machine are of this form; for them, sequential composition is a plain chain of words, and
adapting a specification to other spellings of the words is rewriting.

## Main definitions

* `Turing.MultiTapeTM.TransformsWords`: tape transformations given by equations.

## Main results

* `Turing.MultiTapeTM.TransformsTapes.words`: a specification read on given words.
* `Turing.MultiTapeTM.TransformsWords.seq`: sequential composition.
-/

@[expose] public section

namespace Turing.MultiTapeTM

variable {k : ℕ} {Symbol State State₀ State₁ : Type*}

/-- `TransformsWords tm ws ws' e t s`: started on the words `ws`, the machine `tm` leaves the
words `ws'` and emits `e`, within `t` steps and `s` work-tape cells. -/
abbrev TransformsWords (tm : MultiTapeTM k Symbol State) (ws ws' : Fin k → List Symbol)
    (e : List Symbol) (t s : ℕ) : Prop :=
  TransformsTapes tm (fun _ v => v = ws) (fun _ _ v' e' => v' = ws' ∧ e' = e) t s

/-- **A specification read on given words**: the words satisfy the precondition, and the
postcondition determines the result. -/
theorem TransformsTapes.words {tm : MultiTapeTM k Symbol State}
    {P : List Symbol → (Fin k → List Symbol) → Prop}
    {Q : List Symbol → (Fin k → List Symbol) → (Fin k → List Symbol) → List Symbol → Prop}
    {t s : ℕ} (h : TransformsTapes tm P Q t s) {ws ws' : Fin k → List Symbol} {e : List Symbol}
    (hP : ∀ input, P input ws) (hQ : ∀ input v e', Q input ws v e' → v = ws' ∧ e' = e) :
    TransformsWords tm ws ws' e t s :=
  h.imp (by rintro input _ rfl; exact hP input)
    (by rintro input _ v e' rfl hq; exact hQ input v e' hq) le_rfl le_rfl

namespace TransformsWords

variable {tm : MultiTapeTM k Symbol State} {ws ws' ws₂ ws₂' : Fin k → List Symbol}
  {e e₂ : List Symbol} {t s t' s' : ℕ}

theorem mono (h : TransformsWords tm ws ws' e t s) (ht : t ≤ t') (hs : s ≤ s') :
    TransformsWords tm ws ws' e t' s' :=
  TransformsTapes.mono h ht hs

/-- Other spellings of the words and of the emitted word. -/
theorem congr (h : TransformsWords tm ws ws' e t s) (hws : ws₂ = ws) (hws' : ws' = ws₂')
    (he : e = e₂) : TransformsWords tm ws₂ ws₂' e₂ t s := by
  subst hws hws' he
  exact h

/-- **Sequential composition**: the words left by the first machine are those the second one
starts on, and the emitted words are concatenated. -/
theorem seq {tm₀ : MultiTapeTM k Symbol State₀} {tm₁ : MultiTapeTM k Symbol State₁}
    {ws₀ ws₁ ws₂ : Fin k → List Symbol} {e₀ e₁ : List Symbol} {t₀ s₀ t₁ s₁ : ℕ}
    (h₀ : TransformsWords tm₀ ws₀ ws₁ e₀ t₀ s₀) (h₁ : TransformsWords tm₁ ws₁ ws₂ e₁ t₁ s₁) :
    TransformsWords (tm₀.seq tm₁) ws₀ ws₂ (e₀ ++ e₁) (t₀ + t₁) (s₀ + s₁) :=
  (transformsTapes_seq h₀ h₁ fun _ _ _ _ _ h => h.1).imp (fun _ _ h => h)
    (by rintro _ _ _ _ _ ⟨_, _, _, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, rfl⟩; exact ⟨rfl, rfl⟩) le_rfl le_rfl

end TransformsWords

end Turing.MultiTapeTM


