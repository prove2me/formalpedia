-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Plumbing_Cursor
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Plumbing_Cursor
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:37:29.962394+00:00
-- url     : https://prove2.me/theorems/58556e5b-d39b-4235-9f18-408442926fe2
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Plumbing.Cursor — Tape transformations with the input head anywhere
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Plumbing.Cursor` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   A `Turing.MultiTapeTM.TransformsTapes` specification starts and ends with the input head on the
--   first symbol of the input. A machine that reads its input once, from left to right, keeps a
--   *cursor* there instead: its input head stays where the last round left it.
--   `TransformsTapesAt` is the same specification format with the position of the input head as part
--   of the precondition and the postcondition.
--
--   A machine that never needs the input is run with its input head frozen (`freezeInput`): then every
--   `TransformsTapes` specification of it holds at any position of the input head
--   (`Turing.MultiTapeTM.TransformsTapes.freezeInput`).
--
--   ### Main definitions
--
--   * `Turing.MultiTapeTM.wordsCfgAt`: `Turing.wordsCfg` with the input head anywhere.
--   * `Turing.MultiTapeTM.TransformsTapesAt`: the specification format.
--   * `Turing.MultiTapeTM.freezeInput`: a machine run on a blank input, with its input head fixed.
--
--   ### Main results
--
--   * `Turing.MultiTapeTM.transformsTapesAt_seq`: sequential composition.
--   * `Turing.MultiTapeTM.TransformsTapesAt.seq_eq`: composition with normalized cursor, tape and
--     emitted-word equalities.
--   * `Turing.MultiTapeTM.TransformsTapes.freezeInput`: a specification of `tm` gives one of
--     `tm.freezeInput` at any position of the input head, which it keeps.
--   * `Turing.MultiTapeTM.transformsTapesAt_rewindInput`: rewinding the input head.
--
--   **Contents.** The module is published as a whole: 24 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Plumbing_Cursor`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Plumbing/Cursor.lean

/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: vendored crei:crei/tidy-universal @7f7c0696 (unsubmitted)
-- vendored: `spaceUsed` is the space of a run path since cslib #1133 and #1122

public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Plumbing_ExtendTapes
public import Definitions.Def_Cslib_254e30e_Computability_Machines_Turing_MultiTape_Plumbing_RewindInput
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Plumbing_Sequential
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Plumbing_TransformsTapes
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Plumbing_TransformsWords

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Plumbing.Cursor` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Tape transformations with the input head anywhere

A `Turing.MultiTapeTM.TransformsTapes` specification starts and ends with the input head on the
first symbol of the input. A machine that reads its input once, from left to right, keeps a
*cursor* there instead: its input head stays where the last round left it.
`TransformsTapesAt` is the same specification format with the position of the input head as part
of the precondition and the postcondition.

A machine that never needs the input is run with its input head frozen (`freezeInput`): then every
`TransformsTapes` specification of it holds at any position of the input head
(`Turing.MultiTapeTM.TransformsTapes.freezeInput`).

## Main definitions

* `Turing.MultiTapeTM.wordsCfgAt`: `Turing.wordsCfg` with the input head anywhere.
* `Turing.MultiTapeTM.TransformsTapesAt`: the specification format.
* `Turing.MultiTapeTM.freezeInput`: a machine run on a blank input, with its input head fixed.

## Main results

* `Turing.MultiTapeTM.transformsTapesAt_seq`: sequential composition.
* `Turing.MultiTapeTM.TransformsTapesAt.seq_eq`: composition with normalized cursor, tape and
  emitted-word equalities.
* `Turing.MultiTapeTM.TransformsTapes.freezeInput`: a specification of `tm` gives one of
  `tm.freezeInput` at any position of the input head, which it keeps.
* `Turing.MultiTapeTM.transformsTapesAt_rewindInput`: rewinding the input head.
-/

@[expose] public section

namespace Turing.MultiTapeTM

variable {k : ℕ} {Symbol State State₀ State₁ : Type*}

/-- The configuration whose work tape `i` holds the word `ws i` with its head at the start, with
the input head at position `p`, in state `q` with output `out`. -/
@[simps]
def wordsCfgAt (input : List Symbol) (p : Fin (input.length + 2)) (q : Option State)
    (ws : Fin k → List Symbol) (out : List Symbol) : Cfg k Symbol State input :=
  ⟨q, p, fun i => tapeOfList (ws i), fun _ => 0, out⟩

@[simp]
lemma wordsCfgAt_one (input : List Symbol) (q : Option State) (ws : Fin k → List Symbol)
    (out : List Symbol) : wordsCfgAt input 1 q ws out = wordsCfg input q ws out := rfl

@[simp]
lemma withState_wordsCfgAt {State' : Type*} (input : List Symbol) (p : Fin (input.length + 2))
    (q : Option State) (ws : Fin k → List Symbol) (out : List Symbol) (q' : Option State') :
    (wordsCfgAt input p q ws out).withState q' = wordsCfgAt input p q' ws out := rfl

/-- `TransformsTapesAt tm P Q t s`: started in its initial state with the input head at position
`p` and on tapes holding words `ws` with `P input p ws`, the machine is halted after `t` steps with
the input head at a position `p'`, on tapes holding words `ws'`, having appended `emitted` to the
output, with `Q input p ws p' ws' emitted`, and having used at most `s` work-tape cells. -/
def TransformsTapesAt (tm : MultiTapeTM k Symbol State)
    (P : (input : List Symbol) → Fin (input.length + 2) → (Fin k → List Symbol) → Prop)
    (Q : (input : List Symbol) → Fin (input.length + 2) → (Fin k → List Symbol) →
      Fin (input.length + 2) → (Fin k → List Symbol) → List Symbol → Prop)
    (t s : ℕ) : Prop :=
  ∀ (input : List Symbol) (p : Fin (input.length + 2)) (ws : Fin k → List Symbol)
    (out : List Symbol), P input p ws →
    ∃ p' ws' emitted,
      tm.runFrom (wordsCfgAt input p (some tm.q₀) ws out) t =
        wordsCfgAt input p' none ws' (out ++ emitted) ∧
      Q input p ws p' ws' emitted ∧
      (MultiTapeNTM.RunPath.ofDeterministic tm (wordsCfgAt input p (some tm.q₀) ws out) t).space ≤ s

namespace TransformsTapesAt

variable {tm : MultiTapeTM k Symbol State}
  {P P' : (input : List Symbol) → Fin (input.length + 2) → (Fin k → List Symbol) → Prop}
  {Q Q' : (input : List Symbol) → Fin (input.length + 2) → (Fin k → List Symbol) →
    Fin (input.length + 2) → (Fin k → List Symbol) → List Symbol → Prop} {t s t' s' : ℕ}

/-- A stronger precondition, a weaker postcondition and larger bounds. -/
theorem imp (h : TransformsTapesAt tm P Q t s) (hP : ∀ input p ws, P' input p ws → P input p ws)
    (hQ : ∀ input p ws p' ws' e, P' input p ws → Q input p ws p' ws' e → Q' input p ws p' ws' e)
    (ht : t ≤ t') (hs : s ≤ s') : TransformsTapesAt tm P' Q' t' s' := by
  intro input p ws out hP'
  obtain ⟨p₁, ws₁, e, hrun, hQ₁, hsp⟩ := h input p ws out (hP input p ws hP')
  have hhalt : (tm.runFrom (wordsCfgAt input p (some tm.q₀) ws out) t).Halted := by
    rw [hrun]; rfl
  exact ⟨p₁, ws₁, e, by rw [runFrom_eq_of_halt _ _ ht hhalt, hrun], hQ input p ws p₁ ws₁ e hP' hQ₁,
    by rw [space_eq_of_halt _ ht hhalt]; exact hsp.trans hs⟩

end TransformsTapesAt

/-- A `TransformsTapes` specification is a `TransformsTapesAt` specification with the input head at
the start before and after. -/
theorem TransformsTapes.transformsTapesAt {tm : MultiTapeTM k Symbol State}
    {P : (input : List Symbol) → (Fin k → List Symbol) → Prop}
    {Q : (input : List Symbol) → (Fin k → List Symbol) → (Fin k → List Symbol) →
      List Symbol → Prop} {t s : ℕ} (h : TransformsTapes tm P Q t s) :
    TransformsTapesAt tm (fun input p ws => p = 1 ∧ P input ws)
      (fun input _ ws p' ws' e => p' = 1 ∧ Q input ws ws' e) t s := by
  rintro input _ ws out ⟨rfl, hP⟩
  -- vendored: `TransformsTapes` is stated with run paths since cslib #1117
  obtain ⟨ws', e, hrun, hQ, hsp⟩ := transformsTapes_iff_runFrom.mp h input ws out hP
  exact ⟨1, ws', e, hrun, ⟨rfl, hQ⟩, hsp⟩

/-- A `TransformsTapesAt` specification from and to the start of the input is a `TransformsTapes`
specification. -/
theorem TransformsTapesAt.transformsTapes {tm : MultiTapeTM k Symbol State}
    {P : (input : List Symbol) → Fin (input.length + 2) → (Fin k → List Symbol) → Prop}
    {Q : (input : List Symbol) → Fin (input.length + 2) → (Fin k → List Symbol) →
      Fin (input.length + 2) → (Fin k → List Symbol) → List Symbol → Prop} {t s : ℕ}
    (h : TransformsTapesAt tm P Q t s)
    (hQ : ∀ input p ws p' ws' e, Q input p ws p' ws' e → p' = 1) :
    TransformsTapes tm (fun input ws => P input 1 ws) (fun input ws ws' e => Q input 1 ws 1 ws' e)
      t s := by
  -- vendored: `TransformsTapes` is stated with run paths since cslib #1117
  refine transformsTapes_iff_runFrom.mpr fun input ws out hP => ?_
  obtain ⟨p', ws', e, hrun, hQ', hsp⟩ := h input 1 ws out hP
  obtain rfl := hQ _ _ _ _ _ _ hQ'
  exact ⟨ws', e, hrun, hQ', hsp⟩

open Sequential in
/-- **Sequential composition.** If the postcondition of the first specification implies the
precondition of the second, the composed machine performs the two one after the other. -/
theorem transformsTapesAt_seq {tm₀ : MultiTapeTM k Symbol State₀}
    {tm₁ : MultiTapeTM k Symbol State₁}
    {P₀ P₁ : (input : List Symbol) → Fin (input.length + 2) → (Fin k → List Symbol) → Prop}
    {Q₀ Q₁ : (input : List Symbol) → Fin (input.length + 2) → (Fin k → List Symbol) →
      Fin (input.length + 2) → (Fin k → List Symbol) → List Symbol → Prop} {t₀ s₀ t₁ s₁ : ℕ}
    (h₀ : TransformsTapesAt tm₀ P₀ Q₀ t₀ s₀) (h₁ : TransformsTapesAt tm₁ P₁ Q₁ t₁ s₁)
    (hmid : ∀ input p ws p' ws' e, P₀ input p ws → Q₀ input p ws p' ws' e → P₁ input p' ws') :
    TransformsTapesAt (tm₀.seq tm₁) P₀
      (fun input p ws p'' ws'' e => ∃ p' ws' e₀ e₁, Q₀ input p ws p' ws' e₀ ∧
        Q₁ input p' ws' p'' ws'' e₁ ∧ e = e₀ ++ e₁)
      (t₀ + t₁) (s₀ + s₁) := by
  intro input p ws out hP₀
  obtain ⟨p', ws', e₀, hrun₀, hQ₀, hspace₀⟩ := h₀ input p ws out hP₀
  obtain ⟨p'', ws'', e₁, hrun₁, hQ₁, hspace₁⟩ :=
    h₁ input p' ws' (out ++ e₀) (hmid input p ws p' ws' e₀ hP₀ hQ₀)
  have hstart : wordsCfgAt input p (some (tm₀.seq tm₁).q₀) ws out =
      leftCfg tm₁ (wordsCfgAt input p (some tm₀.q₀) ws out) := rfl
  refine ⟨p'', ws'', e₀ ++ e₁, ?_, ⟨p', ws', e₀, e₁, hQ₀, hQ₁, rfl⟩, ?_⟩
  · rw [hstart, runFrom_seq hrun₀ rfl (by simpa using hrun₁) rfl]
    rfl
  · rw [hstart]
    refine (space_seq_le hrun₀ rfl (by rw [withState_wordsCfgAt, hrun₁]; rfl)).trans ?_
    simpa using Nat.add_le_add hspace₀ hspace₁

-- upstream: candidate
/-- Sequential composition with normalized cursor, tape and emitted-word equalities. -/
theorem TransformsTapesAt.seq_eq {tm₀ : MultiTapeTM k Symbol State₀}
    {tm₁ : MultiTapeTM k Symbol State₁}
    {P : (input : List Symbol) → Fin (input.length + 2) → (Fin k → List Symbol) → Prop}
    {R : List Symbol → Prop} {p₁ p₂ : ℕ} {ws₁ ws₂ : Fin k → List Symbol}
    {e₀ e₁ : List Symbol} {t₀ s₀ t₁ s₁ : ℕ}
    (h₀ : TransformsTapesAt tm₀ P
      (fun input _ _ p' ws' e => R input ∧ p'.val = p₁ ∧ ws' = ws₁ ∧ e = e₀) t₀ s₀)
    (h₁ : TransformsTapesAt tm₁ (fun input p ws => R input ∧ p.val = p₁ ∧ ws = ws₁)
      (fun input _ _ p' ws' e => R input ∧ p'.val = p₂ ∧ ws' = ws₂ ∧ e = e₁) t₁ s₁) :
    TransformsTapesAt (tm₀.seq tm₁) P
      (fun input _ _ p' ws' e => R input ∧ p'.val = p₂ ∧ ws' = ws₂ ∧ e = e₀ ++ e₁)
      (t₀ + t₁) (s₀ + s₁) :=
  (transformsTapesAt_seq h₀ h₁ fun _ _ _ _ _ _ _ h => ⟨h.1, h.2.1, h.2.2.1⟩).imp
    (fun _ _ _ h => h)
    (by rintro _ _ _ _ _ _ _ ⟨_, _, _, _, ⟨hR, _, _, rfl⟩, ⟨_, hp, hws, rfl⟩, rfl⟩
        exact ⟨hR, hp, hws, rfl⟩) le_rfl le_rfl

/-- A fixed-input tape transformation, with its cursor equalities normalized. -/
theorem TransformsTapes.transformsTapesAt_eq {tm : MultiTapeTM k Symbol State}
    {x e : List Symbol} {ws₀ ws₁ : Fin k → List Symbol} {t s : ℕ}
    (h : TransformsTapes tm (fun input ws => input = x ∧ ws = ws₀)
      (fun _ _ ws' e' => ws' = ws₁ ∧ e' = e) t s) :
    TransformsTapesAt tm (fun input p ws => input = x ∧ p.val = 1 ∧ ws = ws₀)
      (fun input _ _ p' ws' e' => input = x ∧ p'.val = 1 ∧ ws' = ws₁ ∧ e' = e) t s :=
  h.transformsTapesAt.imp (fun _ _ _ ⟨hin, hp, hws⟩ => ⟨Fin.ext hp, hin, hws⟩)
    (fun _ _ _ _ _ _ ⟨hin, _, _⟩ ⟨hp, hws, he⟩ => ⟨hin, by simp [hp], hws, he⟩) le_rfl le_rfl

-- upstream: vendored crei:crei/tidy-universal @7f7c0696 (unsubmitted)
/-! ### Freezing the input head -/

/-- `tm`, run as if on a blank input: it reads a blank on the input tape and never moves its input
head. -/
noncomputable def freezeInput (tm : MultiTapeTM k Symbol State) : MultiTapeTM k Symbol State :=
  ofTr tm.q₀ fun q _ work => { tm.tr q none work with inputTape := 0 }

namespace FreezeInput

variable {tm : MultiTapeTM k Symbol State} {input : List Symbol}

/-- A configuration on the empty input, with the input head placed at `p` on `input`. -/
def atPos (p : Fin (input.length + 2)) (c : Cfg k Symbol State []) : Cfg k Symbol State input :=
  ⟨c.state, p, c.workTapes, c.workTapePos, c.output⟩

lemma step_atPos (p : Fin (input.length + 2)) (c : Cfg k Symbol State []) :
    tm.freezeInput.step (atPos p c) = atPos p (tm.step c) := by
  cases hq : c.state with
  | none =>
    rw [step_of_halt (show (atPos p c).state = none from hq), step_of_halt hq]
  | some q =>
    rw [step_of_state (show (atPos p c).state = some q from hq), step_of_state hq,
      inputSymbol_eq_none_of_boundary (cfg := c)
        (by have := c.inputPos.isLt; simp only [List.length_nil] at this ⊢; omega),
      show (atPos (input := input) p c).workTapeSymbols = c.workTapeSymbols from rfl]
    refine Cfg.ext ?_ ?_ ?_ ?_ ?_ <;> simp [freezeInput, atPos, Action.apply, moveInputPos_zero]

lemma runFrom_atPos (p : Fin (input.length + 2)) (c : Cfg k Symbol State []) (n : ℕ) :
    tm.freezeInput.runFrom (atPos p c) n = atPos p (tm.runFrom c n) :=
  (Function.Semiconj.iterate_right (fun c => (step_atPos (tm := tm) p c).symm) n c).symm

end FreezeInput

open FreezeInput in
/-- A specification of `tm` on the empty input is a specification of `tm.freezeInput` at any
position of the input head, which it keeps. -/
theorem TransformsTapes.freezeInput {tm : MultiTapeTM k Symbol State}
    {P : (input : List Symbol) → (Fin k → List Symbol) → Prop}
    {Q : (input : List Symbol) → (Fin k → List Symbol) → (Fin k → List Symbol) →
      List Symbol → Prop} {t s : ℕ} (h : TransformsTapes tm P Q t s) :
    TransformsTapesAt tm.freezeInput (fun _ _ ws => P [] ws)
      (fun _ p ws p' ws' e => p' = p ∧ Q [] ws ws' e) t s := by
  intro input p ws out hP
  -- vendored: `TransformsTapes` is stated with run paths since cslib #1117
  obtain ⟨ws', e, hrun, hQ, hsp⟩ := transformsTapes_iff_runFrom.mp h [] ws out hP
  have hstart : wordsCfgAt input p (some tm.freezeInput.q₀) ws out =
      atPos p (wordsCfg [] (some tm.q₀) ws out) := rfl
  refine ⟨p, ws', e, ?_, ⟨rfl, hQ⟩, ?_⟩
  · rw [hstart, runFrom_atPos, hrun]
    rfl
  · rw [hstart, space_eq_of_workTapePos _ (wordsCfg [] (some tm.q₀) ws out) t
      fun m _ => by rw [runFrom_atPos]; rfl]
    exact hsp

-- upstream: candidate
/-- A fixed tape transformation at an unchanged cursor, with normalized equalities. -/
theorem TransformsTapes.freezeInput_eq {tm : MultiTapeTM k Symbol State}
    {ws₀ ws₁ : Fin k → List Symbol} {e : List Symbol} {t s : ℕ}
    (h : TransformsTapes tm (fun _ ws => ws = ws₀) (fun _ _ ws' e' => ws' = ws₁ ∧ e' = e) t s)
    (x : List Symbol) (p : ℕ) :
    TransformsTapesAt tm.freezeInput (fun input p' ws => input = x ∧ p'.val = p ∧ ws = ws₀)
      (fun input _ _ p' ws' e' => input = x ∧ p'.val = p ∧ ws' = ws₁ ∧ e' = e) t s :=
  h.freezeInput.imp (fun _ _ _ h => h.2.2)
    (fun _ _ _ _ _ _ ⟨hin, hp, _⟩ ⟨hp', hws, he⟩ => ⟨hin, by simpa [hp'] using hp, hws, he⟩)
    le_rfl le_rfl

-- upstream: vendored crei:crei/tidy-universal @7f7c0696 (unsubmitted)
/-! ### Rewinding the input head -/

/-- `rewindInput` on a machine with `k` work tapes. -/
noncomputable def rewindInputOn (k : ℕ) (Symbol : Type*) :
    MultiTapeTM k Symbol RewindState :=
  (rewindInput Symbol).extendTapes (noTapes k)

/-- `rewindInputOn k Symbol` moves the input head from anywhere on the input `x` back to its start
and changes nothing else. -/
theorem transformsTapesAt_rewindInput (x : List Symbol) :
    TransformsTapesAt (rewindInputOn k Symbol) (fun input _ _ => input = x)
      (fun _ _ ws p' ws' e => p' = 1 ∧ ws' = ws ∧ e = []) (x.length + 2) k := by
  rintro input p ws out rfl
  have hrun : (rewindInputOn k Symbol).runFrom
      (wordsCfgAt input p (some (rewindInputOn k Symbol).q₀) ws out) (p.val - 1 + 2) =
        wordsCfgAt input 1 none ws (out ++ []) := by
    have hcfg : noTapesCfg (wordsCfgAt input p (some (rewindInputOn k Symbol).q₀) ws out) =
        ⟨some (rewindInput Symbol).q₀, p, nofun, nofun, out⟩ :=
      Cfg.ext rfl rfl (Subsingleton.elim _ _) (Subsingleton.elim _ _) rfl
    rw [rewindInputOn] at hcfg ⊢
    rw [runFrom_noTapes, hcfg, runFrom_rewindInput, List.append_nil]
    rfl
  have hhalt : ((rewindInputOn k Symbol).runFrom
      (wordsCfgAt input p (some (rewindInputOn k Symbol).q₀) ws out) (p.val - 1 + 2)).Halted := by
    rw [hrun]; rfl
  refine ⟨1, ws, [], ?_, ⟨rfl, rfl, rfl⟩, space_noTapes_le _ _ _⟩
  rw [runFrom_eq_of_halt _ _ (by have := p.isLt; omega) hhalt, hrun]

-- upstream: vendored crei:crei/tidy-universal @9cce4cc7 (unsubmitted)
-- vendored: the `TransformsWordsAt` block below, from that revision's `Plumbing/Cursor`

/-- `TransformsWordsAt tm x p p' ws ws' e t s`: on the input `x` with the input head at the
position `p`, the machine `tm` takes the words `ws` to the words `ws'` emitting `e`, with the input
head ending at `p'`, within `t` steps and `s` work-tape cells. -/
abbrev TransformsWordsAt (tm : MultiTapeTM k Symbol State) (x : List Symbol) (p p' : ℕ)
    (ws ws' : Fin k → List Symbol) (e : List Symbol) (t s : ℕ) : Prop :=
  TransformsTapesAt tm (fun input q v => input = x ∧ q.val = p ∧ v = ws)
    (fun input _ _ q' v' e' => input = x ∧ q'.val = p' ∧ v' = ws' ∧ e' = e) t s

/-- **A specification read on given words**, on the input `x` with the input head at `p`. -/
theorem TransformsTapesAt.wordsAt {tm : MultiTapeTM k Symbol State}
    {P : (input : List Symbol) → Fin (input.length + 2) → (Fin k → List Symbol) → Prop}
    {Q : (input : List Symbol) → Fin (input.length + 2) → (Fin k → List Symbol) →
      Fin (input.length + 2) → (Fin k → List Symbol) → List Symbol → Prop} {t s : ℕ}
    (h : TransformsTapesAt tm P Q t s) {x : List Symbol} {p p' : ℕ} {ws ws' : Fin k → List Symbol}
    {e : List Symbol} (hP : ∀ q : Fin (x.length + 2), q.val = p → P x q ws)
    (hQ : ∀ (q q' : Fin (x.length + 2)) v e', q.val = p → Q x q ws q' v e' →
      q'.val = p' ∧ v = ws' ∧ e' = e) :
    TransformsWordsAt tm x p p' ws ws' e t s :=
  h.imp (by rintro _ q _ ⟨rfl, hq, rfl⟩; exact hP q hq)
    (by rintro _ q _ q' v e' ⟨rfl, hq, rfl⟩ hQ'; exact ⟨rfl, hQ q q' v e' hq hQ'⟩) le_rfl le_rfl

/-- A specification given by equations, with the input head fixed. -/
theorem TransformsWords.freezeInput {tm : MultiTapeTM k Symbol State}
    {ws ws' : Fin k → List Symbol} {e : List Symbol} {t s : ℕ}
    (h : TransformsWords tm ws ws' e t s) (x : List Symbol) (p : ℕ) :
    TransformsWordsAt tm.freezeInput x p p ws ws' e t s :=
  (TransformsTapes.freezeInput h).wordsAt (fun _ _ => rfl)
    fun _ _ _ _ hq ⟨hq', h⟩ => ⟨by rw [hq', hq], h⟩

namespace TransformsWordsAt

variable {tm : MultiTapeTM k Symbol State} {x : List Symbol} {p p' p₂ p₂' : ℕ}
  {ws ws' ws₂ ws₂' : Fin k → List Symbol} {e e₂ : List Symbol} {t s t' s' : ℕ}

theorem mono (h : TransformsWordsAt tm x p p' ws ws' e t s) (ht : t ≤ t') (hs : s ≤ s') :
    TransformsWordsAt tm x p p' ws ws' e t' s' :=
  TransformsTapesAt.imp h (fun _ _ _ h => h) (fun _ _ _ _ _ _ _ h => h) ht hs

/-- Other spellings of the positions, the words and the emitted word. -/
theorem congr (h : TransformsWordsAt tm x p p' ws ws' e t s) (hp : p₂ = p) (hp' : p' = p₂')
    (hws : ws₂ = ws) (hws' : ws' = ws₂') (he : e = e₂) :
    TransformsWordsAt tm x p₂ p₂' ws₂ ws₂' e₂ t s := by
  subst hp hp' hws hws' he
  exact h

/-- **Sequential composition**: the position and the words left by the first machine are those
the second one starts on, and the emitted words are concatenated. -/
theorem seq {tm₀ : MultiTapeTM k Symbol State₀} {tm₁ : MultiTapeTM k Symbol State₁}
    {p₀ p₁ p₂ : ℕ} {ws₀ ws₁ ws₂ : Fin k → List Symbol} {e₀ e₁ : List Symbol}
    {t₀ s₀ t₁ s₁ : ℕ} (h₀ : TransformsWordsAt tm₀ x p₀ p₁ ws₀ ws₁ e₀ t₀ s₀)
    (h₁ : TransformsWordsAt tm₁ x p₁ p₂ ws₁ ws₂ e₁ t₁ s₁) :
    TransformsWordsAt (tm₀.seq tm₁) x p₀ p₂ ws₀ ws₂ (e₀ ++ e₁) (t₀ + t₁) (s₀ + s₁) :=
  (transformsTapesAt_seq h₀ h₁ fun _ _ _ _ _ _ _ ⟨hin, hq, hv, _⟩ => ⟨hin, hq, hv⟩).imp
    (fun _ _ _ h => h)
    (by rintro _ _ _ _ _ _ _ ⟨_, _, _, _, ⟨rfl, -, rfl, rfl⟩, ⟨-, hq, rfl, rfl⟩, rfl⟩
        exact ⟨rfl, hq, rfl, rfl⟩) le_rfl le_rfl

end TransformsWordsAt

end Turing.MultiTapeTM


