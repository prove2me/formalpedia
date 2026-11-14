-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Plumbing_InputFromTape
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Plumbing_InputFromTape
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:37:11.042347+00:00
-- url     : https://prove2.me/theorems/493f2ca6-f499-48a6-a031-097bd2118ad5
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Plumbing.InputFromTape — Reading the input from a word on a work tape
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Plumbing.InputFromTape` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   The additions of cslib PR #1111 to
--   `Cslib.Computability.Machines.Turing.MultiTape.Plumbing.InputFromTape`.
--
--   `inputFromWord M mark` reads the input from a word on the virtual input tape, with blank work tapes
--   around it. It runs three machines in sequence:
--
--   1. `markFlag k (some mark)` writes `mark` to cell `-1` of the flag tape;
--   2. `inputFromTape M` runs `M` on the virtual input tape;
--   3. `markFlag k none` erases the mark again.
--
--   ### Main definitions
--
--   * `Turing.MultiTapeTM.inputFromWord`: the machine reading its input from a word on a work tape.
--
--   ### Main results
--
--   * `Turing.MultiTapeTM.ComputesTidilyInTimeAndSpace.inputFromWord_extendTapes`: run on a selected
--     input tape, preserving it and emitting the output.
--
--   * `Turing.MultiTapeTM.transformsTapes_inputFromWord`: a run path of `M` on the virtual input word,
--     from and to `Turing.wordsCfg` configurations, gives a specification of
--     `inputFromWord M mark`; `Turing.MultiTapeTM.transformsTapes_inputFromWord_of_runFrom` is the same
--     for a run of `M`.
--
--   **Contents.** The module is published as a whole: 14 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Plumbing_InputFromTape`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Plumbing/InputFromTape.lean

/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: submitted #1111 @3441fa81
-- `transformsTapes_inputFromWord_of_runFrom` is from crei:crei/tidy-universal @7f7c0696
-- (unsubmitted).

public import Definitions.Def_Cslib_254e30e_Computability_Machines_Turing_MultiTape_Plumbing_InputFromTape
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Plumbing_ExtendTapes
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Plumbing_MarkWork
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Plumbing_Sequential
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Plumbing_TransformsTapes
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Plumbing_Tidy_Defs
import Definitions.Def_Complexitylib_0ebd467_Foundations_Data_Fin_Tuple

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Plumbing.InputFromTape` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Reading the input from a word on a work tape

The additions of cslib PR #1111 to
`Cslib.Computability.Machines.Turing.MultiTape.Plumbing.InputFromTape`.

`inputFromWord M mark` reads the input from a word on the virtual input tape, with blank work tapes
around it. It runs three machines in sequence:

1. `markFlag k (some mark)` writes `mark` to cell `-1` of the flag tape;
2. `inputFromTape M` runs `M` on the virtual input tape;
3. `markFlag k none` erases the mark again.

## Main definitions

* `Turing.MultiTapeTM.inputFromWord`: the machine reading its input from a word on a work tape.

## Main results

* `Turing.MultiTapeTM.ComputesTidilyInTimeAndSpace.inputFromWord_extendTapes`: run on a selected
  input tape, preserving it and emitting the output.

* `Turing.MultiTapeTM.transformsTapes_inputFromWord`: a run path of `M` on the virtual input word,
  from and to `Turing.wordsCfg` configurations, gives a specification of
  `inputFromWord M mark`; `Turing.MultiTapeTM.transformsTapes_inputFromWord_of_runFrom` is the same
  for a run of `M`.
-/

namespace Turing.MultiTapeTM

variable {k : ℕ} {Symbol State : Type*}

/-! ### Setting and erasing the flag -/

/-- `markWork write` placed on the flag tape, the last of `k + 2` work tapes: it writes `write` to
the cell left of the head of that tape. -/
@[expose] public noncomputable def markFlag (k : ℕ) (write : Option Symbol) :
    MultiTapeTM (k + 2) Symbol MarkWorkState :=
  (markWork Symbol write).extendTapes (tapeEmb (Fin.natAdd k 1))

/-- `M`, reading its input from a word on the virtual input tape `Fin.natAdd k 0`, with `mark`
written to cell `-1` of the flag tape, the last work tape, before and erased after. -/
@[expose] public noncomputable def inputFromWord (M : MultiTapeTM k Symbol State) (mark : Symbol) :
    MultiTapeTM (k + 2) Symbol (MarkWorkState ⊕ State ⊕ MarkWorkState) :=
  (markFlag k (some mark)).seq (M.inputFromTape.seq (markFlag k none))

/-- `Turing.MultiTapeTM.inCfg` of a `wordsCfg` configuration: the input `w` on the virtual input
tape, `mark` at cell `-1` of the flag tape, every head at cell `0`. -/
public lemma inCfg_wordsCfg (mark : Symbol) {w : List Symbol} (q : Option State)
    (ws : Fin k → List Symbol) (o outer : List Symbol) :
    inCfg mark (wordsCfg w q ws o) outer =
      ⟨q, 1, Fin.append (fun j => tapeOfList (ws j))
          ![tapeOfList w, Function.update (fun _ => none) (-1) (some mark)],
        fun _ => 0, o⟩ := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext l <;> cases l using Fin.addCases with
  | left j => simp [inCfg, wordsCfg]
  | right i => match i with | 0 | 1 => simp [inCfg, wordsCfg]

/-- Updating the flag tape of an appended family of tapes only changes the flag entry. -/
private lemma update_append_flag {α : Type*} (ws₀ : Fin k → α) (a b c : α) :
    Function.update (Fin.append ws₀ ![a, b]) (Fin.natAdd k 1) c = Fin.append ws₀ ![a, c] := by
  rw [← Fin.append_update_right]
  congr 1
  simp [funext_iff, Fin.forall_fin_two]

/-- The flag tape of a configuration whose tapes are `Fin.append WS ![vip, flag]`, as a one-tape
configuration of `markWork`. -/
private lemma oneTapeCfg_flag {input : List Symbol} (write : Option Symbol)
    (WS : Fin k → ℤ → Option Symbol) (vip flag : ℤ → Option Symbol) (out : List Symbol)
    (ip : Fin (input.length + 2)) :
    oneTapeCfg (Fin.natAdd k 1)
        (⟨some (markWork Symbol write).q₀, ip, Fin.append WS ![vip, flag], fun _ => 0, out⟩ :
          Cfg (k + 2) Symbol MarkWorkState input) =
      ⟨some (markWork Symbol write).q₀, ip, fun _ => flag, fun _ => 0, out⟩ := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext _ <;> simp [oneTapeCfg, Fin.append_right]

/-- In two steps, `markFlag k write` writes `write` to cell `-1` of the flag tape and changes
nothing else: it runs `markWork write` on the flag tape. -/
private lemma exists_runPath_markFlag {input : List Symbol} (write : Option Symbol)
    (WS : Fin k → ℤ → Option Symbol) (vip flag : ℤ → Option Symbol) (out : List Symbol)
    (ip : Fin (input.length + 2)) :
    ∃ p : (markFlag k write).RunPath input,
      p.head = ⟨some (markFlag k write).q₀, ip, Fin.append WS ![vip, flag], fun _ => 0, out⟩ ∧
      p.last = ⟨none, ip, Fin.append WS ![vip, Function.update flag (-1) write], fun _ => 0, out⟩ ∧
      p.time = 2 ∧ p.space ≤ k + 4 := by
  let cfg : Cfg (k + 2) Symbol MarkWorkState input :=
    ⟨some (markWork Symbol write).q₀, ip, Fin.append WS ![vip, flag], fun _ => 0, out⟩
  let r := MultiTapeNTM.RunPath.ofDeterministic (markWork Symbol write)
    (oneTapeCfg (Fin.natAdd k 1) cfg) 2
  refine ⟨r.map (embedHom _ (tapeEmb (Fin.natAdd k 1)) cfg.workTapes cfg.workTapePos),
    embed_oneTapeCfg _ cfg, ?_, rfl, ?_⟩
  · change embed _ ((markWork Symbol write).runFrom (oneTapeCfg _ cfg) 2) _ _ = _
    rw [oneTapeCfg_flag, runFrom_markWork, embed_tapeEmb]
    refine Cfg.ext rfl rfl ?_ ?_ rfl
    · simpa [cfg] using update_append_flag WS vip flag (Function.update flag (-1) write)
    · funext l; simp [cfg, Function.update_apply]
  · -- `markWork` takes two steps on one tape, every other tape stays where it is
    have : r.space ≤ 1 * (2 + 1) := r.space_le_mul_time_add_one
    exact (space_map_embedHom_le ..).trans (by omega)

/-- A `wordsCfg` configuration whose last two words are `w` and the empty word, written out. -/
private lemma wordsCfg_append_words {State' : Type*} {outer : List Symbol} (q : Option State')
    (ws : Fin k → List Symbol) (w out : List Symbol) :
    wordsCfg outer q (Fin.append ws ![w, []]) out =
      ⟨q, 1, Fin.append (fun j => tapeOfList (ws j)) ![tapeOfList w, fun _ => none],
        fun _ => 0, out⟩ := by
  refine Cfg.ext rfl rfl
    ((Fin.comp_append tapeOfList ws ![w, []]).trans (congrArg _ (funext fun i => ?_))) rfl rfl
  match i with
  | 0 | 1 => simp

section Flag

variable (mark : Symbol) (ws : Fin k → List Symbol) (w out outer : List Symbol)

/-- Setting the flag on a `wordsCfg` configuration leads to the configuration in which
`inputFromTape` starts. -/
private lemma exists_runPath_setFlag :
    ∃ p : (markFlag k (some mark)).RunPath outer,
      p.head = wordsCfg outer (some (markFlag k (some mark)).q₀) (Fin.append ws ![w, []]) out ∧
      p.last = inCfg mark (wordsCfg w (none : Option MarkWorkState) ws out) outer ∧
      p.time = 2 ∧ p.space ≤ k + 4 := by
  rw [wordsCfg_append_words, inCfg_wordsCfg]
  exact exists_runPath_markFlag _ _ _ _ _ _

/-- Erasing the flag on the configuration in which `inputFromTape` halts leads to a `wordsCfg`
configuration. -/
private lemma exists_runPath_eraseFlag :
    ∃ p : (markFlag (Symbol := Symbol) k none).RunPath outer,
      p.head = (inCfg mark (wordsCfg w (none : Option State) ws out) outer).withState
        (some (markFlag (Symbol := Symbol) k none).q₀) ∧
      p.last = wordsCfg outer none (Fin.append ws ![w, []]) out ∧
      p.time = 2 ∧ p.space ≤ k + 4 := by
  obtain ⟨p, hh, hl, ht, hs⟩ := exists_runPath_markFlag none (fun j => tapeOfList (ws j))
    (tapeOfList w) (Function.update (fun _ => none) (-1) (some mark)) out
    (1 : Fin (outer.length + 2))
  refine ⟨p, by rw [hh, inCfg_wordsCfg]; rfl, ?_, ht, hs⟩
  rw [hl, wordsCfg_append_words, Function.update_idem]
  simp

end Flag

open Sequential in
/-- If `M`, run on the input `w` with work tapes `ws₀`, has a run path of at most `t` steps and `s`
cells to the halting configuration with work tapes `ws₁`, every head back at its start, having
emitted `e`, then `inputFromWord M mark` takes the work tapes `Fin.append ws₀ ![w, []]` to
`Fin.append ws₁ ![w, []]` and emits `e`. -/
public theorem transformsTapes_inputFromWord (mark : Symbol)
    {M : MultiTapeTM k Symbol State} {w e : List Symbol} {ws₀ ws₁ : Fin k → List Symbol}
    {t s : ℕ} (hM : ∃ p : M.RunPath w, p.head = wordsCfg w (some M.q₀) ws₀ [] ∧
      p.last = wordsCfg w none ws₁ e ∧ p.time ≤ t ∧ p.space ≤ s) :
    TransformsTapes (M.inputFromWord mark)
      (fun _ ws => ws = Fin.append ws₀ ![w, []])
      (fun _ _ ws' em => ws' = Fin.append ws₁ ![w, []] ∧ em = e)
      (t + 4) (s + 2 * w.length + 2 * k + 12) := by
  obtain ⟨pM, hh, hl, ht, hs⟩ := hM
  unfold inputFromWord
  rw [transformsTapes_iff_nil_output]
  rintro outer _ rfl
  -- set the flag, run `M` on the virtual input tape, erase the flag
  obtain ⟨p₀, hh₀, hl₀, ht₀, hs₀⟩ := exists_runPath_setFlag mark ws₀ w [] outer
  let p₁ := pM.map (inCfgHom M mark outer)
  have hl₁ : p₁.last = inCfg mark (wordsCfg w none ws₁ e) outer := by simp [p₁, hl]
  have hs₁ : p₁.space ≤ pM.space + 2 * (w.length + 2) := space_map_inCfgHom_le M mark outer pM
  obtain ⟨p₂, hh₂, hl₂, ht₂, hs₂⟩ := exists_runPath_eraseFlag (State := State) mark ws₁ w e outer
  obtain ⟨p₁₂, hh₁₂, hl₁₂, ht₁₂, hs₁₂⟩ := exists_runPath_seq_space_le (p₀ := p₁) (p₁ := p₂)
    (by rw [hl₁]; rfl) (by rw [hh₂, hl₁]) (by rw [hl₂]; rfl)
  obtain ⟨p, hph, hpl, hpt, hps⟩ := exists_runPath_seq_space_le (p₀ := p₀) (p₁ := p₁₂)
    (by rw [hl₀]; rfl) (by simp [hh₁₂, p₁, hh, hl₀]; rfl) (by rw [hl₁₂, hl₂]; rfl)
  refine ⟨_, e, ⟨rfl, rfl⟩, p, by rw [hph, hh₀]; rfl, by simp [hpl, hl₁₂, hl₂, rightCfg], ?_, ?_⟩
  · simp only [MultiTapeNTM.RunPath.time] at ht ht₀ ht₂ ⊢
    have : p₁.length = pM.length := rfl
    omega
  · omega

-- vendored: crei:crei/tidy-universal proves this directly, for the space bound
-- `s + 2 * (w.length + 2) + 2 * k + 6`; here it follows from the run-path version of cslib #1111
/-- If `M`, run on the input `w` with work tapes `ws₀`, halts after `t` steps with work tapes `ws₁`
and every head back at its start, having emitted `e`, then `inputFromWord M mark` takes the work
tapes `Fin.append ws₀ ![w, []]` to `Fin.append ws₁ ![w, []]` and emits `e`. -/
public theorem transformsTapes_inputFromWord_of_runFrom (mark : Symbol)
    {M : MultiTapeTM k Symbol State} {w e : List Symbol} {ws₀ ws₁ : Fin k → List Symbol}
    {t s : ℕ} (hrun : M.runFrom (wordsCfg w (some M.q₀) ws₀ []) t = wordsCfg w none ws₁ e)
    (hspace : (MultiTapeNTM.RunPath.ofDeterministic M (wordsCfg w (some M.q₀) ws₀ []) t).space ≤
      s) :
    TransformsTapes (M.inputFromWord mark)
      (fun _ ws => ws = Fin.append ws₀ ![w, []])
      (fun _ _ ws' em => ws' = Fin.append ws₁ ![w, []] ∧ em = e)
      (t + 4) (s + 2 * w.length + 2 * k + 12) :=
  transformsTapes_inputFromWord mark ((exists_runPath_iff_runFrom rfl).mpr ⟨hrun, hspace⟩)

-- upstream: vendored crei:crei/tidy-universal @7f7c0696 (unsubmitted)
-- vendored: these tidy-word specifications previously lived in `Combinators/StreamFold`.
-- The tuple identity is public for reuse by `onWords`.
/-- The work tapes in which `inputFromWord` starts and halts, for a tidy machine. -/
public lemma append_nil_eq_update {k : ℕ} (w : List Symbol) :
    Fin.append (fun _ : Fin k => ([] : List Symbol)) ![w, []] =
      Function.update (fun _ => []) (Fin.natAdd k 0) w := by
  rw [← Fin.append_const (m := k) (n := 2) [], ← Fin.append_update_right]
  congr 1
  simp [funext_iff, Fin.forall_fin_two]

/-- A tidy machine run on the word on a work tape, emitting what it computes. -/
public theorem ComputesTidilyInTimeAndSpace.inputFromWord {k : ℕ} {tm : MultiTapeTM k Symbol State}
    (mark : Symbol) {w y : List Symbol} {t s : ℕ} (h : tm.ComputesTidilyInTimeAndSpace w y t s) :
    TransformsTapes (tm.inputFromWord mark)
      (fun _ ws => True ∧ ws = Function.update (fun _ => []) (Fin.natAdd k 0) w)
      (fun _ ws ws' em => ws' = Function.update ws (Fin.natAdd k 0) w ∧ em = y)
      -- vendored: `+ 8` rather than crei's `+ 6`, as cslib #1111's `inputFromWord` uses two more
      -- cells
      (t + 4) (s + 2 * (w.length + 2) + 2 * k + 8) := by
  -- vendored: `computesTidily_iff` is stated with run paths since cslib #1117
  obtain ⟨hrun, hspace⟩ := computesTidily_iff_runFrom.mp h
  refine (transformsTapes_inputFromWord_of_runFrom mark hrun hspace).imp
    (fun _ ws ⟨_, hws⟩ => by rw [hws, append_nil_eq_update])
    (fun _ ws ws' _ ⟨_, hws⟩ ⟨hws', hy⟩ => ⟨?_, hy⟩) le_rfl (by omega)
  rw [hws', hws, append_nil_eq_update, Function.update_idem]

-- upstream: candidate
-- vendored: generalize the selected-tape helper from `Encodings/MultiPass` to a single run,
-- retaining the exact space bound for streaming clients.
/-- Run a tidy computation on a selected input tape, preserving it and emitting the output. -/
public theorem ComputesTidilyInTimeAndSpace.inputFromWord_extendTapes
    {tm : MultiTapeTM k Symbol State} (mark : Symbol) {input output : List Symbol} {t s K : ℕ}
    (h : tm.ComputesTidilyInTimeAndSpace input output t s)
    {e : Fin (k + 2) ↪ Fin K} {V : Fin K} (he : e (Fin.natAdd k 0) = V) :
    TransformsTapes ((tm.inputFromWord mark).extendTapes e)
      (fun _ ws => ws = Function.update (fun _ => []) V input)
      (fun _ ws ws' em => ws' = ws ∧ em = output)
      (t + 4) (s + 2 * (input.length + 2) + 2 * k + 8 + (K - (k + 2))) := by
  have h' := (h.inputFromWord mark).extendTapes_update e
  rw [he] at h'
  exact h'.imp (fun _ _ hws => ⟨trivial, hws⟩)
    (fun _ _ _ _ hws ⟨h, he⟩ => ⟨by rw [h, hws, Function.update_idem], he⟩) le_rfl le_rfl

end Turing.MultiTapeTM


