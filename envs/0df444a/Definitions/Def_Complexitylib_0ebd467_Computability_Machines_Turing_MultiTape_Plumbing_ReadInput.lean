-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Plumbing_ReadInput
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Plumbing_ReadInput
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:37:57.301104+00:00
-- url     : https://prove2.me/theorems/6b6465df-5d41-4c8a-9fa4-9ff29f40d7bf
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Plumbing.ReadInput — Reading from the input at the input head
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Plumbing.ReadInput` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   An `InputReader` is a finite-state device that reads the input from the input head on: in state
--   `q` on the symbol `a` it emits at most one symbol and continues in a new state, or stops after `a`.
--   It also stops at the end of the input. `appendRead r i` appends what `r` emits to the word on work
--   tape `i` and leaves the input head after what `r` read. Reading one token of a self-delimiting
--   encoding is an instance.
--
--   ### Main definitions
--
--   * `Turing.MultiTapeTM.InputReader`: finite-state input readers.
--   * `Turing.MultiTapeTM.InputReader.read`: the word a reader emits and the number of symbols it
--     reads.
--   * `Turing.MultiTapeTM.appendRead`: the machine that runs a reader, appending to a work tape.
--
--   ### Main results
--
--   * `Turing.MultiTapeTM.transformsTapesAt_appendRead`: its specification.
--
--   **Contents.** The module is published as a whole: 20 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Plumbing_ReadInput`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Plumbing/ReadInput.lean

/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: vendored crei:crei/tidy-universal @7f7c0696 (unsubmitted)
-- vendored: `spaceUsed` is the space of a run path since cslib #1133 and #1122

public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Plumbing_Cursor
public import Definitions.Def_Cslib_254e30e_Computability_Machines_Turing_MultiTape_Plumbing_ForwardWork
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Plumbing_RewindWork

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Plumbing.ReadInput` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Reading from the input at the input head

An `InputReader` is a finite-state device that reads the input from the input head on: in state
`q` on the symbol `a` it emits at most one symbol and continues in a new state, or stops after `a`.
It also stops at the end of the input. `appendRead r i` appends what `r` emits to the word on work
tape `i` and leaves the input head after what `r` read. Reading one token of a self-delimiting
encoding is an instance.

## Main definitions

* `Turing.MultiTapeTM.InputReader`: finite-state input readers.
* `Turing.MultiTapeTM.InputReader.read`: the word a reader emits and the number of symbols it
  reads.
* `Turing.MultiTapeTM.appendRead`: the machine that runs a reader, appending to a work tape.

## Main results

* `Turing.MultiTapeTM.transformsTapesAt_appendRead`: its specification.
-/

namespace Turing.MultiTapeTM

variable {k : ℕ} {Symbol Q : Type*} {input : List Symbol}

/-- A finite-state input reader: in state `q` on the symbol `a` it emits `(step q a).2` and
continues in `(step q a).1`, or stops after `a` if that is `none`. -/
public structure InputReader (Symbol Q : Type*) where
  /-- The initial state. -/
  q₀ : Q
  /-- The next state, or `none` to stop, and the emitted symbol, if any. -/
  step : Q → Symbol → Option Q × Option Symbol

namespace InputReader

variable (r : InputReader Symbol Q)

/-- The word `r` emits on `w` from state `q`, and the number of symbols it reads: it stops after a
symbol leading to `none`, or at the end of `w`. -/
@[expose] public def read : Q → List Symbol → List Symbol × ℕ
  | _, [] => ([], 0)
  | q, a :: w =>
    match (r.step q a).1 with
    | none => ((r.step q a).2.toList, 1)
    | some q' => ((r.step q a).2.toList ++ (read q' w).1, (read q' w).2 + 1)

public lemma read_cons_of_none {q : Q} {a : Symbol} (w : List Symbol) (h : (r.step q a).1 = none) :
    r.read q (a :: w) = ((r.step q a).2.toList, 1) := by
  simp [read, h]

public lemma read_cons_of_some {q q' : Q} {a : Symbol} (w : List Symbol)
    (h : (r.step q a).1 = some q') :
    r.read q (a :: w) = ((r.step q a).2.toList ++ (r.read q' w).1, (r.read q' w).2 + 1) := by
  simp [read, h]

public lemma read_snd_le (q : Q) (w : List Symbol) : (r.read q w).2 ≤ w.length := by
  induction w generalizing q <;> grind [read]

public lemma length_read_fst_le (q : Q) (w : List Symbol) :
    (r.read q w).1.length ≤ (r.read q w).2 := by
  induction w generalizing q <;> grind [read]

/-- `r` as a machine with one work tape: it appends what it emits to the work tape, with the head
on the cell after the word, and moves the input head over what it reads. -/
def core : MultiTapeTM 1 Symbol Q :=
  ofTr r.q₀ fun q inp _ =>
    match inp with
    | none => ⟨0, fun _ => (none, 0), none, none⟩
    | some a =>
      ⟨1, fun _ => ((r.step q a).2.map some, if (r.step q a).2.isSome then 1 else 0), none,
        (r.step q a).1⟩

/-- A configuration of `core` reading position `j` of the input, with `u` on the work tape. -/
def coreCfg (q : Option Q) (j : ℕ) (hj : j ≤ input.length) (u out : List Symbol) :
    Cfg 1 Symbol Q input :=
  ⟨q, ⟨1 + j, by omega⟩, fun _ => tapeOfList u, fun _ => (u.length : ℤ), out⟩

lemma core_step_of_lt (q : Q) {j : ℕ} (hj : j < input.length) (u out : List Symbol) :
    r.core.step (coreCfg (some q) j hj.le u out) =
      coreCfg (r.step q input[j]).1 (j + 1) hj (u ++ (r.step q input[j]).2.toList) out := by
  rw [step_of_state rfl, inputSymbolInner j rfl hj]
  have hpos : moveInputPos (⟨1 + j, by omega⟩ : Fin (input.length + 2)) 1 =
      ⟨1 + (j + 1), by omega⟩ :=
    (moveInputPos_pos_of_ne_right _ (by simp; omega)).trans (Fin.ext (by simp; omega))
  cases he : (r.step q input[j]).2 with
  | none =>
    refine Cfg.ext ?_ ?_ ?_ ?_ ?_ <;> simp [core, coreCfg, Action.apply, he, hpos]
  | some s =>
    refine Cfg.ext ?_ ?_ ?_ ?_ ?_ <;>
      simp [core, coreCfg, Action.apply, he, hpos, tapeOfList_append_single]

lemma core_step_end (q : Q) (u out : List Symbol) :
    r.core.step (coreCfg (input := input) (some q) input.length le_rfl u out) =
      coreCfg none input.length le_rfl u out := by
  rw [step_of_state rfl, inputSymbol_eq_none_of_boundary (.inr (by simp [coreCfg]; omega))]
  refine Cfg.ext ?_ ?_ ?_ ?_ ?_ <;> simp [core, coreCfg, Action.apply, moveInputPos_zero]

/-- The run of `core` from state `q` at position `j`, where the rest of the input is `w`: after
reading `n` symbols and emitting `e`, where `(e, n) = r.read q w`, it halts within `n + 1` steps. -/
lemma core_runFrom (w : List Symbol) (q : Q) (j : ℕ) (hj : j ≤ input.length)
    (hw : input.drop j = w) (u out : List Symbol) :
    ∃ hn : j + (r.read q w).2 ≤ input.length,
      r.core.runFrom (coreCfg (some q) j hj u out) ((r.read q w).2 + 1) =
        coreCfg none (j + (r.read q w).2) hn (u ++ (r.read q w).1) out := by
  induction w generalizing j q u with
  | nil =>
    obtain rfl : j = input.length := by
      have := congrArg List.length hw; simp at this; omega
    refine ⟨by simp [read], ?_⟩
    simp only [read, List.append_nil]
    exact r.core_step_end q u out
  | cons a w ih =>
    have hlen := congrArg List.length hw
    simp only [List.length_drop, List.length_cons] at hlen
    have hj' : j < input.length := by omega
    obtain ⟨ha, hw'⟩ := List.cons_eq_cons.mp ((List.drop_eq_getElem_cons hj').symm.trans hw)
    have h1 : r.core.runFrom (coreCfg (some q) j hj u out) 1 =
        coreCfg (r.step q a).1 (j + 1) hj' (u ++ (r.step q a).2.toList) out := by
      rw [show r.core.runFrom _ 1 = r.core.step _ from rfl, core_step_of_lt r q hj' u out, ha]
    cases hq : (r.step q a).1 with
    | none =>
      rw [hq] at h1
      rw [read_cons_of_none r w hq]
      refine ⟨by omega, ?_⟩
      rw [runFrom_eq_of_halt (τ := 1) _ _ (by omega) (by rw [h1]; rfl), h1]
    | some q' =>
      rw [hq] at h1
      obtain ⟨hn, h⟩ := ih q' (j + 1) hj' hw' (u ++ (r.step q a).2.toList)
      rw [read_cons_of_some r w hq]
      refine ⟨by simp; omega, ?_⟩
      rw [show ((r.step q a).2.toList ++ (r.read q' w).1, (r.read q' w).2 + 1).2 + 1 =
        1 + ((r.read q' w).2 + 1) by simp; omega, runFrom_add, h1, h]
      refine Cfg.ext rfl (Fin.ext ?_) ?_ ?_ rfl <;> simp [coreCfg]
      omega

/-- The head of `core` never moves left. -/
lemma core_workTapePos_le_step (c : Cfg 1 Symbol Q input) :
    c.workTapePos 0 ≤ (r.core.step c).workTapePos 0 := by
  cases hq : c.state with
  | none => rw [step_of_halt hq]
  | some q =>
    rw [step_of_state hq]
    simp only [Action.apply_workTapePos, core, tr_ofTr]
    split
    · simp
    · split_ifs <;> simp [SignType.cast]

lemma core_workTapePos_mono (c : Cfg 1 Symbol Q input) {m n : ℕ} (h : m ≤ n) :
    (r.core.runFrom c m).workTapePos 0 ≤ (r.core.runFrom c n).workTapePos 0 := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (by rw [runFrom_succ]; exact r.core_workTapePos_le_step _)

/-- During its run, the head of `core` stays between the end of the old word and the end of the
new one. -/
lemma core_workTapePos_mem (q : Q) (j : ℕ) (hj : j ≤ input.length) (u out : List Symbol) (m : ℕ) :
    (r.core.runFrom (coreCfg (some q) j hj u out) m).workTapePos 0 ∈
      Set.Icc (u.length : ℤ) (u ++ (r.read q (input.drop j)).1).length := by
  obtain ⟨hn, h⟩ := r.core_runFrom _ q j hj rfl u out
  refine ⟨r.core_workTapePos_mono _ (Nat.zero_le m), ?_⟩
  rcases Nat.le_total m ((r.read q (input.drop j)).2 + 1) with hm | hm
  · refine (r.core_workTapePos_mono _ hm).trans ?_
    rw [h]
    simp [coreCfg]
  · rw [runFrom_eq_of_halt _ _ hm (by rw [h]; rfl), h]
    simp [coreCfg]

end InputReader

/-- `r` run on one work tape: move the head to the end of the word, append what `r` emits while
reading the input, and move the head back to the start. -/
public noncomputable def InputReader.appendOne (r : InputReader Symbol Q) :
    MultiTapeTM 1 Symbol (Unit ⊕ Q ⊕ RewindWorkState) :=
  (forwardWork Symbol).seq (r.core.seq (rewindWork Symbol))

/-- `r` run on work tape `i`, appending what it emits to the word there. -/
public noncomputable def appendRead (r : InputReader Symbol Q) (i : Fin k) :
    MultiTapeTM k Symbol (Unit ⊕ Q ⊕ RewindWorkState) :=
  r.appendOne.extendTapes (tapeEmb i)

namespace InputReader

variable (r : InputReader Symbol Q)

/-- The configuration in which `core` starts within `appendOne`. -/
lemma withState_eq_coreCfg (p : Fin (input.length + 2)) (hp : p.val ≠ 0) (v out : List Symbol) :
    (⟨none, p, fun _ => tapeOfList v, fun _ => (v.length : ℤ), out⟩ :
      Cfg 1 Symbol Unit input).withState (some r.core.q₀) =
        coreCfg (some r.q₀) (p.val - 1) (by have := p.isLt; omega) v out :=
  Cfg.ext rfl (Fin.ext (by simp [coreCfg]; omega)) rfl rfl rfl

open Sequential in
lemma appendOne_runFrom (p : Fin (input.length + 2)) (hp : p.val ≠ 0) (v out : List Symbol)
    (rd : List Symbol × ℕ) (hrd : rd = r.read r.q₀ (input.drop (p.val - 1))) :
    ∃ p' : Fin (input.length + 2), p'.val = p.val + rd.2 ∧
      r.appendOne.runFrom ⟨some r.appendOne.q₀, p, fun _ => tapeOfList v, fun _ => 0, out⟩
          (v.length + 1 + ((rd.2 + 1) + ((v ++ rd.1).length + 2))) =
        ⟨none, p', fun _ => tapeOfList (v ++ rd.1), fun _ => 0, out⟩ := by
  have hp' : p.val - 1 ≤ input.length := by have := p.isLt; omega
  have h₀ := runFrom_forwardWork p v out (p := 0) (n := v.length) (by simp)
  have hmid := r.withState_eq_coreCfg p hp v out
  obtain ⟨hn, h₁⟩ := r.core_runFrom _ r.q₀ (p.val - 1) hp' rfl v out
  subst hrd
  generalize r.read r.q₀ (input.drop (p.val - 1)) = rd at hn h₁ ⊢
  have h₂ := runFrom_rewindWork_none (input := input) ⟨1 + (p.val - 1 + rd.2), by omega⟩
    (tapeOfList (v ++ rd.1)) out rfl le_rfl
  refine ⟨⟨1 + (p.val - 1 + rd.2), by omega⟩, by change 1 + (p.val - 1 + rd.2) = _; omega, ?_⟩
  have h₁₂ := runFrom_seq h₁ rfl h₂ rfl
  rw [← hmid] at h₁₂
  exact (runFrom_seq h₀ rfl h₁₂ rfl).trans rfl

open Sequential in
/-- The head of `appendOne` stays within `[-1, |v ++ e|]`, so it uses at most `|v ++ e| + 2`
cells. -/
lemma appendOne_space_le (p : Fin (input.length + 2)) (hp : p.val ≠ 0) (v out : List Symbol)
    (t : ℕ) :
    (MultiTapeNTM.RunPath.ofDeterministic r.appendOne
        ⟨some r.appendOne.q₀, p, fun _ => tapeOfList v, fun _ => 0, out⟩ t).space ≤
      (v ++ (r.read r.q₀ (input.drop (p.val - 1))).1).length + 2 := by
  have hp' : p.val - 1 ≤ input.length := by have := p.isLt; omega
  set L := (v ++ (r.read r.q₀ (input.drop (p.val - 1))).1).length
  have hvL : v.length ≤ L := by simp [L]
  have h₀ := runFrom_forwardWork p v out (p := 0) (n := v.length) (by simp)
  have hmid := r.withState_eq_coreCfg p hp v out
  obtain ⟨hn, h₁⟩ := r.core_runFrom _ r.q₀ (p.val - 1) hp' rfl v out
  have hinv : ∀ m, (((forwardWork Symbol).seq (r.core.seq (rewindWork Symbol))).runFrom
      (leftCfg (r.core.seq (rewindWork Symbol)) ⟨some (forwardWork Symbol).q₀, p,
        fun _ => tapeOfList v, fun _ => ((0 : ℕ) : ℤ), out⟩) m).forgetState.workTapePos 0 ∈
        Set.Icc (-1 : ℤ) L := by
    refine forgetState_runFrom_seq (P := fun c => c.workTapePos 0 ∈ Set.Icc (-1 : ℤ) L) h₀ rfl
      (fun m _ => ?_) (fun n => ?_)
    · have := workTapePos_runFrom_forwardWork p v out (p := 0) (Nat.zero_le _) m
      simp only [Cfg.forgetState_workTapePos, Set.mem_Icc] at this ⊢
      omega
    · rw [show (⟨none, p, fun _ => tapeOfList v, fun _ => (v.length : ℤ), out⟩ :
          Cfg 1 Symbol Unit input).withState (some (r.core.seq (rewindWork Symbol)).q₀) =
          leftCfg (rewindWork Symbol) ((⟨none, p, fun _ => tapeOfList v,
            fun _ => (v.length : ℤ), out⟩ : Cfg 1 Symbol Unit input).withState (some r.core.q₀))
          from rfl, hmid]
      refine forgetState_runFrom_seq (P := fun c => c.workTapePos 0 ∈ Set.Icc (-1 : ℤ) L) h₁ rfl
        (fun m _ => ?_) (fun n => ?_) n
      · have := r.core_workTapePos_mem r.q₀ (p.val - 1) hp' v out m
        simp only [Cfg.forgetState_workTapePos, Set.mem_Icc] at this ⊢
        omega
      · exact workTapePos_runFrom_rewindWork (input := input) none
          ⟨1 + (p.val - 1 + (r.read r.q₀ (input.drop (p.val - 1))).2), by omega⟩
          (tapeOfList (v ++ (r.read r.q₀ (input.drop (p.val - 1))).1)) out rfl le_rfl n
  rw [MultiTapeNTM.RunPath.space, Fin.sum_univ_one]
  refine (spaceUsedByTape_le_card _ (S := .Icc (-1) (L : ℤ)) fun m _ => ?_).trans ?_
  · exact Finset.mem_Icc.mpr (hinv m)
  · rw [Int.card_Icc]; omega

end InputReader

/-- `appendRead r i`, started with the input head at `p` on the input `x` and `v` on work tape `i`,
appends what `r` emits reading `x` from `p` on to `v`, moves the input head over what `r` read, and
changes nothing else. -/
public theorem transformsTapesAt_appendRead (r : InputReader Symbol Q) (i : Fin k)
    (x : List Symbol) (p₀ : Fin (x.length + 2)) (hp₀ : p₀.val ≠ 0) (v : List Symbol) :
    let rd := r.read r.q₀ (x.drop (p₀.val - 1))
    TransformsTapesAt (appendRead r i) (fun input p ws => input = x ∧ p.val = p₀.val ∧ ws i = v)
      (fun _ _ ws p' ws' e => p'.val = p₀.val + rd.2 ∧ ws' = Function.update ws i (v ++ rd.1) ∧
        e = [])
      (v.length + 1 + ((rd.2 + 1) + ((v ++ rd.1).length + 2)))
      ((v ++ rd.1).length + 2 + (k - 1)) := by
  intro rd
  rintro input p ws out ⟨rfl, hp, hv⟩
  obtain rfl : p = p₀ := Fin.ext hp
  obtain ⟨p', hp', hrun⟩ := r.appendOne_runFrom p hp₀ v out rd rfl
  have hcfg : oneTapeCfg i (wordsCfgAt input p (some (appendRead r i).q₀) ws out) =
      ⟨some r.appendOne.q₀, p, fun _ => tapeOfList v, fun _ => 0, out⟩ := by
    refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext _ <;> simp [oneTapeCfg, wordsCfgAt, hv]
  refine ⟨p', Function.update ws i (v ++ rd.1), [], ?_, ⟨hp', rfl, rfl⟩, ?_⟩
  · rw [appendRead, runFrom_tapeEmb, ← appendRead, hcfg, hrun]
    refine Cfg.ext rfl rfl ?_ ?_ (by simp [embed]) <;> funext l <;> by_cases hl : l = i <;>
      simp [embed, hl, partialInv_tapeEmb, wordsCfgAt]
  · refine (space_tapeEmb_le _ _ _ _).trans (Nat.add_le_add_right ?_ _)
    rw [hcfg]
    exact r.appendOne_space_le p hp₀ v out _

end Turing.MultiTapeTM


