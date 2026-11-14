-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_KernelZipTransducer
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_KernelZipTransducer
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:36:59.417432+00:00
-- url     : https://prove2.me/theorems/e32d85b3-96fd-4cfa-979b-e9a6b8a9c9c2
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Internal.KernelZipTransducer — Zip transducers and their machine semantics
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Internal.KernelZipTransducer` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   A zip transducer reads two binary words in lockstep, least significant digit first, padding the
--   shorter one with `none`. Its machine `ZipTransducer.toTM` reads `frame u ++ v` from the input
--   tape: it copies `u` to its single work tape, rewinds that tape and then reads `v` on the input
--   tape and `u` on the work tape simultaneously. It runs in time linear in the input and uses
--   `u.length + 2` work-tape cells.
--
--   ### Main definitions
--
--   * `Turing.MultiTapeTM.ZipTransducer`: finite-state transducers on pairs of optional bits.
--   * `Turing.MultiTapeTM.ZipTransducer.run`: the word a zip transducer emits on two words.
--   * `Turing.MultiTapeTM.ZipTransducer.toTM`: the zip transducer as a machine with one work tape.
--
--   ### Main results
--
--   * `Turing.MultiTapeTM.ZipTransducer.computesInTimeAndSpace_toTM`: on `frame u ++ v`, `τ.toTM`
--     emits `τ.run τ.q₀ u v` within `3 * (frame u ++ v).length + 1` steps and `u.length + 2` cells.
--
--   **Contents.** The module is published as a whole: 43 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_KernelZipTransducer`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Internal/KernelZipTransducer.lean

/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Run
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Frame_Basic
public import Mathlib.Data.Fintype.Option
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Finite.Sum

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Internal.KernelZipTransducer` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-! # Zip transducers and their machine semantics

A zip transducer reads two binary words in lockstep, least significant digit first, padding the
shorter one with `none`. Its machine `ZipTransducer.toTM` reads `frame u ++ v` from the input
tape: it copies `u` to its single work tape, rewinds that tape and then reads `v` on the input
tape and `u` on the work tape simultaneously. It runs in time linear in the input and uses
`u.length + 2` work-tape cells.

## Main definitions

* `Turing.MultiTapeTM.ZipTransducer`: finite-state transducers on pairs of optional bits.
* `Turing.MultiTapeTM.ZipTransducer.run`: the word a zip transducer emits on two words.
* `Turing.MultiTapeTM.ZipTransducer.toTM`: the zip transducer as a machine with one work tape.

## Main results

* `Turing.MultiTapeTM.ZipTransducer.computesInTimeAndSpace_toTM`: on `frame u ++ v`, `τ.toTM`
  emits `τ.run τ.q₀ u v` within `3 * (frame u ++ v).length + 1` steps and `u.length + 2` cells.
-/

namespace Turing.MultiTapeTM

/-- A finite-state transducer reading two words in lockstep. In state `q`, on the pair `(x, y)` of
the next digits of the two words, where `none` pads the shorter word, it moves to
`(step q (x, y)).1` and emits `(step q (x, y)).2`; when both words are exhausted it emits
`final q`. The value of `step` on `(none, none)` is never used. -/
public structure ZipTransducer (Q : Type*) where
  /-- The initial state. -/
  q₀ : Q
  /-- The successor state and the emitted word on reading a pair of digits. -/
  step : Q → Option Bool × Option Bool → Q × List Bool
  /-- The word emitted when both words are exhausted. -/
  final : Q → List Bool
  /-- At most two symbols are emitted per pair of digits. -/
  length_step_le : ∀ q x, (step q x).2.length ≤ 2
  /-- At most two symbols are emitted at the end. -/
  length_final_le : ∀ q, (final q).length ≤ 2

namespace ZipTransducer

variable {Q : Type*} (τ : ZipTransducer Q)

/-- The word `τ` emits on the words `u` and `v`, started in state `q`. -/
public def run (q : Q) : List Bool → List Bool → List Bool
  | [], [] => τ.final q
  | a :: u, [] => (τ.step q (some a, none)).2 ++ run (τ.step q (some a, none)).1 u []
  | [], b :: v => (τ.step q (none, some b)).2 ++ run (τ.step q (none, some b)).1 [] v
  | a :: u, b :: v => (τ.step q (some a, some b)).2 ++ run (τ.step q (some a, some b)).1 u v

@[simp]
public lemma run_nil_nil (q : Q) : τ.run q [] [] = τ.final q := by
  simp [run]

@[simp]
public lemma run_cons_nil (q : Q) (a : Bool) (u : List Bool) :
    τ.run q (a :: u) [] =
      (τ.step q (some a, none)).2 ++ τ.run (τ.step q (some a, none)).1 u [] := by
  simp [run]

@[simp]
public lemma run_nil_cons (q : Q) (b : Bool) (v : List Bool) :
    τ.run q [] (b :: v) =
      (τ.step q (none, some b)).2 ++ τ.run (τ.step q (none, some b)).1 [] v := by
  simp [run]

@[simp]
public lemma run_cons_cons (q : Q) (a b : Bool) (u v : List Bool) :
    τ.run q (a :: u) (b :: v) =
      (τ.step q (some a, some b)).2 ++ τ.run (τ.step q (some a, some b)).1 u v := by
  simp [run]

/-- Unless both words are exhausted, `τ` reads their first digits and continues on the rest. -/
public lemma run_of_ne {q : Q} {u v : List Bool} (h : ¬(u = [] ∧ v = [])) :
    τ.run q u v = (τ.step q (u.head?, v.head?)).2 ++
      τ.run (τ.step q (u.head?, v.head?)).1 u.tail v.tail := by
  cases u <;> cases v <;> simp_all

/-- The control states of `ZipTransducer.toTM`. -/
public inductive State (Q : Type*) where
  /-- Expecting the next frame marker of the first word. -/
  | copy
  /-- Expecting the next digit of the first word, to be copied to the work tape. -/
  | copyBit
  /-- Moving the work head back to the start of the copied word. -/
  | rewind
  /-- Running `τ` in state `q`, with a pending output symbol. -/
  | zip (q : Q) (pending : Option Bool)
  /-- Emitting the last output symbol before halting. -/
  | flush (b : Bool)

/-- An encoding of the control states into a finite type. -/
private def State.toSum {Q : Type*} : State Q → Fin 3 ⊕ (Q × Option Bool) ⊕ Bool
  | .copy => .inl 0
  | .copyBit => .inl 1
  | .rewind => .inl 2
  | .zip q p => .inr (.inl (q, p))
  | .flush b => .inr (.inr b)

/-- With finitely many states of the transducer, the machine has finitely many states. -/
public instance State.instFinite {Q : Type*} [Finite Q] : Finite (State Q) :=
  Finite.of_injective State.toSum fun a b h => by
    cases a <;> cases b <;> simp_all [State.toSum]

/-- The action that halts without moving or writing. -/
private def haltAction {Q : Type*} : Action 1 Bool (State Q) :=
  { inputTape := 0, workTapes := fun _ => (none, 0), output := none, state := none }

/-- The transition function of `ZipTransducer.toTM`. -/
private def tr : State Q → Option Bool → Option Bool → Action 1 Bool (State Q)
  | .copy, some true, _ =>
    { inputTape := 1, workTapes := fun _ => (none, 0), output := none, state := some .copyBit }
  | .copy, some false, _ =>
    { inputTape := 1, workTapes := fun _ => (none, -1), output := none, state := some .rewind }
  | .copy, none, _ => haltAction
  | .copyBit, some b, _ =>
    { inputTape := 1, workTapes := fun _ => (some (some b), 1), output := none,
      state := some .copy }
  | .copyBit, none, _ => haltAction
  | .rewind, _, some _ =>
    { inputTape := 0, workTapes := fun _ => (none, -1), output := none, state := some .rewind }
  | .rewind, _, none =>
    { inputTape := 0, workTapes := fun _ => (none, 1), output := none,
      state := some (.zip τ.q₀ none) }
  | .zip q (some b), _, _ =>
    { inputTape := 0, workTapes := fun _ => (none, 0), output := some b,
      state := some (.zip q none) }
  | .zip q none, none, none =>
    { inputTape := 0, workTapes := fun _ => (none, 0), output := (τ.final q).head?,
      state := (τ.final q).tail.head?.map .flush }
  | .zip q none, x, y =>
    { inputTape := if x.isSome then 1 else 0,
      workTapes := fun _ => (none, if y.isSome then 1 else 0),
      output := (τ.step q (y, x)).2.head?,
      state := some (.zip (τ.step q (y, x)).1 (τ.step q (y, x)).2.tail.head?) }
  | .flush b, _, _ =>
    { inputTape := 0, workTapes := fun _ => (none, 0), output := some b, state := none }

/-- `τ` as a machine with one work tape. On `frame u ++ v` it copies `u` to the work tape,
rewinds the work tape, and then runs `τ` on `u` from the work tape and `v` from the input tape. -/
public def toTM : MultiTapeTM 1 Bool (State Q) :=
  ofTr .copy fun s x ys => τ.tr s x (ys 0)

/-! ### Configurations -/

variable {w : List Bool}

/-- The configuration in state `st` with the input head at `p` (clamped to the input), the work
tape `tape` with its head at `h`, and the output `o`. -/
private def cfgAt (w : List Bool) (st : Option (State Q)) (p : ℕ) (tape : ℤ → Option Bool) (h : ℤ)
    (o : List Bool) : Cfg 1 Bool (State Q) w :=
  ⟨st, ⟨min p (w.length + 1), by omega⟩, fun _ => tape, fun _ => h, o⟩

private lemma moveInputPosNat_le (n j : ℕ) (d : SignType) (hj : j < n + 2) :
    moveInputPosNat n j d ≤ n + 1 := by
  have := (moveInputPos (⟨j, hj⟩ : Fin (n + 2)) d).isLt
  rw [val_moveInputPos_eq_moveInputPosNat] at this
  exact Nat.lt_succ_iff.mp this

/-- One step of `τ.toTM`, read off its transition function. -/
private lemma step_cfgAt (s : State Q) (p : ℕ) (tape : ℤ → Option Bool) (h : ℤ) (o : List Bool) :
    τ.toTM.step (cfgAt w (some s) p tape h o) =
      cfgAt w (τ.tr s (inputAt w (min p (w.length + 1))) (tape h)).state
        (moveInputPosNat w.length (min p (w.length + 1))
          (τ.tr s (inputAt w (min p (w.length + 1))) (tape h)).inputTape)
        (match ((τ.tr s (inputAt w (min p (w.length + 1))) (tape h)).workTapes 0).1 with
          | none => tape
          | some x => Function.update tape h x)
        (h + (((τ.tr s (inputAt w (min p (w.length + 1))) (tape h)).workTapes 0).2 : ℤ))
        (o ++ (τ.tr s (inputAt w (min p (w.length + 1))) (tape h)).output.toList) := by
  have hw : (cfgAt w (some s) p tape h o).workTapeSymbols = fun _ => tape h := rfl
  have hp : ((cfgAt w (some s) p tape h o).inputPos : ℕ) = min p (w.length + 1) := rfl
  rw [step_of_state rfl, Cfg.inputSymbol_eq_inputAt, hw, hp]
  simp only [toTM, tr_ofTr]
  refine Cfg.ext rfl (Fin.ext ?_) (funext fun i => ?_) (funext fun i => ?_) rfl
  · rw [Action.apply_inputPos, val_moveInputPos_eq_moveInputPosNat, hp]
    exact (min_eq_left (moveInputPosNat_le _ _ _ (by omega))).symm
  · obtain rfl : i = 0 := Subsingleton.elim _ _
    simp only [cfgAt, Action.apply_workTapes]
    rcases ((τ.tr s (inputAt w (min p (w.length + 1))) (tape h)).workTapes 0).1 with _ | _ <;> rfl
  · obtain rfl : i = 0 := Subsingleton.elim _ _
    simp only [cfgAt, Action.apply_workTapePos]

private lemma cfgAt_congr {st : Option (State Q)} {p p' : ℕ} {tape : ℤ → Option Bool} {h h' : ℤ}
    {o : List Bool} (hp : min p (w.length + 1) = min p' (w.length + 1)) (hh : h = h') :
    cfgAt w st p tape h o = cfgAt w st p' tape h' o := by
  subst hh
  simp only [cfgAt, hp]

private lemma moveInputPosNat_one {n j : ℕ} (hj : j ≤ n) : moveInputPosNat n j 1 = j + 1 := by
  simp only [moveInputPosNat, SignType.coe_one]
  omega

private lemma moveInputPosNat_zero {n j : ℕ} (hj : j ≤ n + 1) : moveInputPosNat n j 0 = j := by
  simp only [moveInputPosNat, SignType.coe_zero]
  omega

/-! ### Runs through a set of work-head positions -/

/-- From `c`, `τ.toTM` reaches `c'` within `t` steps, its work head staying in `S`. -/
private def Seg (S : Finset ℤ) (c c' : Cfg 1 Bool (State Q) w) (t : ℕ) : Prop :=
  ∃ n ≤ t, τ.toTM.runFrom c n = c' ∧ ∀ j ≤ n, (τ.toTM.runFrom c j).workTapePos 0 ∈ S

variable {τ} {S : Finset ℤ} {c c' c'' : Cfg 1 Bool (State Q) w} {t t' : ℕ}

private lemma Seg.refl (hc : c.workTapePos 0 ∈ S) : τ.Seg S c c 0 :=
  ⟨0, le_rfl, rfl, fun j hj => by
    obtain rfl : j = 0 := by omega
    exact hc⟩

private lemma Seg.single (hc : c.workTapePos 0 ∈ S) (h : τ.toTM.step c = c')
    (hc' : c'.workTapePos 0 ∈ S) : τ.Seg S c c' 1 :=
  ⟨1, le_rfl, h, fun j hj => by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hj with rfl | rfl
    · exact hc
    · rw [runFrom_one, h]
      exact hc'⟩

private lemma Seg.trans (h₁ : τ.Seg S c c' t) (h₂ : τ.Seg S c' c'' t') :
    τ.Seg S c c'' (t + t') := by
  obtain ⟨n₁, hn₁, hr₁, hs₁⟩ := h₁
  obtain ⟨n₂, hn₂, hr₂, hs₂⟩ := h₂
  refine ⟨n₁ + n₂, by omega, by rw [runFrom_add, hr₁, hr₂], fun j hj => ?_⟩
  rcases Nat.lt_or_ge n₁ j with h | h
  · obtain ⟨d, rfl⟩ : ∃ d, j = n₁ + d := ⟨j - n₁, by omega⟩
    rw [runFrom_add, hr₁]
    exact hs₂ d (by omega)
  · exact hs₁ j h

private lemma Seg.mono (h : τ.Seg S c c' t) (ht : t ≤ t') : τ.Seg S c c' t' :=
  let ⟨n, hn, hr, hs⟩ := h
  ⟨n, hn.trans ht, hr, hs⟩

/-! ### The framed input -/

private lemma getElem?_frame_append (u v : List Bool) {i : ℕ} (hi : i < u.length) :
    (frame u ++ v)[2 * i]? = some true ∧ (frame u ++ v)[2 * i + 1]? = some u[i] := by
  induction u generalizing i with
  | nil => simp at hi
  | cons b u ih =>
    rcases i with _ | i
    · simp [frame_cons]
    · obtain ⟨h₁, h₂⟩ := ih (i := i) (by simpa using hi)
      have e₁ : 2 * (i + 1) = 2 * i + 1 + 1 := by omega
      simp only [frame_cons, List.cons_append, e₁, List.getElem?_cons_succ,
        List.getElem_cons_succ]
      exact ⟨h₁, h₂⟩

private lemma getElem?_frame_append_length (u v : List Bool) (j : ℕ) :
    (frame u ++ v)[2 * u.length]? = some false ∧
      (frame u ++ v)[2 * u.length + 1 + j]? = v[j]? := by
  have hfl : frame u ++ v = u.flatMap (fun b => [true, b]) ++ false :: v := by simp [frame]
  have hlen : (u.flatMap (fun b => [true, b])).length = 2 * u.length := by
    have := length_frame u
    simp only [frame, List.length_append, List.length_singleton] at this
    omega
  rw [hfl, List.getElem?_append_right (by omega), List.getElem?_append_right (by omega), hlen,
    Nat.sub_self, (by omega : 2 * u.length + 1 + j - 2 * u.length = j + 1)]
  exact ⟨rfl, rfl⟩

/-! ### The phases of the machine -/

variable {u v : List Bool}

/-- The work head stays within the cells `-1, …, u.length`. -/
private abbrev cells (u : List Bool) : Finset ℤ := Finset.Icc (-1) u.length

@[simp]
private lemma cfgAt_workTapePos (st : Option (State Q)) (p : ℕ) (tape : ℤ → Option Bool) (h : ℤ)
    (o : List Bool) : (cfgAt w st p tape h o).workTapePos 0 = h :=
  rfl

private lemma cfgAt_mem_cells {st : Option (State Q)} {p : ℕ} {tape : ℤ → Option Bool} {h : ℤ}
    {o : List Bool} (h₀ : -1 ≤ h) (h₁ : h ≤ u.length) :
    (cfgAt w st p tape h o).workTapePos 0 ∈ cells u :=
  Finset.mem_Icc.mpr ⟨h₀, h₁⟩

private lemma length_frame_append (u v : List Bool) :
    (frame u ++ v).length = 2 * u.length + 1 + v.length := by
  rw [List.length_append, length_frame]

/-- Copying the first word to the work tape, digit by digit. -/
private lemma seg_copy {i : ℕ} (hi : i ≤ u.length) :
    τ.Seg (cells u)
      (cfgAt (frame u ++ v) (some .copy) (2 * i + 1) (tapeOfList (u.take i)) i [])
      (cfgAt (frame u ++ v) (some .copy) (2 * u.length + 1) (tapeOfList u) u.length [])
      (2 * (u.length - i)) := by
  obtain ⟨d, hd⟩ : ∃ d, u.length - i = d := ⟨_, rfl⟩
  have hn := length_frame_append u v
  induction d generalizing i with
  | zero =>
    obtain rfl : i = u.length := by omega
    rw [List.take_length]
    exact (Seg.refl (cfgAt_mem_cells (by omega) le_rfl)).mono (Nat.zero_le _)
  | succ d ih =>
    have hi' : i < u.length := by omega
    obtain ⟨h₁, h₂⟩ := getElem?_frame_append u v hi'
    have s₁ : τ.toTM.step
        (cfgAt (frame u ++ v) (some .copy) (2 * i + 1) (tapeOfList (u.take i)) i []) =
        cfgAt (frame u ++ v) (some .copyBit) (2 * i + 2) (tapeOfList (u.take i)) i [] := by
      rw [step_cfgAt]
      have hp : min (2 * i + 1) ((frame u ++ v).length + 1) = 2 * i + 1 := by omega
      have hx : inputAt (frame u ++ v) (2 * i + 1) = some true := by simpa [inputAt] using h₁
      simp only [hp, hx, tr, moveInputPosNat_one (by omega : 2 * i + 1 ≤ (frame u ++ v).length),
        SignType.coe_zero, add_zero, List.append_nil, Option.toList_none]
    have s₂ : τ.toTM.step
        (cfgAt (frame u ++ v) (some .copyBit) (2 * i + 2) (tapeOfList (u.take i)) i []) =
        cfgAt (frame u ++ v) (some .copy) (2 * (i + 1) + 1) (tapeOfList (u.take (i + 1)))
          ((i + 1 : ℕ) : ℤ) [] := by
      rw [step_cfgAt]
      have hp : min (2 * i + 2) ((frame u ++ v).length + 1) = 2 * i + 2 := by omega
      have hx : inputAt (frame u ++ v) (2 * i + 2) = some u[i] := by simpa [inputAt] using h₂
      have ht : Function.update (tapeOfList (u.take i)) (i : ℤ) (some u[i]) =
          tapeOfList (u.take (i + 1)) := by
        rw [List.take_add_one, List.getElem?_eq_getElem hi', Option.toList_some,
          tapeOfList_append_single, List.length_take, min_eq_left hi'.le]
      simp only [hp, hx, tr, moveInputPosNat_one (by omega : 2 * i + 2 ≤ (frame u ++ v).length),
        SignType.coe_one, List.append_nil, Option.toList_none, ht]
      exact cfgAt_congr (by omega) (by push_cast; rfl)
    refine ((Seg.single (cfgAt_mem_cells (by omega) (by omega)) s₁
      (cfgAt_mem_cells (by omega) (by omega))).trans
      ((Seg.single (cfgAt_mem_cells (by omega) (by omega)) s₂
        (cfgAt_mem_cells (by omega) (by omega))).trans
        (ih (i := i + 1) (by omega) (by omega)))).mono (by omega)

/-! The transitions used outside the copy phase, for arbitrary read symbols. -/

private lemma tr_rewind_some (x : Option Bool) (b : Bool) :
    τ.tr .rewind x (some b) =
      { inputTape := 0, workTapes := fun _ => (none, -1), output := none,
        state := some .rewind } := by
  cases x <;> rfl

private lemma tr_rewind_none (x : Option Bool) :
    τ.tr .rewind x none =
      { inputTape := 0, workTapes := fun _ => (none, 1), output := none,
        state := some (.zip τ.q₀ none) } := by
  cases x <;> rfl

private lemma tr_zip_some (q : Q) (b : Bool) (x y : Option Bool) :
    τ.tr (.zip q (some b)) x y =
      { inputTape := 0, workTapes := fun _ => (none, 0), output := some b,
        state := some (.zip q none) } := by
  cases x <;> cases y <;> rfl

private lemma tr_zip_step (q : Q) {x y : Option Bool} (h : ¬(x = none ∧ y = none)) :
    τ.tr (.zip q none) x y =
      { inputTape := if x.isSome then 1 else 0,
        workTapes := fun _ => (none, if y.isSome then 1 else 0),
        output := (τ.step q (y, x)).2.head?,
        state := some (.zip (τ.step q (y, x)).1 (τ.step q (y, x)).2.tail.head?) } := by
  rcases x with _ | _ <;> rcases y with _ | _
  · simp at h
  all_goals rfl

private lemma tr_flush (b : Bool) (x y : Option Bool) :
    τ.tr (.flush b) x y =
      { inputTape := 0, workTapes := fun _ => (none, 0), output := some b, state := none } := by
  cases x <;> cases y <;> rfl

/-- The end of the frame: the input head moves to the second word and the work head starts
moving back. -/
private lemma step_endFrame :
    τ.toTM.step (cfgAt (frame u ++ v) (some .copy) (2 * u.length + 1) (tapeOfList u)
      u.length []) =
      cfgAt (frame u ++ v) (some .rewind) (2 * u.length + 2) (tapeOfList u)
        ((u.length : ℤ) - 1) [] := by
  have hn := length_frame_append u v
  rw [step_cfgAt]
  have hp : min (2 * u.length + 1) ((frame u ++ v).length + 1) = 2 * u.length + 1 := by omega
  have hx : inputAt (frame u ++ v) (2 * u.length + 1) = some false := by
    simpa [inputAt] using (getElem?_frame_append_length u v 0).1
  simp only [hp, hx, tr, moveInputPosNat_one (by omega : 2 * u.length + 1 ≤ (frame u ++ v).length),
    SignType.coe_neg_one, List.append_nil, Option.toList_none]
  exact cfgAt_congr (by omega) (by omega)

/-- Rewinding the work tape. -/
private lemma seg_rewind {i : ℕ} (hi : i ≤ u.length) :
    τ.Seg (cells u)
      (cfgAt (frame u ++ v) (some .rewind) (2 * u.length + 2) (tapeOfList u) ((i : ℤ) - 1) [])
      (cfgAt (frame u ++ v) (some (.zip τ.q₀ none)) (2 * u.length + 2) (tapeOfList u) 0 [])
      (i + 1) := by
  have hn := length_frame_append u v
  have hp : min (2 * u.length + 2) ((frame u ++ v).length + 1) = 2 * u.length + 2 := by omega
  induction i with
  | zero =>
    refine Seg.single (cfgAt_mem_cells (by omega) (by omega)) ?_
      (cfgAt_mem_cells (by omega) (by omega))
    rw [step_cfgAt, hp, (by simp : ((0 : ℕ) : ℤ) - 1 = Int.negSucc 0), tapeOfList_negSucc,
      tr_rewind_none, moveInputPosNat_zero (by omega)]
    simp only [SignType.coe_one, List.append_nil, Option.toList_none]
    exact cfgAt_congr rfl (by omega)
  | succ i ih =>
    have hi' : i < u.length := by omega
    have hs : τ.toTM.step (cfgAt (frame u ++ v) (some .rewind) (2 * u.length + 2) (tapeOfList u)
        (((i + 1 : ℕ) : ℤ) - 1) []) =
        cfgAt (frame u ++ v) (some .rewind) (2 * u.length + 2) (tapeOfList u) ((i : ℤ) - 1) [] := by
      rw [step_cfgAt, hp, (by omega : ((i + 1 : ℕ) : ℤ) - 1 = ((i : ℕ) : ℤ)),
        tapeOfList_ofNat, List.getElem?_eq_getElem hi', tr_rewind_some,
        moveInputPosNat_zero (by omega)]
      simp only [SignType.coe_neg_one, List.append_nil, Option.toList_none]
      exact cfgAt_congr rfl (by omega)
    exact ((Seg.single (cfgAt_mem_cells (by omega) (by omega)) hs
      (cfgAt_mem_cells (by omega) (by omega))).trans (ih (by omega))).mono (by omega)

/-- Emitting a pending output symbol. -/
private lemma seg_flush {q : Q} (pend : Option Bool) {p : ℕ} (hp : p ≤ (frame u ++ v).length + 1)
    {tape : ℤ → Option Bool} {h : ℤ} (h₀ : -1 ≤ h) (h₁ : h ≤ u.length) (o : List Bool) :
    τ.Seg (cells u) (cfgAt (frame u ++ v) (some (.zip q pend)) p tape h o)
      (cfgAt (frame u ++ v) (some (.zip q none)) p tape h (o ++ pend.toList)) 1 := by
  rcases pend with _ | b
  · rw [Option.toList_none, List.append_nil]
    exact (Seg.refl (cfgAt_mem_cells h₀ h₁)).mono (Nat.zero_le _)
  · refine Seg.single (cfgAt_mem_cells h₀ h₁) ?_ (cfgAt_mem_cells h₀ h₁)
    rw [step_cfgAt, tr_zip_some, min_eq_left hp, moveInputPosNat_zero hp]
    simp only [SignType.coe_zero, add_zero, Option.toList_some]

private lemma getElem?_min_length {α : Type*} (l : List α) (r : ℕ) :
    l[min r l.length]? = (l.drop r).head? := by
  rw [List.head?_drop]
  rcases Nat.le_total r l.length with h | h
  · rw [min_eq_left h]
  · rw [min_eq_right h, List.getElem?_eq_none le_rfl, List.getElem?_eq_none h]

/-- Running `τ` on both words in lockstep, from round `r` on. -/
private lemma seg_zip (q : Q) {r : ℕ} (hr : r ≤ max u.length v.length) (o : List Bool) :
    τ.Seg (cells u)
      (cfgAt (frame u ++ v) (some (.zip q none)) (2 * u.length + 2 + min r v.length)
        (tapeOfList u) (min r u.length : ℕ) o)
      (cfgAt (frame u ++ v) none (2 * u.length + 2 + v.length) (tapeOfList u) u.length
        (o ++ τ.run q (u.drop r) (v.drop r)))
      (2 * (max u.length v.length - r) + 2) := by
  obtain ⟨d, hd⟩ : ∃ d, max u.length v.length - r = d := ⟨_, rfl⟩
  have hn := length_frame_append u v
  induction d generalizing r q o with
  | zero =>
    have hu : u.drop r = [] := List.drop_eq_nil_of_le (by omega)
    have hv : v.drop r = [] := List.drop_eq_nil_of_le (by omega)
    have hp : min (2 * u.length + 2 + min r v.length) ((frame u ++ v).length + 1) =
        2 * u.length + 2 + v.length := by omega
    have hx : inputAt (frame u ++ v) (2 * u.length + 2 + v.length) = none := by
      unfold inputAt
      split_ifs
      · rfl
      · exact List.getElem?_eq_none (by omega)
    have hy : tapeOfList u ((min r u.length : ℕ) : ℤ) = none := by
      rw [tapeOfList_ofNat, List.getElem?_eq_none (by omega)]
    have s₁ : τ.toTM.step (cfgAt (frame u ++ v) (some (.zip q none))
        (2 * u.length + 2 + min r v.length) (tapeOfList u) (min r u.length : ℕ) o) =
        cfgAt (frame u ++ v) ((τ.final q).tail.head?.map .flush) (2 * u.length + 2 + v.length)
          (tapeOfList u) u.length (o ++ (τ.final q).head?.toList) := by
      rw [step_cfgAt, hp, hx, hy]
      simp only [tr, SignType.coe_zero, add_zero,
        moveInputPosNat_zero (by omega : 2 * u.length + 2 + v.length ≤ (frame u ++ v).length + 1)]
      exact cfgAt_congr rfl (by omega)
    rw [hu, hv, run_nil_nil]
    have hfin := (List.take_add_one (l := τ.final q) (i := 1)).symm
    rw [List.take_one, ← List.head?_tail, List.take_of_length_le (τ.length_final_le q)] at hfin
    rcases hb : (τ.final q).tail.head? with _ | b
    · rw [hb, Option.toList_none, List.append_nil] at hfin
      rw [hb, Option.map_none] at s₁
      rw [hfin] at s₁
      exact (Seg.single (cfgAt_mem_cells (by omega) (by omega)) s₁
        (cfgAt_mem_cells (by omega) (by omega))).mono (by omega)
    · rw [hb, Option.map_some] at s₁
      have s₂ : τ.toTM.step (cfgAt (frame u ++ v) (some (.flush b)) (2 * u.length + 2 + v.length)
          (tapeOfList u) u.length (o ++ (τ.final q).head?.toList)) =
          cfgAt (frame u ++ v) none (2 * u.length + 2 + v.length) (tapeOfList u) u.length
            (o ++ τ.final q) := by
        rw [step_cfgAt, tr_flush, moveInputPosNat_zero (by omega)]
        rw [hb, Option.toList_some] at hfin
        simp only [SignType.coe_zero, add_zero, Option.toList_some, List.append_assoc, hfin]
        exact cfgAt_congr (by omega) rfl
      exact ((Seg.single (cfgAt_mem_cells (by omega) (by omega)) s₁
        (cfgAt_mem_cells (by omega) (by omega))).trans
        (Seg.single (cfgAt_mem_cells (by omega) (by omega)) s₂
          (cfgAt_mem_cells (by omega) (by omega)))).mono (by omega)
  | succ d ih =>
    have hne : ¬((v.drop r).head? = none ∧ (u.drop r).head? = none) := by
      simp only [List.head?_eq_none_iff, List.drop_eq_nil_iff]
      omega
    have hp : min (2 * u.length + 2 + min r v.length) ((frame u ++ v).length + 1) =
        2 * u.length + 2 + min r v.length := by omega
    have hx : inputAt (frame u ++ v) (2 * u.length + 2 + min r v.length) = (v.drop r).head? := by
      rw [← getElem?_min_length]
      simpa [inputAt,
        (by omega : 2 * u.length + 2 + min r v.length - 1 = 2 * u.length + 1 + min r v.length)]
        using (getElem?_frame_append_length u v (min r v.length)).2
    have hy : tapeOfList u ((min r u.length : ℕ) : ℤ) = (u.drop r).head? := by
      rw [tapeOfList_ofNat, getElem?_min_length]
    set x := (v.drop r).head? with hxdef
    set y := (u.drop r).head? with hydef
    have hxs : x.isSome = decide (r < v.length) := by
      rw [hxdef, List.head?_drop]
      rcases Nat.lt_or_ge r v.length with h | h
      · simp [h]
      · simp [Nat.not_lt.mpr h]
    have hys : y.isSome = decide (r < u.length) := by
      rw [hydef, List.head?_drop]
      rcases Nat.lt_or_ge r u.length with h | h
      · simp [h]
      · simp [Nat.not_lt.mpr h]
    have hmove : moveInputPosNat (frame u ++ v).length (2 * u.length + 2 + min r v.length)
        (if x.isSome then 1 else 0) = 2 * u.length + 2 + min (r + 1) v.length := by
      rw [hxs]
      rcases Nat.lt_or_ge r v.length with h | h
      · simp only [decide_eq_true h, ↓reduceIte]
        rw [moveInputPosNat_one (by omega)]
        omega
      · simp only [decide_eq_false (Nat.not_lt.mpr h), Bool.false_eq_true, ↓reduceIte]
        rw [moveInputPosNat_zero (by omega)]
        omega
    have hhead : ((min r u.length : ℕ) : ℤ) + ((if y.isSome then 1 else 0 : SignType) : ℤ) =
        ((min (r + 1) u.length : ℕ) : ℤ) := by
      rw [hys]
      rcases Nat.lt_or_ge r u.length with h | h
      · simp only [decide_eq_true h, ↓reduceIte, SignType.coe_one]
        omega
      · simp only [decide_eq_false (Nat.not_lt.mpr h), Bool.false_eq_true, ↓reduceIte,
          SignType.coe_zero]
        omega
    have s₁ : τ.toTM.step (cfgAt (frame u ++ v) (some (.zip q none))
        (2 * u.length + 2 + min r v.length) (tapeOfList u) (min r u.length : ℕ) o) =
        cfgAt (frame u ++ v) (some (.zip (τ.step q (y, x)).1 (τ.step q (y, x)).2.tail.head?))
          (2 * u.length + 2 + min (r + 1) v.length) (tapeOfList u) (min (r + 1) u.length : ℕ)
          (o ++ (τ.step q (y, x)).2.head?.toList) := by
      rw [step_cfgAt, hp, hx, hy, tr_zip_step q hne]
      simp only [hmove, hhead]
    have hrun : o ++ τ.run q (u.drop r) (v.drop r) =
        o ++ (τ.step q (y, x)).2.head?.toList ++ (τ.step q (y, x)).2.tail.head?.toList ++
          τ.run (τ.step q (y, x)).1 (u.drop (r + 1)) (v.drop (r + 1)) := by
      rw [τ.run_of_ne (by simpa [hxdef, hydef, and_comm] using hne), List.tail_drop,
        List.tail_drop, List.append_assoc, List.append_assoc,
        ← List.append_assoc ((τ.step q (y, x)).2.head?.toList),
        ← List.take_one, List.head?_tail, ← List.take_add_one,
        List.take_of_length_le (τ.length_step_le _ _)]
    rw [hrun]
    exact ((Seg.single (cfgAt_mem_cells (by omega) (by omega)) s₁
      (cfgAt_mem_cells (by omega) (by omega))).trans
      ((seg_flush _ (by omega) (by omega) (by omega) _).trans
        (ih _ (by omega) _ (by omega)))).mono (by omega)

/-- The complete run on `frame u ++ v`. -/
private lemma seg_run (u v : List Bool) :
    τ.Seg (cells u) (τ.toTM.initCfg (frame u ++ v))
      (cfgAt (frame u ++ v) none (2 * u.length + 2 + v.length) (tapeOfList u) u.length
        (τ.run τ.q₀ u v))
      (3 * (frame u ++ v).length + 1) := by
  have hn := length_frame_append u v
  have hinit : τ.toTM.initCfg (frame u ++ v) =
      cfgAt (frame u ++ v) (some .copy) (2 * 0 + 1) (tapeOfList (u.take 0)) ((0 : ℕ) : ℤ) [] := by
    refine Cfg.ext rfl (Fin.ext ?_) (funext fun _ => ?_) rfl rfl
    · simp [MultiTapeNTM.initCfg, Cfg.init, cfgAt]
    · simp [MultiTapeNTM.initCfg, Cfg.init, cfgAt]
  have hzip := seg_zip (τ := τ) (u := u) (v := v) τ.q₀ (r := 0) (Nat.zero_le _) []
  simp only [Nat.zero_min, Nat.add_zero, Nat.cast_zero, List.drop_zero, List.nil_append,
    Nat.sub_zero] at hzip
  rw [hinit]
  refine (((seg_copy (Nat.zero_le _)).trans ((Seg.single (cfgAt_mem_cells (by omega) le_rfl)
    step_endFrame (cfgAt_mem_cells (by omega) (by omega))).trans
    ((seg_rewind le_rfl).trans hzip))).mono ?_)
  have := Nat.max_le.mpr ⟨(le_rfl : u.length ≤ u.length), le_rfl⟩
  omega

/-- On `frame u ++ v`, `τ.toTM` emits `τ.run τ.q₀ u v` within `3 * (frame u ++ v).length + 1`
steps, visiting the `u.length + 2` work-tape cells `-1, …, u.length`. -/
public theorem computesInTimeAndSpace_toTM (u v : List Bool) :
    τ.toTM.ComputesInTimeAndSpace (frame u ++ v) (τ.run τ.q₀ u v)
      (3 * (frame u ++ v).length + 1) (u.length + 2) := by
  obtain ⟨n, hn, hrun, hcells⟩ := τ.seg_run u v
  have hhalt : (τ.toTM.runFrom (τ.toTM.initCfg (frame u ++ v)) n).Halted := by
    rw [hrun]
    rfl
  refine ⟨⟨n, hhalt, by rw [hrun]; rfl⟩, runsInTime_of_halted ?_, runsInSpace_of_halted hhalt ?_⟩
  · rw [runFrom_eq_of_halt _ _ hn hhalt]
    exact hhalt
  · simp only [MultiTapeNTM.RunPath.space, Finset.univ_unique, Fin.default_eq_zero,
      Finset.sum_singleton]
    refine (spaceUsedByTape_le_card _ hcells).trans_eq ?_
    simp only [cells, Int.card_Icc]
    omega

end ZipTransducer

end Turing.MultiTapeTM


