-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_KernelTakeDropUnary
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_KernelTakeDropUnary
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:43:52.870825+00:00
-- url     : https://prove2.me/theorems/42272215-6e73-4604-ba38-68f423396afc
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Internal.KernelTakeDropUnary — A one-tape machine cutting a framed word at a unary count
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Internal.KernelTakeDropUnary` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   The machine `Turing.MultiTapeTM.TakeDropUnary.toTM keep` reads `frame u ++ List.replicate n true`.
--   It skips the frame, copies the count `n` to its work tape (leaving the head on the last `true`),
--   rewinds the input head and then streams the framed word `u`, reading `u` itself as a sequence of
--   frames: it remembers whether the next inner symbol is a marker or follows a marker `true`. At every
--   inner terminator `false` the work head moves one cell to the left while it is on a `true`, so the
--   head position counts the inner frames still to be taken or dropped. Inner symbols are emitted while
--   the count is positive (`keep = true`) or once it is zero (`keep = false`).
--
--   On `u = encList enc l` this emits the encoded `l.take n` or `l.drop n`. The machine runs in time
--   linear in its input and uses `n + 2` work-tape cells. This is the realization behind
--   `Turing.MultiTapeTM.ComputableInDegree.takeUnary` and `.dropUnary`; folding over the count or over
--   the list would cost quadratic time.
--
--   ### Main definitions
--
--   * `Turing.MultiTapeTM.TakeDropUnary.stream`: the word emitted while streaming an inner word.
--   * `Turing.MultiTapeTM.TakeDropUnary.toTM`: the machine with one work tape.
--
--   ### Main results
--
--   * `Turing.MultiTapeTM.TakeDropUnary.computesInTimeAndSpace_toTM`: on
--     `frame u ++ List.replicate n true`, `toTM keep` emits `stream keep false n u` within
--     `3 * (frame u ++ List.replicate n true).length + 2` steps and `n + 2` cells.
--   * `Turing.MultiTapeTM.TakeDropUnary.stream_encList`: on an encoded list, the stream is the encoded
--     prefix or suffix.
--   * `Turing.MultiTapeTM.TakeDropUnary.computableInTimeAndSpace`: taking or dropping a unary number of
--     encoded list elements within `3 * (input length) + 2` steps and `n + 2` cells.
--
--   **Contents.** The module is published as a whole: 46 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with library lemmas renamed back to their names in this Mathlib and a few proof steps adjusted; no statement is changed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_KernelTakeDropUnary`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Internal/KernelTakeDropUnary.lean

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Run
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Frame_Basic
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_List
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Pair
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Unary
import Mathlib.Data.Finite.Sum

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Internal.KernelTakeDropUnary` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# A one-tape machine cutting a framed word at a unary count

The machine `Turing.MultiTapeTM.TakeDropUnary.toTM keep` reads `frame u ++ List.replicate n true`.
It skips the frame, copies the count `n` to its work tape (leaving the head on the last `true`),
rewinds the input head and then streams the framed word `u`, reading `u` itself as a sequence of
frames: it remembers whether the next inner symbol is a marker or follows a marker `true`. At every
inner terminator `false` the work head moves one cell to the left while it is on a `true`, so the
head position counts the inner frames still to be taken or dropped. Inner symbols are emitted while
the count is positive (`keep = true`) or once it is zero (`keep = false`).

On `u = encList enc l` this emits the encoded `l.take n` or `l.drop n`. The machine runs in time
linear in its input and uses `n + 2` work-tape cells. This is the realization behind
`Turing.MultiTapeTM.ComputableInDegree.takeUnary` and `.dropUnary`; folding over the count or over
the list would cost quadratic time.

## Main definitions

* `Turing.MultiTapeTM.TakeDropUnary.stream`: the word emitted while streaming an inner word.
* `Turing.MultiTapeTM.TakeDropUnary.toTM`: the machine with one work tape.

## Main results

* `Turing.MultiTapeTM.TakeDropUnary.computesInTimeAndSpace_toTM`: on
  `frame u ++ List.replicate n true`, `toTM keep` emits `stream keep false n u` within
  `3 * (frame u ++ List.replicate n true).length + 2` steps and `n + 2` cells.
* `Turing.MultiTapeTM.TakeDropUnary.stream_encList`: on an encoded list, the stream is the encoded
  prefix or suffix.
* `Turing.MultiTapeTM.TakeDropUnary.computableInTimeAndSpace`: taking or dropping a unary number of
  encoded list elements within `3 * (input length) + 2` steps and `n + 2` cells.
-/

namespace Turing.MultiTapeTM

namespace TakeDropUnary

/-! ### The streaming semantics -/

/-- Whether inner symbols are emitted when the remaining count is `c`: while `c` is positive when
taking (`keep = true`), once it is zero when dropping (`keep = false`). -/
@[expose] public def emits (keep : Bool) (c : ℕ) : Bool :=
  decide (0 < c) == keep

/-- `stream keep inBit c u`: the word emitted while streaming the inner word `u` with remaining
count `c`, where `inBit` says whether the next inner symbol follows a marker `true` (and so is a
symbol of the current inner frame). Each inner terminator `false` decrements the count. -/
@[expose] public def stream (keep : Bool) : Bool → ℕ → List Bool → List Bool
  | _, _, [] => []
  | false, c, b :: u =>
    (if emits keep c then [b] else []) ++ stream keep b (if b then c else c - 1) u
  | true, c, b :: u => (if emits keep c then [b] else []) ++ stream keep false c u

/-- The kind of the next inner symbol after reading `b` in kind `inBit`. -/
@[expose] public def nextKind (inBit b : Bool) : Bool :=
  if inBit then false else b

/-- The count after reading `b` in kind `inBit`. -/
@[expose] public def nextCount (inBit b : Bool) (c : ℕ) : ℕ :=
  if inBit then c else if b then c else c - 1

public lemma stream_cons (keep inBit : Bool) (c : ℕ) (b : Bool) (u : List Bool) :
    stream keep inBit c (b :: u) =
      (if emits keep c then [b] else []) ++
        stream keep (nextKind inBit b) (nextCount inBit b c) u := by
  cases inBit <;> cases b <;> rfl

/-- **Streaming one inner frame** emits it when the count admits emission and then continues with
the count decremented. -/
public theorem stream_frame_append (keep : Bool) (c : ℕ) (w rest : List Bool) :
    stream keep false c (frame w ++ rest) =
      (if emits keep c then frame w else []) ++ stream keep false (c - 1) rest := by
  induction w with
  | nil => cases h : emits keep c <;> simp [frame_nil, stream, h]
  | cons b w ih =>
    simp only [frame_cons, List.cons_append, stream, ↓reduceIte, ih]
    cases emits keep c <;> simp

/-! ### The machine -/

/-- The control states of `TakeDropUnary.toTM`. -/
public inductive State where
  /-- Skipping the framed word: expecting a marker. -/
  | skip
  /-- Skipping the framed word: expecting a symbol. -/
  | skipBit
  /-- Copying the unary count to the work tape. -/
  | copy
  /-- Moving the input head back to its start. -/
  | rewind
  /-- Streaming: expecting a marker of the outer frame. -/
  | marker (inBit : Bool)
  /-- Streaming: expecting an inner symbol of kind `inBit`. -/
  | symbol (inBit : Bool)

/-- An encoding of the control states into a finite type. -/
private def State.toSum : State → Fin 4 ⊕ Bool ⊕ Bool
  | .skip => .inl 0
  | .skipBit => .inl 1
  | .copy => .inl 2
  | .rewind => .inl 3
  | .marker b => .inr (.inl b)
  | .symbol b => .inr (.inr b)

public instance State.instFinite : Finite State :=
  Finite.of_injective State.toSum fun a b h => by
    cases a <;> cases b <;> simp_all [State.toSum]

/-- The action that halts without moving or writing. -/
private def haltAction : Action 1 Bool State :=
  { inputTape := 0, workTapes := fun _ => (none, 0), output := none, state := none }

/-- The action moving the input head by `d` into state `q`. -/
private def moveTo (d : SignType) (q : State) : Action 1 Bool State :=
  { inputTape := d, workTapes := fun _ => (none, 0), output := none, state := some q }

/-- The transition function of `TakeDropUnary.toTM`. -/
private def tr (keep : Bool) : State → Option Bool → Option Bool → Action 1 Bool State
  | .skip, some true, _ => moveTo 1 .skipBit
  | .skip, some false, _ => moveTo 1 .copy
  | .skip, none, _ => haltAction
  | .skipBit, some _, _ => moveTo 1 .skip
  | .skipBit, none, _ => haltAction
  | .copy, some true, _ =>
    { inputTape := 1, workTapes := fun _ => (some (some true), 1), output := none,
      state := some .copy }
  | .copy, some false, _ => haltAction
  | .copy, none, _ =>
    { inputTape := -1, workTapes := fun _ => (none, -1), output := none, state := some .rewind }
  | .rewind, some _, _ => moveTo (-1) .rewind
  | .rewind, none, _ => moveTo 1 (.marker false)
  | .marker b, some true, _ => moveTo 1 (.symbol b)
  | .marker _, some false, _ => haltAction
  | .marker _, none, _ => haltAction
  | .symbol inBit, some b, y =>
    { inputTape := 1,
      workTapes := fun _ => (none, if !inBit && !b && y.isSome then -1 else 0),
      output := if y.isSome == keep then some b else none,
      state := some (.marker (nextKind inBit b)) }
  | .symbol _, none, _ => haltAction

/-- The machine with one work tape cutting `frame u ++ List.replicate n true`: it emits the inner
frames of `u` while the count `n` lasts (`keep = true`) or after it is used up (`keep = false`). -/
public def toTM (keep : Bool) : MultiTapeTM 1 Bool State :=
  ofTr .skip fun s x ys => tr keep s x (ys 0)

/-! ### Configurations -/

variable {keep : Bool} {w : List Bool}

/-- The configuration in state `st` with the input head at `p` (clamped to the input), the work
tape `tape` with its head at `h`, and the output `o`. -/
private def cfgAt (w : List Bool) (st : Option State) (p : ℕ) (tape : ℤ → Option Bool) (h : ℤ)
    (o : List Bool) : Cfg 1 Bool State w :=
  ⟨st, ⟨min p (w.length + 1), by omega⟩, fun _ => tape, fun _ => h, o⟩

private lemma moveInputPosNat_le (n j : ℕ) (d : SignType) (hj : j < n + 2) :
    moveInputPosNat n j d ≤ n + 1 := by
  have := (moveInputPos (⟨j, hj⟩ : Fin (n + 2)) d).isLt
  rw [val_moveInputPos_eq_moveInputPosNat] at this
  exact Nat.lt_succ_iff.mp this

/-- One step of `toTM`, read off its transition function. -/
private lemma step_cfgAt (s : State) (p : ℕ) (tape : ℤ → Option Bool) (h : ℤ) (o : List Bool) :
    (toTM keep).step (cfgAt w (some s) p tape h o) =
      cfgAt w (tr keep s (inputAt w (min p (w.length + 1))) (tape h)).state
        (moveInputPosNat w.length (min p (w.length + 1))
          (tr keep s (inputAt w (min p (w.length + 1))) (tape h)).inputTape)
        (match ((tr keep s (inputAt w (min p (w.length + 1))) (tape h)).workTapes 0).1 with
          | none => tape
          | some x => Function.update tape h x)
        (h + (((tr keep s (inputAt w (min p (w.length + 1))) (tape h)).workTapes 0).2 : ℤ))
        (o ++ (tr keep s (inputAt w (min p (w.length + 1))) (tape h)).output.toList) := by
  have hw : (cfgAt w (some s) p tape h o).workTapeSymbols = fun _ => tape h := rfl
  have hp : ((cfgAt w (some s) p tape h o).inputPos : ℕ) = min p (w.length + 1) := rfl
  rw [step_of_state rfl, Cfg.inputSymbol_eq_inputAt, hw, hp]
  simp only [toTM, tr_ofTr]
  refine Cfg.ext rfl (Fin.ext ?_) (funext fun i => ?_) (funext fun i => ?_) rfl
  · rw [Action.apply_inputPos, val_moveInputPos_eq_moveInputPosNat, hp]
    exact (min_eq_left (moveInputPosNat_le _ _ _ (by omega))).symm
  · obtain rfl : i = 0 := Subsingleton.elim _ _
    simp only [cfgAt, Action.apply_workTapes]
    rcases ((tr keep s (inputAt w (min p (w.length + 1))) (tape h)).workTapes 0).1 with _ | _ <;>
      rfl
  · obtain rfl : i = 0 := Subsingleton.elim _ _
    simp only [cfgAt, Action.apply_workTapePos]

private lemma cfgAt_congr {st : Option State} {p p' : ℕ} {tape : ℤ → Option Bool} {h h' : ℤ}
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

private lemma moveInputPosNat_neg_one {n j : ℕ} (hj : j ≤ n + 1) :
    moveInputPosNat n j (-1) = j - 1 := by
  simp only [moveInputPosNat, SignType.coe_neg_one]
  omega

/-! ### Runs through a set of work-head positions -/

/-- From `c`, `toTM keep` reaches `c'` within `t` steps, its work head staying in `S`. -/
private def Seg (keep : Bool) (S : Finset ℤ) (c c' : Cfg 1 Bool State w) (t : ℕ) : Prop :=
  ∃ n ≤ t, (toTM keep).runFrom c n = c' ∧ ∀ j ≤ n, ((toTM keep).runFrom c j).workTapePos 0 ∈ S

variable {S : Finset ℤ} {c c' c'' : Cfg 1 Bool State w} {t t' : ℕ}

private lemma Seg.refl (hc : c.workTapePos 0 ∈ S) : Seg keep S c c 0 :=
  ⟨0, le_rfl, rfl, fun j hj => by
    obtain rfl : j = 0 := by omega
    exact hc⟩

private lemma Seg.single (hc : c.workTapePos 0 ∈ S) (h : (toTM keep).step c = c')
    (hc' : c'.workTapePos 0 ∈ S) : Seg keep S c c' 1 :=
  ⟨1, le_rfl, h, fun j hj => by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hj with rfl | rfl
    · exact hc
    · rw [runFrom_one, h]
      exact hc'⟩

private lemma Seg.trans (h₁ : Seg keep S c c' t) (h₂ : Seg keep S c' c'' t') :
    Seg keep S c c'' (t + t') := by
  obtain ⟨n₁, hn₁, hr₁, hs₁⟩ := h₁
  obtain ⟨n₂, hn₂, hr₂, hs₂⟩ := h₂
  refine ⟨n₁ + n₂, by omega, by rw [runFrom_add, hr₁, hr₂], fun j hj => ?_⟩
  rcases Nat.lt_or_ge n₁ j with h | h
  · obtain ⟨d, rfl⟩ : ∃ d, j = n₁ + d := ⟨j - n₁, by omega⟩
    rw [runFrom_add, hr₁]
    exact hs₂ d (by omega)
  · exact hs₁ j h

private lemma Seg.mono (h : Seg keep S c c' t) (ht : t ≤ t') : Seg keep S c c' t' :=
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

private lemma length_frame_append (u v : List Bool) :
    (frame u ++ v).length = 2 * u.length + 1 + v.length := by
  rw [List.length_append, length_frame]

/-- The inner symbols of `frame u ++ v`: the marker `true` and the symbol `u[i]`. -/
private lemma inputAt_frame_append (u v : List Bool) {i : ℕ} (hi : i < u.length) :
    inputAt (frame u ++ v) (2 * i + 1) = some true ∧
      inputAt (frame u ++ v) (2 * i + 2) = some u[i] := by
  obtain ⟨h₁, h₂⟩ := getElem?_frame_append u v hi
  exact ⟨by simpa [inputAt] using h₁, by simpa [inputAt] using h₂⟩

/-- The terminator of the frame. -/
private lemma inputAt_frame_append_length (u v : List Bool) :
    inputAt (frame u ++ v) (2 * u.length + 1) = some false := by
  simpa [inputAt] using (getElem?_frame_append_length u v 0).1

/-! ### The phases of the machine -/

variable {u : List Bool} {n : ℕ}

/-- The work head stays within the cells `-1, …, n`. -/
private noncomputable abbrev cells (n : ℕ) : Finset ℤ := Finset.Icc (-1) n

@[simp]
private lemma cfgAt_workTapePos (st : Option State) (p : ℕ) (tape : ℤ → Option Bool) (h : ℤ)
    (o : List Bool) : (cfgAt w st p tape h o).workTapePos 0 = h :=
  rfl

private lemma cfgAt_mem_cells {st : Option State} {p : ℕ} {tape : ℤ → Option Bool} {h : ℤ}
    {o : List Bool} (h₀ : -1 ≤ h) (h₁ : h ≤ n) :
    (cfgAt w st p tape h o).workTapePos 0 ∈ cells n :=
  Finset.mem_Icc.mpr ⟨h₀, h₁⟩

/-- The input word. -/
private abbrev word (u : List Bool) (n : ℕ) : List Bool := frame u ++ List.replicate n true

private lemma length_word (u : List Bool) (n : ℕ) : (word u n).length = 2 * u.length + 1 + n := by
  rw [length_frame_append, List.length_replicate]

/-- Skipping the frame. -/
private lemma seg_skip {i : ℕ} (hi : i ≤ u.length) :
    Seg keep (cells n) (cfgAt (word u n) (some .skip) (2 * i + 1) (tapeOfList []) 0 [])
      (cfgAt (word u n) (some .skip) (2 * u.length + 1) (tapeOfList []) 0 [])
      (2 * (u.length - i)) := by
  obtain ⟨d, hd⟩ : ∃ d, u.length - i = d := ⟨_, rfl⟩
  have hn := length_word u n
  induction d generalizing i with
  | zero =>
    obtain rfl : i = u.length := by omega
    exact (Seg.refl (cfgAt_mem_cells (by omega) (by omega))).mono (Nat.zero_le _)
  | succ d ih =>
    have hi' : i < u.length := by omega
    obtain ⟨h₁, h₂⟩ := inputAt_frame_append u (List.replicate n true) hi'
    have s₁ : (toTM keep).step
        (cfgAt (word u n) (some .skip) (2 * i + 1) (tapeOfList []) 0 []) =
        cfgAt (word u n) (some .skipBit) (2 * i + 2) (tapeOfList []) 0 [] := by
      rw [step_cfgAt, min_eq_left (by omega), h₁]
      simp only [tr, moveTo, moveInputPosNat_one (by omega : 2 * i + 1 ≤ (word u n).length),
        SignType.coe_zero, add_zero, List.append_nil, Option.toList_none]
    have s₂ : (toTM keep).step
        (cfgAt (word u n) (some .skipBit) (2 * i + 2) (tapeOfList []) 0 []) =
        cfgAt (word u n) (some .skip) (2 * (i + 1) + 1) (tapeOfList []) 0 [] := by
      rw [step_cfgAt, min_eq_left (by omega), h₂]
      simp only [tr, moveTo, moveInputPosNat_one (by omega : 2 * i + 2 ≤ (word u n).length),
        SignType.coe_zero, add_zero, List.append_nil, Option.toList_none]
      exact cfgAt_congr (by omega) rfl
    refine ((Seg.single (cfgAt_mem_cells (by omega) (by omega)) s₁
      (cfgAt_mem_cells (by omega) (by omega))).trans
      ((Seg.single (cfgAt_mem_cells (by omega) (by omega)) s₂
        (cfgAt_mem_cells (by omega) (by omega))).trans
        (ih (i := i + 1) (by omega) (by omega)))).mono (by omega)

/-- The end of the frame: the input head moves to the count. -/
private lemma step_endFrame :
    (toTM keep).step (cfgAt (word u n) (some .skip) (2 * u.length + 1) (tapeOfList []) 0 []) =
      cfgAt (word u n) (some .copy) (2 * u.length + 2 + 0) (tapeOfList (List.replicate 0 true))
        ((0 : ℕ) : ℤ) [] := by
  have hn := length_word u n
  rw [step_cfgAt, min_eq_left (by omega), inputAt_frame_append_length]
  simp only [tr, moveTo, moveInputPosNat_one (by omega : 2 * u.length + 1 ≤ (word u n).length),
    SignType.coe_zero, add_zero, List.append_nil, Option.toList_none, List.replicate_zero]
  exact cfgAt_congr (by omega) (by simp)

/-- Copying the count to the work tape. -/
private lemma seg_copy {i : ℕ} (hi : i ≤ n) :
    Seg keep (cells n)
      (cfgAt (word u n) (some .copy) (2 * u.length + 2 + i) (tapeOfList (List.replicate i true))
        i [])
      (cfgAt (word u n) (some .copy) (2 * u.length + 2 + n) (tapeOfList (List.replicate n true))
        n [])
      (n - i) := by
  obtain ⟨d, hd⟩ : ∃ d, n - i = d := ⟨_, rfl⟩
  have hn := length_word u n
  induction d generalizing i with
  | zero =>
    obtain rfl : i = n := by omega
    exact (Seg.refl (cfgAt_mem_cells (by omega) le_rfl)).mono (Nat.zero_le _)
  | succ d ih =>
    have hi' : i < n := by omega
    have hx : inputAt (word u n) (2 * u.length + 2 + i) = some true := by
      have := (getElem?_frame_append_length u (List.replicate n true) i).2
      rw [List.getElem?_replicate_of_lt hi'] at this
      simpa [inputAt, (by omega : 2 * u.length + 2 + i - 1 = 2 * u.length + 1 + i)] using this
    have ht : Function.update (tapeOfList (List.replicate i true)) (i : ℤ) (some true) =
        tapeOfList (List.replicate (i + 1) true) := by
      rw [List.replicate_succ', tapeOfList_append_single, List.length_replicate]
    have s : (toTM keep).step
        (cfgAt (word u n) (some .copy) (2 * u.length + 2 + i)
          (tapeOfList (List.replicate i true)) i []) =
        cfgAt (word u n) (some .copy) (2 * u.length + 2 + (i + 1))
          (tapeOfList (List.replicate (i + 1) true)) ((i + 1 : ℕ) : ℤ) [] := by
      rw [step_cfgAt, min_eq_left (by omega), hx]
      simp only [tr, moveInputPosNat_one (by omega : 2 * u.length + 2 + i ≤ (word u n).length),
        SignType.coe_one, List.append_nil, Option.toList_none, ht]
      exact cfgAt_congr (by omega) (by push_cast; rfl)
    exact ((Seg.single (cfgAt_mem_cells (by omega) (by omega)) s
      (cfgAt_mem_cells (by omega) (by omega))).trans (ih (i := i + 1) (by omega) (by omega))).mono
      (by omega)

/-- The end of the count: the work head moves onto the last copied `true`. -/
private lemma step_endCount :
    (toTM keep).step (cfgAt (word u n) (some .copy) (2 * u.length + 2 + n)
      (tapeOfList (List.replicate n true)) n []) =
      cfgAt (word u n) (some .rewind) (word u n).length (tapeOfList (List.replicate n true))
        ((n : ℤ) - 1) [] := by
  have hn := length_word u n
  have hx : inputAt (word u n) (2 * u.length + 2 + n) = none := by
    simp only [inputAt]
    split_ifs
    · rfl
    · exact List.getElem?_eq_none (by omega)
  rw [step_cfgAt, min_eq_left (by omega), hx]
  simp only [tr, moveInputPosNat_neg_one (by omega : 2 * u.length + 2 + n ≤ (word u n).length + 1),
    SignType.coe_neg_one, List.append_nil, Option.toList_none]
  exact cfgAt_congr (by omega) (by omega)

/-- Rewinding the input head. -/
private lemma seg_rewind {j : ℕ} (hj : j ≤ (word u n).length) :
    Seg keep (cells n)
      (cfgAt (word u n) (some .rewind) j (tapeOfList (List.replicate n true)) ((n : ℤ) - 1) [])
      (cfgAt (word u n) (some (.marker false)) (2 * 0 + 1) (tapeOfList (List.replicate n true))
        ((n : ℤ) - 1) [])
      (j + 1) := by
  induction j with
  | zero =>
    refine Seg.single (cfgAt_mem_cells (by omega) (by omega)) ?_
      (cfgAt_mem_cells (by omega) (by omega))
    have h0 : inputAt (word u n) 0 = none := by simp [inputAt]
    rw [step_cfgAt, min_eq_left (by omega), h0]
    simp only [tr, moveTo,
      moveInputPosNat_one (Nat.zero_le (word u n).length), SignType.coe_zero, add_zero,
      List.append_nil, Option.toList_none]
  | succ j ih =>
    have hx : inputAt (word u n) (j + 1) = some (word u n)[j] := by
      simp only [inputAt, Nat.add_sub_cancel, List.getElem?_eq_getElem (by omega : j <
        (word u n).length)]
      rfl
    have s : (toTM keep).step
        (cfgAt (word u n) (some .rewind) (j + 1) (tapeOfList (List.replicate n true))
          ((n : ℤ) - 1) []) =
        cfgAt (word u n) (some .rewind) j (tapeOfList (List.replicate n true))
          ((n : ℤ) - 1) [] := by
      rw [step_cfgAt, min_eq_left (by omega), hx]
      simp only [tr, moveTo, moveInputPosNat_neg_one (by omega : j + 1 ≤ (word u n).length + 1),
        SignType.coe_zero, add_zero, List.append_nil, Option.toList_none, Nat.add_sub_cancel]
    exact ((Seg.single (cfgAt_mem_cells (by omega) (by omega)) s
      (cfgAt_mem_cells (by omega) (by omega))).trans (ih (by omega))).mono (by omega)

/-- The work cell under the head holds `true` exactly while the count is positive. -/
private lemma tapeOfList_replicate_count {c : ℕ} (hc : c ≤ n) :
    tapeOfList (List.replicate n true) ((c : ℤ) - 1) = if 0 < c then some true else none := by
  rcases c with _ | c
  · exact rfl
  · rw [(by push_cast; omega : ((c + 1 : ℕ) : ℤ) - 1 = ((c : ℕ) : ℤ)), tapeOfList_ofNat,
      List.getElem?_replicate_of_lt (by omega)]
    simp

/-- Streaming the inner word `u`, from inner position `r` on, with remaining count `c`. -/
private lemma seg_stream (v : List Bool) (inBit : Bool) {r : ℕ} (hr : r ≤ u.length) {c : ℕ}
    (hc : c ≤ n) (o : List Bool) :
    ∃ h' : ℤ, -1 ≤ h' ∧ h' ≤ n ∧ Seg keep (cells n)
      (cfgAt (frame u ++ v) (some (.marker inBit)) (2 * r + 1)
        (tapeOfList (List.replicate n true)) ((c : ℤ) - 1) o)
      (cfgAt (frame u ++ v) none (2 * u.length + 1) (tapeOfList (List.replicate n true)) h'
        (o ++ stream keep inBit c (u.drop r)))
      (2 * (u.length - r) + 1) := by
  obtain ⟨d, hd⟩ : ∃ d, u.length - r = d := ⟨_, rfl⟩
  have hn := length_frame_append u v
  induction d generalizing r inBit c o with
  | zero =>
    obtain rfl : r = u.length := by omega
    refine ⟨(c : ℤ) - 1, by omega, by omega, ?_⟩
    rw [List.drop_length]
    refine (Seg.single (cfgAt_mem_cells (by omega) (by omega)) ?_
      (cfgAt_mem_cells (by omega) (by omega))).mono (by omega)
    rw [step_cfgAt, min_eq_left (by omega), inputAt_frame_append_length]
    simp only [tr, haltAction, moveInputPosNat_zero (by omega : 2 * u.length + 1 ≤
      (frame u ++ v).length + 1), SignType.coe_zero, add_zero, Option.toList_none, stream]
  | succ d ih =>
    have hr' : r < u.length := by omega
    obtain ⟨h₁, h₂⟩ := inputAt_frame_append u v hr'
    have s₁ : (toTM keep).step
        (cfgAt (frame u ++ v) (some (.marker inBit)) (2 * r + 1)
          (tapeOfList (List.replicate n true)) ((c : ℤ) - 1) o) =
        cfgAt (frame u ++ v) (some (.symbol inBit)) (2 * r + 2)
          (tapeOfList (List.replicate n true)) ((c : ℤ) - 1) o := by
      rw [step_cfgAt, min_eq_left (by omega), h₁]
      simp only [tr, moveTo, moveInputPosNat_one (by omega : 2 * r + 1 ≤ (frame u ++ v).length),
        SignType.coe_zero, add_zero, List.append_nil, Option.toList_none]
    have hcell := tapeOfList_replicate_count (n := n) hc
    have hsome : (tapeOfList (List.replicate n true) ((c : ℤ) - 1)).isSome = decide (0 < c) := by
      rw [hcell]
      split_ifs with h <;> simp [h]
    have hnext : nextCount inBit u[r] c ≤ n := by
      simp only [nextCount]
      split_ifs <;> omega
    have hhead : (c : ℤ) - 1 +
        ((if !inBit && !u[r] && (tapeOfList (List.replicate n true) ((c : ℤ) - 1)).isSome then -1
          else 0 : SignType) : ℤ) = ((nextCount inBit u[r] c : ℕ) : ℤ) - 1 := by
      rw [hsome]
      cases inBit <;> cases hb : u[r] <;> rcases Nat.eq_zero_or_pos c with h | h <;>
        simp [nextCount, h]
      omega
    have s₂ : (toTM keep).step
        (cfgAt (frame u ++ v) (some (.symbol inBit)) (2 * r + 2)
          (tapeOfList (List.replicate n true)) ((c : ℤ) - 1) o) =
        cfgAt (frame u ++ v) (some (.marker (nextKind inBit u[r]))) (2 * (r + 1) + 1)
          (tapeOfList (List.replicate n true)) (((nextCount inBit u[r] c : ℕ) : ℤ) - 1)
          (o ++ if emits keep c then [u[r]] else []) := by
      rw [step_cfgAt, min_eq_left (by omega), h₂]
      have ho : (if ((tapeOfList (List.replicate n true) ((c : ℤ) - 1)).isSome == keep) = true
          then some u[r] else none).toList = if emits keep c then [u[r]] else [] := by
        rw [hsome, emits]
        split_ifs <;> rfl
      simp only [tr, moveInputPosNat_one (by omega : 2 * r + 2 ≤ (frame u ++ v).length), hhead, ho]
      exact cfgAt_congr (by omega) rfl
    obtain ⟨h', hh₀, hh₁, hseg⟩ := ih (nextKind inBit u[r]) (r := r + 1) (by omega) hnext
      (o ++ if emits keep c then [u[r]] else []) (by omega)
    refine ⟨h', hh₀, hh₁, ?_⟩
    rw [List.drop_eq_getElem_cons hr', stream_cons, ← List.append_assoc]
    refine ((Seg.single (cfgAt_mem_cells (by omega) (by omega)) s₁
      (cfgAt_mem_cells (by omega) (by omega))).trans
      ((Seg.single (cfgAt_mem_cells (by omega) (by omega)) s₂
        (cfgAt_mem_cells (by omega) (by omega))).trans hseg)).mono (by omega)

/-- The complete run on `frame u ++ List.replicate n true`. -/
private lemma seg_run (u : List Bool) (n : ℕ) :
    ∃ h' : ℤ, -1 ≤ h' ∧ h' ≤ n ∧ Seg keep (cells n) ((toTM keep).initCfg (word u n))
      (cfgAt (word u n) none (2 * u.length + 1) (tapeOfList (List.replicate n true)) h'
        (stream keep false n u))
      (3 * (word u n).length + 2) := by
  have hn := length_word u n
  have hinit : (toTM keep).initCfg (word u n) =
      cfgAt (word u n) (some .skip) (2 * 0 + 1) (tapeOfList []) 0 [] := by
    refine Cfg.ext rfl (Fin.ext ?_) (funext fun _ => ?_) rfl rfl
    · simp [MultiTapeNTM.initCfg, Cfg.init, cfgAt]
    · simp [MultiTapeNTM.initCfg, Cfg.init, cfgAt, tapeOfList_nil]
  obtain ⟨h', hh₀, hh₁, hstream⟩ := seg_stream (keep := keep) (u := u) (n := n)
    (List.replicate n true) false (r := 0) (Nat.zero_le _) le_rfl []
  rw [List.drop_zero, List.nil_append] at hstream
  refine ⟨h', hh₀, hh₁, ?_⟩
  rw [hinit]
  refine ((seg_skip (Nat.zero_le _)).trans ((Seg.single (cfgAt_mem_cells (by omega) (by omega))
    step_endFrame (cfgAt_mem_cells (by omega) (by omega))).trans ((seg_copy (Nat.zero_le _)).trans
    ((Seg.single (cfgAt_mem_cells (by omega) (by omega)) step_endCount
      (cfgAt_mem_cells (by omega) (by omega))).trans
    ((seg_rewind le_rfl).trans hstream))))).mono ?_
  omega

/-- On `frame u ++ List.replicate n true`, `toTM keep` emits `stream keep false n u` within
`3 * (frame u ++ List.replicate n true).length + 2` steps, visiting the `n + 2` work-tape cells
`-1, …, n`. -/
public theorem computesInTimeAndSpace_toTM (keep : Bool) (u : List Bool) (n : ℕ) :
    (toTM keep).ComputesInTimeAndSpace (frame u ++ List.replicate n true) (stream keep false n u)
      (3 * (frame u ++ List.replicate n true).length + 2) (n + 2) := by
  obtain ⟨h', -, -, m, hm, hrun, hcells⟩ := seg_run (keep := keep) u n
  have hhalt : ((toTM keep).runFrom ((toTM keep).initCfg (word u n)) m).Halted := by
    rw [hrun]
    rfl
  refine ⟨⟨m, hhalt, by rw [hrun]; rfl⟩, runsInTime_of_halted ?_, runsInSpace_of_halted hhalt ?_⟩
  · rw [runFrom_eq_of_halt _ _ hm hhalt]
    exact hhalt
  · simp only [MultiTapeNTM.RunPath.space, Finset.univ_unique, Fin.default_eq_zero,
      Finset.sum_singleton]
    refine (spaceUsedByTape_le_card _ hcells).trans_eq ?_
    simp only [cells, Int.card_Icc]
    omega

/-! ### Encoded lists -/

variable {α : Type}

/-- **Streaming an encoded list** emits the encoded prefix (`keep = true`) or suffix
(`keep = false`) at the count. -/
public theorem stream_encList (keep : Bool) (enc : α ↪ List Bool) (l : List α) (c : ℕ) :
    stream keep false c (encList enc l) = encList enc (if keep then l.take c else l.drop c) := by
  induction l generalizing c with
  | nil => cases keep <;> simp [stream]
  | cons a l ih =>
    rw [encList_cons, stream_frame_append, ih]
    rcases c with _ | c <;> cases keep <;> simp [emits]

/-- **Taking (`keep = true`) or dropping (`keep = false`) a unary number of elements** of an
encoded list, by `toTM keep`, within `3 * (encPair (encList enc) encUnary p).length + 2` steps and
`p.2 + 2` work-tape cells. -/
public theorem computableInTimeAndSpace (keep : Bool) (enc : α ↪ List Bool) :
    ComputableInTimeAndSpace (fun p : List α × ℕ => if keep then p.1.take p.2 else p.1.drop p.2)
      (encPair (encList enc) encUnary) (encList enc)
      (fun p => 3 * (encPair (encList enc) encUnary p).length + 2) (fun p => p.2 + 2) :=
  ⟨1, State, inferInstance, toTM keep, fun p => by
    simpa only [encPair_apply, encUnary_apply, stream_encList] using
      computesInTimeAndSpace_toTM keep (encList enc p.1) p.2⟩

end TakeDropUnary

end Turing.MultiTapeTM


