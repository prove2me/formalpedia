-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Universal_Complexity
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Universal_Complexity
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:59:51.007231+00:00
-- url     : https://prove2.me/theorems/75496cdb-b299-4ea4-b1f7-1b315119c605
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Universal.Complexity — The cost of a step of the simulation
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Universal.Complexity` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   States, symbols and moves are encoded in unary (`Turing.MultiTapeTM.encUnary`), head positions on
--   the work tapes as integers (`Turing.MultiTapeTM.encInt`), the position of the input head in binary
--   (`Turing.MultiTapeTM.encNat`), and a structure as the framed tuple of its fields.
--
--   Reading, writing and moving on a zipper are computable in linear time and space
--   (`Turing.MultiTapeTM.ComputableInDegree` with degrees one). A step of
--   the simulation (`Turing.MultiTapeTM.Universal.step_inO`) takes space linear in the length `L` of
--   the encoded context (the description, the input and the configuration). Its time bound separates
--   the configuration length from description lookup and input scanning: for `K` work tapes, `E`
--   transitions, description length `D`, encoded input length `N`, input position `p` and binary
--   position length `P`, the bound is
--   `(K + E + 1) * (D + 1) * (L + 1) + (N + 1) * (P + 1) ^ 2`.
--   The first word in a transition comparison comes from the description, so its length is bounded
--   by `D`, even when the simulated configuration is large. The input scanner streams the encoded
--   list with a binary countdown, whose arithmetic is charged to `P`. The configuration is still
--   copied each round; this bound does not implement the buffered Hennie–Stearns simulation.
--
--   ### Main definitions
--
--   * `Turing.MultiTapeTM.Universal.eDesc`, `.eCfg`: the encodings of descriptions and configurations.
--   * `Turing.MultiTapeTM.Universal.Ctx`, `.WCtx`: the contexts of a step, with and without the input,
--     and their named parts (`Ctx.desc`, `Ctx.input`, `Ctx.cfg`, `WCtx.desc`, `WCtx.cfg`, `WCtx.sym`).
--   * `Turing.MultiTapeTM.Universal.stepTime`: the time bound of a step.
--
--   ### Main results
--
--   * `Turing.MultiTapeTM.Universal.step_inO`: a step is computable (`Turing.MultiTapeTM.ComputableInO`)
--     within the time `stepTime` and linear space.
--   * `Turing.MultiTapeTM.Universal.stepWith_inO`, `.applyTapes_inO`, `.reads_inO`, `.moveInput_inO`:
--     its parts.
--
--   **Contents.** The module is published as a whole: 71 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Universal_Complexity`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Universal/Complexity.lean

/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: vendored crei:crei/tidy-universal @7f7c0696 (unsubmitted)

public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_BigO
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_OCountedIteration
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Combinators_IterateWhile
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Universal_Basic
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Bool
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Universal_Input
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_Quantitative
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_EqualityPrimitives
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_OLoops
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_BigO_Lists

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Universal.Complexity` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# The cost of a step of the simulation

States, symbols and moves are encoded in unary (`Turing.MultiTapeTM.encUnary`), head positions on
the work tapes as integers (`Turing.MultiTapeTM.encInt`), the position of the input head in binary
(`Turing.MultiTapeTM.encNat`), and a structure as the framed tuple of its fields.

Reading, writing and moving on a zipper are computable in linear time and space
(`Turing.MultiTapeTM.ComputableInDegree` with degrees one). A step of
the simulation (`Turing.MultiTapeTM.Universal.step_inO`) takes space linear in the length `L` of
the encoded context (the description, the input and the configuration). Its time bound separates
the configuration length from description lookup and input scanning: for `K` work tapes, `E`
transitions, description length `D`, encoded input length `N`, input position `p` and binary
position length `P`, the bound is
`(K + E + 1) * (D + 1) * (L + 1) + (N + 1) * (P + 1) ^ 2`.
The first word in a transition comparison comes from the description, so its length is bounded
by `D`, even when the simulated configuration is large. The input scanner streams the encoded
list with a binary countdown, whose arithmetic is charged to `P`. The configuration is still
copied each round; this bound does not implement the buffered Hennie–Stearns simulation.

## Main definitions

* `Turing.MultiTapeTM.Universal.eDesc`, `.eCfg`: the encodings of descriptions and configurations.
* `Turing.MultiTapeTM.Universal.Ctx`, `.WCtx`: the contexts of a step, with and without the input,
  and their named parts (`Ctx.desc`, `Ctx.input`, `Ctx.cfg`, `WCtx.desc`, `WCtx.cfg`, `WCtx.sym`).
* `Turing.MultiTapeTM.Universal.stepTime`: the time bound of a step.

## Main results

* `Turing.MultiTapeTM.Universal.step_inO`: a step is computable (`Turing.MultiTapeTM.ComputableInO`)
  within the time `stepTime` and linear space.
* `Turing.MultiTapeTM.Universal.stepWith_inO`, `.applyTapes_inO`, `.reads_inO`, `.moveInput_inO`:
  its parts.
-/

namespace Turing.MultiTapeTM.Universal

/-! ### Encodings -/

/-- Symbols and blanks. -/
public abbrev eSym : Option ℕ ↪ List Bool := encOption encUnary

/-- Keys of transitions, as their fields. -/
@[expose] public def eKey : Key ↪ List Bool :=
  (⟨fun k => (k.state, k.input, k.work), fun ⟨_, _, _⟩ ⟨_, _, _⟩ h => by simp_all⟩ :
    Key ↪ _).trans (encPair encUnary (encPair eSym (encList eSym)))

/-- An action on a work tape. -/
public abbrev TapeAct := Option (Option ℕ) × SignType

/-- Actions on a work tape. -/
public abbrev eTA : Option (Option ℕ) × SignType ↪ List Bool := encPair (encOption eSym) encSign

/-- Actions, as their fields. -/
@[expose] public def eAct : Act ↪ List Bool :=
  (⟨fun a => (a.inputTape, a.workTapes, a.output, a.state),
    fun ⟨_, _, _, _⟩ ⟨_, _, _, _⟩ h => by simp_all⟩ : Act ↪ _).trans
    (encPair encSign (encPair (encList eTA) (encPair eSym eSym)))

/-- Descriptions, as their fields. -/
@[expose] public def eDesc : Desc ↪ List Bool :=
  (⟨fun d => (d.tapes, d.q₀, d.table), fun ⟨_, _, _⟩ ⟨_, _, _⟩ h => by simp_all⟩ :
    Desc ↪ _).trans (encPair encUnary (encPair encUnary (encList (encPair eKey eAct))))

/-- The fields of a work tape. -/
public abbrev eTapeFields : ℤ × List (Option ℕ) × List (Option ℕ) ↪ List Bool :=
  encPair encInt (encPair (encList eSym) (encList eSym))

/-- Work tapes, as their fields. -/
@[expose] public def eTape : Tape ↪ List Bool :=
  (⟨fun t => (t.head, t.left, t.right), fun ⟨_, _, _⟩ ⟨_, _, _⟩ h => by simp_all⟩ :
    Tape ↪ _).trans eTapeFields

/-- The fields of a configuration. -/
public abbrev eCfgFields : Option ℕ × ℕ × List Tape ↪ List Bool :=
  encPair eSym (encPair encNat (encList eTape))

/-- Configurations, as their fields. -/
@[expose] public def eCfg : SCfg ↪ List Bool :=
  (⟨fun c => (c.state, c.inputPos, c.workTapes), fun ⟨_, _, _⟩ ⟨_, _, _⟩ h => by simp_all⟩ :
    SCfg ↪ _).trans eCfgFields

@[simp] public lemma eKey_apply (k : Key) :
    eKey k = encPair encUnary (encPair eSym (encList eSym)) (k.state, k.input, k.work) := rfl
@[simp] public lemma eAct_apply (a : Act) :
    eAct a = encPair encSign (encPair (encList eTA) (encPair eSym eSym))
      (a.inputTape, a.workTapes, a.output, a.state) := rfl
@[simp] public lemma eDesc_apply (d : Desc) :
    eDesc d = encPair encUnary (encPair encUnary (encList (encPair eKey eAct)))
      (d.tapes, d.q₀, d.table) := rfl
@[simp] public lemma eTape_apply (t : Tape) : eTape t = eTapeFields (t.head, t.left, t.right) :=
  rfl
@[simp] public lemma eCfg_apply (c : SCfg) :
    eCfg c = eCfgFields (c.state, c.inputPos, c.workTapes) := rfl

/-- The state of a configuration, in linear time. -/
public lemma state_inO : ComputableInO SCfg.state eCfg eSym (fun c => (eCfg c).length)
    fun c => (eCfg c).length :=
  .of_linear (.of_unframe fun c => by simp [eCfg_apply])

/-! ### Reading, writing and moving on a work tape, in linear time -/

section Tape

open ComputableInDegree

lemma tapeFields_deg : ComputableInDegree (fun t : Tape => (t.head, t.left, t.right)) eTape
    eTapeFields 1 1 :=
  of_eq fun _ => rfl

@[local fun_prop]
lemma tapeMk_deg : ComputableInDegree
    (fun p : ℤ × List (Option ℕ) × List (Option ℕ) => Tape.mk p.1 p.2.1 p.2.2) eTapeFields eTape
    1 1 :=
  of_eq fun _ => rfl

@[local fun_prop]
lemma tapeHead_deg : ComputableInDegree Tape.head eTape encInt 1 1 :=
  tapeFields_deg.fst'

@[local fun_prop]
lemma tapeLeft_deg : ComputableInDegree Tape.left eTape (encList eSym) 1 1 :=
  tapeFields_deg.snd'.fst'

@[local fun_prop]
lemma tapeRight_deg : ComputableInDegree Tape.right eTape (encList eSym) 1 1 :=
  tapeFields_deg.snd'.snd'

/-- The symbol under the head. -/
@[local fun_prop]
public lemma read_deg : ComputableInDegree Tape.read eTape eSym 1 1 := by
  unfold Tape.read
  fun_prop (disch := lia)

/-- Writing under the head. -/
@[local fun_prop]
lemma write_deg : ComputableInDegree (fun p : Tape × Option ℕ => p.1.write p.2)
    (encPair eTape eSym) eTape 1 1 := by
  unfold Tape.write
  fun_prop (disch := lia)

/-- A right move. -/
@[local fun_prop]
public lemma movePos_deg :
    ComputableInDegree (fun t : Tape => t.move .pos) eTape eTape 1 1 := by
  simp only [Tape.move]
  fun_prop (disch := lia)

/-- A left move. -/
@[local fun_prop]
public lemma moveNeg_deg :
    ComputableInDegree (fun t : Tape => t.move .neg) eTape eTape 1 1 := by
  simp only [Tape.move]
  fun_prop (disch := lia)

/-- Moving the head. -/
@[local fun_prop]
lemma move_deg : ComputableInDegree (fun p : Tape × SignType => p.1.move p.2)
    (encPair eTape encSign) eTape 1 1 := by
  have ht := fst eTape encSign
  have hm := snd eTape encSign
  have hpos := (of_finite (encMid := encBool) fun m : SignType => decide (m = .pos)).comp hm
  have hneg := (of_finite (encMid := encBool) fun m : SignType => decide (m = .neg)).comp hm
  convert (hpos.ite ((movePos_deg.comp ht).restrict _)
    ((hneg.ite ((moveNeg_deg.comp ht).restrict _) (ht.restrict _)).restrict _)).mono
      (d' := 1) (e' := 1) using 1
  funext ⟨t, m⟩
  rcases m with _ | _ | _ <;> rfl

/-- Applying an action to a work tape: write, then move. -/
@[local fun_prop]
lemma apply_deg : ComputableInDegree (fun p : Tape × TapeAct =>
    p.1.apply p.2) (encPair eTape eTA) eTape 1 1 := by
  convert (show ComputableInDegree (fun p : Tape × TapeAct =>
    (if p.2.1.isSome then p.1.write (p.2.1.getD none) else p.1).move p.2.2)
    (encPair eTape eTA) eTape 1 1 by fun_prop (disch := first | apply le_refl | lia)) using 1
  funext ⟨t, w, m⟩
  cases w <;> rfl

/-! ### Applying actions to all work tapes -/

/-- One step of applying actions to the work tapes in order: the remaining actions, and the tapes
done so far. -/
@[expose] public def applyStep (s : List TapeAct × List Tape) (t : Tape) :
    List TapeAct × List Tape :=
  (s.1.tail, s.2 ++ [match s.1.head? with | none => t | some a => t.apply a])

lemma applyTapes_nil_right (ts : List Tape) : applyTapes ts [] = ts := by
  cases ts <;> rfl

lemma foldl_applyStep (ts : List Tape) (as : List TapeAct) (acc : List Tape) :
    ts.foldl applyStep (as, acc) = (as.drop ts.length, acc ++ applyTapes ts as) := by
  induction ts generalizing as acc with
  | nil => simp [applyTapes]
  | cons t ts ih =>
    rw [List.foldl_cons]
    cases as with
    | nil => simp [applyStep, ih, applyTapes, applyTapes_nil_right]
    | cons a as => simp [applyStep, ih, applyTapes]

lemma applyStep_deg : ComputableInDegree
    (fun q : (List TapeAct × List Tape) × Tape => applyStep q.1 q.2)
    (encPair (encPair (encList eTA) (encList eTape)) eTape)
    (encPair (encList eTA) (encList eTape)) 1 1 := by
  convert (show ComputableInDegree (fun q : (List TapeAct × List Tape) × Tape =>
    (q.1.1.tail, q.1.2 ++ [if q.1.1.isEmpty then q.2 else q.2.apply (q.1.1.headD (none, 0))]))
    (encPair (encPair (encList eTA) (encList eTape)) eTape)
    (encPair (encList eTA) (encList eTape)) 1 1 by
      fun_prop (disch := first | apply le_refl | lia)) using 1
  funext ⟨⟨as, acc⟩, t⟩
  cases as <;> rfl

end Tape

/-! ### Sizes -/

lemma length_eSym_headD_le (l : List (Option ℕ)) :
    (eSym (l.headD none)).length ≤ (encList eSym l).length := by
  cases l <;> simp; omega

lemma length_encList_eq_le (l : List (Option ℕ)) :
    2 * (eSym (l.headD none)).length + (encList eSym l.tail).length ≤
      (encList eSym l).length := by
  cases l <;> simp

/-- Applying an action at most doubles a work tape, up to the length of the action. -/
lemma length_eTape_apply (t : Tape) (a : Option (Option ℕ) × SignType) :
    (eTape (t.apply a)).length ≤ 2 * (eTape t).length + 2 * (eTA a).length + 8 := by
  obtain ⟨h, l, r⟩ := t
  obtain ⟨w, m⟩ := a
  have := length_encList_eq_le l
  have := length_encList_eq_le r
  have := length_encInt_add_one_le h
  have := length_encInt_sub_one_le h
  rcases w with _ | o <;> rcases m with _ | _ | _ <;>
    simp only [Tape.apply, Tape.move, Tape.write, Tape.read, Option.elim, eTape_apply,
      length_encPair, encList_cons, List.length_append, length_frame, encOption_some,
      List.length_cons, List.headD_cons, List.tail_cons] <;> omega

lemma four_le_length_eTape (t : Tape) : 4 ≤ (eTape t).length := by
  have : 1 ≤ (encInt t.head).length := by rw [length_encInt]; split_ifs <;> omega
  simp only [eTape_apply, length_encPair]
  omega

lemma length_applyTapes (ts : List Tape) (as : List TapeAct) :
    (encList eTape (applyTapes ts as)).length ≤
      4 * (encList eTape ts).length + 4 * (encList eTA as).length := by
  induction ts generalizing as with
  | nil => simp [applyTapes]
  | cons t ts ih =>
    cases as with
    | nil => simp [applyTapes]
    | cons a as =>
      have := ih as
      have := length_eTape_apply t a
      have := four_le_length_eTape t
      simp only [applyTapes, encList_cons, List.length_append, length_frame] at *
      omega

/-- The symbol under the head is no longer than the work tape. -/
lemma length_read_le (t : Tape) : (eSym t.read).length ≤ (eTape t).length := by
  have := length_eSym_headD_le t.right
  simp only [Tape.read, eTape_apply, length_encPair] at *
  omega

/-- The symbols under the heads are no longer than the work tapes. -/
lemma length_encList_map_read_le (ts : List Tape) :
    (encList eSym (ts.map Tape.read)).length ≤ (encList eTape ts).length := by
  induction ts with
  | nil => simp
  | cons t ts ih =>
    have := length_read_le t
    simp only [List.map_cons, encList_cons, List.length_append, length_frame] at *
    omega

/-! ### All work tapes -/

open ComputableInO

/-- Applying actions to the work tapes, within time the number of work tapes times the length of
the arguments, and linear space. -/
public theorem applyTapes_inO :
    ComputableInO (Function.uncurry applyTapes)
      (encPair (encList eTape) (encList eTA)) (encList eTape)
      (fun p => (p.1.length + 1) * ((encPair (encList eTape) (encList eTA) p).length + 1))
      fun p => (encPair (encList eTape) (encList eTA) p).length := by
  have hlen (p : List Tape × List TapeAct) (i : ℕ) :
      (encPair (encList eTA) (encList eTape) ((p.1.take i).foldl applyStep (p.2, []))).length ≤
        6 * (encPair (encList eTape) (encList eTA) p).length := by
    rw [foldl_applyStep]
    have h₁ := length_applyTapes (p.1.take i) p.2
    have h₂ := length_encList_take_le eTape p.1 i
    have h₃ := SizedListEncoding.length_drop_le (encA := eTA) (encL := encList eTA) p.2
      (p.1.take i).length
    simp only [length_encPair, List.nil_append] at h₁ h₂ h₃ ⊢
    omega
  have hfold := (ComputableInO.foldl (encL := encList eTape)
    (encB := encPair (encList eTA) (encList eTape))
    (fst (encList eTape) (encList eTA))
    ((snd (encList eTape) (encList eTA)).prod (const []))
    applyStep_deg.inO_one
    (R := fun p => 14 * (encPair (encList eTape) (encList eTA) p).length + 1)
    (Q := fun p => 14 * (encPair (encList eTape) (encList eTA) p).length + 1)
    (B := fun p => 6 * (encPair (encList eTape) (encList eTA) p).length)
    (fun p i hi => by
      have h₁ := hlen p i
      have h₂ := length_le_encList_of_mem eTape (List.getElem_mem hi)
      simp only [length_encPair] at h₁ h₂ ⊢
      omega)
    (fun p i hi => by
      have h₁ := hlen p i
      have h₂ := length_le_encList_of_mem eTape (List.getElem_mem hi)
      simp only [length_encPair] at h₁ h₂ ⊢
      omega)
    (fun p i hi => hlen p i))
  refine (((snd (encList eTA) (encList eTape)).comp_linear hfold).mono 32 (fun p => ?_)
    fun p => ?_).of_enc_eq fun p => ?_
  · simp only [length_encPair]
    nlinarith
  · simp only [length_encPair]
    omega
  · simp [foldl_applyStep, Function.uncurry]

/-- The symbols under the heads of the work tapes, within time the number of work tapes times
their length, and linear space. -/
public theorem reads_inO :
    ComputableInO (fun ts : List Tape => ts.map Tape.read) (encList eTape) (encList eSym)
      (fun ts => (ts.length + 1) * ((encList eTape ts).length + 1))
      fun ts => (encList eTape ts).length := by
  refine ((mapWith (encP := encUnit) (f := fun p : Unit × Tape => p.2.read)
    (read_deg.inO_one.comp_linear (snd encUnit eTape)) (const ())
    (of_linear (.of_eq fun _ => rfl))).mono 8 (fun ts => ?_) fun ts => ?_)
  all_goals
    have h₁ : (encList eSym (ts.map fun t => t.read)).length ≤ _ := length_encList_map_read_le ts
    have h₂ : listMax (fun t => (encPair encUnit eTape ((), t)).length) ts ≤
        (encList eTape ts).length + 1 :=
      listMax_le fun t ht => by
        have := length_le_encList_of_mem eTape ht
        simp only [length_encPair, encUnit_apply, List.length_nil]
        omega
    simp only [encUnit_apply, List.length_nil] at h₁ h₂ ⊢
  · nlinarith
  · omega

/-! ### The input head -/

/-- Moving the input head, charging binary arithmetic only to the encoded position length. -/
public theorem moveInput_inO :
    ComputableInO (fun (p, a, m) => moveInput p a m)
      (encPair encNat (encPair eSym encSign)) encNat
      (fun q => (encPair encNat (encPair eSym encSign) q).length +
        ((encNat q.1).length + 1) ^ 2)
      fun q => (encPair encNat (encPair eSym encSign) q).length + 1 := by
  have hp := fst encNat (encPair eSym encSign)
  have ha := (snd encNat (encPair eSym encSign)).fst'
  have hm := (snd encNat (encPair eSym encSign)).snd'
  have hsign (s : SignType) := (ComputableInDegree.of_finite (encIn := encSign)
    (encMid := encBool) fun m : SignType => decide (m = s)).inO_one.comp_linear hm
  have hright := (ComputableInDegree.of_finite (encIn := encPair encBool encBool)
    (encMid := encBool) fun b : Bool × Bool => b.1 || b.2).inO_one.comp_linear
      ((ComputableInO.natIsZero.comp_linear hp).prod
        ((ComputableInDegree.isSome encUnary).inO_one.comp_linear ha))
  refine (((hsign .zero).ite hp ((hsign .neg).ite (ComputableInO.natPred.comp hp)
    (hright.ite (ComputableInO.natSucc.comp hp) hp))).mono 8 (fun q => ?_)
    fun q => ?_).of_enc_eq fun ⟨p, a, m⟩ => ?_
  · have h₁ : (encNat q.1).length ≤ (encPair encNat (encPair eSym encSign) q).length := by
      rw [length_encPair]; omega
    simp only [Function.comp_apply]
    have : (encNat q.1).length + 1 ≤ ((encNat q.1).length + 1) ^ 2 :=
      Nat.le_self_pow two_ne_zero _
    split_ifs <;> omega
  · have h₁ : (encNat q.1).length ≤ (encPair encNat (encPair eSym encSign) q).length := by
      rw [length_encPair]; omega
    simp only [Function.comp_apply]
    split_ifs <;> omega
  · rcases m with _ | _ | _ <;> simp [moveInput]

/-! ### A step without the input -/

/-- The context of a step without the input: the description, the configuration and the symbol
under the input head. -/
public abbrev WCtx := (Desc × SCfg) × Option ℕ

/-- The encoding of contexts without the input. -/
public abbrev eWCtx : WCtx ↪ List Bool := encPair (encPair eDesc eCfg) eSym

/-- The description of a context without the input. -/
public abbrev WCtx.desc (c : WCtx) : Desc := c.1.1

/-- The configuration of a context without the input. -/
public abbrev WCtx.cfg (c : WCtx) : SCfg := c.1.2

/-- The symbol under the input head, in a context without the input. -/
public abbrev WCtx.sym (c : WCtx) : Option ℕ := c.2

/-- The key of the transition to take. -/
@[expose] public def wKey (c : WCtx) : Key :=
  ⟨c.cfg.state.getD 0, c.sym, c.cfg.workTapes.map Tape.read⟩

/-- The transition to take, if any. -/
@[expose] public def wFound (c : WCtx) : Option (Key × Act) :=
  c.desc.table.find? (·.1 = wKey c)

/-- The default transition, never taken. -/
@[expose] public def defaultEntry : Key × Act := (⟨0, none, []⟩, ⟨0, [], none, none⟩)

/-- The action of the transition to take. -/
@[expose] public def wAct (c : WCtx) : Act := ((wFound c).getD defaultEntry).2

public lemma stepWith_eq (c : WCtx) : stepWith c.desc c.cfg c.sym =
    if c.cfg.state.isSome then
      (if (wFound c).isSome then
        (⟨(wAct c).state, moveInput c.cfg.inputPos c.sym (wAct c).inputTape,
          applyTapes c.cfg.workTapes (wAct c).workTapes⟩, (wAct c).output)
        else (⟨none, c.cfg.inputPos, c.cfg.workTapes⟩, none))
    else (c.cfg, none) := by
  obtain ⟨⟨d, ⟨_ | q, ip, ts⟩⟩, a⟩ := c
  · rfl
  · simp only [stepWith, Option.isSome_some, ↓reduceIte]
    rw [show d.table.find? (·.1 = ⟨q, a, ts.map Tape.read⟩) = wFound ((d, ⟨some q, ip, ts⟩), a)
      from rfl]
    rcases h : wFound ((d, ⟨some q, ip, ts⟩), a) with _ | e
    · rfl
    · simp [wAct, h]

/-- A step without input lookup: tape passes and description comparisons are linear in context
length; only binary input-head arithmetic is quadratic in its own encoded length. -/
@[expose] public def wTime (c : WCtx) : ℕ :=
  (c.cfg.workTapes.length + c.desc.table.length + 1) * ((eDesc c.desc).length + 1) *
    ((eWCtx c).length + 1) + ((encNat c.cfg.inputPos).length + 1) ^ 2

section Lengths

variable (c : WCtx)

lemma length_eWCtx : (eWCtx c).length = 2 * (2 * (eDesc c.desc).length + 1 +
    (2 * (eSym c.cfg.state).length + 1 + (2 * (encNat c.cfg.inputPos).length + 1 +
      (encList eTape c.cfg.workTapes).length))) + 1 + (eSym c.sym).length := by
  simp only [eWCtx, eCfg_apply, length_encPair]

lemma length_wTable_le :
    (encList (encPair eKey eAct) c.desc.table).length ≤ (eWCtx c).length := by
  rw [length_eWCtx]; simp only [eDesc_apply, length_encPair]; omega

lemma length_le_wTime {A B k : ℕ}
    (hA : A ≤ c.cfg.workTapes.length + c.desc.table.length)
    (hB : B ≤ (eWCtx c).length) (hk : k ≤ (eDesc c.desc).length + 1) :
    (A + 1) * k * (B + 1) ≤ wTime c :=
  (Nat.mul_le_mul (Nat.mul_le_mul (by omega) hk) (by omega)).trans (Nat.le_add_right _ _)

/-- An entry of the table is no longer than the context. -/
lemma length_le_of_mem_table {e : Key × Act} (he : e ∈ c.desc.table) :
    (encPair eKey eAct e).length ≤ (eWCtx c).length :=
  (length_le_encList_of_mem (encPair eKey eAct) he).trans (length_wTable_le c)

/-- An entry of the table is no longer than the description. -/
lemma length_le_eDesc_of_mem_table {e : Key × Act} (he : e ∈ c.desc.table) :
    (encPair eKey eAct e).length ≤ (eDesc c.desc).length := by
  have := length_le_encList_of_mem (encPair eKey eAct) he
  simp only [eDesc_apply, length_encPair] at *
  omega

lemma length_wKey_le : (eKey (wKey c)).length ≤ 4 * (eWCtx c).length + 4 := by
  have h₂ := length_encList_map_read_le c.cfg.workTapes
  have h₃ : (c.cfg.state.getD 0) ≤ (eSym c.cfg.state).length := by cases c.cfg.state <;> simp
  rw [length_eWCtx]
  simp only [wKey, eKey_apply, length_encPair, encUnary_apply, List.length_replicate]
  omega

lemma length_wFound_le :
    (encOption (encPair eKey eAct) (wFound c)).length ≤ (eWCtx c).length + 1 :=
  (length_encOption_find?_le _ _ _).trans (Nat.add_le_add_right (length_wTable_le c) 1)

lemma length_wAct_le : (eAct (wAct c)).length ≤ (eWCtx c).length + 6 := by
  have := length_wFound_le c
  unfold wAct
  generalize wFound c = o at *
  rcases o with _ | e
  · simp [defaultEntry, encSign]
  · have := length_le_encPair_right eKey eAct e
    simp only [Option.getD_some, encOption_some, List.length_cons] at *
    omega

end Lengths

/-- A part of a step within the time `wTime` and linear space. -/
abbrev WPart {β : Type} (f : WCtx → β) (enc : β ↪ List Bool) : Prop :=
  ComputableInO f eWCtx enc wTime fun c => (eWCtx c).length

lemma le_wTime (c : WCtx) : (eWCtx c).length + 1 ≤ wTime c :=
  by simpa using length_le_wTime c (A := 0) (Nat.zero_le _) le_rfl (k := 1) (by omega)

/-- One step of the simulation without the input, within the time `wTime` and linear space. -/
public theorem stepWith_inO :
    ComputableInO (fun c : WCtx => stepWith c.desc c.cfg c.sym) eWCtx (encPair eCfg eSym)
      wTime fun c => (eWCtx c).length := by
  -- the parts of the context
  have hd := (fst (encPair eDesc eCfg) eSym).fst'
  have hc := (fst (encPair eDesc eCfg) eSym).snd'
  have hf := hc.of_enc_eq (encOut := eCfgFields)
    (g := fun c : WCtx => (c.cfg.state, c.cfg.inputPos, c.cfg.workTapes)) fun _ => rfl
  have htable := (hd.of_enc_eq (encOut := encPair encUnary (encPair encUnary
    (encList (encPair eKey eAct)))) (g := fun c : WCtx => (c.desc.tapes, c.desc.q₀, c.desc.table))
    fun _ => rfl).snd'.snd'
  -- the key
  have hreads : WPart (fun c => c.cfg.workTapes.map Tape.read) (encList eSym) := by
    refine (reads_inO.comp hf.snd'.snd').mono 2 (fun c => ?_) fun c => ?_
    all_goals
      have h₁ := length_eWCtx c
      have h₂ := le_wTime c
      have h₃ := length_le_wTime c (A := c.cfg.workTapes.length) (by omega)
        (B := (encList eTape c.cfg.workTapes).length) (by omega) (k := 1) (by omega)
      simp only [eWCtx, Nat.mul_one] at *
      omega
  have hsym : WPart (fun c => c.sym) eSym :=
    (snd (encPair eDesc eCfg) eSym).mono 1 (fun c => by
      have := le_wTime c; dsimp only [eWCtx] at *; omega) fun c => by dsimp only [eWCtx]; omega
  have hkey : WPart wKey eKey := by
    refine ((((ComputableInDegree.getD (enc₁ := encUnary) 0).inO_one.comp_linear
      hf.fst').prod (hsym.prod hreads)).mono 4 (fun c => ?_) fun c => ?_).of_enc_eq
      fun _ => rfl
    all_goals
      have := le_wTime c
      dsimp only [eWCtx, Function.comp_apply] at *
      omega
  -- the transition
  have htest := (ComputableInO.eq eKey).comp ((snd eKey (encPair eKey eAct)).fst'.prod
    (fst eKey (encPair eKey eAct)))
  have hfound : WPart wFound (encOption (encPair eKey eAct)) := by
    refine (findWith htest hkey htable).mono 64 (fun c => ?_) fun c => ?_
    all_goals
      have hk := length_wKey_le c
      have ht := length_wTable_le c
      have hst := le_wTime c
      have hlinear : (eWCtx c).length + 1 ≤
          ((eDesc c.desc).length + 1) * ((eWCtx c).length + 1) := by nlinarith
      have hlen := length_le_length_encList (encPair eKey eAct) c.desc.table
    · have h₁ : listMax (fun e => (encPair eKey (encPair eKey eAct) (wKey c, e)).length +
          (encPair eKey (encPair eKey eAct) (wKey c, e)).length +
          ((eKey (e.1, wKey c).1).length + 1) *
            ((eKey (e.1, wKey c).1).length + (eKey (e.1, wKey c).2).length + 1))
          c.desc.table ≤ 32 * ((eDesc c.desc).length + 1) * ((eWCtx c).length + 1) :=
        listMax_le fun e he => by
          have h₁ := length_le_of_mem_table c he
          have h₂ := length_le_encPair_left eKey eAct e
          have hD := length_le_eDesc_of_mem_table c he
          have h₃ : ((eKey e.1).length + 1) * ((eKey e.1).length + (eKey (wKey c)).length + 1)
              ≤ ((eDesc c.desc).length + 1) * (5 * ((eWCtx c).length + 1)) :=
            Nat.mul_le_mul (by omega) (by omega)
          simp only [length_encPair] at *
          nlinarith
      have h₂ := length_le_wTime c (A := c.desc.table.length) (by omega)
        (B := (eWCtx c).length) le_rfl le_rfl
      have h₃ := Nat.mul_le_mul_left (c.desc.table.length + 1) (Nat.add_le_add
        (Nat.add_le_add (hk.trans (show 4 * (eWCtx c).length + 4 ≤
          4 * ((eDesc c.desc).length + 1) * ((eWCtx c).length + 1) by nlinarith))
          (ht.trans (show (eWCtx c).length ≤
            ((eDesc c.desc).length + 1) * ((eWCtx c).length + 1) by omega)))
          h₁)
      dsimp only [eWCtx, Function.comp_apply] at *
      nlinarith
    · have h₁ : listMax (fun e => (encPair eKey (encPair eKey eAct) (wKey c, e)).length +
          (encPair eKey (encPair eKey eAct) (wKey c, e)).length +
          (encPair eKey eKey (e.1, wKey c)).length) c.desc.table ≤
          32 * ((eWCtx c).length + 1) :=
        listMax_le fun e he => by
          have h₁ := length_le_of_mem_table c he
          have h₂ := length_le_encPair_left eKey eAct e
          simp only [length_encPair] at *
          omega
      dsimp only [eWCtx, Function.comp_apply] at *
      omega
  -- the action and the new configuration
  have hact := (((ComputableInDegree.getD (enc₁ := encPair eKey eAct)
    (enc := encOption (encPair eKey eAct)) defaultEntry).inO_one.comp_linear hfound).snd').of_enc_eq
    (encOut := encPair encSign (encPair (encList eTA) (encPair eSym eSym)))
    (g := fun c => ((wAct c).inputTape, (wAct c).workTapes, (wAct c).output,
      (wAct c).state)) fun _ => rfl
  have hmove : WPart (fun c => moveInput c.cfg.inputPos (wKey c).input (wAct c).inputTape)
      encNat := by
    have hinput := (hkey.of_enc_eq (encOut := encPair encUnary (encPair eSym (encList eSym)))
      (g := fun c => ((wKey c).state, (wKey c).input, (wKey c).work)) fun _ => rfl)
      |>.snd'.fst'
    refine (moveInput_inO.comp (hf.snd'.fst'.prod (hinput.prod hact.fst'))).mono 256
      (fun c => ?_) fun c => ?_
    all_goals
      have hk := length_wKey_le c
      have ha := length_wAct_le c
      have hst := le_wTime c
      have hp : (encPair encNat (encPair eSym encSign) (c.cfg.inputPos, (wKey c).input,
          (wAct c).inputTape)).length ≤ 8 * ((eWCtx c).length + 1) := by
        have := length_eWCtx c
        simp only [eKey_apply, eAct_apply, length_encPair] at *
        omega
      have h₂ : ((encNat c.cfg.inputPos).length + 1) ^ 2 ≤ wTime c :=
        Nat.le_add_left _ _
    · dsimp only [eWCtx, Function.comp_apply] at *
      omega
    · dsimp only [eWCtx, Function.comp_apply] at *
      omega
  have happ : WPart (fun c => applyTapes c.cfg.workTapes (wAct c).workTapes)
      (encList eTape) := by
    refine (applyTapes_inO.comp (hf.snd'.snd'.prod hact.snd'.fst')).mono 16 (fun c => ?_)
      fun c => ?_
    all_goals
      have ha := length_wAct_le c
      have hst := le_wTime c
      have hp : (encPair (encList eTape) (encList eTA) (c.cfg.workTapes,
          (wAct c).workTapes)).length ≤ 4 * ((eWCtx c).length + 1) := by
        have := length_eWCtx c
        simp only [eAct_apply, length_encPair] at *
        omega
      have h₂ := length_le_wTime c (A := c.cfg.workTapes.length) (by omega)
        (B := (eWCtx c).length) le_rfl (k := 1) (by omega)
      rw [Nat.mul_one] at h₂
    · have h₁ := Nat.mul_le_mul_left (c.cfg.workTapes.length + 1) (Nat.add_le_add_right hp 1)
      dsimp only [eWCtx, Function.comp_apply] at *
      nlinarith
    · dsimp only [eWCtx, Function.comp_apply] at *
      omega
  -- the result
  have hlive := (((hact.snd'.snd'.snd'.prod (hmove.prod happ)).of_enc_eq (encOut := eCfg)
    (g := fun c => (⟨(wAct c).state, moveInput c.cfg.inputPos (wKey c).input
      (wAct c).inputTape, applyTapes c.cfg.workTapes (wAct c).workTapes⟩ : SCfg))
    fun _ => rfl).prod hact.snd'.snd'.fst')
  have hhalt := ((((const (encMid := eSym) none).prod hf.snd').of_enc_eq (encOut := eCfg)
    (g := fun c : WCtx => (⟨none, c.cfg.inputPos, c.cfg.workTapes⟩ : SCfg)) fun _ => rfl).prod
      (const (encMid := eSym) none))
  have hidle := hc.prod (const (encMid := eSym) none)
  refine ((((ComputableInDegree.isSome encUnary).inO_one.comp_linear hf.fst').ite
    (((ComputableInDegree.isSome (encPair eKey eAct)).inO_one.comp_linear hfound).ite
      hlive hhalt) hidle).mono 16 (fun c => ?_) fun c => ?_).of_enc_eq fun c => ?_
  · have := le_wTime c
    dsimp only [eWCtx, Function.comp_apply] at *
    split_ifs <;> omega
  · dsimp only [eWCtx, Function.comp_apply] at *
    split_ifs <;> omega
  · rw [stepWith_eq]
    simp only [Function.comp_apply, wKey]

/-! ### A step -/

/-- The context of a step: the description, the input and the configuration. -/
public abbrev Ctx := (Desc × List ℕ) × SCfg

/-- The encoding of contexts. -/
public abbrev eCtx : Ctx ↪ List Bool := encPair (encPair eDesc (encList encUnary)) eCfg

/-- The description of a context. -/
public abbrev Ctx.desc (c : Ctx) : Desc := c.1.1

/-- The input of a context. -/
public abbrev Ctx.input (c : Ctx) : List ℕ := c.1.2

/-- The configuration of a context. -/
public abbrev Ctx.cfg (c : Ctx) : SCfg := c.2

/-- The step bound separates linear configuration passes from a streaming input lookup with
binary countdown arithmetic. In particular, the whole configuration length is never squared. -/
@[expose] public def stepTime (c : Ctx) : ℕ :=
  (c.cfg.workTapes.length + c.desc.table.length + 1) * ((eDesc c.desc).length + 1) *
    ((eCtx c).length + 1) +
    ((encList encUnary c.input).length + 1) * ((encNat c.cfg.inputPos).length + 1) ^ 2

lemma le_stepTime_ctx (c : Ctx) : (eCtx c).length + 1 ≤ stepTime c :=
  (Nat.le_mul_of_pos_left _ (Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _))).trans
    (Nat.le_add_right _ _)

/-- One step of the simulation, on contexts, within the time `stepTime` and linear space: the
symbol under the input head, and the step without the input. -/
public theorem step_inO :
    ComputableInO (fun c : Ctx => step c.desc c.input c.cfg) eCtx (encPair eCfg eSym)
      stepTime fun c => (eCtx c).length := by
  have hd := (fst (encPair eDesc (encList encUnary)) eCfg).fst'
  have hx := (fst (encPair eDesc (encList encUnary)) eCfg).snd'
  have hc := snd (encPair eDesc (encList encUnary)) eCfg
  have hip := (hc.of_enc_eq (encOut := eCfgFields)
    (g := fun c : Ctx => (c.2.state, c.2.inputPos, c.2.workTapes)) fun _ => rfl).snd'.fst'
  refine ((stepWith_inO.comp
    ((hd.prod hc).prod (inputSymbol_stream_inO.comp (hx.prod hip)))).mono 32
    (fun c => ?_) fun c => ?_).of_enc_eq fun c => by rw [step_eq_stepWith]; rfl
  all_goals
    have h₁ : (eSym (inputSymbol c.1.2 c.2.inputPos)).length ≤
        (encList encUnary c.1.2).length + 1 := length_inputSymbol_le c.1.2 c.2.inputPos
    have h₂ : (encPair (encList encUnary) encNat (c.1.2, c.2.inputPos)).length ≤
        (eCtx c).length := by
      simp only [eCtx, eCfg_apply, length_encPair]; omega
    have h₃ : (eWCtx ((c.1.1, c.2), inputSymbol c.1.2 c.2.inputPos)).length + 1 ≤
        3 * ((eCtx c).length + 1) := by
      simp only [eWCtx, eCtx, length_encPair] at *; omega
    have h₄ := le_stepTime_ctx c
    simp only [Function.comp_apply]
  · have h₅ : wTime ((c.1.1, c.2), inputSymbol c.1.2 c.2.inputPos) ≤ 3 * stepTime c := by
      have hprod := Nat.mul_le_mul_left
        ((c.2.workTapes.length + c.1.1.table.length + 1) * ((eDesc c.1.1).length + 1)) h₃
      have hcounter : ((encNat c.2.inputPos).length + 1) ^ 2 ≤
          ((encList encUnary c.1.2).length + 1) * ((encNat c.2.inputPos).length + 1) ^ 2 :=
        Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
      dsimp only [wTime, stepTime]
      nlinarith
    have h₆ : ((encList encUnary c.1.2).length + 1) *
        ((encNat c.2.inputPos).length + 1) ^ 2 ≤ stepTime c := Nat.le_add_left _ _
    dsimp only [eCtx] at *
    omega
  · dsimp only [eCtx, eWCtx] at *
    omega

end Turing.MultiTapeTM.Universal


