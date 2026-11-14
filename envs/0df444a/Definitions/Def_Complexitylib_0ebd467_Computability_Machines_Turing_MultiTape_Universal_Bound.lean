-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Universal_Bound
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Universal_Bound
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T17:02:04.066234+00:00
-- url     : https://prove2.me/theorems/f344e18b-5713-4e74-bc4b-f8f7395bbed7
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Universal.Bound — The size of the simulated configurations
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Universal.Bound` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   After `j` steps, the configuration of the simulation is bounded in the length of the encoded
--   description, the length of the input and `j`: the state and all symbols on the work tapes and the
--   output are numbers from the description, the input head stays on the input, every head moves by at
--   most one cell per step, and every zipper grows by at most two cells per step.
--
--   ### Main definitions
--
--   * `Turing.MultiTapeTM.Universal.cfgBound`: the bound on the configurations.
--   * `Turing.MultiTapeTM.Universal.stepBound`: `Turing.MultiTapeTM.Universal.stepTime` at the largest
--     sizes the invariant allows.
--
--   ### Main results
--
--   * `Turing.MultiTapeTM.Universal.length_eCfg_iterate_le`: the size of the configuration after `j`
--     steps.
--   * `Turing.MultiTapeTM.Universal.stepTime_iterate_le`: the time of the step after `j` steps.
--
--   **Contents.** The module is published as a whole: 34 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Universal_Bound`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Universal/Bound.lean

/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: vendored crei:crei/tidy-universal @7f7c0696 (unsubmitted)

public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Universal_Complexity
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_BinarySizeFacts
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Universal.Bound` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# The size of the simulated configurations

After `j` steps, the configuration of the simulation is bounded in the length of the encoded
description, the length of the input and `j`: the state and all symbols on the work tapes and the
output are numbers from the description, the input head stays on the input, every head moves by at
most one cell per step, and every zipper grows by at most two cells per step.

## Main definitions

* `Turing.MultiTapeTM.Universal.cfgBound`: the bound on the configurations.
* `Turing.MultiTapeTM.Universal.stepBound`: `Turing.MultiTapeTM.Universal.stepTime` at the largest
  sizes the invariant allows.

## Main results

* `Turing.MultiTapeTM.Universal.length_eCfg_iterate_le`: the size of the configuration after `j`
  steps.
* `Turing.MultiTapeTM.Universal.stepTime_iterate_le`: the time of the step after `j` steps.
-/

namespace Turing.MultiTapeTM.Universal

/-! ### Numbers in the description -/

lemma getD_le_length (o : Option ℕ) : o.getD 0 ≤ (eSym o).length := by
  cases o <;> simp

public lemma length_eSym_le {o : Option ℕ} {b : ℕ} (h : o.getD 0 ≤ b) :
    (eSym o).length ≤ b + 1 := by
  cases o <;> simp_all

variable (d : Desc)

/-- The length of the encoded description, which bounds all numbers in it. -/
public abbrev descLen : ℕ := (eDesc d).length

lemma length_act_le' {e : Key × Act} (he : e ∈ d.table) : (eAct e.2).length ≤ descLen d := by
  have := length_le_encList_of_mem (encPair eKey eAct) he
  simp only [descLen, eDesc_apply, length_encPair] at this ⊢
  omega

lemma next_le {e : Key × Act} (he : e ∈ d.table) : e.2.state.getD 0 ≤ descLen d := by
  have := length_act_le' d he
  have := getD_le_length e.2.state
  simp only [eAct_apply, length_encPair] at *
  omega

lemma out_le {e : Key × Act} (he : e ∈ d.table) : e.2.output.getD 0 ≤ descLen d := by
  have := length_act_le' d he
  have := getD_le_length e.2.output
  simp only [eAct_apply, length_encPair] at *
  omega

lemma write_le {e : Key × Act} (he : e ∈ d.table) {ta : TapeAct} (hta : ta ∈ e.2.workTapes) :
    (ta.1.getD none).getD 0 ≤ descLen d := by
  have h₁ := length_act_le' d he
  have h₂ := length_le_encList_of_mem eTA hta
  have h₃ := getD_le_length (ta.1.getD none)
  have h₄ : (eSym (ta.1.getD none)).length ≤ (encOption eSym ta.1).length := by
    cases ta.1 <;> simp
  simp only [eAct_apply, length_encPair] at *
  omega

lemma q₀_le : d.q₀ ≤ descLen d := by
  simp only [descLen, eDesc_apply, length_encPair, encUnary_apply, List.length_replicate]; omega

lemma tapes_le : d.tapes ≤ descLen d := by
  simp only [descLen, eDesc_apply, length_encPair, encUnary_apply, List.length_replicate]; omega

lemma table_le : d.table.length ≤ descLen d := by
  have := length_le_length_encList (encPair eKey eAct) d.table
  simp only [descLen, eDesc_apply, length_encPair] at this ⊢
  omega

/-! ### The invariant -/

/-- A work tape after at most `j` steps, with symbols at most `D`: the head is within `[-j, j]` and
the zipper holds at most `2 * j` cells. -/
public structure TapeInv (D j : ℕ) (t : Tape) : Prop where
  head : t.head.natAbs ≤ j
  length : t.left.length + t.right.length ≤ 2 * j
  val : ∀ o ∈ t.left ++ t.right, o.getD 0 ≤ D

/-- A configuration after at most `j` steps, for a description of length `D` and an input of
length `X`. -/
public structure Inv (D X j : ℕ) (c : SCfg) : Prop where
  state : c.state.getD 0 ≤ D
  inputPos : c.inputPos ≤ X + 1
  tapes : c.workTapes.length ≤ D
  workTapes : ∀ t ∈ c.workTapes, TapeInv D j t

lemma TapeInv.mono {D j j' : ℕ} {t : Tape} (h : TapeInv D j t) (hj : j ≤ j') : TapeInv D j' t :=
  ⟨h.head.trans hj, h.length.trans (by omega), h.val⟩

lemma getD_headD_le {D : ℕ} {l : List (Option ℕ)} (h : ∀ o ∈ l, o.getD 0 ≤ D) :
    (l.headD none).getD 0 ≤ D := by
  cases l with
  | nil => simp
  | cons o l => exact h o (List.mem_cons_self ..)

lemma TapeInv.apply {D j : ℕ} {t : Tape} (h : TapeInv D j t) {a : TapeAct}
    (ha : (a.1.getD none).getD 0 ≤ D) : TapeInv D (j + 1) (t.apply a) := by
  obtain ⟨hh, hl, hv⟩ := h
  obtain ⟨w, m⟩ := a
  -- writing
  obtain ⟨hl', hv'⟩ : (w.elim t t.write).left.length + (w.elim t t.write).right.length ≤
      2 * j + 1 ∧ ∀ o ∈ (w.elim t t.write).left ++ (w.elim t t.write).right, o.getD 0 ≤ D := by
    rcases w with _ | o
    · exact ⟨by simp; omega, hv⟩
    · refine ⟨by simp only [Option.elim, Tape.write, List.length_cons, List.length_tail]; omega,
        fun o' ho' => ?_⟩
      simp only [Option.elim, Tape.write, List.mem_append, List.mem_cons] at ho'
      rcases ho' with ho' | rfl | ho'
      · exact hv o' (List.mem_append_left _ ho')
      · exact ha
      · exact hv o' (List.mem_append_right _ (List.mem_of_mem_tail ho'))
  have hhead : (w.elim t t.write).head = t.head := by cases w <;> rfl
  -- moving
  have hvl : ∀ o ∈ (w.elim t t.write).left, o.getD 0 ≤ D :=
    fun o ho => hv' o (List.mem_append_left _ ho)
  have hvr : ∀ o ∈ (w.elim t t.write).right, o.getD 0 ≤ D :=
    fun o ho => hv' o (List.mem_append_right _ ho)
  rcases m with _ | _ | _
  · exact ⟨by simp only [Tape.apply, Tape.move, hhead]; omega, by
      simp only [Tape.apply, Tape.move]; omega, hv'⟩
  · refine ⟨by simp only [Tape.apply, Tape.move, hhead]; omega,
      by simp only [Tape.apply, Tape.move, List.length_tail, List.length_cons]; omega,
      fun o ho => ?_⟩
    simp only [Tape.apply, Tape.move, List.mem_append, List.mem_cons] at ho
    rcases ho with ho | rfl | ho
    · exact hvl o (List.mem_of_mem_tail ho)
    · exact getD_headD_le hvl
    · exact hvr o ho
  · refine ⟨by simp only [Tape.apply, Tape.move, hhead]; omega,
      by simp only [Tape.apply, Tape.move, List.length_tail, List.length_cons]; omega,
      fun o ho => ?_⟩
    simp only [Tape.apply, Tape.move, Tape.read, List.mem_append, List.mem_cons] at ho
    rcases ho with (rfl | ho) | ho
    · exact getD_headD_le hvr
    · exact hvl o ho
    · exact hvr o (List.mem_of_mem_tail ho)

public lemma length_applyTapes_eq (ts : List Tape) (as : List TapeAct) :
    (applyTapes ts as).length = ts.length := by
  induction ts generalizing as with
  | nil => rfl
  | cons t ts ih => cases as <;> simp [applyTapes, ih]

lemma mem_applyTapes {ts : List Tape} {as : List TapeAct} {t' : Tape}
    (h : t' ∈ applyTapes ts as) : ∃ t ∈ ts, t' = t ∨ ∃ a ∈ as, t' = t.apply a := by
  induction ts generalizing as with
  | nil => simp [applyTapes] at h
  | cons t ts ih => cases as <;> simp only [applyTapes, List.mem_cons] at h <;> grind

lemma Inv.mono {D X j j' : ℕ} {c : SCfg} (h : Inv D X j c) (hj : j ≤ j') : Inv D X j' c :=
  ⟨h.state, h.inputPos, h.tapes, fun t ht => (h.workTapes t ht).mono hj⟩

/-- The initial configuration satisfies the invariant. -/
lemma inv_init (x : List ℕ) : Inv (descLen d) x.length 0 (init d) := by
  refine ⟨q₀_le d, by simp [init], by simpa [init] using tapes_le d, fun t ht => ?_⟩
  obtain ⟨-, rfl⟩ := List.mem_replicate.mp ht
  exact ⟨by simp, by simp, by simp⟩

/-- Every step preserves the invariant, with one more step, and emits a number from the
description. -/
lemma Inv.step {x : List ℕ} {j : ℕ} {c : SCfg} (h : Inv (descLen d) x.length j c) :
    Inv (descLen d) x.length (j + 1) (step d x c).1 ∧ (step d x c).2.getD 0 ≤ descLen d := by
  rcases hs : c.state with _ | q
  · rw [show Universal.step d x c = (c, none) by simp [Universal.step, hs]]
    exact ⟨h.mono (Nat.le_succ _), by simp⟩
  rcases hf : d.table.find? (·.1 = c.key x q) with _ | ⟨k, a⟩
  · rw [show Universal.step d x c = ({ c with state := none }, none) by
      simp [Universal.step, hs, hf]]
    exact ⟨⟨by simp, h.inputPos, h.tapes, fun t ht => (h.workTapes t ht).mono (Nat.le_succ _)⟩,
      by simp⟩
  rw [show Universal.step d x c = (a.apply x c, a.output) by simp [Universal.step, hs, hf]]
  have he := List.mem_of_find?_eq_some hf
  refine ⟨⟨next_le d he, moveInput_le h.inputPos _, ?_, fun t' ht' => ?_⟩, out_le d he⟩
  · simpa [Act.apply, length_applyTapes_eq] using h.tapes
  · obtain ⟨t, ht, h' | ⟨ta, hta, h'⟩⟩ := mem_applyTapes ht'
    · exact h' ▸ (h.workTapes t ht).mono (Nat.le_succ _)
    · exact h' ▸ (h.workTapes t ht).apply (write_le d he hta)

/-- The configuration and the output after `j` steps. -/
public lemma inv_iterate (x : List ℕ) (j : ℕ) :
    Inv (descLen d) x.length j ((stepOut d x)^[j] (init d, [])).1 ∧
      ((stepOut d x)^[j] (init d, [])).2.length ≤ j ∧
      ∀ o ∈ ((stepOut d x)^[j] (init d, [])).2, o ≤ descLen d := by
  induction j with
  | zero => exact ⟨inv_init d x, by simp, by simp⟩
  | succ j ih =>
    obtain ⟨h₁, h₂, h₃⟩ := ih
    obtain ⟨h₄, h₅⟩ := h₁.step d
    rw [Function.iterate_succ_apply']
    refine ⟨h₄, ?_, fun o ho => ?_⟩
    · simp only [stepOut, List.length_append]
      cases (step d x _).2 <;> simp <;> omega
    · simp only [stepOut, List.mem_append, Option.mem_toList] at ho
      rcases ho with ho | ho
      · exact h₃ o ho
      · simpa [ho] using h₅

/-! ### The size bound -/

public lemma length_encInt_le (z : ℤ) : (encInt z).length ≤ z.natAbs + 1 := by
  rw [length_encInt]; split_ifs <;> omega

public lemma length_encNat_le (n : ℕ) : (encNat n).length ≤ n := by
  simpa [Nat.size_eq_bits_len] using Nat.size_le.mpr (Nat.lt_two_pow_self (n := n))

public lemma length_cells_le {D : ℕ} {l : List (Option ℕ)} (h : ∀ o ∈ l, o.getD 0 ≤ D) :
    (encList eSym l).length ≤ l.length * (2 * D + 3) :=
  (length_encList_le eSym l (b := D + 1) fun o ho => length_eSym_le (h o ho)).trans
    (le_of_eq (by ring))

/-- The bound on the encoded work tapes. -/
public abbrev tapeBound (D j : ℕ) : ℕ := 2 * (j + 1) + 2 + 3 * (2 * j) * (2 * D + 3)

lemma length_eTape_le {D j : ℕ} {t : Tape} (h : TapeInv D j t) :
    (eTape t).length ≤ tapeBound D j := by
  have h₁ := length_encInt_le t.head
  have h₂ := length_cells_le fun o ho => h.val o (List.mem_append_left t.right ho)
  have h₃ := length_cells_le fun o ho => h.val o (List.mem_append_right t.left ho)
  have h₄ := Nat.mul_le_mul_right (2 * D + 3) h.length
  have := h.head
  simp only [eTape_apply, length_encPair, tapeBound]
  nlinarith

/-- The bound on the encoded configurations, after `j` steps. -/
public abbrev cfgBound (D X j : ℕ) : ℕ :=
  2 * (D + 1) + 1 + (2 * (X + 1) + 1 + D * (2 * tapeBound D j + 1))

lemma length_eCfg_le {D X j : ℕ} {c : SCfg} (h : Inv D X j c) :
    (eCfg c).length ≤ cfgBound D X j := by
  have h₁ := length_eSym_le h.state
  have h₂ := (length_encNat_le c.inputPos).trans h.inputPos
  have h₃ := (length_encList_le eTape c.workTapes (b := tapeBound D j) fun t ht =>
    length_eTape_le (h.workTapes t ht)).trans (Nat.mul_le_mul_right _ h.tapes)
  simp only [eCfg_apply, length_encPair, cfgBound]
  omega

/-- **The size of the simulated configurations** after `j` steps. -/
public theorem length_eCfg_iterate_le (x : List ℕ) (j : ℕ) :
    (eCfg ((stepOut d x)^[j] (init d, [])).1).length ≤ cfgBound (descLen d) x.length j :=
  length_eCfg_le (inv_iterate d x j).1

/-! ### The time of a step -/

/-- The bound on the context of a step after `j` steps, for a description of length `D` and an
input of encoded length `N`. -/
public abbrev ctxBound (D N j : ℕ) : ℕ := 2 * (2 * D + 1 + N) + 1 + cfgBound D N j

/-- The bound on the time of a step after `j` steps, for a description of length `D` and an input
of encoded length `N`: `Turing.MultiTapeTM.Universal.stepTime` at the largest sizes the invariant
allows. -/
@[expose] public def stepBound (D N j : ℕ) : ℕ :=
  (2 * D + 1) * (D + 1) * (ctxBound D N j + 1) +
    (N + 1) * ((encNat (N + 1)).length + 1) ^ 2

public lemma stepBound_mono {D N j D' N' j' : ℕ} (hD : D ≤ D') (hN : N ≤ N') (hj : j ≤ j') :
    stepBound D N j ≤ stepBound D' N' j' := by
  unfold stepBound ctxBound cfgBound tapeBound
  have hbits := ComputableTidilyInO.length_encNat_mono (Nat.add_le_add_right hN 1)
  gcongr

public lemma length_eCtx_le (x : List ℕ) {j : ℕ} {c : SCfg} (h : Inv (descLen d) x.length j c) :
    (eCtx ((d, x), c)).length ≤ ctxBound (descLen d) (encList encUnary x).length j := by
  have h₁ := length_eCfg_le h
  have h₂ : cfgBound (descLen d) x.length j ≤
      cfgBound (descLen d) (encList encUnary x).length j := by
    have := length_le_length_encList encUnary x
    unfold cfgBound
    omega
  simp only [eCtx, length_encPair, descLen, ctxBound] at h₁ h₂ ⊢
  omega

/-- **The time of a step** after `j` steps, in the length of the description, the length of the
encoded input and `j`. -/
public theorem stepTime_iterate_le (x : List ℕ) (j : ℕ) :
    stepTime ((d, x), ((stepOut d x)^[j] (init d, [])).1) ≤
      stepBound (descLen d) (encList encUnary x).length j := by
  have hinv := (inv_iterate d x j).1
  generalize ((stepOut d x)^[j] (init d, [])).1 = cfg at hinv ⊢
  have hX := length_le_length_encList encUnary x
  have hK := hinv.tapes
  have hE := table_le d
  have hp := hinv.inputPos
  have hL := length_eCtx_le d x hinv
  have hbits := ComputableTidilyInO.length_encNat_mono
    (show cfg.inputPos ≤ (encList encUnary x).length + 1 by omega)
  unfold stepTime stepBound
  dsimp only [Ctx.desc, Ctx.input, Ctx.cfg]
  exact Nat.add_le_add
    (Nat.mul_le_mul (Nat.mul_le_mul_right _ (by omega)) (by omega))
    (Nat.mul_le_mul (by omega) (by gcongr))

end Turing.MultiTapeTM.Universal


