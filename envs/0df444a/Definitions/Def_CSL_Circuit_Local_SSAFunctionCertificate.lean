-- Prove2me | Definitions.Def_CSL_Circuit_Local_SSAFunctionCertificate
-- name    : CSL_Circuit_Local_SSAFunctionCertificate
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T12:32:05.472363+00:00
-- url     : https://prove2.me/theorems/f6ae8d85-71e8-4fb1-a086-5ae0af5751a9
-- title:
--   Coded sorting library: Circuit / Local / SSAFunctionCertificate
-- statement:
--   Module `CodedSorting.Circuit.Local.SSAFunctionCertificate` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   # Function-indexed SSA certificates
--
--   The register-to-row state is a function, avoiding repeated reduction of array
--   length/get!/set! operations while kernel-checking the concrete row equations.
--   The local row equations remain ordinary propositions checked by Lean.  No
--   concrete Construction replay certificate is asserted by this generic consumer.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Circuit.Local.SSAFunctionCertificate

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Circuit_Local_SSACertificate

/-!
# Function-indexed SSA certificates

The register-to-row state is a function, avoiding repeated reduction of array
length/get!/set! operations while kernel-checking the concrete row equations.
The local row equations remain ordinary propositions checked by Lean.  No
concrete Construction replay certificate is asserted by this generic consumer.
-/

set_option autoImplicit false

namespace CSL.Construction.SSAFunctionCertificate

open CSL.Construction.FiniteCertificate

abbrev Step := SSACertificate.Step

def stepIds (ids : Nat → Nat) (e : Step) : Nat → Nat :=
  fun r => if r = e.gate.destination then e.next else ids r

def stepFunction (state : Nat → Nat) (g : Gate) : Nat → Nat :=
  fun r => if r = g.destination then
    g.sources.foldl (fun a s => Nat.xor a (state s)) (state g.destination)
  else state r

def ValidAt (rows : Nat → Nat) (ids : Nat → Nat) (e : Step) : Prop :=
  rows e.next = e.gate.sources.foldl
    (fun a s => Nat.xor a (rows (ids s))) (rows (ids e.gate.destination))

def ValidTrace (rows : Nat → Nat) : (Nat → Nat) → List Step → Prop
  | _, [] => True
  | ids, e :: es => ValidAt rows ids e ∧ ValidTrace rows (stepIds ids e) es

def runIds (es : List Step) (ids : Nat → Nat) : Nat → Nat :=
  es.foldl stepIds ids

/-- Explicit instances keep typeclass search from unfolding the complete
trace just to discover its decidability. -/
instance validAtDecidable (rows ids : Nat → Nat) (e : Step) :
    Decidable (ValidAt rows ids e) :=
  inferInstanceAs (Decidable (rows e.next = e.gate.sources.foldl
    (fun a s => Nat.xor a (rows (ids s))) (rows (ids e.gate.destination))))

def traceDecidable (rows ids : Nat → Nat) (es : List Step) :
    Decidable (ValidTrace rows ids es) :=
  match es with
  | [] => isTrue True.intro
  | e :: es =>
      let _ := traceDecidable rows (stepIds ids e) es
      inferInstanceAs (Decidable (ValidAt rows ids e ∧ ValidTrace rows (stepIds ids e) es))

attribute [instance] traceDecidable

theorem step_sound (rows ids : Nat → Nat) (e : Step) (hvalid : ValidAt rows ids e) :
    stepFunction (fun r => rows (ids r)) e.gate =
      fun r => rows (stepIds ids e r) := by
  funext r
  by_cases h : r = e.gate.destination
  · simpa only [stepFunction, stepIds, if_pos h] using hvalid.symm
  · simp only [stepFunction, stepIds, if_neg h]

theorem trace_sound (rows : Nat → Nat) (es : List Step) (ids : Nat → Nat)
    (hvalid : ValidTrace rows ids es) :
    (es.map SSACertificate.Step.gate).foldl stepFunction (fun r => rows (ids r)) =
      fun r => rows (runIds es ids r) := by
  induction es generalizing ids with
  | nil => rfl
  | cons e es ih =>
      obtain ⟨hhead,htail⟩ := hvalid
      simp only [List.map_cons, List.foldl_cons, runIds]
      rw [step_sound rows ids e hhead]
      exact ih (stepIds ids e) htail

theorem validTrace_append (rows : Nat → Nat) (a b : List Step) (ids : Nat → Nat) :
    ValidTrace rows ids (a ++ b) ↔
      ValidTrace rows ids a ∧ ValidTrace rows (runIds a ids) b := by
  induction a generalizing ids with
  | nil => simp [ValidTrace, runIds]
  | cons e es ih =>
      simp only [List.cons_append, ValidTrace, ih, runIds, List.foldl_cons]
      exact and_assoc.symm

theorem validTrace_join (rows : Nat → Nat) (a b : List Step)
    (before middle : Nat → Nat)
    (ha : ValidTrace rows before a) (hend : runIds a before = middle)
    (hb : ValidTrace rows middle b) : ValidTrace rows before (a ++ b) := by
  apply (validTrace_append rows a b before).2
  exact ⟨ha, hend ▸ hb⟩

theorem checked_block (rows : Nat → Nat) (es : List Step) (before after : Nat → Nat)
    (hvalid : ValidTrace rows before es) (hend : runIds es before = after) :
    (es.map SSACertificate.Step.gate).foldl stepFunction (fun r => rows (before r)) =
      fun r => rows (after r) := by
  rw [trace_sound rows es before hvalid, hend]


/-- All operands read or written by the trace are actual registers. -/
def OperandsBound (n : Nat) : List Step → Prop
  | [] => True
  | e :: es => e.gate.destination < n ∧
      (∀ s ∈ e.gate.sources, s < n) ∧ OperandsBound n es

def operandsBoundDecidable (n : Nat) (es : List Step) :
    Decidable (OperandsBound n es) :=
  match es with
  | [] => isTrue True.intro
  | e :: es =>
      let _ := operandsBoundDecidable n es
      inferInstanceAs (Decidable (e.gate.destination < n ∧
        (∀ s ∈ e.gate.sources, s < n) ∧ OperandsBound n es))

attribute [instance] operandsBoundDecidable

theorem operandsBound_of_all (n : Nat) (es : List Step)
    (h : es.all (fun e => e.gate.destination < n &&
      e.gate.sources.all (fun s => s < n)) = true) : OperandsBound n es := by
  induction es with
  | nil => trivial
  | cons e es ih =>
      simp only [List.all_cons, Bool.and_eq_true] at h
      exact ⟨of_decide_eq_true h.1.1,
        fun s hs => of_decide_eq_true ((List.all_eq_true.mp h.1.2) s hs), ih h.2⟩

/-- The invariant only concerns valid array indices. No assumption about
out-of-bounds reads or the default value of an ID snapshot is required. -/
def Represents (rows ids : Nat → Nat) (state : Array Nat) : Prop :=
  ∀ r, r < state.size → state[r]! = rows (ids r)

private theorem foldl_reads (state : Array Nat) (values : Nat → Nat)
    (sources : List Nat) (hread : ∀ r, r < state.size → state[r]! = values r)
    (hbound : ∀ s ∈ sources, s < state.size) (start : Nat) :
    sources.foldl (fun a s => Nat.xor a state[s]!) start =
      sources.foldl (fun a s => Nat.xor a (values s)) start := by
  induction sources generalizing start with
  | nil => rfl
  | cons s ss ih =>
      simp only [List.foldl_cons]
      rw [hread s (hbound s (by simp))]
      exact ih (fun t ht => hbound t (by simp [ht])) _

@[simp] theorem stepCoefficients_size (state : Array Nat) (g : Gate) :
    (stepCoefficients state g).size = state.size := by
  simp [stepCoefficients]

private theorem step_array_agrees (state : Array Nat) (values : Nat → Nat)
    (g : Gate) (hread : ∀ r, r < state.size → state[r]! = values r)
    (hsrc : ∀ s ∈ g.sources, s < state.size) :
    ∀ r, r < (stepCoefficients state g).size →
      (stepCoefficients state g)[r]! = stepFunction values g r := by
  intro r hr
  have hr0 : r < state.size := by simpa using hr
  rw [getElem!_pos _ r hr]
  simp only [stepCoefficients, Array.set!_eq_setIfInBounds]
  rw [Array.getElem_setIfInBounds hr0]
  by_cases h : r = g.destination
  · subst r
    simp only [ite_true, stepFunction]
    rw [foldl_reads state values g.sources hread hsrc,
      hread g.destination hr0]
  · have h' : g.destination ≠ r := Ne.symm h
    simp only [if_neg h', stepFunction, if_neg h]
    rw [← getElem!_pos state r hr0]
    exact hread r hr0

theorem step_array_sound (rows ids : Nat → Nat) (state : Array Nat) (e : Step)
    (hstate : Represents rows ids state) (hvalid : ValidAt rows ids e)
    (hsrc : ∀ s ∈ e.gate.sources, s < state.size) :
    Represents rows (stepIds ids e) (stepCoefficients state e.gate) := by
  intro r hr
  rw [step_array_agrees state (fun r => rows (ids r)) e.gate hstate hsrc r hr]
  exact congrFun (step_sound rows ids e hvalid) r

@[simp] theorem array_trace_size (es : List Step) (state : Array Nat) :
    ((es.map SSACertificate.Step.gate).foldl stepCoefficients state).size =
      state.size := by
  induction es generalizing state with
  | nil => rfl
  | cons e es ih =>
      simp only [List.map_cons, List.foldl_cons, ih, stepCoefficients_size]

theorem trace_array_sound (rows : Nat → Nat) (es : List Step)
    (ids : Nat → Nat) (state : Array Nat)
    (hstate : Represents rows ids state) (hvalid : ValidTrace rows ids es)
    (hbound : OperandsBound state.size es) :
    Represents rows (runIds es ids)
      ((es.map SSACertificate.Step.gate).foldl stepCoefficients state) := by
  induction es generalizing ids state with
  | nil => exact hstate
  | cons e es ih =>
      obtain ⟨hv, hvs⟩ := hvalid
      obtain ⟨_, hsrc, hb⟩ := hbound
      simp only [List.map_cons, List.foldl_cons, runIds]
      exact ih (stepIds ids e) (stepCoefficients state e.gate)
        (step_array_sound rows ids state e hstate hv hsrc) hvs (by simpa using hb)

/-- Independently checked finite snapshots compose directly in the actual
array interpreter; equality of their values outside the register set is unused. -/
theorem checked_array_block_fin (rows : Nat → Nat) (es : List Step)
    (before after : Nat → Nat) (state : Array Nat) (n : Nat)
    (hsize : state.size = n) (hstate : Represents rows before state)
    (hvalid : ValidTrace rows before es) (hbound : OperandsBound n es)
    (hend : ∀ r : Fin n, runIds es before r.val = after r.val) :
    Represents rows after
      ((es.map SSACertificate.Step.gate).foldl stepCoefficients state) := by
  intro r hr
  have hr0 : r < state.size := by simpa using hr
  have hrn : r < n := hsize ▸ hr0
  rw [trace_array_sound rows es before state hstate hvalid
    (hsize ▸ hbound) r hr, hend ⟨r, hrn⟩]

/-- Convert a represented final snapshot into exact array equality. -/
theorem array_eq_of_represents (rows ids : Nat → Nat) (state expected : Array Nat)
    (hsize : state.size = expected.size) (hstate : Represents rows ids state)
    (hfinish : ∀ r : Fin expected.size, rows (ids r.val) = expected[r.val]!) :
    state = expected := by
  apply Array.ext hsize
  intro r hr he
  rw [← getElem!_pos state r hr, ← getElem!_pos expected r he,
    hstate r hr, hfinish ⟨r, he⟩]

/-- Exact bridge to the original finite-word replay proposition. This theorem
requires checked initial/final snapshots and does not assert a concrete trace. -/
theorem runCoefficients_of_certificate (rows : Nat → Nat) (word : Array Gate)
    (es : List Step) (before after : Nat → Nat)
    (hprogram : word.toList = es.map SSACertificate.Step.gate)
    (hstart : Represents rows before coefficientStart)
    (hvalid : ValidTrace rows before es)
    (hbound : OperandsBound registerCount es)
    (hend : ∀ r : Fin registerCount, runIds es before r.val = after r.val)
    (hfinish : ∀ r : Fin registerCount,
      rows (after r.val) = coefficientExpected[r.val]!) :
    runCoefficients word = coefficientExpected := by
  have hs : coefficientStart.size = registerCount := by simp [coefficientStart]
  have he : coefficientExpected.size = registerCount := by simp [coefficientExpected]
  unfold runCoefficients
  rw [← Array.foldl_toList, hprogram]
  apply array_eq_of_represents rows after
  · simp only [array_trace_size, hs, he]
  · exact checked_array_block_fin rows es before after coefficientStart registerCount
      hs hstart hvalid hbound hend
  · intro r
    exact hfinish ⟨r.val, he ▸ r.isLt⟩


/-- A named block theorem can be composed without expanding any concrete
coefficient array or the earlier trace. -/
def ArrayBlockSound (rows : Nat → Nat) (n : Nat) (before after : Nat → Nat)
    (es : List Step) : Prop :=
  ∀ state : Array Nat, state.size = n → Represents rows before state →
    Represents rows after ((es.map SSACertificate.Step.gate).foldl stepCoefficients state)

theorem arrayBlockSound_of_certificate (rows : Nat → Nat) (n : Nat)
    (before after : Nat → Nat) (es : List Step)
    (hvalid : ValidTrace rows before es) (hbound : OperandsBound n es)
    (hend : ∀ r : Fin n, runIds es before r.val = after r.val) :
    ArrayBlockSound rows n before after es := by
  intro state hsize hstate
  exact checked_array_block_fin rows es before after state n hsize hstate hvalid hbound hend

theorem sound_nil (rows : Nat → Nat) (n : Nat) (ids : Nat → Nat) :
    ArrayBlockSound rows n ids ids [] := by
  intro state _ hstate
  exact hstate

/-- Compose actual array executions at the shared literal ID snapshot. -/
theorem sound_append (rows : Nat → Nat) (n : Nat) (before middle after : Nat → Nat)
    (a b : List Step) (ha : ArrayBlockSound rows n before middle a)
    (hb : ArrayBlockSound rows n middle after b) :
    ArrayBlockSound rows n before after (a ++ b) := by
  intro state hsize hstate
  simp only [List.map_append, List.foldl_append]
  exact hb _ (by simpa only [array_trace_size] using hsize) (ha state hsize hstate)

/-- Final consumer for a sequence of independently checked, named blocks.
`hblocks` can be proved exclusively by `sound_append`; no full-trace numerical
replay is needed at this endpoint. -/
theorem runCoefficients_of_blocks (rows : Nat → Nat) (word : Array Gate)
    (es : List Step) (before after : Nat → Nat)
    (hprogram : word.toList = es.map SSACertificate.Step.gate)
    (hstart : Represents rows before coefficientStart)
    (hblocks : ArrayBlockSound rows registerCount before after es)
    (hfinish : ∀ r : Fin registerCount,
      rows (after r.val) = coefficientExpected[r.val]!) :
    runCoefficients word = coefficientExpected := by
  have hs : coefficientStart.size = registerCount := by simp [coefficientStart]
  have he : coefficientExpected.size = registerCount := by simp [coefficientExpected]
  unfold runCoefficients
  rw [← Array.foldl_toList, hprogram]
  apply array_eq_of_represents rows after
  · simp only [array_trace_size, hs, he]
  · exact hblocks coefficientStart hs hstart
  · intro r
    exact hfinish ⟨r.val, he ▸ r.isLt⟩

end CSL.Construction.SSAFunctionCertificate

#print axioms CSL.Construction.SSAFunctionCertificate.trace_sound

#print axioms CSL.Construction.SSAFunctionCertificate.runCoefficients_of_certificate

#print axioms CSL.Construction.SSAFunctionCertificate.runCoefficients_of_blocks


