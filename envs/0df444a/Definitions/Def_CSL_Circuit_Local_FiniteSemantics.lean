-- Prove2me | Definitions.Def_CSL_Circuit_Local_FiniteSemantics
-- name    : CSL_Circuit_Local_FiniteSemantics
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T12:34:04.271236+00:00
-- url     : https://prove2.me/theorems/32e1c22f-f65e-4877-9e06-92560a1253ff
-- title:
--   Coded sorting library: Circuit / Local / FiniteSemantics
-- statement:
--   Module `CodedSorting.Circuit.Local.FiniteSemantics` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   Meaning of the finite bit-mask XOR computation. A natural-number bit mask represents a linear form on input vectors over ZMod 2. Evaluating a symbolic row after an XOR gate gives the same result as applying that gate to the evaluated rows. This relates the finite computation to every input vector.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Circuit.Local.FiniteSemantics

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Circuit_Framework_CircuitProgram
import Definitions.Def_CSL_Circuit_Local_FiniteTypes
import Mathlib.Data.Nat.Bitwise

section SymbolicXor
/-! Meaning of the finite bit-mask XOR computation. A natural-number bit mask represents a linear form on input vectors over ZMod 2. Evaluating a symbolic row after an XOR gate gives the same result as applying that gate to the evaluated rows. This relates the finite computation to every input vector. 











-/

set_option autoImplicit false

namespace CSL.Construction.SymbolicXor

open CSL.Circuit CSL.CircuitProgram
open CSL.Construction.FiniteCertificate
open scoped BigOperators

variable {n : ℕ}

/-- Interpret a finite-support binary linear form on arbitrary payloads. -/
def rowValue (input : Fin n → Bit) (mask : Nat) : Bit :=
  ∑ i : Fin n, if mask.testBit i.val then input i else 0

@[simp] theorem rowValue_zero (input : Fin n → Bit) : rowValue input 0 = 0 := by
  simp [rowValue]

private theorem bit_add_self (a : Bit) : a + a = 0 :=
  (by decide : ∀ b : Bit, b + b = 0) a

/-- XOR of masks denotes addition of the corresponding linear forms. -/
theorem rowValue_xor (input : Fin n → Bit) (a b : Nat) :
    rowValue input (Nat.xor a b) = rowValue input a + rowValue input b := by
  unfold rowValue
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [Nat.xor, Nat.testBit_bitwise rfl]
  cases a.testBit i.val <;> cases b.testBit i.val <;> simp [bit_add_self]

@[simp] theorem rowValue_singleton (input : Fin n → Bit) (i : Fin n) :
    rowValue input (2 ^ i.val) = input i := by
  unfold rowValue
  have hentry (j : Fin n) :
      (if (2 ^ i.val).testBit j.val then input j else 0) =
        if j = i then input i else 0 := by
    by_cases h : j = i
    · subst j
      simp [Nat.testBit_two_pow]
    · have hv : i.val ≠ j.val := fun he => h (Fin.ext he.symm)
      simp [Nat.testBit_two_pow, h, hv]
  simp_rw [hentry]
  simp

/-- A list of XOR controls has its literal sum semantics. Repetition, if
present, is preserved here and cancels only through characteristic two. -/
theorem rowValue_foldl (input : Fin n → Bit) (state : Nat → Nat)
    (sources : List Nat) (start : Nat) :
    rowValue input (sources.foldl (fun a s => Nat.xor a (state s)) start) =
      sources.foldl (fun a s => a + rowValue input (state s)) (rowValue input start) := by
  induction sources generalizing start with
  | nil => rfl
  | cons s ss ih =>
    simp only [List.foldl_cons, ih, rowValue_xor]

theorem add_foldl_eq_sum (values : Nat → Bit) (sources : List Nat) (start : Bit) :
    sources.foldl (fun a s => a + values s) start = start + (sources.map values).sum := by
  induction sources generalizing start with
  | nil => simp
  | cons s ss ih => simp [List.foldl_cons, ih, add_assoc]

/-- The payload-array interpreter uses the exact gate list from the finite
certificate; reads use the pre-gate state, just as the symbolic checker does. -/
def stepValues (state : Array Bit) (g : Gate) : Array Bit :=
  state.set! g.destination
    (g.sources.foldl (fun a s => a + state[s]!) state[g.destination]!)

def runValues (program : Array Gate) (state : Array Bit) : Array Bit :=
  program.foldl stepValues state

theorem rowValue_array_get (input : Fin n → Bit) (state : Array Nat) (r : Nat) :
    (state.map (rowValue input))[r]! = rowValue input state[r]! := by
  by_cases h : r < state.size
  · have hmap : r < (state.map (rowValue input)).size := by simpa using h
    rw [getElem!_pos (state.map (rowValue input)) r hmap,
      getElem!_pos state r h, Array.getElem_map]
  · have hmap : ¬ r < (state.map (rowValue input)).size := by simpa using h
    rw [getElem!_neg (state.map (rowValue input)) r hmap, getElem!_neg state r h]
    change (0 : Bit) = rowValue input 0
    simp

/-- One symbolic step and one payload step commute with interpretation. -/
theorem stepValues_eq_rowValue (input : Fin n → Bit) (state : Array Nat) (g : Gate) :
    stepValues (state.map (rowValue input)) g =
      (stepCoefficients state g).map (rowValue input) := by
  simp only [stepValues, stepCoefficients, Array.set!_eq_setIfInBounds,
    Array.map_setIfInBounds]
  congr 1
  rw [rowValue_foldl]
  simp only [rowValue_array_get]

theorem foldl_values_eq_rowValue (input : Fin n → Bit)
    (program : List Gate) (state : Array Nat) :
    program.foldl stepValues (state.map (rowValue input)) =
      (program.foldl stepCoefficients state).map (rowValue input) := by
  induction program generalizing state with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons, stepValues_eq_rowValue, ih]

/-- All symbolic steps commute with interpretation, for arbitrary initial
linear forms and arbitrary payload values. -/
theorem runValues_eq_rowValue (input : Fin n → Bit)
    (program : Array Gate) (state : Array Nat) :
    runValues program (state.map (rowValue input)) =
      (program.foldl stepCoefficients state).map (rowValue input) := by
  unfold runValues
  rw [← Array.foldl_toList, ← Array.foldl_toList]
  exact foldl_values_eq_rowValue input program.toList state

/-! ## Connection to the existing `XorGate` interpreter -/

/-- Register values viewed as the fixed finite register type of the original
program-network interface. -/
def arrayState (state : Array Bit) : Fin n → Bit := fun r => state[r.val]!

def sourceRegisters (n : ℕ) (g : Gate) : Finset (Fin n) :=
  Finset.univ.filter (fun r => r.val ∈ g.sources)

/-- The gate has the same destination and controls as the finite certificate.
The frame field specifies a matrix label and does not change XOR semantics. -/
def compileGate (n : ℕ) (g : Gate) : XorGate (Fin n) where
  ports := Finset.univ.filter (fun r => r.val = g.destination ∨ r.val ∈ g.sources)
  targets := Finset.univ.filter (fun r => r.val = g.destination)
  controls _ := sourceRegisters n g
  targets_subset := by
    intro r hr
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
    exact Or.inl hr
  controls_subset := by
    intro r _ c hc
    simp only [sourceRegisters, Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
    exact Or.inr hc

theorem source_sum_eq (values : Nat → Bit) (g : Gate)
    (hbound : ∀ s ∈ g.sources, s < n) :
    (∑ s ∈ g.sources.toFinset, values s) =
      ∑ r ∈ sourceRegisters n g, values r.val := by
  classical
  refine Finset.sum_bij
    (fun s hs => (⟨s, hbound s (List.mem_toFinset.mp hs)⟩ : Fin n)) ?_ ?_ ?_ ?_
  · intro s hs
    simpa only [sourceRegisters, Finset.mem_filter, Finset.mem_univ, true_and]
      using List.mem_toFinset.mp hs
  · intro a _ b _ hab
    exact congrArg Fin.val hab
  · intro r hr
    refine ⟨r.val, ?_, ?_⟩
    · simpa only [sourceRegisters, Finset.mem_filter, Finset.mem_univ,
        true_and, List.mem_toFinset] using hr
    · rfl
  · intro s _
    rfl

@[simp] theorem stepValues_size (state : Array Bit) (g : Gate) :
    (stepValues state g).size = state.size := by
  simp [stepValues]

/-- For a well-formed gate, the array step is the existing `XorGate.eval` on
the finite register type. This includes every source port and control. -/
theorem stepValues_eq_eval (state : Array Bit) (g : Gate)
    (hsize : state.size = n) (hnodup : g.sources.Nodup)
    (hbound : ∀ s ∈ g.sources, s < n) :
    arrayState (n := n) (stepValues state g) =
      (compileGate n g).eval (arrayState state) := by
  have hsum :
      g.sources.foldl (fun a s => a + state[s]!) state[g.destination]! =
        state[g.destination]! + ∑ r ∈ sourceRegisters n g, state[r.val]! := by
    rw [add_foldl_eq_sum, ← List.sum_toFinset _ hnodup]
    rw [source_sum_eq (fun r => state[r]!) g hbound]
  funext r
  have hr : r.val < state.size := by simpa [hsize] using r.isLt
  have hr' : r.val < (stepValues state g).size := by simpa using hr
  change (stepValues state g)[r.val]! = _
  rw [getElem!_pos (stepValues state g) r.val hr']
  simp only [stepValues, Array.set!_eq_setIfInBounds]
  rw [Array.getElem_setIfInBounds hr, hsum]
  simp only [XorGate.eval, compileGate, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases heq : g.destination = r.val
  · simp [heq, arrayState]
  · simp [heq, Ne.symm heq, arrayState, getElem!_pos state r.val hr]

def compileProgram (n : ℕ) (program : Array Gate) : List (XorGate (Fin n)) :=
  program.toList.map (compileGate n)

theorem listValues_eq_runProgram (program : List Gate) (state : Array Bit)
    (hsize : state.size = n)
    (hnodup : ∀ g ∈ program, g.sources.Nodup)
    (hbound : ∀ g ∈ program, ∀ s ∈ g.sources, s < n) :
    arrayState (n := n) (program.foldl stepValues state) =
      runProgram (program.map (compileGate n)) (arrayState state) := by
  induction program generalizing state with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons, List.map_cons, runProgram]
    rw [ih (stepValues state g) (by simpa using hsize)
      (fun h hh => hnodup h (List.mem_cons_of_mem g hh))
      (fun h hh => hbound h (List.mem_cons_of_mem g hh))]
    rw [stepValues_eq_eval state g hsize
      (hnodup g (by simp)) (hbound g (by simp))]

/-- Exact link from the literal certificate array program to the original
functional interpreter used to construct the physical program network. -/
theorem runValues_eq_runProgram (program : Array Gate) (state : Array Bit)
    (hsize : state.size = n)
    (hnodup : ∀ g ∈ program.toList, g.sources.Nodup)
    (hbound : ∀ g ∈ program.toList, ∀ s ∈ g.sources, s < n) :
    arrayState (n := n) (runValues program state) =
      runProgram (compileProgram n program) (arrayState state) := by
  unfold runValues compileProgram
  rw [← Array.foldl_toList]
  exact listValues_eq_runProgram program.toList state hsize hnodup hbound


end CSL.Construction.SymbolicXor
end SymbolicXor

section FiniteSemantics
/-!
# Interpreting a local-word certificate

This module makes the finite replay equality and operand validity explicit
premises. It checks the remaining semantic conversion independently of the
large numerical certificate. Instantiation with the actual checked gate list
is a separate theorem. The scalar word omits nine temporary scatter copies;
its payload semantics is not a physical rank-budget proof.
-/

set_option autoImplicit false

namespace CSL.Construction.FiniteSemantics

open CSL.Circuit CSL.CircuitProgram
open CSL.Construction.FiniteCertificate CSL.Construction.SymbolicXor
open scoped BigOperators

/-- Keep range-array indexing symbolic instead of expanding 661 entries. -/
theorem map_range_get {α : Type*} [Inhabited α]
    (n : Nat) (f : Nat → α) (r : Fin n) :
    ((List.range n).toArray.map f)[r.val]! = f r.val := by
  have hr : r.val < ((List.range n).toArray.map f).size := by simpa using r.isLt
  rw [getElem!_pos ((List.range n).toArray.map f) r.val hr]
  simp

/-- This theorem applies the finite replay certificate to actual arbitrary
`ZMod 2` inputs. It is a semantic theorem for the literal array program. -/
theorem scalarValueReplay_of_replay (program : Array Gate)
    (hreplay : runCoefficients program = coefficientExpected)
    (input : Fin registerCount → Bit) :
    runValues program (coefficientStart.map (rowValue input)) =
      coefficientExpected.map (rowValue input) := by
  rw [runValues_eq_rowValue]
  change (runCoefficients program).map (rowValue input) = _
  rw [hreplay]

theorem initial_values (input : Fin registerCount → Bit) :
    arrayState (coefficientStart.map (rowValue input)) = input := by
  funext r
  unfold arrayState
  rw [rowValue_array_get]
  change rowValue input (((List.range registerCount).toArray.map (fun i => 2 ^ i))[r.val]!) = _
  rw [map_range_get]
  exact rowValue_singleton input r

/-- The checked local word, compiled to the existing `XorGate` type, has the
advertised output linear forms for every input, including dirty helpers. -/
theorem scalarProgramReplay_of_certificate (program : Array Gate)
    (hreplay : runCoefficients program = coefficientExpected)
    (hnodup : ∀ g ∈ program.toList, g.sources.Nodup)
    (hbound : ∀ g ∈ program.toList, ∀ s ∈ g.sources, s < registerCount)
    (input : Fin registerCount → Bit) :
    runProgram (compileProgram registerCount program) input =
      arrayState (coefficientExpected.map (rowValue input)) := by
  have hsize : (coefficientStart.map (rowValue input)).size = registerCount := by
    simp [coefficientStart]
  have h := runValues_eq_runProgram program (coefficientStart.map (rowValue input))
    hsize hnodup hbound
  rw [initial_values, scalarValueReplay_of_replay program hreplay] at h
  exact h.symm

theorem rowValue_hxor (input : Fin registerCount → Bit) (a b : Nat) :
    rowValue input (a ^^^ b) = rowValue input a + rowValue input b :=
  rowValue_xor input a b

/-- The matching source index for a target in the second block of ports.
The total definition also makes the output formula easy to read. -/
def previousPort (r : Fin registerCount) : Fin registerCount :=
  ⟨r.val - portCount, Nat.lt_of_le_of_lt (Nat.sub_le _ _) r.isLt⟩

def localOutput (input : Fin registerCount → Bit) (r : Fin registerCount) : Bit :=
  if portCount ≤ r.val ∧ r.val < 2 * portCount then
    input r + input (previousPort r)
  else input r

theorem coefficientExpected_values (input : Fin registerCount → Bit) :
    arrayState (coefficientExpected.map (rowValue input)) = localOutput input := by
  funext r
  unfold arrayState
  rw [rowValue_array_get]
  change rowValue input (((List.range registerCount).toArray.map
    (fun i => if portCount ≤ i && i < 2 * portCount then
      Nat.xor (2 ^ i) (2 ^ (i - portCount)) else 2 ^ i))[r.val]!) = _
  rw [map_range_get]
  have hself := rowValue_singleton input r
  have hprev := rowValue_singleton input (previousPort r)
  simp only [previousPort] at hprev
  by_cases hlo : portCount ≤ r.val <;>
    by_cases hhi : r.val < 2 * portCount <;>
    simp [localOutput, previousPort, hlo, hhi,
      rowValue_xor, rowValue_hxor, hself, hprev]

/-- Readable local correctness: the first 111 source values and all 439
helper values are unchanged; each of the next 111 values gains its source.
No helper-initialization assumption is made. -/
theorem localProgram_correct_of_certificate (program : Array Gate)
    (hreplay : runCoefficients program = coefficientExpected)
    (hnodup : ∀ g ∈ program.toList, g.sources.Nodup)
    (hbound : ∀ g ∈ program.toList, ∀ s ∈ g.sources, s < registerCount)
    (input : Fin registerCount → Bit) :
    runProgram (compileProgram registerCount program) input = localOutput input := by
  rw [scalarProgramReplay_of_certificate program hreplay hnodup hbound,
    coefficientExpected_values]


end CSL.Construction.FiniteSemantics
end FiniteSemantics


