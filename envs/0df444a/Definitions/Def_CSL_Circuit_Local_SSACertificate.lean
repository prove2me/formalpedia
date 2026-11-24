-- Prove2me | Definitions.Def_CSL_Circuit_Local_SSACertificate
-- name    : CSL_Circuit_Local_SSACertificate
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T12:20:49.039614+00:00
-- url     : https://prove2.me/theorems/dcfc9653-5c24-428e-b724-87e3f595dd6b
-- title:
--   Coded sorting library: Circuit / Local / SSACertificate
-- statement:
--   Module `CodedSorting.Circuit.Local.SSACertificate` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   An SSA certificate separates the small register-to-row index trace from the
--   large bit-mask values. Local row equations are ordinary kernel propositions;
--   the theorem below connects them to the existing coefficient interpreter.
--   Row index zero denotes zero, including every out-of-bounds array read.
--   This module supplies a generic consumer, not the concrete Construction certificate.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Circuit.Local.SSACertificate

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Circuit_Local_FiniteTypes
import Mathlib.Data.Array.Defs

/-!
An SSA certificate separates the small register-to-row index trace from the
large bit-mask values. Local row equations are ordinary kernel propositions;
the theorem below connects them to the existing coefficient interpreter.
Row index zero denotes zero, including every out-of-bounds array read.
This module supplies a generic consumer, not the concrete Construction certificate.
-/

set_option autoImplicit false

namespace CSL.Construction.SSACertificate

open CSL.Construction.FiniteCertificate

structure Step where
  gate : Gate
  next : Nat
  deriving Inhabited

def stepIds (ids : Array Nat) (e : Step) : Array Nat :=
  ids.set! e.gate.destination e.next

def ValidAt (rows : Nat → Nat) (ids : Array Nat) (e : Step) : Prop :=
  rows e.next = e.gate.sources.foldl
    (fun a s => Nat.xor a (rows ids[s]!)) (rows ids[e.gate.destination]!)

def ValidTrace (rows : Nat → Nat) : Array Nat → List Step → Prop
  | _, [] => True
  | ids, e :: es => ValidAt rows ids e ∧ ValidTrace rows (stepIds ids e) es

def runIds (es : List Step) (ids : Array Nat) : Array Nat :=
  es.foldl stepIds ids

theorem map_rows_get (rows : Nat → Nat) (hzero : rows 0 = 0)
    (ids : Array Nat) (r : Nat) :
    (ids.map rows)[r]! = rows ids[r]! := by
  by_cases h : r < ids.size
  · have hm : r < (ids.map rows).size := by simpa using h
    rw [getElem!_pos (ids.map rows) r hm, getElem!_pos ids r h,
      Array.getElem_map]
  · have hm : ¬ r < (ids.map rows).size := by simpa using h
    rw [getElem!_neg (ids.map rows) r hm, getElem!_neg ids r h]
    exact hzero.symm

theorem step_sound (rows : Nat → Nat) (hzero : rows 0 = 0)
    (ids : Array Nat) (e : Step) (hvalid : ValidAt rows ids e) :
    stepCoefficients (ids.map rows) e.gate = (stepIds ids e).map rows := by
  simp only [stepCoefficients, stepIds, Array.set!_eq_setIfInBounds,
    Array.map_setIfInBounds]
  congr 1
  simpa only [map_rows_get rows hzero] using hvalid.symm

theorem trace_sound (rows : Nat → Nat) (hzero : rows 0 = 0)
    (es : List Step) (ids : Array Nat) (hvalid : ValidTrace rows ids es) :
    (es.map Step.gate).foldl stepCoefficients (ids.map rows) =
      (runIds es ids).map rows := by
  induction es generalizing ids with
  | nil => rfl
  | cons e es ih =>
    obtain ⟨hhead, htail⟩ := hvalid
    simp only [List.map_cons, List.foldl_cons, runIds]
    rw [step_sound rows hzero ids e hhead]
    exact ih (stepIds ids e) htail

theorem validTrace_append (rows : Nat → Nat) (a b : List Step)
    (ids : Array Nat) :
    ValidTrace rows ids (a ++ b) ↔
      ValidTrace rows ids a ∧ ValidTrace rows (runIds a ids) b := by
  induction a generalizing ids with
  | nil => simp [ValidTrace, runIds]
  | cons e es ih =>
    simp only [List.cons_append, ValidTrace, ih, runIds, List.foldl_cons]
    exact and_assoc.symm

/-- Compose independently checked chunks at explicit small-index snapshots. -/
theorem validTrace_join (rows : Nat → Nat) (a b : List Step)
    (before middle : Array Nat)
    (ha : ValidTrace rows before a) (hend : runIds a before = middle)
    (hb : ValidTrace rows middle b) : ValidTrace rows before (a ++ b) := by
  apply (validTrace_append rows a b before).2
  exact ⟨ha, hend ▸ hb⟩

/-- A block may use a literal final index snapshot, avoiding expansion of the
entire earlier coefficient computation in later kernel proofs. -/
theorem checked_block (rows : Nat → Nat) (hzero : rows 0 = 0)
    (es : List Step) (before after : Array Nat)
    (hvalid : ValidTrace rows before es) (hend : runIds es before = after) :
    (es.map Step.gate).foldl stepCoefficients (before.map rows) = after.map rows := by
  rw [trace_sound rows hzero es before hvalid, hend]

/-- The final certificate consumer targets exactly the existing finite-word
replay proposition. Each premise remains an explicit proof obligation. -/
theorem runCoefficients_of_certificate (rows : Nat → Nat) (hzero : rows 0 = 0)
    (word : Array Gate) (es : List Step) (before after : Array Nat)
    (hprogram : word.toList = es.map Step.gate)
    (hstart : before.map rows = coefficientStart)
    (hvalid : ValidTrace rows before es) (hend : runIds es before = after)
    (hfinish : after.map rows = coefficientExpected) :
    runCoefficients word = coefficientExpected := by
  unfold runCoefficients
  rw [← Array.foldl_toList, hprogram, ← hstart,
    checked_block rows hzero es before after hvalid hend, hfinish]

end CSL.Construction.SSACertificate


