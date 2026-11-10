-- Prove2me | Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_OccurrenceCounting
-- name    : QEC_Coding_ProbabilisticConstruction_Resampling_OccurrenceCounting
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-09T19:24:36.144975+00:00
-- url     : https://prove2.me/theorems/6f14c802-abad-41b1-aa86-8f0d0f2b63b0
-- title:
--   Occurrence Counting
-- statement:
--   Definitions and structural lemmas for Occurrence Counting, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/OccurrenceCounting.lean

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_TreeProbability
import Mathlib.Data.Fintype.Fin
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_occurrenceHistory_length
attribute [local simp] QEC.Coding.ProbabilisticConstruction.Resampling.occurrenceHistory_length


set_option autoImplicit false
namespace QEC.Coding.ProbabilisticConstruction.Resampling
open scoped BigOperators
variable {I V : Type*} [Fintype I] [LinearOrder I] [Fintype V] [DecidableEq V]
variable {X : V → Type*} [∀ v, MeasurableSpace (X v)]
variable (vars : I → Finset V) (bad : ∀ i, Set (∀ v : vars i, X v))
variable [∀ i, DecidablePred (· ∈ bad i)]
def occurrences (R : Table (X := X)) (T : ℕ) (i : I) : Finset ℕ :=
  (Finset.range T).filter (fun n => selected vars bad R n = some i)
def prefixCount (R : Table (X := X)) (T : ℕ) (i : I) : ℕ :=
  (occurrences vars bad R T i).card
noncomputable def occurrenceTree (R : Table (X := X)) (T : ℕ) (i : I)
    (n : occurrences vars bad R T i) : WitnessTree (supportGraph vars) (T + 1) i :=
  let hn := (Finset.mem_filter.mp n.property).2
  let L := occurrenceHistory vars bad R n.val i hn
  pathsToTree (supportGraph vars) (T + 1) i (historyWitness (supportGraph vars) i L)
    (historyWitness_proper (supportGraph vars) i L) (by
      intro p hp
      have hd := historyWitness_depth (supportGraph vars) i L p hp
      have hl : L.length = n.val := occurrenceHistory_length vars bad R n.val i hn
      have ht := Finset.mem_range.mp (Finset.mem_filter.mp n.property).1
      omega)
end QEC.Coding.ProbabilisticConstruction.Resampling


