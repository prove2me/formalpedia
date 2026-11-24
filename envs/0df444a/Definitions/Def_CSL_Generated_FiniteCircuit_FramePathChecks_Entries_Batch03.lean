-- Prove2me | Definitions.Def_CSL_Generated_FiniteCircuit_FramePathChecks_Entries_Batch03
-- name    : CSL_Generated_FiniteCircuit_FramePathChecks_Entries_Batch03
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T13:38:44.837922+00:00
-- url     : https://prove2.me/theorems/f9467776-3f4d-4097-9562-f7998c323bc5
-- title:
--   Coded sorting library: Generated / FiniteCircuit / FramePathChecks / Entries / Batch03
-- statement:
--   Module `CodedSorting.Generated.FiniteCircuit.FramePathChecks.Entries.Batch03` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   Generated physical-frame checks. Uncompiled until a build record exists.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Generated.FiniteCircuit.FramePathChecks.Entries.Batch03

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Generated_FiniteCircuit_FramePathChecks_FunctionBase

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def nestingProjection384 : Projection := ⟨4,6,#[3,1,0,0,0,0,-1,1,1,2,0,-1,0,-1,1,0,0,0,4,0,0,0,0,0,0,-1,0,3,0,-1,0,1,0,0,0,0,4,0,0,0,0,-1,0,-1,0,3,0,1,-1,1,0,0,0,0,3,1,1,0,0,1,0,1,1,2]⟩
theorem nestingLookup384 : projections[384]! = nestingProjection384 := by
  rw [projections_lookup]
  rfl
def nestingEntries384 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 1) else 0) else (if n < 6 then 0 else (if n < 7 then (-1) else 1))) else (if n < 12 then (if n < 10 then (if n < 9 then 1 else 2) else (if n < 11 then 0 else (-1))) else (if n < 14 then (if n < 13 then 0 else (-1)) else (if n < 15 then 1 else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 4 else 0)) else 0) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else (-1)) else (if n < 27 then 0 else 3)) else (if n < 30 then (if n < 29 then 0 else (-1)) else (if n < 31 then 0 else 1))))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 4 else 0) else 0)) else (if n < 44 then (if n < 42 then (if n < 41 then 0 else (-1)) else (if n < 43 then 0 else (-1))) else (if n < 46 then (if n < 45 then 0 else 3) else (if n < 47 then 0 else 1)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then (-1) else 1) else 0) else (if n < 54 then 0 else (if n < 55 then 3 else 1))) else (if n < 60 then (if n < 58 then (if n < 57 then 1 else 0) else (if n < 59 then 0 else 1)) else (if n < 62 then (if n < 61 then 0 else 1) else (if n < 63 then 1 else 2)))))) else 0
theorem nestingEntries_eq384 (n : Nat) :
    nestingProjection384.numerator[n]! = nestingEntries384 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries384, if_neg (by omega : ¬ n < 64)]

def nestingProjection385 : Projection := ⟨4,6,#[4,0,0,0,0,0,0,0,0,3,0,-1,0,-1,0,1,0,0,3,-1,-1,1,0,0,0,-1,-1,2,-1,0,0,1,0,0,-1,-1,3,1,0,0,0,-1,1,0,1,2,0,1,0,0,0,0,0,0,4,0,0,1,0,1,0,1,0,3]⟩
theorem nestingLookup385 : projections[385]! = nestingProjection385 := by
  rw [projections_lookup]
  rfl
def nestingEntries385 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 4 else 0) else 0) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 3) else (if n < 11 then 0 else (-1))) else (if n < 14 then (if n < 13 then 0 else (-1)) else (if n < 15 then 0 else 1)))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 3 else (-1))) else (if n < 22 then (if n < 21 then (-1) else 1) else 0)) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else (-1)) else (if n < 27 then (-1) else 2)) else (if n < 30 then (if n < 29 then (-1) else 0) else (if n < 31 then 0 else 1))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then 0 else (-1)) else (if n < 38 then (if n < 37 then 3 else 1) else 0)) else (if n < 44 then (if n < 42 then (if n < 41 then 0 else (-1)) else (if n < 43 then 1 else 0)) else (if n < 46 then (if n < 45 then 1 else 2) else (if n < 47 then 0 else 1)))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 0 else (if n < 55 then 4 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then 0 else 1) else (if n < 59 then 0 else 1)) else (if n < 62 then (if n < 61 then 0 else 1) else (if n < 63 then 0 else 3)))))) else 0
theorem nestingEntries_eq385 (n : Nat) :
    nestingProjection385.numerator[n]! = nestingEntries385 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries385, if_neg (by omega : ¬ n < 64)]

def nestingProjection386 : Projection := ⟨4,6,#[2,1,1,0,-1,0,0,1,1,3,0,0,1,-1,0,0,1,0,3,0,0,1,0,-1,0,0,0,4,0,0,0,0,-1,1,0,0,3,1,0,0,0,-1,1,0,1,2,0,1,0,0,0,0,0,0,4,0,1,0,-1,0,0,1,0,3]⟩
theorem nestingLookup386 : projections[386]! = nestingProjection386 := by
  rw [projections_lookup]
  rfl
def nestingEntries386 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 2 else 1) else (if n < 3 then 1 else 0)) else (if n < 6 then (if n < 5 then (-1) else 0) else (if n < 7 then 0 else 1))) else (if n < 12 then (if n < 10 then (if n < 9 then 1 else 3) else 0) else (if n < 14 then (if n < 13 then 1 else (-1)) else 0))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 1 else 0) else (if n < 19 then 3 else 0)) else (if n < 22 then (if n < 21 then 0 else 1) else (if n < 23 then 0 else (-1)))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 4)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then (-1) else 1) else 0) else (if n < 38 then (if n < 37 then 3 else 1) else 0)) else (if n < 44 then (if n < 42 then (if n < 41 then 0 else (-1)) else (if n < 43 then 1 else 0)) else (if n < 46 then (if n < 45 then 1 else 2) else (if n < 47 then 0 else 1)))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 0 else (if n < 55 then 4 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then 1 else 0) else (if n < 59 then (-1) else 0)) else (if n < 62 then (if n < 61 then 0 else 1) else (if n < 63 then 0 else 3)))))) else 0
theorem nestingEntries_eq386 (n : Nat) :
    nestingProjection386.numerator[n]! = nestingEntries386 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries386, if_neg (by omega : ¬ n < 64)]

def nestingProjection387 : Projection := ⟨4,6,#[3,1,0,0,-1,1,0,0,1,2,0,-1,0,-1,1,0,0,0,4,0,0,0,0,0,0,-1,0,3,-1,0,1,0,-1,0,0,-1,2,1,1,0,1,-1,0,0,1,3,0,0,0,1,0,1,1,0,3,0,0,0,0,0,0,0,0,4]⟩
theorem nestingLookup387 : projections[387]! = nestingProjection387 := by
  rw [projections_lookup]
  rfl
def nestingEntries387 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 1) else 0) else (if n < 6 then (if n < 5 then (-1) else 1) else 0)) else (if n < 12 then (if n < 10 then (if n < 9 then 1 else 2) else (if n < 11 then 0 else (-1))) else (if n < 14 then (if n < 13 then 0 else (-1)) else (if n < 15 then 1 else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 4 else 0)) else 0) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else (-1)) else (if n < 27 then 0 else 3)) else (if n < 30 then (if n < 29 then (-1) else 0) else (if n < 31 then 1 else 0))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then (-1) else 0) else (if n < 35 then 0 else (-1))) else (if n < 38 then (if n < 37 then 2 else 1) else (if n < 39 then 1 else 0))) else (if n < 44 then (if n < 42 then (if n < 41 then 1 else (-1)) else 0) else (if n < 46 then (if n < 45 then 1 else 3) else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else 1) else (if n < 51 then 0 else 1)) else (if n < 54 then (if n < 53 then 1 else 0) else (if n < 55 then 3 else 0))) else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 4)))))) else 0
theorem nestingEntries_eq387 (n : Nat) :
    nestingProjection387.numerator[n]! = nestingEntries387 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries387, if_neg (by omega : ¬ n < 64)]

def nestingProjection388 : Projection := ⟨4,6,#[3,1,0,0,-1,1,0,0,1,3,0,0,1,-1,0,0,0,0,3,-1,0,0,-1,1,0,0,-1,3,0,0,-1,1,-1,1,0,0,3,1,0,0,1,-1,0,0,1,3,0,0,0,0,-1,-1,0,0,3,1,0,0,1,1,0,0,1,3]⟩
theorem nestingLookup388 : projections[388]! = nestingProjection388 := by
  rw [projections_lookup]
  rfl
def nestingEntries388 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 1) else 0) else (if n < 6 then (if n < 5 then (-1) else 1) else 0)) else (if n < 12 then (if n < 10 then (if n < 9 then 1 else 3) else 0) else (if n < 14 then (if n < 13 then 1 else (-1)) else 0))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 3 else (-1))) else (if n < 22 then 0 else (if n < 23 then (-1) else 1))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then (-1) else 3)) else (if n < 30 then 0 else (if n < 31 then (-1) else 1))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then (-1) else 1) else 0) else (if n < 38 then (if n < 37 then 3 else 1) else 0)) else (if n < 44 then (if n < 42 then (if n < 41 then 1 else (-1)) else 0) else (if n < 46 then (if n < 45 then 1 else 3) else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then 0 else (-1)) else (if n < 54 then 0 else (if n < 55 then 3 else 1))) else (if n < 60 then (if n < 58 then 0 else 1) else (if n < 62 then 0 else (if n < 63 then 1 else 3)))))) else 0
theorem nestingEntries_eq388 (n : Nat) :
    nestingProjection388.numerator[n]! = nestingEntries388 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries388, if_neg (by omega : ¬ n < 64)]

def nestingProjection389 : Projection := ⟨4,6,#[3,0,1,0,0,-1,0,1,0,3,0,-1,-1,0,1,0,1,0,3,0,0,1,0,-1,0,-1,0,3,-1,0,1,0,0,-1,0,-1,3,0,1,0,-1,0,1,0,0,3,0,1,0,1,0,1,1,0,3,0,1,0,-1,0,0,1,0,3]⟩
theorem nestingLookup389 : projections[389]! = nestingProjection389 := by
  rw [projections_lookup]
  rfl
def nestingEntries389 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 0) else (if n < 3 then 1 else 0)) else (if n < 6 then (if n < 5 then 0 else (-1)) else (if n < 7 then 0 else 1))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 3) else (if n < 11 then 0 else (-1))) else (if n < 14 then (if n < 13 then (-1) else 0) else (if n < 15 then 1 else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 1 else 0) else (if n < 19 then 3 else 0)) else (if n < 22 then (if n < 21 then 0 else 1) else (if n < 23 then 0 else (-1)))) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else (-1)) else (if n < 27 then 0 else 3)) else (if n < 30 then (if n < 29 then (-1) else 0) else (if n < 31 then 1 else 0))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 0 else (-1)) else (if n < 35 then 0 else (-1))) else (if n < 38 then (if n < 37 then 3 else 0) else (if n < 39 then 1 else 0))) else (if n < 44 then (if n < 42 then (if n < 41 then (-1) else 0) else (if n < 43 then 1 else 0)) else (if n < 46 then (if n < 45 then 0 else 3) else (if n < 47 then 0 else 1)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else 1) else (if n < 51 then 0 else 1)) else (if n < 54 then (if n < 53 then 1 else 0) else (if n < 55 then 3 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then 1 else 0) else (if n < 59 then (-1) else 0)) else (if n < 62 then (if n < 61 then 0 else 1) else (if n < 63 then 0 else 3)))))) else 0
theorem nestingEntries_eq389 (n : Nat) :
    nestingProjection389.numerator[n]! = nestingEntries389 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries389, if_neg (by omega : ¬ n < 64)]

def nestingProjection390 : Projection := ⟨4,6,#[3,0,1,0,0,-1,0,1,0,4,0,0,0,0,0,0,1,0,2,-1,0,1,-1,0,0,0,-1,3,0,0,-1,1,0,0,0,0,4,0,0,0,-1,0,1,0,0,3,0,1,0,0,-1,-1,0,0,3,1,1,0,0,1,0,1,1,2]⟩
theorem nestingLookup390 : projections[390]! = nestingProjection390 := by
  rw [projections_lookup]
  rfl
def nestingEntries390 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 0) else (if n < 3 then 1 else 0)) else (if n < 6 then (if n < 5 then 0 else (-1)) else (if n < 7 then 0 else 1))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 4) else 0) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 1 else 0) else (if n < 19 then 2 else (-1))) else (if n < 22 then (if n < 21 then 0 else 1) else (if n < 23 then (-1) else 0))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then (-1) else 3)) else (if n < 30 then 0 else (if n < 31 then (-1) else 1))))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 4 else 0) else 0)) else (if n < 44 then (if n < 42 then (if n < 41 then (-1) else 0) else (if n < 43 then 1 else 0)) else (if n < 46 then (if n < 45 then 0 else 3) else (if n < 47 then 0 else 1)))) else (if n < 56 then (if n < 52 then (if n < 50 then 0 else (-1)) else (if n < 54 then 0 else (if n < 55 then 3 else 1))) else (if n < 60 then (if n < 58 then (if n < 57 then 1 else 0) else (if n < 59 then 0 else 1)) else (if n < 62 then (if n < 61 then 0 else 1) else (if n < 63 then 1 else 2)))))) else 0
theorem nestingEntries_eq390 (n : Nat) :
    nestingProjection390.numerator[n]! = nestingEntries390 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries390, if_neg (by omega : ¬ n < 64)]

def nestingProjection391 : Projection := ⟨4,6,#[4,0,0,0,0,0,0,0,0,3,0,-1,-1,0,1,0,0,0,3,-1,0,0,-1,1,0,-1,-1,2,-1,0,0,1,0,-1,0,-1,3,0,1,0,0,0,0,0,0,4,0,0,0,1,-1,0,1,0,2,1,0,0,1,1,0,0,1,3]⟩
theorem nestingLookup391 : projections[391]! = nestingProjection391 := by
  rw [projections_lookup]
  rfl
def nestingEntries391 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 4 else 0) else 0) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 3) else (if n < 11 then 0 else (-1))) else (if n < 14 then (if n < 13 then (-1) else 0) else (if n < 15 then 1 else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 3 else (-1))) else (if n < 22 then 0 else (if n < 23 then (-1) else 1))) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else (-1)) else (if n < 27 then (-1) else 2)) else (if n < 30 then (if n < 29 then (-1) else 0) else (if n < 31 then 0 else 1))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 0 else (-1)) else (if n < 35 then 0 else (-1))) else (if n < 38 then (if n < 37 then 3 else 0) else (if n < 39 then 1 else 0))) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 4) else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else 1) else (if n < 51 then (-1) else 0)) else (if n < 54 then (if n < 53 then 1 else 0) else (if n < 55 then 2 else 1))) else (if n < 60 then (if n < 58 then 0 else 1) else (if n < 62 then 0 else (if n < 63 then 1 else 3)))))) else 0
theorem nestingEntries_eq391 (n : Nat) :
    nestingProjection391.numerator[n]! = nestingEntries391 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries391, if_neg (by omega : ¬ n < 64)]

def nestingProjection392 : Projection := ⟨4,6,#[4,0,0,0,0,0,0,0,0,3,1,0,0,-1,1,0,0,1,3,0,0,1,-1,0,0,0,0,4,0,0,0,0,0,0,0,0,3,1,1,-1,0,-1,1,0,1,2,0,1,0,1,-1,0,1,0,2,1,0,0,0,0,-1,1,1,3]⟩
theorem nestingLookup392 : projections[392]! = nestingProjection392 := by
  rw [projections_lookup]
  rfl
def nestingEntries392 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 4 else 0) else 0) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 3) else (if n < 11 then 1 else 0)) else (if n < 14 then (if n < 13 then 0 else (-1)) else (if n < 15 then 1 else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 0 else 1) else (if n < 19 then 3 else 0)) else (if n < 22 then (if n < 21 then 0 else 1) else (if n < 23 then (-1) else 0))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 4)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 3 else 1) else (if n < 39 then 1 else (-1)))) else (if n < 44 then (if n < 42 then (if n < 41 then 0 else (-1)) else (if n < 43 then 1 else 0)) else (if n < 46 then (if n < 45 then 1 else 2) else (if n < 47 then 0 else 1)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else 1) else (if n < 51 then (-1) else 0)) else (if n < 54 then (if n < 53 then 1 else 0) else (if n < 55 then 2 else 1))) else (if n < 60 then 0 else (if n < 62 then (if n < 61 then (-1) else 1) else (if n < 63 then 1 else 3)))))) else 0
theorem nestingEntries_eq392 (n : Nat) :
    nestingProjection392.numerator[n]! = nestingEntries392 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries392, if_neg (by omega : ¬ n < 64)]

def nestingProjection393 : Projection := ⟨4,6,#[3,1,1,1,0,0,0,0,1,2,0,-1,0,-1,1,0,1,0,2,-1,0,1,-1,0,1,-1,-1,3,0,0,0,0,0,0,0,0,4,0,0,0,0,-1,1,0,0,3,1,0,0,1,-1,0,0,1,3,0,0,0,0,0,0,0,0,4]⟩
theorem nestingLookup393 : projections[393]! = nestingProjection393 := by
  rw [projections_lookup]
  rfl
def nestingEntries393 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 1) else 1) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 1 else 2) else (if n < 11 then 0 else (-1))) else (if n < 14 then (if n < 13 then 0 else (-1)) else (if n < 15 then 1 else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 1 else 0) else (if n < 19 then 2 else (-1))) else (if n < 22 then (if n < 21 then 0 else 1) else (if n < 23 then (-1) else 0))) else (if n < 28 then (if n < 26 then (if n < 25 then 1 else (-1)) else (if n < 27 then (-1) else 3)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 4 else 0) else 0)) else (if n < 44 then (if n < 42 then (if n < 41 then 0 else (-1)) else (if n < 43 then 1 else 0)) else (if n < 46 then (if n < 45 then 0 else 3) else (if n < 47 then 1 else 0)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else 1) else (if n < 51 then (-1) else 0)) else (if n < 54 then (if n < 53 then 0 else 1) else (if n < 55 then 3 else 0))) else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 4)))))) else 0
theorem nestingEntries_eq393 (n : Nat) :
    nestingProjection393.numerator[n]! = nestingEntries393 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries393, if_neg (by omega : ¬ n < 64)]

def nestingProjection394 : Projection := ⟨4,6,#[3,0,0,-1,-1,0,0,1,0,3,1,0,0,-1,1,0,0,1,3,0,0,1,-1,0,-1,0,0,3,-1,0,0,1,-1,0,0,-1,3,0,0,1,0,-1,1,0,0,3,1,0,0,1,-1,0,0,1,3,0,1,0,0,1,1,0,0,3]⟩
theorem nestingLookup394 : projections[394]! = nestingProjection394 := by
  rw [projections_lookup]
  rfl
def nestingEntries394 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 0) else (if n < 3 then 0 else (-1))) else (if n < 6 then (if n < 5 then (-1) else 0) else (if n < 7 then 0 else 1))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 3) else (if n < 11 then 1 else 0)) else (if n < 14 then (if n < 13 then 0 else (-1)) else (if n < 15 then 1 else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 0 else 1) else (if n < 19 then 3 else 0)) else (if n < 22 then (if n < 21 then 0 else 1) else (if n < 23 then (-1) else 0))) else (if n < 28 then (if n < 26 then (if n < 25 then (-1) else 0) else (if n < 27 then 0 else 3)) else (if n < 30 then (if n < 29 then (-1) else 0) else (if n < 31 then 0 else 1))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then (-1) else 0) else (if n < 35 then 0 else (-1))) else (if n < 38 then (if n < 37 then 3 else 0) else (if n < 39 then 0 else 1))) else (if n < 44 then (if n < 42 then (if n < 41 then 0 else (-1)) else (if n < 43 then 1 else 0)) else (if n < 46 then (if n < 45 then 0 else 3) else (if n < 47 then 1 else 0)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else 1) else (if n < 51 then (-1) else 0)) else (if n < 54 then (if n < 53 then 0 else 1) else (if n < 55 then 3 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then 1 else 0) else (if n < 59 then 0 else 1)) else (if n < 62 then (if n < 61 then 1 else 0) else (if n < 63 then 0 else 3)))))) else 0
theorem nestingEntries_eq394 (n : Nat) :
    nestingProjection394.numerator[n]! = nestingEntries394 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries394, if_neg (by omega : ¬ n < 64)]

def nestingProjection395 : Projection := ⟨4,6,#[3,1,1,1,0,0,0,0,1,3,-1,-1,0,0,0,0,1,-1,3,-1,0,0,0,0,1,-1,-1,3,0,0,0,0,0,0,0,0,3,1,1,-1,0,0,0,0,1,3,-1,1,0,0,0,0,1,-1,3,1,0,0,0,0,-1,1,1,3]⟩
theorem nestingLookup395 : projections[395]! = nestingProjection395 := by
  rw [projections_lookup]
  rfl
def nestingEntries395 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 1) else 1) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 1 else 3) else (-1)) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 1 else (-1)) else (if n < 19 then 3 else (-1))) else 0) else (if n < 28 then (if n < 26 then (if n < 25 then 1 else (-1)) else (if n < 27 then (-1) else 3)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 3 else 1) else (if n < 39 then 1 else (-1)))) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 1 else 3) else (if n < 47 then (-1) else 1)))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then (if n < 53 then 1 else (-1)) else (if n < 55 then 3 else 1))) else (if n < 60 then 0 else (if n < 62 then (if n < 61 then (-1) else 1) else (if n < 63 then 1 else 3)))))) else 0
theorem nestingEntries_eq395 (n : Nat) :
    nestingProjection395.numerator[n]! = nestingEntries395 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries395, if_neg (by omega : ¬ n < 64)]

def nestingProjection396 : Projection := ⟨4,6,#[3,0,0,-1,-1,0,0,1,0,4,0,0,0,0,0,0,0,0,4,0,0,0,0,0,-1,0,0,3,-1,0,0,1,-1,0,0,-1,2,1,1,0,0,0,0,0,1,3,-1,1,0,0,0,0,1,-1,3,1,1,0,0,1,0,1,1,2]⟩
theorem nestingLookup396 : projections[396]! = nestingProjection396 := by
  rw [projections_lookup]
  rfl
def nestingEntries396 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 0) else (if n < 3 then 0 else (-1))) else (if n < 6 then (if n < 5 then (-1) else 0) else (if n < 7 then 0 else 1))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 4) else 0) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 4 else 0)) else 0) else (if n < 28 then (if n < 26 then (if n < 25 then (-1) else 0) else (if n < 27 then 0 else 3)) else (if n < 30 then (if n < 29 then (-1) else 0) else (if n < 31 then 0 else 1))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then (-1) else 0) else (if n < 35 then 0 else (-1))) else (if n < 38 then (if n < 37 then 2 else 1) else (if n < 39 then 1 else 0))) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 1 else 3) else (if n < 47 then (-1) else 1)))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then (if n < 53 then 1 else (-1)) else (if n < 55 then 3 else 1))) else (if n < 60 then (if n < 58 then (if n < 57 then 1 else 0) else (if n < 59 then 0 else 1)) else (if n < 62 then (if n < 61 then 0 else 1) else (if n < 63 then 1 else 2)))))) else 0
theorem nestingEntries_eq396 (n : Nat) :
    nestingProjection396.numerator[n]! = nestingEntries396 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries396, if_neg (by omega : ¬ n < 64)]

def nestingProjection397 : Projection := ⟨4,6,#[2,1,1,0,-1,0,0,1,1,3,-1,-1,0,0,0,0,1,-1,3,-1,0,0,0,0,0,-1,-1,2,-1,0,0,1,-1,0,0,-1,3,0,0,1,0,0,0,0,0,4,0,0,0,0,0,0,0,0,4,0,1,0,0,1,1,0,0,3]⟩
theorem nestingLookup397 : projections[397]! = nestingProjection397 := by
  rw [projections_lookup]
  rfl
def nestingEntries397 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 2 else 1) else (if n < 3 then 1 else 0)) else (if n < 6 then (if n < 5 then (-1) else 0) else (if n < 7 then 0 else 1))) else (if n < 12 then (if n < 10 then (if n < 9 then 1 else 3) else (-1)) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 1 else (-1)) else (if n < 19 then 3 else (-1))) else 0) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else (-1)) else (if n < 27 then (-1) else 2)) else (if n < 30 then (if n < 29 then (-1) else 0) else (if n < 31 then 0 else 1))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then (-1) else 0) else (if n < 35 then 0 else (-1))) else (if n < 38 then (if n < 37 then 3 else 0) else (if n < 39 then 0 else 1))) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 4) else 0))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 0 else (if n < 55 then 4 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then 1 else 0) else (if n < 59 then 0 else 1)) else (if n < 62 then (if n < 61 then 1 else 0) else (if n < 63 then 0 else 3)))))) else 0
theorem nestingEntries_eq397 (n : Nat) :
    nestingProjection397.numerator[n]! = nestingEntries397 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries397, if_neg (by omega : ¬ n < 64)]

def nestingProjection398 : Projection := ⟨4,6,#[2,1,1,0,1,0,0,-1,1,3,0,0,0,0,1,1,1,0,3,0,-1,0,-1,0,0,0,0,4,0,0,0,0,1,0,-1,0,3,0,-1,0,0,0,0,0,0,4,0,0,0,1,-1,0,-1,0,2,-1,-1,1,0,0,0,0,-1,3]⟩
theorem nestingLookup398 : projections[398]! = nestingProjection398 := by
  rw [projections_lookup]
  rfl
def nestingEntries398 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 2 else 1) else (if n < 3 then 1 else 0)) else (if n < 6 then (if n < 5 then 1 else 0) else (if n < 7 then 0 else (-1)))) else (if n < 12 then (if n < 10 then (if n < 9 then 1 else 3) else 0) else (if n < 14 then 0 else 1))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 1 else 0) else (if n < 19 then 3 else 0)) else (if n < 22 then (if n < 21 then (-1) else 0) else (if n < 23 then (-1) else 0))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 4)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 1 else 0) else (if n < 35 then (-1) else 0)) else (if n < 38 then (if n < 37 then 3 else 0) else (if n < 39 then (-1) else 0))) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 4) else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else 1) else (if n < 51 then (-1) else 0)) else (if n < 54 then (if n < 53 then (-1) else 0) else (if n < 55 then 2 else (-1)))) else (if n < 60 then (if n < 58 then (if n < 57 then (-1) else 1) else 0) else (if n < 62 then 0 else (if n < 63 then (-1) else 3)))))) else 0
theorem nestingEntries_eq398 (n : Nat) :
    nestingProjection398.numerator[n]! = nestingEntries398 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries398, if_neg (by omega : ¬ n < 64)]

def nestingProjection399 : Projection := ⟨4,6,#[3,0,1,0,1,0,1,0,0,4,0,0,0,0,0,0,1,0,2,1,0,-1,-1,0,0,0,1,3,-1,1,0,0,1,0,0,-1,2,1,-1,0,0,0,-1,1,1,3,0,0,1,0,-1,0,-1,0,3,0,0,0,0,0,0,0,0,4]⟩
theorem nestingLookup399 : projections[399]! = nestingProjection399 := by
  rw [projections_lookup]
  rfl
def nestingEntries399 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 0) else (if n < 3 then 1 else 0)) else (if n < 6 then (if n < 5 then 1 else 0) else (if n < 7 then 1 else 0))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 4) else 0) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 1 else 0) else (if n < 19 then 2 else 1)) else (if n < 22 then (if n < 21 then 0 else (-1)) else (if n < 23 then (-1) else 0))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 1 else 3)) else (if n < 30 then (if n < 29 then (-1) else 1) else 0)))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 1 else 0) else (if n < 35 then 0 else (-1))) else (if n < 38 then (if n < 37 then 2 else 1) else (if n < 39 then (-1) else 0))) else (if n < 44 then (if n < 42 then 0 else (if n < 43 then (-1) else 1)) else (if n < 46 then (if n < 45 then 1 else 3) else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 1 else 0) else (if n < 51 then (-1) else 0)) else (if n < 54 then (if n < 53 then (-1) else 0) else (if n < 55 then 3 else 0))) else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 4)))))) else 0
theorem nestingEntries_eq399 (n : Nat) :
    nestingProjection399.numerator[n]! = nestingEntries399 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries399, if_neg (by omega : ¬ n < 64)]

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def nestingProjection400 : Projection := ⟨4,6,#[3,0,1,0,1,0,1,0,0,3,0,1,0,1,0,-1,1,0,3,0,-1,0,-1,0,0,1,0,3,0,-1,0,1,1,0,-1,0,3,0,-1,0,0,1,0,-1,0,3,0,1,1,0,-1,0,-1,0,3,0,0,-1,0,1,0,1,0,3]⟩
theorem nestingLookup400 : projections[400]! = nestingProjection400 := by
  rw [projections_lookup]
  rfl
def nestingEntries400 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 0) else (if n < 3 then 1 else 0)) else (if n < 6 then (if n < 5 then 1 else 0) else (if n < 7 then 1 else 0))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 3) else (if n < 11 then 0 else 1)) else (if n < 14 then (if n < 13 then 0 else 1) else (if n < 15 then 0 else (-1))))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 1 else 0) else (if n < 19 then 3 else 0)) else (if n < 22 then (if n < 21 then (-1) else 0) else (if n < 23 then (-1) else 0))) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else 1) else (if n < 27 then 0 else 3)) else (if n < 30 then (if n < 29 then 0 else (-1)) else (if n < 31 then 0 else 1))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 1 else 0) else (if n < 35 then (-1) else 0)) else (if n < 38 then (if n < 37 then 3 else 0) else (if n < 39 then (-1) else 0))) else (if n < 44 then (if n < 42 then (if n < 41 then 0 else 1) else (if n < 43 then 0 else (-1))) else (if n < 46 then (if n < 45 then 0 else 3) else (if n < 47 then 0 else 1)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 1 else 0) else (if n < 51 then (-1) else 0)) else (if n < 54 then (if n < 53 then (-1) else 0) else (if n < 55 then 3 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then 0 else (-1)) else (if n < 59 then 0 else 1)) else (if n < 62 then (if n < 61 then 0 else 1) else (if n < 63 then 0 else 3)))))) else 0
theorem nestingEntries_eq400 (n : Nat) :
    nestingProjection400.numerator[n]! = nestingEntries400 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries400, if_neg (by omega : ¬ n < 64)]

def nestingProjection401 : Projection := ⟨4,6,#[3,1,0,0,0,0,-1,-1,1,3,0,0,0,0,1,1,0,0,3,1,1,-1,0,0,0,0,1,3,-1,1,0,0,0,0,1,-1,3,1,0,0,0,0,-1,1,1,3,0,0,-1,1,0,0,0,0,3,-1,-1,1,0,0,0,0,-1,3]⟩
theorem nestingLookup401 : projections[401]! = nestingProjection401 := by
  rw [projections_lookup]
  rfl
def nestingEntries401 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 1) else 0) else (if n < 6 then 0 else (-1))) else (if n < 12 then (if n < 10 then (if n < 9 then 1 else 3) else 0) else (if n < 14 then 0 else 1))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 3 else 1)) else (if n < 22 then (if n < 21 then 1 else (-1)) else 0)) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 1 else 3)) else (if n < 30 then (if n < 29 then (-1) else 1) else 0)))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then 0 else (if n < 35 then 1 else (-1))) else (if n < 38 then (if n < 37 then 3 else 1) else 0)) else (if n < 44 then (if n < 42 then 0 else (if n < 43 then (-1) else 1)) else (if n < 46 then (if n < 45 then 1 else 3) else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then (-1) else 1) else 0) else (if n < 54 then 0 else (if n < 55 then 3 else (-1)))) else (if n < 60 then (if n < 58 then (if n < 57 then (-1) else 1) else 0) else (if n < 62 then 0 else (if n < 63 then (-1) else 3)))))) else 0
theorem nestingEntries_eq401 (n : Nat) :
    nestingProjection401.numerator[n]! = nestingEntries401 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries401, if_neg (by omega : ¬ n < 64)]

def nestingProjection402 : Projection := ⟨4,6,#[3,1,0,0,0,0,-1,-1,1,2,0,1,0,1,1,0,0,0,4,0,0,0,0,0,0,1,0,3,0,-1,0,1,0,0,0,0,4,0,0,0,0,1,0,-1,0,3,0,1,-1,1,0,0,0,0,3,-1,-1,0,0,1,0,1,-1,2]⟩
theorem nestingLookup402 : projections[402]! = nestingProjection402 := by
  rw [projections_lookup]
  rfl
def nestingEntries402 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 1) else 0) else (if n < 6 then 0 else (-1))) else (if n < 12 then (if n < 10 then (if n < 9 then 1 else 2) else (if n < 11 then 0 else 1)) else (if n < 14 then (if n < 13 then 0 else 1) else (if n < 15 then 1 else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 4 else 0)) else 0) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else 1) else (if n < 27 then 0 else 3)) else (if n < 30 then (if n < 29 then 0 else (-1)) else (if n < 31 then 0 else 1))))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 4 else 0) else 0)) else (if n < 44 then (if n < 42 then (if n < 41 then 0 else 1) else (if n < 43 then 0 else (-1))) else (if n < 46 then (if n < 45 then 0 else 3) else (if n < 47 then 0 else 1)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then (-1) else 1) else 0) else (if n < 54 then 0 else (if n < 55 then 3 else (-1)))) else (if n < 60 then (if n < 58 then (if n < 57 then (-1) else 0) else (if n < 59 then 0 else 1)) else (if n < 62 then (if n < 61 then 0 else 1) else (if n < 63 then (-1) else 2)))))) else 0
theorem nestingEntries_eq402 (n : Nat) :
    nestingProjection402.numerator[n]! = nestingEntries402 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries402, if_neg (by omega : ¬ n < 64)]

def nestingProjection403 : Projection := ⟨4,6,#[4,0,0,0,0,0,0,0,0,3,0,1,0,1,0,-1,0,0,3,1,1,-1,0,0,0,1,1,2,-1,0,0,1,0,0,1,-1,3,1,0,0,0,1,-1,0,1,2,0,1,0,0,0,0,0,0,4,0,0,-1,0,1,0,1,0,3]⟩
theorem nestingLookup403 : projections[403]! = nestingProjection403 := by
  rw [projections_lookup]
  rfl
def nestingEntries403 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 4 else 0) else 0) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 3) else (if n < 11 then 0 else 1)) else (if n < 14 then (if n < 13 then 0 else 1) else (if n < 15 then 0 else (-1))))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 3 else 1)) else (if n < 22 then (if n < 21 then 1 else (-1)) else 0)) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else 1) else (if n < 27 then 1 else 2)) else (if n < 30 then (if n < 29 then (-1) else 0) else (if n < 31 then 0 else 1))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then 0 else (if n < 35 then 1 else (-1))) else (if n < 38 then (if n < 37 then 3 else 1) else 0)) else (if n < 44 then (if n < 42 then (if n < 41 then 0 else 1) else (if n < 43 then (-1) else 0)) else (if n < 46 then (if n < 45 then 1 else 2) else (if n < 47 then 0 else 1)))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 0 else (if n < 55 then 4 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then 0 else (-1)) else (if n < 59 then 0 else 1)) else (if n < 62 then (if n < 61 then 0 else 1) else (if n < 63 then 0 else 3)))))) else 0
theorem nestingEntries_eq403 (n : Nat) :
    nestingProjection403.numerator[n]! = nestingEntries403 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries403, if_neg (by omega : ¬ n < 64)]

def nestingProjection404 : Projection := ⟨4,6,#[2,1,1,0,1,0,0,-1,1,3,0,0,-1,1,0,0,1,0,3,0,0,-1,0,1,0,0,0,4,0,0,0,0,1,-1,0,0,3,1,0,0,0,1,-1,0,1,2,0,1,0,0,0,0,0,0,4,0,-1,0,1,0,0,1,0,3]⟩
theorem nestingLookup404 : projections[404]! = nestingProjection404 := by
  rw [projections_lookup]
  rfl
def nestingEntries404 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 2 else 1) else (if n < 3 then 1 else 0)) else (if n < 6 then (if n < 5 then 1 else 0) else (if n < 7 then 0 else (-1)))) else (if n < 12 then (if n < 10 then (if n < 9 then 1 else 3) else 0) else (if n < 14 then (if n < 13 then (-1) else 1) else 0))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 1 else 0) else (if n < 19 then 3 else 0)) else (if n < 22 then (if n < 21 then 0 else (-1)) else (if n < 23 then 0 else 1))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 4)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 1 else (-1)) else 0) else (if n < 38 then (if n < 37 then 3 else 1) else 0)) else (if n < 44 then (if n < 42 then (if n < 41 then 0 else 1) else (if n < 43 then (-1) else 0)) else (if n < 46 then (if n < 45 then 1 else 2) else (if n < 47 then 0 else 1)))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 0 else (if n < 55 then 4 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then (-1) else 0) else (if n < 59 then 1 else 0)) else (if n < 62 then (if n < 61 then 0 else 1) else (if n < 63 then 0 else 3)))))) else 0
theorem nestingEntries_eq404 (n : Nat) :
    nestingProjection404.numerator[n]! = nestingEntries404 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries404, if_neg (by omega : ¬ n < 64)]

def nestingProjection405 : Projection := ⟨4,6,#[3,1,0,0,1,-1,0,0,1,2,0,1,0,1,1,0,0,0,4,0,0,0,0,0,0,1,0,3,-1,0,-1,0,1,0,0,-1,2,1,-1,0,-1,1,0,0,1,3,0,0,0,1,0,-1,-1,0,3,0,0,0,0,0,0,0,0,4]⟩
theorem nestingLookup405 : projections[405]! = nestingProjection405 := by
  rw [projections_lookup]
  rfl
def nestingEntries405 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 1) else 0) else (if n < 6 then (if n < 5 then 1 else (-1)) else 0)) else (if n < 12 then (if n < 10 then (if n < 9 then 1 else 2) else (if n < 11 then 0 else 1)) else (if n < 14 then (if n < 13 then 0 else 1) else (if n < 15 then 1 else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 4 else 0)) else 0) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else 1) else (if n < 27 then 0 else 3)) else (if n < 30 then (if n < 29 then (-1) else 0) else (if n < 31 then (-1) else 0))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 1 else 0) else (if n < 35 then 0 else (-1))) else (if n < 38 then (if n < 37 then 2 else 1) else (if n < 39 then (-1) else 0))) else (if n < 44 then (if n < 42 then (if n < 41 then (-1) else 1) else 0) else (if n < 46 then (if n < 45 then 1 else 3) else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else 1) else (if n < 51 then 0 else (-1))) else (if n < 54 then (if n < 53 then (-1) else 0) else (if n < 55 then 3 else 0))) else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 4)))))) else 0
theorem nestingEntries_eq405 (n : Nat) :
    nestingProjection405.numerator[n]! = nestingEntries405 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries405, if_neg (by omega : ¬ n < 64)]

def nestingProjection406 : Projection := ⟨4,6,#[3,1,0,0,1,-1,0,0,1,3,0,0,-1,1,0,0,0,0,3,1,0,0,-1,-1,0,0,1,3,0,0,1,1,1,-1,0,0,3,1,0,0,-1,1,0,0,1,3,0,0,0,0,-1,1,0,0,3,-1,0,0,-1,1,0,0,-1,3]⟩
theorem nestingLookup406 : projections[406]! = nestingProjection406 := by
  rw [projections_lookup]
  rfl
def nestingEntries406 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 1) else 0) else (if n < 6 then (if n < 5 then 1 else (-1)) else 0)) else (if n < 12 then (if n < 10 then (if n < 9 then 1 else 3) else 0) else (if n < 14 then (if n < 13 then (-1) else 1) else 0))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 3 else 1)) else (if n < 22 then 0 else (-1))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 1 else 3)) else (if n < 30 then 0 else 1)))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 1 else (-1)) else 0) else (if n < 38 then (if n < 37 then 3 else 1) else 0)) else (if n < 44 then (if n < 42 then (if n < 41 then (-1) else 1) else 0) else (if n < 46 then (if n < 45 then 1 else 3) else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then 0 else (if n < 51 then (-1) else 1)) else (if n < 54 then 0 else (if n < 55 then 3 else (-1)))) else (if n < 60 then (if n < 58 then 0 else (if n < 59 then (-1) else 1)) else (if n < 62 then 0 else (if n < 63 then (-1) else 3)))))) else 0
theorem nestingEntries_eq406 (n : Nat) :
    nestingProjection406.numerator[n]! = nestingEntries406 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries406, if_neg (by omega : ¬ n < 64)]

def nestingProjection407 : Projection := ⟨4,6,#[3,0,1,0,0,1,0,-1,0,3,0,1,1,0,1,0,1,0,3,0,0,-1,0,1,0,1,0,3,-1,0,-1,0,0,1,0,-1,3,0,-1,0,1,0,-1,0,0,3,0,1,0,1,0,-1,-1,0,3,0,-1,0,1,0,0,1,0,3]⟩
theorem nestingLookup407 : projections[407]! = nestingProjection407 := by
  rw [projections_lookup]
  rfl
def nestingEntries407 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 0) else (if n < 3 then 1 else 0)) else (if n < 6 then (if n < 5 then 0 else 1) else (if n < 7 then 0 else (-1)))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 3) else (if n < 11 then 0 else 1)) else (if n < 14 then (if n < 13 then 1 else 0) else (if n < 15 then 1 else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 1 else 0) else (if n < 19 then 3 else 0)) else (if n < 22 then (if n < 21 then 0 else (-1)) else (if n < 23 then 0 else 1))) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else 1) else (if n < 27 then 0 else 3)) else (if n < 30 then (if n < 29 then (-1) else 0) else (if n < 31 then (-1) else 0))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 0 else 1) else (if n < 35 then 0 else (-1))) else (if n < 38 then (if n < 37 then 3 else 0) else (if n < 39 then (-1) else 0))) else (if n < 44 then (if n < 42 then (if n < 41 then 1 else 0) else (if n < 43 then (-1) else 0)) else (if n < 46 then (if n < 45 then 0 else 3) else (if n < 47 then 0 else 1)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else 1) else (if n < 51 then 0 else (-1))) else (if n < 54 then (if n < 53 then (-1) else 0) else (if n < 55 then 3 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then (-1) else 0) else (if n < 59 then 1 else 0)) else (if n < 62 then (if n < 61 then 0 else 1) else (if n < 63 then 0 else 3)))))) else 0
theorem nestingEntries_eq407 (n : Nat) :
    nestingProjection407.numerator[n]! = nestingEntries407 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries407, if_neg (by omega : ¬ n < 64)]

def nestingProjection408 : Projection := ⟨4,6,#[3,0,1,0,0,1,0,-1,0,4,0,0,0,0,0,0,1,0,2,1,0,-1,-1,0,0,0,1,3,0,0,1,1,0,0,0,0,4,0,0,0,1,0,-1,0,0,3,0,1,0,0,-1,1,0,0,3,-1,-1,0,0,1,0,1,-1,2]⟩
theorem nestingLookup408 : projections[408]! = nestingProjection408 := by
  rw [projections_lookup]
  rfl
def nestingEntries408 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 0) else (if n < 3 then 1 else 0)) else (if n < 6 then (if n < 5 then 0 else 1) else (if n < 7 then 0 else (-1)))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 4) else 0) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 1 else 0) else (if n < 19 then 2 else 1)) else (if n < 22 then (if n < 21 then 0 else (-1)) else (if n < 23 then (-1) else 0))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 1 else 3)) else (if n < 30 then 0 else 1)))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 4 else 0) else 0)) else (if n < 44 then (if n < 42 then (if n < 41 then 1 else 0) else (if n < 43 then (-1) else 0)) else (if n < 46 then (if n < 45 then 0 else 3) else (if n < 47 then 0 else 1)))) else (if n < 56 then (if n < 52 then (if n < 50 then 0 else (if n < 51 then (-1) else 1)) else (if n < 54 then 0 else (if n < 55 then 3 else (-1)))) else (if n < 60 then (if n < 58 then (if n < 57 then (-1) else 0) else (if n < 59 then 0 else 1)) else (if n < 62 then (if n < 61 then 0 else 1) else (if n < 63 then (-1) else 2)))))) else 0
theorem nestingEntries_eq408 (n : Nat) :
    nestingProjection408.numerator[n]! = nestingEntries408 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries408, if_neg (by omega : ¬ n < 64)]

def nestingProjection409 : Projection := ⟨4,6,#[4,0,0,0,0,0,0,0,0,3,0,1,1,0,1,0,0,0,3,1,0,0,-1,-1,0,1,1,2,-1,0,0,1,0,1,0,-1,3,0,-1,0,0,0,0,0,0,4,0,0,0,1,-1,0,-1,0,2,-1,0,0,-1,1,0,0,-1,3]⟩
theorem nestingLookup409 : projections[409]! = nestingProjection409 := by
  rw [projections_lookup]
  rfl
def nestingEntries409 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 4 else 0) else 0) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 3) else (if n < 11 then 0 else 1)) else (if n < 14 then (if n < 13 then 1 else 0) else (if n < 15 then 1 else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 3 else 1)) else (if n < 22 then 0 else (-1))) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else 1) else (if n < 27 then 1 else 2)) else (if n < 30 then (if n < 29 then (-1) else 0) else (if n < 31 then 0 else 1))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 0 else 1) else (if n < 35 then 0 else (-1))) else (if n < 38 then (if n < 37 then 3 else 0) else (if n < 39 then (-1) else 0))) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 4) else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else 1) else (if n < 51 then (-1) else 0)) else (if n < 54 then (if n < 53 then (-1) else 0) else (if n < 55 then 2 else (-1)))) else (if n < 60 then (if n < 58 then 0 else (if n < 59 then (-1) else 1)) else (if n < 62 then 0 else (if n < 63 then (-1) else 3)))))) else 0
theorem nestingEntries_eq409 (n : Nat) :
    nestingProjection409.numerator[n]! = nestingEntries409 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries409, if_neg (by omega : ¬ n < 64)]

def nestingProjection410 : Projection := ⟨4,6,#[4,0,0,0,0,0,0,0,0,3,1,0,0,1,1,0,0,1,3,0,0,-1,-1,0,0,0,0,4,0,0,0,0,0,0,0,0,3,1,-1,-1,0,1,-1,0,1,2,0,1,0,1,-1,0,-1,0,2,-1,0,0,0,0,-1,1,-1,3]⟩
theorem nestingLookup410 : projections[410]! = nestingProjection410 := by
  rw [projections_lookup]
  rfl
def nestingEntries410 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 4 else 0) else 0) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 3) else (if n < 11 then 1 else 0)) else (if n < 14 then (if n < 13 then 0 else 1) else (if n < 15 then 1 else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 0 else 1) else (if n < 19 then 3 else 0)) else (if n < 22 then (if n < 21 then 0 else (-1)) else (if n < 23 then (-1) else 0))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 4)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 3 else 1) else (-1))) else (if n < 44 then (if n < 42 then (if n < 41 then 0 else 1) else (if n < 43 then (-1) else 0)) else (if n < 46 then (if n < 45 then 1 else 2) else (if n < 47 then 0 else 1)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else 1) else (if n < 51 then (-1) else 0)) else (if n < 54 then (if n < 53 then (-1) else 0) else (if n < 55 then 2 else (-1)))) else (if n < 60 then 0 else (if n < 62 then (if n < 61 then (-1) else 1) else (if n < 63 then (-1) else 3)))))) else 0
theorem nestingEntries_eq410 (n : Nat) :
    nestingProjection410.numerator[n]! = nestingEntries410 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries410, if_neg (by omega : ¬ n < 64)]

def nestingProjection411 : Projection := ⟨4,6,#[3,1,1,-1,0,0,0,0,1,2,0,1,0,1,1,0,1,0,2,1,0,-1,-1,0,-1,1,1,3,0,0,0,0,0,0,0,0,4,0,0,0,0,1,-1,0,0,3,-1,0,0,1,-1,0,0,-1,3,0,0,0,0,0,0,0,0,4]⟩
theorem nestingLookup411 : projections[411]! = nestingProjection411 := by
  rw [projections_lookup]
  rfl
def nestingEntries411 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 1) else (if n < 3 then 1 else (-1))) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 1 else 2) else (if n < 11 then 0 else 1)) else (if n < 14 then (if n < 13 then 0 else 1) else (if n < 15 then 1 else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 1 else 0) else (if n < 19 then 2 else 1)) else (if n < 22 then (if n < 21 then 0 else (-1)) else (if n < 23 then (-1) else 0))) else (if n < 28 then (if n < 26 then (if n < 25 then (-1) else 1) else (if n < 27 then 1 else 3)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 4 else 0) else 0)) else (if n < 44 then (if n < 42 then (if n < 41 then 0 else 1) else (if n < 43 then (-1) else 0)) else (if n < 46 then (if n < 45 then 0 else 3) else (if n < 47 then (-1) else 0)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else 1) else (if n < 51 then (-1) else 0)) else (if n < 54 then (if n < 53 then 0 else (-1)) else (if n < 55 then 3 else 0))) else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 4)))))) else 0
theorem nestingEntries_eq411 (n : Nat) :
    nestingProjection411.numerator[n]! = nestingEntries411 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries411, if_neg (by omega : ¬ n < 64)]

def nestingProjection412 : Projection := ⟨4,6,#[3,0,0,1,1,0,0,-1,0,3,1,0,0,1,1,0,0,1,3,0,0,-1,-1,0,1,0,0,3,-1,0,0,1,1,0,0,-1,3,0,0,1,0,1,-1,0,0,3,-1,0,0,1,-1,0,0,-1,3,0,-1,0,0,1,1,0,0,3]⟩
theorem nestingLookup412 : projections[412]! = nestingProjection412 := by
  rw [projections_lookup]
  rfl
def nestingEntries412 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 0) else (if n < 3 then 0 else 1)) else (if n < 6 then (if n < 5 then 1 else 0) else (if n < 7 then 0 else (-1)))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 3) else (if n < 11 then 1 else 0)) else (if n < 14 then (if n < 13 then 0 else 1) else (if n < 15 then 1 else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 0 else 1) else (if n < 19 then 3 else 0)) else (if n < 22 then (if n < 21 then 0 else (-1)) else (if n < 23 then (-1) else 0))) else (if n < 28 then (if n < 26 then (if n < 25 then 1 else 0) else (if n < 27 then 0 else 3)) else (if n < 30 then (if n < 29 then (-1) else 0) else (if n < 31 then 0 else 1))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 1 else 0) else (if n < 35 then 0 else (-1))) else (if n < 38 then (if n < 37 then 3 else 0) else (if n < 39 then 0 else 1))) else (if n < 44 then (if n < 42 then (if n < 41 then 0 else 1) else (if n < 43 then (-1) else 0)) else (if n < 46 then (if n < 45 then 0 else 3) else (if n < 47 then (-1) else 0)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else 1) else (if n < 51 then (-1) else 0)) else (if n < 54 then (if n < 53 then 0 else (-1)) else (if n < 55 then 3 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then (-1) else 0) else (if n < 59 then 0 else 1)) else (if n < 62 then (if n < 61 then 1 else 0) else (if n < 63 then 0 else 3)))))) else 0
theorem nestingEntries_eq412 (n : Nat) :
    nestingProjection412.numerator[n]! = nestingEntries412 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries412, if_neg (by omega : ¬ n < 64)]

def nestingProjection413 : Projection := ⟨4,6,#[3,1,1,-1,0,0,0,0,1,3,-1,1,0,0,0,0,1,-1,3,1,0,0,0,0,-1,1,1,3,0,0,0,0,0,0,0,0,3,1,-1,-1,0,0,0,0,1,3,1,1,0,0,0,0,-1,1,3,-1,0,0,0,0,-1,1,-1,3]⟩
theorem nestingLookup413 : projections[413]! = nestingProjection413 := by
  rw [projections_lookup]
  rfl
def nestingEntries413 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 1) else (if n < 3 then 1 else (-1))) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 1 else 3) else (if n < 11 then (-1) else 1)) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 1 else (-1)) else (if n < 19 then 3 else 1)) else 0) else (if n < 28 then (if n < 26 then (if n < 25 then (-1) else 1) else (if n < 27 then 1 else 3)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 3 else 1) else (-1))) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 1 else 3) else 1))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then (if n < 53 then (-1) else 1) else (if n < 55 then 3 else (-1)))) else (if n < 60 then 0 else (if n < 62 then (if n < 61 then (-1) else 1) else (if n < 63 then (-1) else 3)))))) else 0
theorem nestingEntries_eq413 (n : Nat) :
    nestingProjection413.numerator[n]! = nestingEntries413 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries413, if_neg (by omega : ¬ n < 64)]

def nestingProjection414 : Projection := ⟨4,6,#[3,0,0,1,1,0,0,-1,0,4,0,0,0,0,0,0,0,0,4,0,0,0,0,0,1,0,0,3,-1,0,0,1,1,0,0,-1,2,1,-1,0,0,0,0,0,1,3,1,1,0,0,0,0,-1,1,3,-1,-1,0,0,1,0,1,-1,2]⟩
theorem nestingLookup414 : projections[414]! = nestingProjection414 := by
  rw [projections_lookup]
  rfl
def nestingEntries414 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 0) else (if n < 3 then 0 else 1)) else (if n < 6 then (if n < 5 then 1 else 0) else (if n < 7 then 0 else (-1)))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 4) else 0) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 4 else 0)) else 0) else (if n < 28 then (if n < 26 then (if n < 25 then 1 else 0) else (if n < 27 then 0 else 3)) else (if n < 30 then (if n < 29 then (-1) else 0) else (if n < 31 then 0 else 1))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 1 else 0) else (if n < 35 then 0 else (-1))) else (if n < 38 then (if n < 37 then 2 else 1) else (if n < 39 then (-1) else 0))) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 1 else 3) else 1))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then (if n < 53 then (-1) else 1) else (if n < 55 then 3 else (-1)))) else (if n < 60 then (if n < 58 then (if n < 57 then (-1) else 0) else (if n < 59 then 0 else 1)) else (if n < 62 then (if n < 61 then 0 else 1) else (if n < 63 then (-1) else 2)))))) else 0
theorem nestingEntries_eq414 (n : Nat) :
    nestingProjection414.numerator[n]! = nestingEntries414 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries414, if_neg (by omega : ¬ n < 64)]

def nestingProjection415 : Projection := ⟨4,6,#[2,1,1,0,1,0,0,-1,1,3,-1,1,0,0,0,0,1,-1,3,1,0,0,0,0,0,1,1,2,-1,0,0,1,1,0,0,-1,3,0,0,1,0,0,0,0,0,4,0,0,0,0,0,0,0,0,4,0,-1,0,0,1,1,0,0,3]⟩
theorem nestingLookup415 : projections[415]! = nestingProjection415 := by
  rw [projections_lookup]
  rfl
def nestingEntries415 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 2 else 1) else (if n < 3 then 1 else 0)) else (if n < 6 then (if n < 5 then 1 else 0) else (if n < 7 then 0 else (-1)))) else (if n < 12 then (if n < 10 then (if n < 9 then 1 else 3) else (if n < 11 then (-1) else 1)) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 1 else (-1)) else (if n < 19 then 3 else 1)) else 0) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else 1) else (if n < 27 then 1 else 2)) else (if n < 30 then (if n < 29 then (-1) else 0) else (if n < 31 then 0 else 1))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 1 else 0) else (if n < 35 then 0 else (-1))) else (if n < 38 then (if n < 37 then 3 else 0) else (if n < 39 then 0 else 1))) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 4) else 0))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 0 else (if n < 55 then 4 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then (-1) else 0) else (if n < 59 then 0 else 1)) else (if n < 62 then (if n < 61 then 1 else 0) else (if n < 63 then 0 else 3)))))) else 0
theorem nestingEntries_eq415 (n : Nat) :
    nestingProjection415.numerator[n]! = nestingEntries415 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries415, if_neg (by omega : ¬ n < 64)]

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def nestingProjection416 : Projection := ⟨4,6,#[2,-1,-1,0,1,0,0,-1,-1,3,0,0,0,0,-1,-1,-1,0,3,0,1,0,1,0,0,0,0,4,0,0,0,0,1,0,1,0,3,0,-1,0,0,0,0,0,0,4,0,0,0,-1,1,0,-1,0,2,-1,-1,-1,0,0,0,0,-1,3]⟩
theorem nestingLookup416 : projections[416]! = nestingProjection416 := by
  rw [projections_lookup]
  rfl
def nestingEntries416 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 2 else (-1)) else (if n < 3 then (-1) else 0)) else (if n < 6 then (if n < 5 then 1 else 0) else (if n < 7 then 0 else (-1)))) else (if n < 12 then (if n < 10 then (if n < 9 then (-1) else 3) else 0) else (if n < 14 then 0 else (-1)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then (-1) else 0) else (if n < 19 then 3 else 0)) else (if n < 22 then (if n < 21 then 1 else 0) else (if n < 23 then 1 else 0))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 4)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 1 else 0) else (if n < 35 then 1 else 0)) else (if n < 38 then (if n < 37 then 3 else 0) else (if n < 39 then (-1) else 0))) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 4) else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else (-1)) else (if n < 51 then 1 else 0)) else (if n < 54 then (if n < 53 then (-1) else 0) else (if n < 55 then 2 else (-1)))) else (if n < 60 then (if n < 58 then (-1) else 0) else (if n < 62 then 0 else (if n < 63 then (-1) else 3)))))) else 0
theorem nestingEntries_eq416 (n : Nat) :
    nestingProjection416.numerator[n]! = nestingEntries416 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries416, if_neg (by omega : ¬ n < 64)]

def nestingProjection417 : Projection := ⟨4,6,#[3,0,-1,0,1,0,1,0,0,4,0,0,0,0,0,0,-1,0,2,1,0,-1,1,0,0,0,1,3,1,1,0,0,1,0,0,1,2,-1,-1,0,0,0,-1,1,-1,3,0,0,1,0,1,0,-1,0,3,0,0,0,0,0,0,0,0,4]⟩
theorem nestingLookup417 : projections[417]! = nestingProjection417 := by
  rw [projections_lookup]
  rfl
def nestingEntries417 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 0) else (if n < 3 then (-1) else 0)) else (if n < 6 then (if n < 5 then 1 else 0) else (if n < 7 then 1 else 0))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 4) else 0) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then (-1) else 0) else (if n < 19 then 2 else 1)) else (if n < 22 then (if n < 21 then 0 else (-1)) else (if n < 23 then 1 else 0))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 1 else 3)) else (if n < 30 then 1 else 0)))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 1 else 0) else (if n < 35 then 0 else 1)) else (if n < 38 then (if n < 37 then 2 else (-1)) else (if n < 39 then (-1) else 0))) else (if n < 44 then (if n < 42 then 0 else (if n < 43 then (-1) else 1)) else (if n < 46 then (if n < 45 then (-1) else 3) else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 1 else 0) else (if n < 51 then 1 else 0)) else (if n < 54 then (if n < 53 then (-1) else 0) else (if n < 55 then 3 else 0))) else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 4)))))) else 0
theorem nestingEntries_eq417 (n : Nat) :
    nestingProjection417.numerator[n]! = nestingEntries417 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries417, if_neg (by omega : ¬ n < 64)]

def nestingProjection418 : Projection := ⟨4,6,#[3,0,-1,0,1,0,1,0,0,3,0,1,0,1,0,1,-1,0,3,0,1,0,1,0,0,1,0,3,0,-1,0,-1,1,0,1,0,3,0,-1,0,0,1,0,-1,0,3,0,-1,1,0,1,0,-1,0,3,0,0,1,0,-1,0,-1,0,3]⟩
theorem nestingLookup418 : projections[418]! = nestingProjection418 := by
  rw [projections_lookup]
  rfl
def nestingEntries418 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 0) else (if n < 3 then (-1) else 0)) else (if n < 6 then (if n < 5 then 1 else 0) else (if n < 7 then 1 else 0))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 3) else (if n < 11 then 0 else 1)) else (if n < 14 then (if n < 13 then 0 else 1) else (if n < 15 then 0 else 1)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then (-1) else 0) else (if n < 19 then 3 else 0)) else (if n < 22 then (if n < 21 then 1 else 0) else (if n < 23 then 1 else 0))) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else 1) else (if n < 27 then 0 else 3)) else (if n < 30 then (if n < 29 then 0 else (-1)) else (if n < 31 then 0 else (-1)))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 1 else 0) else (if n < 35 then 1 else 0)) else (if n < 38 then (if n < 37 then 3 else 0) else (if n < 39 then (-1) else 0))) else (if n < 44 then (if n < 42 then (if n < 41 then 0 else 1) else (if n < 43 then 0 else (-1))) else (if n < 46 then (if n < 45 then 0 else 3) else (if n < 47 then 0 else (-1))))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 1 else 0) else (if n < 51 then 1 else 0)) else (if n < 54 then (if n < 53 then (-1) else 0) else (if n < 55 then 3 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then 0 else 1) else (if n < 59 then 0 else (-1))) else (if n < 62 then (if n < 61 then 0 else (-1)) else (if n < 63 then 0 else 3)))))) else 0
theorem nestingEntries_eq418 (n : Nat) :
    nestingProjection418.numerator[n]! = nestingEntries418 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries418, if_neg (by omega : ¬ n < 64)]

def nestingProjection419 : Projection := ⟨4,6,#[3,-1,0,0,0,0,-1,-1,-1,3,0,0,0,0,-1,-1,0,0,3,1,-1,-1,0,0,0,0,1,3,1,1,0,0,0,0,-1,1,3,-1,0,0,0,0,-1,1,-1,3,0,0,-1,-1,0,0,0,0,3,-1,-1,-1,0,0,0,0,-1,3]⟩
theorem nestingLookup419 : projections[419]! = nestingProjection419 := by
  rw [projections_lookup]
  rfl
def nestingEntries419 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else (-1)) else 0) else (if n < 6 then 0 else (-1))) else (if n < 12 then (if n < 10 then (if n < 9 then (-1) else 3) else 0) else (if n < 14 then 0 else (-1)))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 3 else 1)) else (if n < 22 then (-1) else 0)) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 1 else 3)) else (if n < 30 then 1 else 0)))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then 0 else (if n < 35 then (-1) else 1)) else (if n < 38 then (if n < 37 then 3 else (-1)) else 0)) else (if n < 44 then (if n < 42 then 0 else (if n < 43 then (-1) else 1)) else (if n < 46 then (if n < 45 then (-1) else 3) else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then (-1) else 0) else (if n < 54 then 0 else (if n < 55 then 3 else (-1)))) else (if n < 60 then (if n < 58 then (-1) else 0) else (if n < 62 then 0 else (if n < 63 then (-1) else 3)))))) else 0
theorem nestingEntries_eq419 (n : Nat) :
    nestingProjection419.numerator[n]! = nestingEntries419 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries419, if_neg (by omega : ¬ n < 64)]

def nestingProjection420 : Projection := ⟨4,6,#[3,-1,0,0,0,0,-1,-1,-1,2,0,1,0,1,-1,0,0,0,4,0,0,0,0,0,0,1,0,3,0,-1,0,-1,0,0,0,0,4,0,0,0,0,1,0,-1,0,3,0,-1,-1,-1,0,0,0,0,3,-1,-1,0,0,-1,0,-1,-1,2]⟩
theorem nestingLookup420 : projections[420]! = nestingProjection420 := by
  rw [projections_lookup]
  rfl
def nestingEntries420 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else (-1)) else 0) else (if n < 6 then 0 else (-1))) else (if n < 12 then (if n < 10 then (if n < 9 then (-1) else 2) else (if n < 11 then 0 else 1)) else (if n < 14 then (if n < 13 then 0 else 1) else (if n < 15 then (-1) else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 4 else 0)) else 0) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else 1) else (if n < 27 then 0 else 3)) else (if n < 30 then (if n < 29 then 0 else (-1)) else (if n < 31 then 0 else (-1)))))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 4 else 0) else 0)) else (if n < 44 then (if n < 42 then (if n < 41 then 0 else 1) else (if n < 43 then 0 else (-1))) else (if n < 46 then (if n < 45 then 0 else 3) else (if n < 47 then 0 else (-1))))) else (if n < 56 then (if n < 52 then (if n < 50 then (-1) else 0) else (if n < 54 then 0 else (if n < 55 then 3 else (-1)))) else (if n < 60 then (if n < 58 then (if n < 57 then (-1) else 0) else (if n < 59 then 0 else (-1))) else (if n < 62 then (if n < 61 then 0 else (-1)) else (if n < 63 then (-1) else 2)))))) else 0
theorem nestingEntries_eq420 (n : Nat) :
    nestingProjection420.numerator[n]! = nestingEntries420 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries420, if_neg (by omega : ¬ n < 64)]

def nestingProjection421 : Projection := ⟨4,6,#[4,0,0,0,0,0,0,0,0,3,0,1,0,1,0,1,0,0,3,1,-1,-1,0,0,0,1,1,2,1,0,0,-1,0,0,-1,1,3,-1,0,0,0,1,-1,0,-1,2,0,-1,0,0,0,0,0,0,4,0,0,1,0,-1,0,-1,0,3]⟩
theorem nestingLookup421 : projections[421]! = nestingProjection421 := by
  rw [projections_lookup]
  rfl
def nestingEntries421 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 4 else 0) else 0) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 3) else (if n < 11 then 0 else 1)) else (if n < 14 then (if n < 13 then 0 else 1) else (if n < 15 then 0 else 1)))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 3 else 1)) else (if n < 22 then (-1) else 0)) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else 1) else (if n < 27 then 1 else 2)) else (if n < 30 then (if n < 29 then 1 else 0) else (if n < 31 then 0 else (-1)))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then 0 else (if n < 35 then (-1) else 1)) else (if n < 38 then (if n < 37 then 3 else (-1)) else 0)) else (if n < 44 then (if n < 42 then (if n < 41 then 0 else 1) else (if n < 43 then (-1) else 0)) else (if n < 46 then (if n < 45 then (-1) else 2) else (if n < 47 then 0 else (-1))))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 0 else (if n < 55 then 4 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then 0 else 1) else (if n < 59 then 0 else (-1))) else (if n < 62 then (if n < 61 then 0 else (-1)) else (if n < 63 then 0 else 3)))))) else 0
theorem nestingEntries_eq421 (n : Nat) :
    nestingProjection421.numerator[n]! = nestingEntries421 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries421, if_neg (by omega : ¬ n < 64)]

def nestingProjection422 : Projection := ⟨4,6,#[2,-1,-1,0,1,0,0,-1,-1,3,0,0,1,1,0,0,-1,0,3,0,0,-1,0,-1,0,0,0,4,0,0,0,0,1,1,0,0,3,-1,0,0,0,1,-1,0,-1,2,0,-1,0,0,0,0,0,0,4,0,-1,0,-1,0,0,-1,0,3]⟩
theorem nestingLookup422 : projections[422]! = nestingProjection422 := by
  rw [projections_lookup]
  rfl
def nestingEntries422 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 2 else (-1)) else (if n < 3 then (-1) else 0)) else (if n < 6 then (if n < 5 then 1 else 0) else (if n < 7 then 0 else (-1)))) else (if n < 12 then (if n < 10 then (if n < 9 then (-1) else 3) else 0) else (if n < 14 then 1 else 0))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then (-1) else 0) else (if n < 19 then 3 else 0)) else (if n < 22 then (if n < 21 then 0 else (-1)) else (if n < 23 then 0 else (-1)))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 4)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then 1 else 0) else (if n < 38 then (if n < 37 then 3 else (-1)) else 0)) else (if n < 44 then (if n < 42 then (if n < 41 then 0 else 1) else (if n < 43 then (-1) else 0)) else (if n < 46 then (if n < 45 then (-1) else 2) else (if n < 47 then 0 else (-1))))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 0 else (if n < 55 then 4 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then (-1) else 0) else (if n < 59 then (-1) else 0)) else (if n < 62 then (if n < 61 then 0 else (-1)) else (if n < 63 then 0 else 3)))))) else 0
theorem nestingEntries_eq422 (n : Nat) :
    nestingProjection422.numerator[n]! = nestingEntries422 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries422, if_neg (by omega : ¬ n < 64)]

def nestingProjection423 : Projection := ⟨4,6,#[3,-1,0,0,1,1,0,0,-1,2,0,1,0,1,-1,0,0,0,4,0,0,0,0,0,0,1,0,3,1,0,1,0,1,0,0,1,2,-1,-1,0,1,1,0,0,-1,3,0,0,0,-1,0,1,-1,0,3,0,0,0,0,0,0,0,0,4]⟩
theorem nestingLookup423 : projections[423]! = nestingProjection423 := by
  rw [projections_lookup]
  rfl
def nestingEntries423 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else (-1)) else 0) else (if n < 6 then 1 else 0)) else (if n < 12 then (if n < 10 then (if n < 9 then (-1) else 2) else (if n < 11 then 0 else 1)) else (if n < 14 then (if n < 13 then 0 else 1) else (if n < 15 then (-1) else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 4 else 0)) else 0) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else 1) else (if n < 27 then 0 else 3)) else (if n < 30 then (if n < 29 then 1 else 0) else (if n < 31 then 1 else 0))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 1 else 0) else (if n < 35 then 0 else 1)) else (if n < 38 then (if n < 37 then 2 else (-1)) else (if n < 39 then (-1) else 0))) else (if n < 44 then (if n < 42 then 1 else 0) else (if n < 46 then (if n < 45 then (-1) else 3) else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else (-1)) else (if n < 51 then 0 else 1)) else (if n < 54 then (if n < 53 then (-1) else 0) else (if n < 55 then 3 else 0))) else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 4)))))) else 0
theorem nestingEntries_eq423 (n : Nat) :
    nestingProjection423.numerator[n]! = nestingEntries423 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries423, if_neg (by omega : ¬ n < 64)]

def nestingProjection424 : Projection := ⟨4,6,#[3,-1,0,0,1,1,0,0,-1,3,0,0,1,1,0,0,0,0,3,1,0,0,1,1,0,0,1,3,0,0,-1,-1,1,1,0,0,3,-1,0,0,1,1,0,0,-1,3,0,0,0,0,1,-1,0,0,3,-1,0,0,1,-1,0,0,-1,3]⟩
theorem nestingLookup424 : projections[424]! = nestingProjection424 := by
  rw [projections_lookup]
  rfl
def nestingEntries424 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else (-1)) else 0) else (if n < 6 then 1 else 0)) else (if n < 12 then (if n < 10 then (if n < 9 then (-1) else 3) else 0) else (if n < 14 then 1 else 0))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 3 else 1)) else (if n < 22 then 0 else 1)) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 1 else 3)) else (if n < 30 then 0 else (-1))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then 1 else 0) else (if n < 38 then (if n < 37 then 3 else (-1)) else 0)) else (if n < 44 then (if n < 42 then 1 else 0) else (if n < 46 then (if n < 45 then (-1) else 3) else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then 0 else (if n < 51 then 1 else (-1))) else (if n < 54 then 0 else (if n < 55 then 3 else (-1)))) else (if n < 60 then (if n < 58 then 0 else (if n < 59 then 1 else (-1))) else (if n < 62 then 0 else (if n < 63 then (-1) else 3)))))) else 0
theorem nestingEntries_eq424 (n : Nat) :
    nestingProjection424.numerator[n]! = nestingEntries424 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries424, if_neg (by omega : ¬ n < 64)]

def nestingProjection425 : Projection := ⟨4,6,#[3,0,-1,0,0,-1,0,-1,0,3,0,1,-1,0,-1,0,-1,0,3,0,0,-1,0,-1,0,1,0,3,1,0,1,0,0,-1,0,1,3,0,-1,0,-1,0,-1,0,0,3,0,-1,0,-1,0,1,-1,0,3,0,-1,0,-1,0,0,-1,0,3]⟩
theorem nestingLookup425 : projections[425]! = nestingProjection425 := by
  rw [projections_lookup]
  rfl
def nestingEntries425 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 0) else (if n < 3 then (-1) else 0)) else (if n < 6 then (if n < 5 then 0 else (-1)) else (if n < 7 then 0 else (-1)))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 3) else (if n < 11 then 0 else 1)) else (if n < 14 then (if n < 13 then (-1) else 0) else (if n < 15 then (-1) else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then (-1) else 0) else (if n < 19 then 3 else 0)) else (if n < 22 then (if n < 21 then 0 else (-1)) else (if n < 23 then 0 else (-1)))) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else 1) else (if n < 27 then 0 else 3)) else (if n < 30 then (if n < 29 then 1 else 0) else (if n < 31 then 1 else 0))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 0 else (-1)) else (if n < 35 then 0 else 1)) else (if n < 38 then (if n < 37 then 3 else 0) else (if n < 39 then (-1) else 0))) else (if n < 44 then (if n < 42 then (if n < 41 then (-1) else 0) else (if n < 43 then (-1) else 0)) else (if n < 46 then (if n < 45 then 0 else 3) else (if n < 47 then 0 else (-1))))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else (-1)) else (if n < 51 then 0 else 1)) else (if n < 54 then (if n < 53 then (-1) else 0) else (if n < 55 then 3 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then (-1) else 0) else (if n < 59 then (-1) else 0)) else (if n < 62 then (if n < 61 then 0 else (-1)) else (if n < 63 then 0 else 3)))))) else 0
theorem nestingEntries_eq425 (n : Nat) :
    nestingProjection425.numerator[n]! = nestingEntries425 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries425, if_neg (by omega : ¬ n < 64)]

def nestingProjection426 : Projection := ⟨4,6,#[3,0,-1,0,0,-1,0,-1,0,4,0,0,0,0,0,0,-1,0,2,1,0,-1,1,0,0,0,1,3,0,0,-1,-1,0,0,0,0,4,0,0,0,-1,0,-1,0,0,3,0,-1,0,0,1,-1,0,0,3,-1,-1,0,0,-1,0,-1,-1,2]⟩
theorem nestingLookup426 : projections[426]! = nestingProjection426 := by
  rw [projections_lookup]
  rfl
def nestingEntries426 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 0) else (if n < 3 then (-1) else 0)) else (if n < 6 then (if n < 5 then 0 else (-1)) else (if n < 7 then 0 else (-1)))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 4) else 0) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then (-1) else 0) else (if n < 19 then 2 else 1)) else (if n < 22 then (if n < 21 then 0 else (-1)) else (if n < 23 then 1 else 0))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 1 else 3)) else (if n < 30 then 0 else (-1))))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 4 else 0) else 0)) else (if n < 44 then (if n < 42 then (if n < 41 then (-1) else 0) else (if n < 43 then (-1) else 0)) else (if n < 46 then (if n < 45 then 0 else 3) else (if n < 47 then 0 else (-1))))) else (if n < 56 then (if n < 52 then (if n < 50 then 0 else (if n < 51 then 1 else (-1))) else (if n < 54 then 0 else (if n < 55 then 3 else (-1)))) else (if n < 60 then (if n < 58 then (if n < 57 then (-1) else 0) else (if n < 59 then 0 else (-1))) else (if n < 62 then (if n < 61 then 0 else (-1)) else (if n < 63 then (-1) else 2)))))) else 0
theorem nestingEntries_eq426 (n : Nat) :
    nestingProjection426.numerator[n]! = nestingEntries426 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries426, if_neg (by omega : ¬ n < 64)]

def nestingProjection427 : Projection := ⟨4,6,#[4,0,0,0,0,0,0,0,0,3,0,1,-1,0,-1,0,0,0,3,1,0,0,1,1,0,1,1,2,1,0,0,-1,0,-1,0,1,3,0,-1,0,0,0,0,0,0,4,0,0,0,-1,1,0,-1,0,2,-1,0,0,1,-1,0,0,-1,3]⟩
theorem nestingLookup427 : projections[427]! = nestingProjection427 := by
  rw [projections_lookup]
  rfl
def nestingEntries427 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 4 else 0) else 0) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 3) else (if n < 11 then 0 else 1)) else (if n < 14 then (if n < 13 then (-1) else 0) else (if n < 15 then (-1) else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 3 else 1)) else (if n < 22 then 0 else 1)) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else 1) else (if n < 27 then 1 else 2)) else (if n < 30 then (if n < 29 then 1 else 0) else (if n < 31 then 0 else (-1)))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 0 else (-1)) else (if n < 35 then 0 else 1)) else (if n < 38 then (if n < 37 then 3 else 0) else (if n < 39 then (-1) else 0))) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 4) else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else (-1)) else (if n < 51 then 1 else 0)) else (if n < 54 then (if n < 53 then (-1) else 0) else (if n < 55 then 2 else (-1)))) else (if n < 60 then (if n < 58 then 0 else (if n < 59 then 1 else (-1))) else (if n < 62 then 0 else (if n < 63 then (-1) else 3)))))) else 0
theorem nestingEntries_eq427 (n : Nat) :
    nestingProjection427.numerator[n]! = nestingEntries427 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries427, if_neg (by omega : ¬ n < 64)]

def nestingProjection428 : Projection := ⟨4,6,#[4,0,0,0,0,0,0,0,0,3,1,0,0,1,-1,0,0,1,3,0,0,-1,1,0,0,0,0,4,0,0,0,0,0,0,0,0,3,-1,-1,-1,0,1,-1,0,-1,2,0,-1,0,-1,1,0,-1,0,2,-1,0,0,0,0,-1,-1,-1,3]⟩
theorem nestingLookup428 : projections[428]! = nestingProjection428 := by
  rw [projections_lookup]
  rfl
def nestingEntries428 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 4 else 0) else 0) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 3) else (if n < 11 then 1 else 0)) else (if n < 14 then (if n < 13 then 0 else 1) else (if n < 15 then (-1) else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 0 else 1) else (if n < 19 then 3 else 0)) else (if n < 22 then (if n < 21 then 0 else (-1)) else (if n < 23 then 1 else 0))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 4)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 3 else (-1)) else (-1))) else (if n < 44 then (if n < 42 then (if n < 41 then 0 else 1) else (if n < 43 then (-1) else 0)) else (if n < 46 then (if n < 45 then (-1) else 2) else (if n < 47 then 0 else (-1))))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else (-1)) else (if n < 51 then 1 else 0)) else (if n < 54 then (if n < 53 then (-1) else 0) else (if n < 55 then 2 else (-1)))) else (if n < 60 then 0 else (if n < 62 then (-1) else (if n < 63 then (-1) else 3)))))) else 0
theorem nestingEntries_eq428 (n : Nat) :
    nestingProjection428.numerator[n]! = nestingEntries428 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries428, if_neg (by omega : ¬ n < 64)]

def nestingProjection429 : Projection := ⟨4,6,#[3,-1,-1,1,0,0,0,0,-1,2,0,1,0,1,-1,0,-1,0,2,1,0,-1,1,0,1,1,1,3,0,0,0,0,0,0,0,0,4,0,0,0,0,1,-1,0,0,3,1,0,0,-1,1,0,0,1,3,0,0,0,0,0,0,0,0,4]⟩
theorem nestingLookup429 : projections[429]! = nestingProjection429 := by
  rw [projections_lookup]
  rfl
def nestingEntries429 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else (-1)) else (if n < 3 then (-1) else 1)) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then (-1) else 2) else (if n < 11 then 0 else 1)) else (if n < 14 then (if n < 13 then 0 else 1) else (if n < 15 then (-1) else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then (-1) else 0) else (if n < 19 then 2 else 1)) else (if n < 22 then (if n < 21 then 0 else (-1)) else (if n < 23 then 1 else 0))) else (if n < 28 then (if n < 26 then 1 else (if n < 27 then 1 else 3)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 4 else 0) else 0)) else (if n < 44 then (if n < 42 then (if n < 41 then 0 else 1) else (if n < 43 then (-1) else 0)) else (if n < 46 then (if n < 45 then 0 else 3) else (if n < 47 then 1 else 0)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else (-1)) else (if n < 51 then 1 else 0)) else (if n < 54 then (if n < 53 then 0 else 1) else (if n < 55 then 3 else 0))) else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 4)))))) else 0
theorem nestingEntries_eq429 (n : Nat) :
    nestingProjection429.numerator[n]! = nestingEntries429 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries429, if_neg (by omega : ¬ n < 64)]

def nestingProjection430 : Projection := ⟨4,6,#[3,0,0,-1,1,0,0,-1,0,3,1,0,0,1,-1,0,0,1,3,0,0,-1,1,0,-1,0,0,3,1,0,0,-1,1,0,0,1,3,0,0,1,0,1,-1,0,0,3,1,0,0,-1,1,0,0,1,3,0,-1,0,0,-1,1,0,0,3]⟩
theorem nestingLookup430 : projections[430]! = nestingProjection430 := by
  rw [projections_lookup]
  rfl
def nestingEntries430 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 0) else (if n < 3 then 0 else (-1))) else (if n < 6 then (if n < 5 then 1 else 0) else (if n < 7 then 0 else (-1)))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 3) else (if n < 11 then 1 else 0)) else (if n < 14 then (if n < 13 then 0 else 1) else (if n < 15 then (-1) else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 0 else 1) else (if n < 19 then 3 else 0)) else (if n < 22 then (if n < 21 then 0 else (-1)) else (if n < 23 then 1 else 0))) else (if n < 28 then (if n < 26 then (if n < 25 then (-1) else 0) else (if n < 27 then 0 else 3)) else (if n < 30 then (if n < 29 then 1 else 0) else (if n < 31 then 0 else (-1)))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 1 else 0) else (if n < 35 then 0 else 1)) else (if n < 38 then (if n < 37 then 3 else 0) else (if n < 39 then 0 else 1))) else (if n < 44 then (if n < 42 then (if n < 41 then 0 else 1) else (if n < 43 then (-1) else 0)) else (if n < 46 then (if n < 45 then 0 else 3) else (if n < 47 then 1 else 0)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else (-1)) else (if n < 51 then 1 else 0)) else (if n < 54 then (if n < 53 then 0 else 1) else (if n < 55 then 3 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then (-1) else 0) else (if n < 59 then 0 else (-1))) else (if n < 62 then (if n < 61 then 1 else 0) else (if n < 63 then 0 else 3)))))) else 0
theorem nestingEntries_eq430 (n : Nat) :
    nestingProjection430.numerator[n]! = nestingEntries430 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries430, if_neg (by omega : ¬ n < 64)]

def nestingProjection431 : Projection := ⟨4,6,#[3,-1,-1,1,0,0,0,0,-1,3,-1,1,0,0,0,0,-1,-1,3,1,0,0,0,0,1,1,1,3,0,0,0,0,0,0,0,0,3,-1,-1,-1,0,0,0,0,-1,3,-1,-1,0,0,0,0,-1,-1,3,-1,0,0,0,0,-1,-1,-1,3]⟩
theorem nestingLookup431 : projections[431]! = nestingProjection431 := by
  rw [projections_lookup]
  rfl
def nestingEntries431 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else (-1)) else (if n < 3 then (-1) else 1)) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then (-1) else 3) else (if n < 11 then (-1) else 1)) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then (-1) else (if n < 19 then 3 else 1)) else 0) else (if n < 28 then (if n < 26 then 1 else (if n < 27 then 1 else 3)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 3 else (-1)) else (-1))) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then (-1) else 3) else (-1)))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then (-1) else (if n < 55 then 3 else (-1)))) else (if n < 60 then 0 else (if n < 62 then (-1) else (if n < 63 then (-1) else 3)))))) else 0
theorem nestingEntries_eq431 (n : Nat) :
    nestingProjection431.numerator[n]! = nestingEntries431 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries431, if_neg (by omega : ¬ n < 64)]

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def nestingProjection432 : Projection := ⟨4,6,#[3,0,0,-1,1,0,0,-1,0,4,0,0,0,0,0,0,0,0,4,0,0,0,0,0,-1,0,0,3,1,0,0,-1,1,0,0,1,2,-1,-1,0,0,0,0,0,-1,3,-1,-1,0,0,0,0,-1,-1,3,-1,-1,0,0,-1,0,-1,-1,2]⟩
theorem nestingLookup432 : projections[432]! = nestingProjection432 := by
  rw [projections_lookup]
  rfl
def nestingEntries432 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 0) else (if n < 3 then 0 else (-1))) else (if n < 6 then (if n < 5 then 1 else 0) else (if n < 7 then 0 else (-1)))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 4) else 0) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 4 else 0)) else 0) else (if n < 28 then (if n < 26 then (if n < 25 then (-1) else 0) else (if n < 27 then 0 else 3)) else (if n < 30 then (if n < 29 then 1 else 0) else (if n < 31 then 0 else (-1)))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 1 else 0) else (if n < 35 then 0 else 1)) else (if n < 38 then (if n < 37 then 2 else (-1)) else (if n < 39 then (-1) else 0))) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then (-1) else 3) else (-1)))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then (-1) else (if n < 55 then 3 else (-1)))) else (if n < 60 then (if n < 58 then (if n < 57 then (-1) else 0) else (if n < 59 then 0 else (-1))) else (if n < 62 then (if n < 61 then 0 else (-1)) else (if n < 63 then (-1) else 2)))))) else 0
theorem nestingEntries_eq432 (n : Nat) :
    nestingProjection432.numerator[n]! = nestingEntries432 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries432, if_neg (by omega : ¬ n < 64)]

def nestingProjection433 : Projection := ⟨4,6,#[2,-1,-1,0,1,0,0,-1,-1,3,-1,1,0,0,0,0,-1,-1,3,1,0,0,0,0,0,1,1,2,1,0,0,-1,1,0,0,1,3,0,0,1,0,0,0,0,0,4,0,0,0,0,0,0,0,0,4,0,-1,0,0,-1,1,0,0,3]⟩
theorem nestingLookup433 : projections[433]! = nestingProjection433 := by
  rw [projections_lookup]
  rfl
def nestingEntries433 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 2 else (-1)) else (if n < 3 then (-1) else 0)) else (if n < 6 then (if n < 5 then 1 else 0) else (if n < 7 then 0 else (-1)))) else (if n < 12 then (if n < 10 then (if n < 9 then (-1) else 3) else (if n < 11 then (-1) else 1)) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then (-1) else (if n < 19 then 3 else 1)) else 0) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else 1) else (if n < 27 then 1 else 2)) else (if n < 30 then (if n < 29 then 1 else 0) else (if n < 31 then 0 else (-1)))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 1 else 0) else (if n < 35 then 0 else 1)) else (if n < 38 then (if n < 37 then 3 else 0) else (if n < 39 then 0 else 1))) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 4) else 0))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 0 else (if n < 55 then 4 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then (-1) else 0) else (if n < 59 then 0 else (-1))) else (if n < 62 then (if n < 61 then 1 else 0) else (if n < 63 then 0 else 3)))))) else 0
theorem nestingEntries_eq433 (n : Nat) :
    nestingProjection433.numerator[n]! = nestingEntries433 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries433, if_neg (by omega : ¬ n < 64)]

def nestingProjection434 : Projection := ⟨2,6,#[2,0,0,0,0,0,0,0,0,1,0,0,1,0,0,0,0,0,1,0,0,0,0,1,0,0,0,2,0,0,0,0,0,1,0,0,1,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,2,0,0,0,1,0,0,0,0,1]⟩
theorem nestingLookup434 : projections[434]! = nestingProjection434 := by
  rw [projections_lookup]
  rfl
def nestingEntries434 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 2 else 0) else 0) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else 0) else (if n < 14 then (if n < 13 then 1 else 0) else 0))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 1 else 0)) else (if n < 22 then 0 else (if n < 23 then 0 else 1))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 2)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 0 else 1) else 0) else (if n < 38 then (if n < 37 then 1 else 0) else 0)) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 2) else 0))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 0 else (if n < 55 then 2 else 0))) else (if n < 60 then (if n < 58 then 0 else (if n < 59 then 1 else 0)) else (if n < 62 then 0 else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq434 (n : Nat) :
    nestingProjection434.numerator[n]! = nestingEntries434 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries434, if_neg (by omega : ¬ n < 64)]

def nestingProjection435 : Projection := ⟨4,6,#[3,0,0,-1,0,-1,1,0,0,3,-1,0,1,0,0,1,0,-1,3,0,1,0,0,1,-1,0,0,3,0,-1,1,0,0,1,1,0,3,0,0,-1,-1,0,0,-1,0,3,1,0,1,0,0,1,0,1,3,0,0,1,1,0,-1,0,0,3]⟩
theorem nestingLookup435 : projections[435]! = nestingProjection435 := by
  rw [projections_lookup]
  rfl
def nestingEntries435 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 0) else (if n < 3 then 0 else (-1))) else (if n < 6 then (if n < 5 then 0 else (-1)) else (if n < 7 then 1 else 0))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 3) else (if n < 11 then (-1) else 0)) else (if n < 14 then (if n < 13 then 1 else 0) else (if n < 15 then 0 else 1)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 0 else (-1)) else (if n < 19 then 3 else 0)) else (if n < 22 then (if n < 21 then 1 else 0) else (if n < 23 then 0 else 1))) else (if n < 28 then (if n < 26 then (if n < 25 then (-1) else 0) else (if n < 27 then 0 else 3)) else (if n < 30 then (if n < 29 then 0 else (-1)) else (if n < 31 then 1 else 0))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 0 else 1) else (if n < 35 then 1 else 0)) else (if n < 38 then (if n < 37 then 3 else 0) else (if n < 39 then 0 else (-1)))) else (if n < 44 then (if n < 42 then (if n < 41 then (-1) else 0) else (if n < 43 then 0 else (-1))) else (if n < 46 then (if n < 45 then 0 else 3) else (if n < 47 then 1 else 0)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 1 else 0) else (if n < 51 then 0 else 1)) else (if n < 54 then (if n < 53 then 0 else 1) else (if n < 55 then 3 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then 0 else 1) else (if n < 59 then 1 else 0)) else (if n < 62 then (if n < 61 then (-1) else 0) else (if n < 63 then 0 else 3)))))) else 0
theorem nestingEntries_eq435 (n : Nat) :
    nestingProjection435.numerator[n]! = nestingEntries435 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries435, if_neg (by omega : ¬ n < 64)]

def nestingProjection436 : Projection := ⟨4,6,#[3,0,0,1,0,-1,-1,0,0,3,-1,0,1,0,0,1,0,-1,3,0,1,0,0,1,1,0,0,3,0,1,1,0,0,1,1,0,3,0,0,-1,-1,0,0,1,0,3,-1,0,-1,0,0,1,0,-1,3,0,0,1,1,0,-1,0,0,3]⟩
theorem nestingLookup436 : projections[436]! = nestingProjection436 := by
  rw [projections_lookup]
  rfl
def nestingEntries436 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 0) else (if n < 3 then 0 else 1)) else (if n < 6 then (if n < 5 then 0 else (-1)) else (if n < 7 then (-1) else 0))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 3) else (if n < 11 then (-1) else 0)) else (if n < 14 then (if n < 13 then 1 else 0) else (if n < 15 then 0 else 1)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 0 else (-1)) else (if n < 19 then 3 else 0)) else (if n < 22 then (if n < 21 then 1 else 0) else (if n < 23 then 0 else 1))) else (if n < 28 then (if n < 26 then (if n < 25 then 1 else 0) else (if n < 27 then 0 else 3)) else (if n < 30 then (if n < 29 then 0 else 1) else (if n < 31 then 1 else 0))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 0 else 1) else (if n < 35 then 1 else 0)) else (if n < 38 then (if n < 37 then 3 else 0) else (if n < 39 then 0 else (-1)))) else (if n < 44 then (if n < 42 then (if n < 41 then (-1) else 0) else (if n < 43 then 0 else 1)) else (if n < 46 then (if n < 45 then 0 else 3) else (if n < 47 then (-1) else 0)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then (-1) else 0) else (if n < 51 then 0 else 1)) else (if n < 54 then (if n < 53 then 0 else (-1)) else (if n < 55 then 3 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then 0 else 1) else (if n < 59 then 1 else 0)) else (if n < 62 then (if n < 61 then (-1) else 0) else (if n < 63 then 0 else 3)))))) else 0
theorem nestingEntries_eq436 (n : Nat) :
    nestingProjection436.numerator[n]! = nestingEntries436 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries436, if_neg (by omega : ¬ n < 64)]

def nestingProjection437 : Projection := ⟨4,6,#[3,0,0,-1,0,-1,1,0,0,3,1,0,1,0,0,-1,0,1,3,0,-1,0,0,1,-1,0,0,3,0,-1,1,0,0,1,-1,0,3,0,0,1,-1,0,0,-1,0,3,1,0,1,0,0,1,0,1,3,0,0,-1,1,0,1,0,0,3]⟩
theorem nestingLookup437 : projections[437]! = nestingProjection437 := by
  rw [projections_lookup]
  rfl
def nestingEntries437 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 0) else (if n < 3 then 0 else (-1))) else (if n < 6 then (if n < 5 then 0 else (-1)) else (if n < 7 then 1 else 0))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 3) else (if n < 11 then 1 else 0)) else (if n < 14 then (if n < 13 then 1 else 0) else (if n < 15 then 0 else (-1))))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 0 else 1) else (if n < 19 then 3 else 0)) else (if n < 22 then (if n < 21 then (-1) else 0) else (if n < 23 then 0 else 1))) else (if n < 28 then (if n < 26 then (if n < 25 then (-1) else 0) else (if n < 27 then 0 else 3)) else (if n < 30 then (if n < 29 then 0 else (-1)) else (if n < 31 then 1 else 0))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 0 else 1) else (if n < 35 then (-1) else 0)) else (if n < 38 then (if n < 37 then 3 else 0) else (if n < 39 then 0 else 1))) else (if n < 44 then (if n < 42 then (if n < 41 then (-1) else 0) else (if n < 43 then 0 else (-1))) else (if n < 46 then (if n < 45 then 0 else 3) else (if n < 47 then 1 else 0)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 1 else 0) else (if n < 51 then 0 else 1)) else (if n < 54 then (if n < 53 then 0 else 1) else (if n < 55 then 3 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then 0 else (-1)) else (if n < 59 then 1 else 0)) else (if n < 62 then (if n < 61 then 1 else 0) else (if n < 63 then 0 else 3)))))) else 0
theorem nestingEntries_eq437 (n : Nat) :
    nestingProjection437.numerator[n]! = nestingEntries437 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries437, if_neg (by omega : ¬ n < 64)]

def nestingProjection438 : Projection := ⟨4,6,#[3,0,0,1,0,-1,-1,0,0,3,1,0,1,0,0,-1,0,1,3,0,-1,0,0,1,1,0,0,3,0,1,1,0,0,1,-1,0,3,0,0,1,-1,0,0,1,0,3,-1,0,-1,0,0,1,0,-1,3,0,0,-1,1,0,1,0,0,3]⟩
theorem nestingLookup438 : projections[438]! = nestingProjection438 := by
  rw [projections_lookup]
  rfl
def nestingEntries438 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 0) else (if n < 3 then 0 else 1)) else (if n < 6 then (if n < 5 then 0 else (-1)) else (if n < 7 then (-1) else 0))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 3) else (if n < 11 then 1 else 0)) else (if n < 14 then (if n < 13 then 1 else 0) else (if n < 15 then 0 else (-1))))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 0 else 1) else (if n < 19 then 3 else 0)) else (if n < 22 then (if n < 21 then (-1) else 0) else (if n < 23 then 0 else 1))) else (if n < 28 then (if n < 26 then (if n < 25 then 1 else 0) else (if n < 27 then 0 else 3)) else (if n < 30 then (if n < 29 then 0 else 1) else (if n < 31 then 1 else 0))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 0 else 1) else (if n < 35 then (-1) else 0)) else (if n < 38 then (if n < 37 then 3 else 0) else (if n < 39 then 0 else 1))) else (if n < 44 then (if n < 42 then (if n < 41 then (-1) else 0) else (if n < 43 then 0 else 1)) else (if n < 46 then (if n < 45 then 0 else 3) else (if n < 47 then (-1) else 0)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then (-1) else 0) else (if n < 51 then 0 else 1)) else (if n < 54 then (if n < 53 then 0 else (-1)) else (if n < 55 then 3 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then 0 else (-1)) else (if n < 59 then 1 else 0)) else (if n < 62 then (if n < 61 then 1 else 0) else (if n < 63 then 0 else 3)))))) else 0
theorem nestingEntries_eq438 (n : Nat) :
    nestingProjection438.numerator[n]! = nestingEntries438 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries438, if_neg (by omega : ¬ n < 64)]

def nestingProjection439 : Projection := ⟨2,6,#[1,0,0,0,0,-1,0,0,0,2,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,1,0,0,1,0,0,0,0,0,2,0,0,0,-1,0,0,0,0,1,0,0,0,0,0,1,0,0,1,0,0,0,0,0,0,0,0,2]⟩
theorem nestingLookup439 : projections[439]! = nestingProjection439 := by
  rw [projections_lookup]
  rfl
def nestingEntries439 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else 0) else (if n < 6 then (if n < 5 then 0 else (-1)) else 0)) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 2) else 0) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 2 else 0)) else 0) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 1)) else (if n < 30 then 0 else (if n < 31 then 1 else 0))))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 2 else 0) else 0)) else (if n < 44 then (if n < 42 then (if n < 41 then (-1) else 0) else 0) else (if n < 46 then (if n < 45 then 0 else 1) else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then 0 else (if n < 51 then 0 else 1)) else (if n < 54 then 0 else (if n < 55 then 1 else 0))) else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 2)))))) else 0
theorem nestingEntries_eq439 (n : Nat) :
    nestingProjection439.numerator[n]! = nestingEntries439 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries439, if_neg (by omega : ¬ n < 64)]

def nestingProjection440 : Projection := ⟨2,6,#[1,0,0,0,0,-1,0,0,0,1,0,0,1,0,0,0,0,0,2,0,0,0,0,0,0,0,0,2,0,0,0,0,0,1,0,0,1,0,0,0,-1,0,0,0,0,1,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,2]⟩
theorem nestingLookup440 : projections[440]! = nestingProjection440 := by
  rw [projections_lookup]
  rfl
def nestingEntries440 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else 0) else (if n < 6 then (if n < 5 then 0 else (-1)) else 0)) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else 0) else (if n < 14 then (if n < 13 then 1 else 0) else 0))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 2 else 0)) else 0) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 2)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 0 else 1) else 0) else (if n < 38 then (if n < 37 then 1 else 0) else 0)) else (if n < 44 then (if n < 42 then (if n < 41 then (-1) else 0) else 0) else (if n < 46 then (if n < 45 then 0 else 1) else 0))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 0 else (if n < 55 then 2 else 0))) else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 2)))))) else 0
theorem nestingEntries_eq440 (n : Nat) :
    nestingProjection440.numerator[n]! = nestingEntries440 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries440, if_neg (by omega : ¬ n < 64)]

def nestingProjection441 : Projection := ⟨4,6,#[3,-1,0,0,1,-1,0,0,-1,3,0,0,1,-1,0,0,0,0,3,-1,0,0,1,1,0,0,-1,3,0,0,1,1,1,1,0,0,3,1,0,0,-1,-1,0,0,1,3,0,0,0,0,1,1,0,0,3,-1,0,0,1,1,0,0,-1,3]⟩
theorem nestingLookup441 : projections[441]! = nestingProjection441 := by
  rw [projections_lookup]
  rfl
def nestingEntries441 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else (-1)) else 0) else (if n < 6 then (if n < 5 then 1 else (-1)) else 0)) else (if n < 12 then (if n < 10 then (if n < 9 then (-1) else 3) else 0) else (if n < 14 then (if n < 13 then 1 else (-1)) else 0))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 3 else (-1))) else (if n < 22 then 0 else 1)) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then (-1) else 3)) else (if n < 30 then 0 else 1)))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then 1 else 0) else (if n < 38 then (if n < 37 then 3 else 1) else 0)) else (if n < 44 then (if n < 42 then (-1) else 0) else (if n < 46 then (if n < 45 then 1 else 3) else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then 0 else 1) else (if n < 54 then 0 else (if n < 55 then 3 else (-1)))) else (if n < 60 then (if n < 58 then 0 else 1) else (if n < 62 then 0 else (if n < 63 then (-1) else 3)))))) else 0
theorem nestingEntries_eq441 (n : Nat) :
    nestingProjection441.numerator[n]! = nestingEntries441 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries441, if_neg (by omega : ¬ n < 64)]

def nestingProjection442 : Projection := ⟨4,6,#[3,-1,0,0,1,-1,0,0,-1,3,0,0,1,-1,0,0,0,0,3,1,0,0,-1,1,0,0,1,3,0,0,1,-1,1,1,0,0,3,1,0,0,-1,-1,0,0,1,3,0,0,0,0,-1,1,0,0,3,1,0,0,1,-1,0,0,1,3]⟩
theorem nestingLookup442 : projections[442]! = nestingProjection442 := by
  rw [projections_lookup]
  rfl
def nestingEntries442 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else (-1)) else 0) else (if n < 6 then (if n < 5 then 1 else (-1)) else 0)) else (if n < 12 then (if n < 10 then (if n < 9 then (-1) else 3) else 0) else (if n < 14 then (if n < 13 then 1 else (-1)) else 0))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 3 else 1)) else (if n < 22 then 0 else (if n < 23 then (-1) else 1))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 1 else 3)) else (if n < 30 then 0 else (if n < 31 then 1 else (-1)))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then 1 else 0) else (if n < 38 then (if n < 37 then 3 else 1) else 0)) else (if n < 44 then (if n < 42 then (-1) else 0) else (if n < 46 then (if n < 45 then 1 else 3) else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then 0 else (if n < 51 then (-1) else 1)) else (if n < 54 then 0 else (if n < 55 then 3 else 1))) else (if n < 60 then (if n < 58 then 0 else (if n < 59 then 1 else (-1))) else (if n < 62 then 0 else (if n < 63 then 1 else 3)))))) else 0
theorem nestingEntries_eq442 (n : Nat) :
    nestingProjection442.numerator[n]! = nestingEntries442 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries442, if_neg (by omega : ¬ n < 64)]

def nestingProjection443 : Projection := ⟨4,6,#[3,1,0,0,-1,-1,0,0,1,3,0,0,1,1,0,0,0,0,3,-1,0,0,1,1,0,0,-1,3,0,0,1,1,-1,1,0,0,3,-1,0,0,-1,1,0,0,-1,3,0,0,0,0,1,1,0,0,3,-1,0,0,1,1,0,0,-1,3]⟩
theorem nestingLookup443 : projections[443]! = nestingProjection443 := by
  rw [projections_lookup]
  rfl
def nestingEntries443 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 1) else 0) else (if n < 6 then (-1) else 0)) else (if n < 12 then (if n < 10 then (if n < 9 then 1 else 3) else 0) else (if n < 14 then 1 else 0))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 3 else (-1))) else (if n < 22 then 0 else 1)) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then (-1) else 3)) else (if n < 30 then 0 else 1)))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then (-1) else 1) else 0) else (if n < 38 then (if n < 37 then 3 else (-1)) else 0)) else (if n < 44 then (if n < 42 then (if n < 41 then (-1) else 1) else 0) else (if n < 46 then (if n < 45 then (-1) else 3) else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then 0 else 1) else (if n < 54 then 0 else (if n < 55 then 3 else (-1)))) else (if n < 60 then (if n < 58 then 0 else 1) else (if n < 62 then 0 else (if n < 63 then (-1) else 3)))))) else 0
theorem nestingEntries_eq443 (n : Nat) :
    nestingProjection443.numerator[n]! = nestingEntries443 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries443, if_neg (by omega : ¬ n < 64)]

def nestingProjection444 : Projection := ⟨4,6,#[3,1,0,0,-1,-1,0,0,1,3,0,0,1,1,0,0,0,0,3,1,0,0,-1,1,0,0,1,3,0,0,1,-1,-1,1,0,0,3,-1,0,0,-1,1,0,0,-1,3,0,0,0,0,-1,1,0,0,3,1,0,0,1,-1,0,0,1,3]⟩
theorem nestingLookup444 : projections[444]! = nestingProjection444 := by
  rw [projections_lookup]
  rfl
def nestingEntries444 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 1) else 0) else (if n < 6 then (-1) else 0)) else (if n < 12 then (if n < 10 then (if n < 9 then 1 else 3) else 0) else (if n < 14 then 1 else 0))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 3 else 1)) else (if n < 22 then 0 else (if n < 23 then (-1) else 1))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 1 else 3)) else (if n < 30 then 0 else (if n < 31 then 1 else (-1)))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then (-1) else 1) else 0) else (if n < 38 then (if n < 37 then 3 else (-1)) else 0)) else (if n < 44 then (if n < 42 then (if n < 41 then (-1) else 1) else 0) else (if n < 46 then (if n < 45 then (-1) else 3) else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then 0 else (if n < 51 then (-1) else 1)) else (if n < 54 then 0 else (if n < 55 then 3 else 1))) else (if n < 60 then (if n < 58 then 0 else (if n < 59 then 1 else (-1))) else (if n < 62 then 0 else (if n < 63 then 1 else 3)))))) else 0
theorem nestingEntries_eq444 (n : Nat) :
    nestingProjection444.numerator[n]! = nestingEntries444 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries444, if_neg (by omega : ¬ n < 64)]

def nestingProjection445 : Projection := ⟨2,6,#[2,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,1,0,0,0,0,1,0,0,0,1,0,0,1,0,0,0,0,0,2,0,0,0,0,0,0,0,0,2,0,0,0,0,0,1,0,0,1,0,0,0,1,0,0,0,0,1]⟩
theorem nestingLookup445 : projections[445]! = nestingProjection445 := by
  rw [projections_lookup]
  rfl
def nestingEntries445 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 2 else 0) else 0) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 2) else 0) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 1 else 0)) else (if n < 22 then 0 else (if n < 23 then 0 else 1))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 1)) else (if n < 30 then 0 else (if n < 31 then 1 else 0))))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 2 else 0) else 0)) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 2) else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then 0 else (if n < 51 then 0 else 1)) else (if n < 54 then 0 else (if n < 55 then 1 else 0))) else (if n < 60 then (if n < 58 then 0 else (if n < 59 then 1 else 0)) else (if n < 62 then 0 else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq445 (n : Nat) :
    nestingProjection445.numerator[n]! = nestingEntries445 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries445, if_neg (by omega : ¬ n < 64)]

def nestingProjection446 : Projection := ⟨2,6,#[1,0,0,0,0,-1,0,0,0,2,0,0,0,0,0,0,0,0,1,0,0,0,0,1,0,0,0,2,0,0,0,0,0,0,0,0,2,0,0,0,-1,0,0,0,0,1,0,0,0,0,0,0,0,0,2,0,0,0,1,0,0,0,0,1]⟩
theorem nestingLookup446 : projections[446]! = nestingProjection446 := by
  rw [projections_lookup]
  rfl
def nestingEntries446 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else 0) else (if n < 6 then (if n < 5 then 0 else (-1)) else 0)) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 2) else 0) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 1 else 0)) else (if n < 22 then 0 else (if n < 23 then 0 else 1))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 2)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 2 else 0) else 0)) else (if n < 44 then (if n < 42 then (if n < 41 then (-1) else 0) else 0) else (if n < 46 then (if n < 45 then 0 else 1) else 0))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 0 else (if n < 55 then 2 else 0))) else (if n < 60 then (if n < 58 then 0 else (if n < 59 then 1 else 0)) else (if n < 62 then 0 else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq446 (n : Nat) :
    nestingProjection446.numerator[n]! = nestingEntries446 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries446, if_neg (by omega : ¬ n < 64)]

def nestingProjection447 : Projection := ⟨4,6,#[3,0,-1,0,0,-1,0,1,0,3,0,-1,1,0,1,0,-1,0,3,0,0,-1,0,1,0,-1,0,3,1,0,1,0,0,1,0,1,3,0,-1,0,-1,0,-1,0,0,3,0,1,0,1,0,1,-1,0,3,0,1,0,1,0,0,1,0,3]⟩
theorem nestingLookup447 : projections[447]! = nestingProjection447 := by
  rw [projections_lookup]
  rfl
def nestingEntries447 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 0) else (if n < 3 then (-1) else 0)) else (if n < 6 then (if n < 5 then 0 else (-1)) else (if n < 7 then 0 else 1))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 3) else (if n < 11 then 0 else (-1))) else (if n < 14 then (if n < 13 then 1 else 0) else (if n < 15 then 1 else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then (-1) else 0) else (if n < 19 then 3 else 0)) else (if n < 22 then (if n < 21 then 0 else (-1)) else (if n < 23 then 0 else 1))) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else (-1)) else (if n < 27 then 0 else 3)) else (if n < 30 then (if n < 29 then 1 else 0) else (if n < 31 then 1 else 0))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 0 else 1) else (if n < 35 then 0 else 1)) else (if n < 38 then (if n < 37 then 3 else 0) else (if n < 39 then (-1) else 0))) else (if n < 44 then (if n < 42 then (if n < 41 then (-1) else 0) else (if n < 43 then (-1) else 0)) else (if n < 46 then (if n < 45 then 0 else 3) else (if n < 47 then 0 else 1)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else 1) else (if n < 51 then 0 else 1)) else (if n < 54 then (if n < 53 then (-1) else 0) else (if n < 55 then 3 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then 1 else 0) else (if n < 59 then 1 else 0)) else (if n < 62 then (if n < 61 then 0 else 1) else (if n < 63 then 0 else 3)))))) else 0
theorem nestingEntries_eq447 (n : Nat) :
    nestingProjection447.numerator[n]! = nestingEntries447 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries447, if_neg (by omega : ¬ n < 64)]

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def nestingProjection448 : Projection := ⟨4,6,#[3,0,-1,0,0,-1,0,1,0,3,0,1,1,0,-1,0,-1,0,3,0,0,-1,0,1,0,1,0,3,-1,0,1,0,0,1,0,-1,3,0,1,0,-1,0,-1,0,0,3,0,1,0,-1,0,1,1,0,3,0,1,0,1,0,0,1,0,3]⟩
theorem nestingLookup448 : projections[448]! = nestingProjection448 := by
  rw [projections_lookup]
  rfl
def nestingEntries448 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 0) else (if n < 3 then (-1) else 0)) else (if n < 6 then (if n < 5 then 0 else (-1)) else (if n < 7 then 0 else 1))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 3) else (if n < 11 then 0 else 1)) else (if n < 14 then (if n < 13 then 1 else 0) else (if n < 15 then (-1) else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then (-1) else 0) else (if n < 19 then 3 else 0)) else (if n < 22 then (if n < 21 then 0 else (-1)) else (if n < 23 then 0 else 1))) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else 1) else (if n < 27 then 0 else 3)) else (if n < 30 then (if n < 29 then (-1) else 0) else (if n < 31 then 1 else 0))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 0 else 1) else (if n < 35 then 0 else (-1))) else (if n < 38 then (if n < 37 then 3 else 0) else (if n < 39 then 1 else 0))) else (if n < 44 then (if n < 42 then (if n < 41 then (-1) else 0) else (if n < 43 then (-1) else 0)) else (if n < 46 then (if n < 45 then 0 else 3) else (if n < 47 then 0 else 1)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else (-1)) else (if n < 51 then 0 else 1)) else (if n < 54 then (if n < 53 then 1 else 0) else (if n < 55 then 3 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then 1 else 0) else (if n < 59 then 1 else 0)) else (if n < 62 then (if n < 61 then 0 else 1) else (if n < 63 then 0 else 3)))))) else 0
theorem nestingEntries_eq448 (n : Nat) :
    nestingProjection448.numerator[n]! = nestingEntries448 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries448, if_neg (by omega : ¬ n < 64)]

def nestingProjection449 : Projection := ⟨4,6,#[3,0,1,0,0,-1,0,-1,0,3,0,-1,1,0,1,0,1,0,3,0,0,1,0,1,0,-1,0,3,1,0,1,0,0,1,0,1,3,0,-1,0,-1,0,1,0,0,3,0,-1,0,1,0,1,-1,0,3,0,-1,0,1,0,0,-1,0,3]⟩
theorem nestingLookup449 : projections[449]! = nestingProjection449 := by
  rw [projections_lookup]
  rfl
def nestingEntries449 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 0) else (if n < 3 then 1 else 0)) else (if n < 6 then (if n < 5 then 0 else (-1)) else (if n < 7 then 0 else (-1)))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 3) else (if n < 11 then 0 else (-1))) else (if n < 14 then (if n < 13 then 1 else 0) else (if n < 15 then 1 else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 1 else 0) else (if n < 19 then 3 else 0)) else (if n < 22 then (if n < 21 then 0 else 1) else (if n < 23 then 0 else 1))) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else (-1)) else (if n < 27 then 0 else 3)) else (if n < 30 then (if n < 29 then 1 else 0) else (if n < 31 then 1 else 0))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 0 else 1) else (if n < 35 then 0 else 1)) else (if n < 38 then (if n < 37 then 3 else 0) else (if n < 39 then (-1) else 0))) else (if n < 44 then (if n < 42 then (if n < 41 then (-1) else 0) else (if n < 43 then 1 else 0)) else (if n < 46 then (if n < 45 then 0 else 3) else (if n < 47 then 0 else (-1))))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else 1) else (if n < 51 then 0 else 1)) else (if n < 54 then (if n < 53 then (-1) else 0) else (if n < 55 then 3 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then (-1) else 0) else (if n < 59 then 1 else 0)) else (if n < 62 then (if n < 61 then 0 else (-1)) else (if n < 63 then 0 else 3)))))) else 0
theorem nestingEntries_eq449 (n : Nat) :
    nestingProjection449.numerator[n]! = nestingEntries449 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries449, if_neg (by omega : ¬ n < 64)]

def nestingProjection450 : Projection := ⟨4,6,#[3,0,1,0,0,-1,0,-1,0,3,0,1,1,0,-1,0,1,0,3,0,0,1,0,1,0,1,0,3,-1,0,1,0,0,1,0,-1,3,0,1,0,-1,0,1,0,0,3,0,-1,0,-1,0,1,1,0,3,0,-1,0,1,0,0,-1,0,3]⟩
theorem nestingLookup450 : projections[450]! = nestingProjection450 := by
  rw [projections_lookup]
  rfl
def nestingEntries450 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 0) else (if n < 3 then 1 else 0)) else (if n < 6 then (if n < 5 then 0 else (-1)) else (if n < 7 then 0 else (-1)))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 3) else (if n < 11 then 0 else 1)) else (if n < 14 then (if n < 13 then 1 else 0) else (if n < 15 then (-1) else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 1 else 0) else (if n < 19 then 3 else 0)) else (if n < 22 then (if n < 21 then 0 else 1) else (if n < 23 then 0 else 1))) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else 1) else (if n < 27 then 0 else 3)) else (if n < 30 then (if n < 29 then (-1) else 0) else (if n < 31 then 1 else 0))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 0 else 1) else (if n < 35 then 0 else (-1))) else (if n < 38 then (if n < 37 then 3 else 0) else (if n < 39 then 1 else 0))) else (if n < 44 then (if n < 42 then (if n < 41 then (-1) else 0) else (if n < 43 then 1 else 0)) else (if n < 46 then (if n < 45 then 0 else 3) else (if n < 47 then 0 else (-1))))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else (-1)) else (if n < 51 then 0 else 1)) else (if n < 54 then (if n < 53 then 1 else 0) else (if n < 55 then 3 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then (-1) else 0) else (if n < 59 then 1 else 0)) else (if n < 62 then (if n < 61 then 0 else (-1)) else (if n < 63 then 0 else 3)))))) else 0
theorem nestingEntries_eq450 (n : Nat) :
    nestingProjection450.numerator[n]! = nestingEntries450 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries450, if_neg (by omega : ¬ n < 64)]

def nestingProjection451 : Projection := ⟨2,6,#[2,0,0,0,0,0,0,0,0,1,0,0,1,0,0,0,0,0,2,0,0,0,0,0,0,0,0,1,0,0,1,0,0,1,0,0,1,0,0,0,0,0,0,0,0,2,0,0,0,0,0,1,0,0,1,0,0,0,0,0,0,0,0,2]⟩
theorem nestingLookup451 : projections[451]! = nestingProjection451 := by
  rw [projections_lookup]
  rfl
def nestingEntries451 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 2 else 0) else 0) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else 0) else (if n < 14 then (if n < 13 then 1 else 0) else 0))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 2 else 0)) else 0) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 1)) else (if n < 30 then 0 else (if n < 31 then 1 else 0))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 0 else 1) else 0) else (if n < 38 then (if n < 37 then 1 else 0) else 0)) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 2) else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then 0 else (if n < 51 then 0 else 1)) else (if n < 54 then 0 else (if n < 55 then 1 else 0))) else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 2)))))) else 0
theorem nestingEntries_eq451 (n : Nat) :
    nestingProjection451.numerator[n]! = nestingEntries451 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries451, if_neg (by omega : ¬ n < 64)]

def nestingProjection452 : Projection := ⟨1,6,#[1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0]⟩
theorem nestingLookup452 : projections[452]! = nestingProjection452 := by
  rw [projections_lookup]
  rfl
def nestingEntries452 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else 0) else 0) else 0) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 1 else 0)) else 0) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 1)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 1 else 0) else 0)) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 1) else 0))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 0 else (if n < 55 then 1 else 0))) else 0))) else 0
theorem nestingEntries_eq452 (n : Nat) :
    nestingProjection452.numerator[n]! = nestingEntries452 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries452, if_neg (by omega : ¬ n < 64)]

def nestingProjection453 : Projection := ⟨4,6,#[3,0,0,-1,0,1,1,0,0,0,0,0,0,0,0,0,0,0,4,0,0,0,0,0,-1,0,0,3,0,1,1,0,0,0,0,0,4,0,0,0,1,0,0,1,0,3,-1,0,1,0,0,1,0,-1,3,0,0,0,0,0,0,0,0,4]⟩
theorem nestingLookup453 : projections[453]! = nestingProjection453 := by
  rw [projections_lookup]
  rfl
def nestingEntries453 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 0) else (if n < 3 then 0 else (-1))) else (if n < 6 then (if n < 5 then 0 else 1) else (if n < 7 then 1 else 0))) else 0) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 4 else 0)) else 0) else (if n < 28 then (if n < 26 then (if n < 25 then (-1) else 0) else (if n < 27 then 0 else 3)) else (if n < 30 then (if n < 29 then 0 else 1) else (if n < 31 then 1 else 0))))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 4 else 0) else 0)) else (if n < 44 then (if n < 42 then (if n < 41 then 1 else 0) else (if n < 43 then 0 else 1)) else (if n < 46 then (if n < 45 then 0 else 3) else (if n < 47 then (-1) else 0)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 1 else 0) else (if n < 51 then 0 else 1)) else (if n < 54 then (if n < 53 then 0 else (-1)) else (if n < 55 then 3 else 0))) else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 4)))))) else 0
theorem nestingEntries_eq453 (n : Nat) :
    nestingProjection453.numerator[n]! = nestingEntries453 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries453, if_neg (by omega : ¬ n < 64)]

def nestingProjection454 : Projection := ⟨4,6,#[3,0,0,1,0,-1,1,0,0,0,0,0,0,0,0,0,0,0,4,0,0,0,0,0,1,0,0,3,0,1,-1,0,0,0,0,0,4,0,0,0,-1,0,0,1,0,3,1,0,1,0,0,-1,0,1,3,0,0,0,0,0,0,0,0,4]⟩
theorem nestingLookup454 : projections[454]! = nestingProjection454 := by
  rw [projections_lookup]
  rfl
def nestingEntries454 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 0) else (if n < 3 then 0 else 1)) else (if n < 6 then (if n < 5 then 0 else (-1)) else (if n < 7 then 1 else 0))) else 0) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 4 else 0)) else 0) else (if n < 28 then (if n < 26 then (if n < 25 then 1 else 0) else (if n < 27 then 0 else 3)) else (if n < 30 then (if n < 29 then 0 else 1) else (if n < 31 then (-1) else 0))))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 4 else 0) else 0)) else (if n < 44 then (if n < 42 then (if n < 41 then (-1) else 0) else (if n < 43 then 0 else 1)) else (if n < 46 then (if n < 45 then 0 else 3) else (if n < 47 then 1 else 0)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 1 else 0) else (if n < 51 then 0 else (-1))) else (if n < 54 then (if n < 53 then 0 else 1) else (if n < 55 then 3 else 0))) else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 4)))))) else 0
theorem nestingEntries_eq454 (n : Nat) :
    nestingProjection454.numerator[n]! = nestingEntries454 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries454, if_neg (by omega : ¬ n < 64)]

def nestingProjection455 : Projection := ⟨4,6,#[3,0,0,-1,0,1,1,0,0,4,0,0,0,0,0,0,0,0,4,0,0,0,0,0,-1,0,0,3,0,1,1,0,0,0,0,0,4,0,0,0,1,0,0,1,0,3,-1,0,1,0,0,1,0,-1,3,0,0,0,0,0,0,0,0,0]⟩
theorem nestingLookup455 : projections[455]! = nestingProjection455 := by
  rw [projections_lookup]
  rfl
def nestingEntries455 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 0) else (if n < 3 then 0 else (-1))) else (if n < 6 then (if n < 5 then 0 else 1) else (if n < 7 then 1 else 0))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 4) else 0) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 4 else 0)) else 0) else (if n < 28 then (if n < 26 then (if n < 25 then (-1) else 0) else (if n < 27 then 0 else 3)) else (if n < 30 then (if n < 29 then 0 else 1) else (if n < 31 then 1 else 0))))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 4 else 0) else 0)) else (if n < 44 then (if n < 42 then (if n < 41 then 1 else 0) else (if n < 43 then 0 else 1)) else (if n < 46 then (if n < 45 then 0 else 3) else (if n < 47 then (-1) else 0)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 1 else 0) else (if n < 51 then 0 else 1)) else (if n < 54 then (if n < 53 then 0 else (-1)) else (if n < 55 then 3 else 0))) else 0))) else 0
theorem nestingEntries_eq455 (n : Nat) :
    nestingProjection455.numerator[n]! = nestingEntries455 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries455, if_neg (by omega : ¬ n < 64)]

def nestingProjection456 : Projection := ⟨4,6,#[3,0,0,1,0,-1,1,0,0,4,0,0,0,0,0,0,0,0,4,0,0,0,0,0,1,0,0,3,0,1,-1,0,0,0,0,0,4,0,0,0,-1,0,0,1,0,3,1,0,1,0,0,-1,0,1,3,0,0,0,0,0,0,0,0,0]⟩
theorem nestingLookup456 : projections[456]! = nestingProjection456 := by
  rw [projections_lookup]
  rfl
def nestingEntries456 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 0) else (if n < 3 then 0 else 1)) else (if n < 6 then (if n < 5 then 0 else (-1)) else (if n < 7 then 1 else 0))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 4) else 0) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 4 else 0)) else 0) else (if n < 28 then (if n < 26 then (if n < 25 then 1 else 0) else (if n < 27 then 0 else 3)) else (if n < 30 then (if n < 29 then 0 else 1) else (if n < 31 then (-1) else 0))))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 4 else 0) else 0)) else (if n < 44 then (if n < 42 then (if n < 41 then (-1) else 0) else (if n < 43 then 0 else 1)) else (if n < 46 then (if n < 45 then 0 else 3) else (if n < 47 then 1 else 0)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 1 else 0) else (if n < 51 then 0 else (-1))) else (if n < 54 then (if n < 53 then 0 else 1) else (if n < 55 then 3 else 0))) else 0))) else 0
theorem nestingEntries_eq456 (n : Nat) :
    nestingProjection456.numerator[n]! = nestingEntries456 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries456, if_neg (by omega : ¬ n < 64)]

def nestingProjection457 : Projection := ⟨2,6,#[1,0,0,0,0,0,1,0,0,2,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,1,0,1,0,0,0,0,0,0,2,0,0,0,0,0,0,1,0,1,0,0,1,0,0,0,0,0,1,0,0,0,0,0,0,0,0,2]⟩
theorem nestingLookup457 : projections[457]! = nestingProjection457 := by
  rw [projections_lookup]
  rfl
def nestingEntries457 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else 0) else (if n < 6 then 0 else (if n < 7 then 1 else 0))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 2) else 0) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 2 else 0)) else 0) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 1)) else (if n < 30 then (if n < 29 then 0 else 1) else 0)))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 2 else 0) else 0)) else (if n < 44 then (if n < 42 then 0 else (if n < 43 then 0 else 1)) else (if n < 46 then (if n < 45 then 0 else 1) else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 1 else 0) else 0) else (if n < 54 then 0 else (if n < 55 then 1 else 0))) else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 2)))))) else 0
theorem nestingEntries_eq457 (n : Nat) :
    nestingProjection457.numerator[n]! = nestingEntries457 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries457, if_neg (by omega : ¬ n < 64)]

def nestingProjection458 : Projection := ⟨2,6,#[1,0,0,0,0,0,1,0,0,1,0,0,0,0,0,-1,0,0,2,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,2,0,0,1,0,0,0,0,0,1,0,0,-1,0,0,0,0,0,1]⟩
theorem nestingLookup458 : projections[458]! = nestingProjection458 := by
  rw [projections_lookup]
  rfl
def nestingEntries458 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else 0) else (if n < 6 then 0 else (if n < 7 then 1 else 0))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else 0) else (if n < 14 then 0 else (if n < 15 then 0 else (-1))))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 2 else 0)) else 0) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 2)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 2 else 0) else 0)) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 2) else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 1 else 0) else 0) else (if n < 54 then 0 else (if n < 55 then 1 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then 0 else (-1)) else 0) else (if n < 62 then 0 else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq458 (n : Nat) :
    nestingProjection458.numerator[n]! = nestingEntries458 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries458, if_neg (by omega : ¬ n < 64)]

def nestingProjection459 : Projection := ⟨4,6,#[3,-1,0,0,0,0,1,-1,-1,2,0,-1,0,1,1,0,0,0,4,0,0,0,0,0,0,-1,0,3,0,1,0,1,0,0,0,0,4,0,0,0,0,1,0,1,0,3,0,-1,1,1,0,0,0,0,3,1,-1,0,0,1,0,-1,1,2]⟩
theorem nestingLookup459 : projections[459]! = nestingProjection459 := by
  rw [projections_lookup]
  rfl
def nestingEntries459 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else (-1)) else 0) else (if n < 6 then 0 else (if n < 7 then 1 else (-1)))) else (if n < 12 then (if n < 10 then (if n < 9 then (-1) else 2) else (if n < 11 then 0 else (-1))) else (if n < 14 then (if n < 13 then 0 else 1) else (if n < 15 then 1 else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 4 else 0)) else 0) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else (-1)) else (if n < 27 then 0 else 3)) else (if n < 30 then (if n < 29 then 0 else 1) else (if n < 31 then 0 else 1))))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 4 else 0) else 0)) else (if n < 44 then (if n < 42 then (if n < 41 then 0 else 1) else (if n < 43 then 0 else 1)) else (if n < 46 then (if n < 45 then 0 else 3) else (if n < 47 then 0 else (-1))))) else (if n < 56 then (if n < 52 then (if n < 50 then 1 else 0) else (if n < 54 then 0 else (if n < 55 then 3 else 1))) else (if n < 60 then (if n < 58 then (if n < 57 then (-1) else 0) else (if n < 59 then 0 else 1)) else (if n < 62 then (if n < 61 then 0 else (-1)) else (if n < 63 then 1 else 2)))))) else 0
theorem nestingEntries_eq459 (n : Nat) :
    nestingProjection459.numerator[n]! = nestingEntries459 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries459, if_neg (by omega : ¬ n < 64)]

def nestingProjection460 : Projection := ⟨4,6,#[3,-1,0,0,0,0,1,-1,-1,2,0,1,0,-1,1,0,0,0,4,0,0,0,0,0,0,1,0,3,0,1,0,-1,0,0,0,0,4,0,0,0,0,-1,0,1,0,3,0,1,1,1,0,0,0,0,3,1,-1,0,0,-1,0,1,1,2]⟩
theorem nestingLookup460 : projections[460]! = nestingProjection460 := by
  rw [projections_lookup]
  rfl
def nestingEntries460 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else (-1)) else 0) else (if n < 6 then 0 else (if n < 7 then 1 else (-1)))) else (if n < 12 then (if n < 10 then (if n < 9 then (-1) else 2) else (if n < 11 then 0 else 1)) else (if n < 14 then (if n < 13 then 0 else (-1)) else (if n < 15 then 1 else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 4 else 0)) else 0) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else 1) else (if n < 27 then 0 else 3)) else (if n < 30 then (if n < 29 then 0 else 1) else (if n < 31 then 0 else (-1)))))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 4 else 0) else 0)) else (if n < 44 then (if n < 42 then (if n < 41 then 0 else (-1)) else (if n < 43 then 0 else 1)) else (if n < 46 then (if n < 45 then 0 else 3) else (if n < 47 then 0 else 1)))) else (if n < 56 then (if n < 52 then (if n < 50 then 1 else 0) else (if n < 54 then 0 else (if n < 55 then 3 else 1))) else (if n < 60 then (if n < 58 then (if n < 57 then (-1) else 0) else (if n < 59 then 0 else (-1))) else (if n < 62 then (if n < 61 then 0 else 1) else (if n < 63 then 1 else 2)))))) else 0
theorem nestingEntries_eq460 (n : Nat) :
    nestingProjection460.numerator[n]! = nestingEntries460 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries460, if_neg (by omega : ¬ n < 64)]

def nestingProjection461 : Projection := ⟨4,6,#[3,1,0,0,0,0,1,1,1,2,0,-1,0,1,-1,0,0,0,4,0,0,0,0,0,0,-1,0,3,0,1,0,1,0,0,0,0,4,0,0,0,0,1,0,1,0,3,0,-1,1,-1,0,0,0,0,3,-1,1,0,0,1,0,-1,-1,2]⟩
theorem nestingLookup461 : projections[461]! = nestingProjection461 := by
  rw [projections_lookup]
  rfl
def nestingEntries461 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 1) else 0) else (if n < 6 then 0 else 1)) else (if n < 12 then (if n < 10 then (if n < 9 then 1 else 2) else (if n < 11 then 0 else (-1))) else (if n < 14 then (if n < 13 then 0 else 1) else (if n < 15 then (-1) else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 4 else 0)) else 0) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else (-1)) else (if n < 27 then 0 else 3)) else (if n < 30 then (if n < 29 then 0 else 1) else (if n < 31 then 0 else 1))))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 4 else 0) else 0)) else (if n < 44 then (if n < 42 then (if n < 41 then 0 else 1) else (if n < 43 then 0 else 1)) else (if n < 46 then (if n < 45 then 0 else 3) else (if n < 47 then 0 else (-1))))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 1 else (-1)) else 0) else (if n < 54 then 0 else (if n < 55 then 3 else (-1)))) else (if n < 60 then (if n < 58 then (if n < 57 then 1 else 0) else (if n < 59 then 0 else 1)) else (if n < 62 then (if n < 61 then 0 else (-1)) else (if n < 63 then (-1) else 2)))))) else 0
theorem nestingEntries_eq461 (n : Nat) :
    nestingProjection461.numerator[n]! = nestingEntries461 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries461, if_neg (by omega : ¬ n < 64)]

def nestingProjection462 : Projection := ⟨4,6,#[3,1,0,0,0,0,1,1,1,2,0,1,0,-1,-1,0,0,0,4,0,0,0,0,0,0,1,0,3,0,1,0,-1,0,0,0,0,4,0,0,0,0,-1,0,1,0,3,0,1,1,-1,0,0,0,0,3,-1,1,0,0,-1,0,1,-1,2]⟩
theorem nestingLookup462 : projections[462]! = nestingProjection462 := by
  rw [projections_lookup]
  rfl
def nestingEntries462 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 1) else 0) else (if n < 6 then 0 else 1)) else (if n < 12 then (if n < 10 then (if n < 9 then 1 else 2) else (if n < 11 then 0 else 1)) else (if n < 14 then (if n < 13 then 0 else (-1)) else (if n < 15 then (-1) else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 4 else 0)) else 0) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else 1) else (if n < 27 then 0 else 3)) else (if n < 30 then (if n < 29 then 0 else 1) else (if n < 31 then 0 else (-1)))))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 4 else 0) else 0)) else (if n < 44 then (if n < 42 then (if n < 41 then 0 else (-1)) else (if n < 43 then 0 else 1)) else (if n < 46 then (if n < 45 then 0 else 3) else (if n < 47 then 0 else 1)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 1 else (-1)) else 0) else (if n < 54 then 0 else (if n < 55 then 3 else (-1)))) else (if n < 60 then (if n < 58 then (if n < 57 then 1 else 0) else (if n < 59 then 0 else (-1))) else (if n < 62 then (if n < 61 then 0 else 1) else (if n < 63 then (-1) else 2)))))) else 0
theorem nestingEntries_eq462 (n : Nat) :
    nestingProjection462.numerator[n]! = nestingEntries462 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries462, if_neg (by omega : ¬ n < 64)]

def nestingProjection463 : Projection := ⟨2,6,#[2,0,0,0,0,0,0,0,0,1,0,0,0,0,0,1,0,0,2,0,0,0,0,0,0,0,0,1,0,1,0,0,0,0,0,0,2,0,0,0,0,0,0,1,0,1,0,0,0,0,0,0,0,0,2,0,0,1,0,0,0,0,0,1]⟩
theorem nestingLookup463 : projections[463]! = nestingProjection463 := by
  rw [projections_lookup]
  rfl
def nestingEntries463 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 2 else 0) else 0) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else 0) else (if n < 14 then 0 else (if n < 15 then 0 else 1)))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 2 else 0)) else 0) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 1)) else (if n < 30 then (if n < 29 then 0 else 1) else 0)))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 2 else 0) else 0)) else (if n < 44 then (if n < 42 then 0 else (if n < 43 then 0 else 1)) else (if n < 46 then (if n < 45 then 0 else 1) else 0))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 0 else (if n < 55 then 2 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then 0 else 1) else 0) else (if n < 62 then 0 else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq463 (n : Nat) :
    nestingProjection463.numerator[n]! = nestingEntries463 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries463, if_neg (by omega : ¬ n < 64)]

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def nestingProjection464 : Projection := ⟨2,6,#[1,0,0,0,0,0,1,0,0,1,0,0,0,0,0,1,0,0,2,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,2,0,0,1,0,0,0,0,0,1,0,0,1,0,0,0,0,0,1]⟩
theorem nestingLookup464 : projections[464]! = nestingProjection464 := by
  rw [projections_lookup]
  rfl
def nestingEntries464 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else 0) else (if n < 6 then 0 else (if n < 7 then 1 else 0))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else 0) else (if n < 14 then 0 else (if n < 15 then 0 else 1)))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 2 else 0)) else 0) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 2)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 2 else 0) else 0)) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 2) else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 1 else 0) else 0) else (if n < 54 then 0 else (if n < 55 then 1 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then 0 else 1) else 0) else (if n < 62 then 0 else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq464 (n : Nat) :
    nestingProjection464.numerator[n]! = nestingEntries464 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries464, if_neg (by omega : ¬ n < 64)]

def nestingProjection465 : Projection := ⟨4,6,#[3,-1,0,0,0,0,1,1,-1,2,0,-1,0,1,1,0,0,0,4,0,0,0,0,0,0,-1,0,3,0,1,0,-1,0,0,0,0,4,0,0,0,0,1,0,1,0,3,0,1,1,1,0,0,0,0,3,-1,1,0,0,-1,0,1,-1,2]⟩
theorem nestingLookup465 : projections[465]! = nestingProjection465 := by
  rw [projections_lookup]
  rfl
def nestingEntries465 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else (-1)) else 0) else (if n < 6 then 0 else 1)) else (if n < 12 then (if n < 10 then (if n < 9 then (-1) else 2) else (if n < 11 then 0 else (-1))) else (if n < 14 then (if n < 13 then 0 else 1) else (if n < 15 then 1 else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 4 else 0)) else 0) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else (-1)) else (if n < 27 then 0 else 3)) else (if n < 30 then (if n < 29 then 0 else 1) else (if n < 31 then 0 else (-1)))))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 4 else 0) else 0)) else (if n < 44 then (if n < 42 then (if n < 41 then 0 else 1) else (if n < 43 then 0 else 1)) else (if n < 46 then (if n < 45 then 0 else 3) else (if n < 47 then 0 else 1)))) else (if n < 56 then (if n < 52 then (if n < 50 then 1 else 0) else (if n < 54 then 0 else (if n < 55 then 3 else (-1)))) else (if n < 60 then (if n < 58 then (if n < 57 then 1 else 0) else (if n < 59 then 0 else (-1))) else (if n < 62 then (if n < 61 then 0 else 1) else (if n < 63 then (-1) else 2)))))) else 0
theorem nestingEntries_eq465 (n : Nat) :
    nestingProjection465.numerator[n]! = nestingEntries465 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries465, if_neg (by omega : ¬ n < 64)]

def nestingProjection466 : Projection := ⟨4,6,#[3,-1,0,0,0,0,1,1,-1,2,0,1,0,-1,1,0,0,0,4,0,0,0,0,0,0,1,0,3,0,1,0,1,0,0,0,0,4,0,0,0,0,-1,0,1,0,3,0,-1,1,1,0,0,0,0,3,-1,1,0,0,1,0,-1,-1,2]⟩
theorem nestingLookup466 : projections[466]! = nestingProjection466 := by
  rw [projections_lookup]
  rfl
def nestingEntries466 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else (-1)) else 0) else (if n < 6 then 0 else 1)) else (if n < 12 then (if n < 10 then (if n < 9 then (-1) else 2) else (if n < 11 then 0 else 1)) else (if n < 14 then (if n < 13 then 0 else (-1)) else (if n < 15 then 1 else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 4 else 0)) else 0) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else 1) else (if n < 27 then 0 else 3)) else (if n < 30 then (if n < 29 then 0 else 1) else (if n < 31 then 0 else 1))))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 4 else 0) else 0)) else (if n < 44 then (if n < 42 then (if n < 41 then 0 else (-1)) else (if n < 43 then 0 else 1)) else (if n < 46 then (if n < 45 then 0 else 3) else (if n < 47 then 0 else (-1))))) else (if n < 56 then (if n < 52 then (if n < 50 then 1 else 0) else (if n < 54 then 0 else (if n < 55 then 3 else (-1)))) else (if n < 60 then (if n < 58 then (if n < 57 then 1 else 0) else (if n < 59 then 0 else 1)) else (if n < 62 then (if n < 61 then 0 else (-1)) else (if n < 63 then (-1) else 2)))))) else 0
theorem nestingEntries_eq466 (n : Nat) :
    nestingProjection466.numerator[n]! = nestingEntries466 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries466, if_neg (by omega : ¬ n < 64)]

def nestingProjection467 : Projection := ⟨4,6,#[3,1,0,0,0,0,1,-1,1,2,0,-1,0,1,-1,0,0,0,4,0,0,0,0,0,0,-1,0,3,0,1,0,-1,0,0,0,0,4,0,0,0,0,1,0,1,0,3,0,1,1,-1,0,0,0,0,3,1,-1,0,0,-1,0,1,1,2]⟩
theorem nestingLookup467 : projections[467]! = nestingProjection467 := by
  rw [projections_lookup]
  rfl
def nestingEntries467 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 1) else 0) else (if n < 6 then 0 else (if n < 7 then 1 else (-1)))) else (if n < 12 then (if n < 10 then (if n < 9 then 1 else 2) else (if n < 11 then 0 else (-1))) else (if n < 14 then (if n < 13 then 0 else 1) else (if n < 15 then (-1) else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 4 else 0)) else 0) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else (-1)) else (if n < 27 then 0 else 3)) else (if n < 30 then (if n < 29 then 0 else 1) else (if n < 31 then 0 else (-1)))))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 4 else 0) else 0)) else (if n < 44 then (if n < 42 then (if n < 41 then 0 else 1) else (if n < 43 then 0 else 1)) else (if n < 46 then (if n < 45 then 0 else 3) else (if n < 47 then 0 else 1)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 1 else (-1)) else 0) else (if n < 54 then 0 else (if n < 55 then 3 else 1))) else (if n < 60 then (if n < 58 then (if n < 57 then (-1) else 0) else (if n < 59 then 0 else (-1))) else (if n < 62 then (if n < 61 then 0 else 1) else (if n < 63 then 1 else 2)))))) else 0
theorem nestingEntries_eq467 (n : Nat) :
    nestingProjection467.numerator[n]! = nestingEntries467 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries467, if_neg (by omega : ¬ n < 64)]

def nestingProjection468 : Projection := ⟨4,6,#[3,1,0,0,0,0,1,-1,1,2,0,1,0,-1,-1,0,0,0,4,0,0,0,0,0,0,1,0,3,0,1,0,1,0,0,0,0,4,0,0,0,0,-1,0,1,0,3,0,-1,1,-1,0,0,0,0,3,1,-1,0,0,1,0,-1,1,2]⟩
theorem nestingLookup468 : projections[468]! = nestingProjection468 := by
  rw [projections_lookup]
  rfl
def nestingEntries468 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 1) else 0) else (if n < 6 then 0 else (if n < 7 then 1 else (-1)))) else (if n < 12 then (if n < 10 then (if n < 9 then 1 else 2) else (if n < 11 then 0 else 1)) else (if n < 14 then (if n < 13 then 0 else (-1)) else (if n < 15 then (-1) else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 4 else 0)) else 0) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else 1) else (if n < 27 then 0 else 3)) else (if n < 30 then (if n < 29 then 0 else 1) else (if n < 31 then 0 else 1))))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 4 else 0) else 0)) else (if n < 44 then (if n < 42 then (if n < 41 then 0 else (-1)) else (if n < 43 then 0 else 1)) else (if n < 46 then (if n < 45 then 0 else 3) else (if n < 47 then 0 else (-1))))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 1 else (-1)) else 0) else (if n < 54 then 0 else (if n < 55 then 3 else 1))) else (if n < 60 then (if n < 58 then (if n < 57 then (-1) else 0) else (if n < 59 then 0 else 1)) else (if n < 62 then (if n < 61 then 0 else (-1)) else (if n < 63 then 1 else 2)))))) else 0
theorem nestingEntries_eq468 (n : Nat) :
    nestingProjection468.numerator[n]! = nestingEntries468 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries468, if_neg (by omega : ¬ n < 64)]

def nestingProjection469 : Projection := ⟨2,6,#[2,0,0,0,0,0,0,0,0,1,0,0,0,0,0,-1,0,0,2,0,0,0,0,0,0,0,0,1,0,1,0,0,0,0,0,0,2,0,0,0,0,0,0,1,0,1,0,0,0,0,0,0,0,0,2,0,0,-1,0,0,0,0,0,1]⟩
theorem nestingLookup469 : projections[469]! = nestingProjection469 := by
  rw [projections_lookup]
  rfl
def nestingEntries469 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 2 else 0) else 0) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else 0) else (if n < 14 then 0 else (if n < 15 then 0 else (-1))))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 2 else 0)) else 0) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 1)) else (if n < 30 then (if n < 29 then 0 else 1) else 0)))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 2 else 0) else 0)) else (if n < 44 then (if n < 42 then 0 else (if n < 43 then 0 else 1)) else (if n < 46 then (if n < 45 then 0 else 1) else 0))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 0 else (if n < 55 then 2 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then 0 else (-1)) else 0) else (if n < 62 then 0 else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq469 (n : Nat) :
    nestingProjection469.numerator[n]! = nestingEntries469 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries469, if_neg (by omega : ¬ n < 64)]

def nestingProjection470 : Projection := ⟨1,6,#[1,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,1]⟩
theorem nestingLookup470 : projections[470]! = nestingProjection470 := by
  rw [projections_lookup]
  rfl
def nestingEntries470 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else 0) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else 0) else 0)) else (if n < 24 then 0 else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 1)) else 0))) else (if n < 48 then (if n < 40 then 0 else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 1) else 0))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 0 else (if n < 55 then 1 else 0))) else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq470 (n : Nat) :
    nestingProjection470.numerator[n]! = nestingEntries470 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries470, if_neg (by omega : ¬ n < 64)]

def nestingProjection471 : Projection := ⟨4,6,#[3,0,0,-1,0,-1,-1,0,0,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,0,0,3,0,-1,-1,0,0,0,0,0,4,0,0,0,-1,0,0,-1,0,3,-1,0,-1,0,0,-1,0,-1,3,0,0,0,0,0,0,0,0,4]⟩
theorem nestingLookup471 : projections[471]! = nestingProjection471 := by
  rw [projections_lookup]
  rfl
def nestingEntries471 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 0) else (if n < 3 then 0 else (-1))) else (if n < 6 then (if n < 5 then 0 else (-1)) else (if n < 7 then (-1) else 0))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 4) else 0) else 0)) else (if n < 24 then 0 else (if n < 28 then (if n < 26 then (if n < 25 then (-1) else 0) else (if n < 27 then 0 else 3)) else (if n < 30 then (if n < 29 then 0 else (-1)) else (if n < 31 then (-1) else 0))))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 4 else 0) else 0)) else (if n < 44 then (if n < 42 then (if n < 41 then (-1) else 0) else (if n < 43 then 0 else (-1))) else (if n < 46 then (if n < 45 then 0 else 3) else (if n < 47 then (-1) else 0)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then (-1) else 0) else (if n < 51 then 0 else (-1))) else (if n < 54 then (if n < 53 then 0 else (-1)) else (if n < 55 then 3 else 0))) else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 4)))))) else 0
theorem nestingEntries_eq471 (n : Nat) :
    nestingProjection471.numerator[n]! = nestingEntries471 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries471, if_neg (by omega : ¬ n < 64)]

def nestingProjection472 : Projection := ⟨4,6,#[3,0,0,1,0,1,-1,0,0,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,3,0,-1,1,0,0,0,0,0,4,0,0,0,1,0,0,-1,0,3,1,0,-1,0,0,1,0,1,3,0,0,0,0,0,0,0,0,4]⟩
theorem nestingLookup472 : projections[472]! = nestingProjection472 := by
  rw [projections_lookup]
  rfl
def nestingEntries472 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 0) else (if n < 3 then 0 else 1)) else (if n < 6 then (if n < 5 then 0 else 1) else (if n < 7 then (-1) else 0))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 4) else 0) else 0)) else (if n < 24 then 0 else (if n < 28 then (if n < 26 then (if n < 25 then 1 else 0) else (if n < 27 then 0 else 3)) else (if n < 30 then (if n < 29 then 0 else (-1)) else (if n < 31 then 1 else 0))))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 4 else 0) else 0)) else (if n < 44 then (if n < 42 then (if n < 41 then 1 else 0) else (if n < 43 then 0 else (-1))) else (if n < 46 then (if n < 45 then 0 else 3) else (if n < 47 then 1 else 0)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then (-1) else 0) else (if n < 51 then 0 else 1)) else (if n < 54 then (if n < 53 then 0 else 1) else (if n < 55 then 3 else 0))) else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 4)))))) else 0
theorem nestingEntries_eq472 (n : Nat) :
    nestingProjection472.numerator[n]! = nestingEntries472 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries472, if_neg (by omega : ¬ n < 64)]

def nestingProjection473 : Projection := ⟨4,6,#[3,0,0,-1,0,-1,-1,0,0,4,0,0,0,0,0,0,0,0,4,0,0,0,0,0,-1,0,0,3,0,-1,-1,0,0,0,0,0,0,0,0,0,-1,0,0,-1,0,3,-1,0,-1,0,0,-1,0,-1,3,0,0,0,0,0,0,0,0,4]⟩
theorem nestingLookup473 : projections[473]! = nestingProjection473 := by
  rw [projections_lookup]
  rfl
def nestingEntries473 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 0) else (if n < 3 then 0 else (-1))) else (if n < 6 then (if n < 5 then 0 else (-1)) else (if n < 7 then (-1) else 0))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 4) else 0) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 4 else 0)) else 0) else (if n < 28 then (if n < 26 then (if n < 25 then (-1) else 0) else (if n < 27 then 0 else 3)) else (if n < 30 then (if n < 29 then 0 else (-1)) else (if n < 31 then (-1) else 0))))) else (if n < 48 then (if n < 40 then 0 else (if n < 44 then (if n < 42 then (if n < 41 then (-1) else 0) else (if n < 43 then 0 else (-1))) else (if n < 46 then (if n < 45 then 0 else 3) else (if n < 47 then (-1) else 0)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then (-1) else 0) else (if n < 51 then 0 else (-1))) else (if n < 54 then (if n < 53 then 0 else (-1)) else (if n < 55 then 3 else 0))) else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 4)))))) else 0
theorem nestingEntries_eq473 (n : Nat) :
    nestingProjection473.numerator[n]! = nestingEntries473 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries473, if_neg (by omega : ¬ n < 64)]

def nestingProjection474 : Projection := ⟨4,6,#[3,0,0,1,0,1,-1,0,0,4,0,0,0,0,0,0,0,0,4,0,0,0,0,0,1,0,0,3,0,-1,1,0,0,0,0,0,0,0,0,0,1,0,0,-1,0,3,1,0,-1,0,0,1,0,1,3,0,0,0,0,0,0,0,0,4]⟩
theorem nestingLookup474 : projections[474]! = nestingProjection474 := by
  rw [projections_lookup]
  rfl
def nestingEntries474 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 0) else (if n < 3 then 0 else 1)) else (if n < 6 then (if n < 5 then 0 else 1) else (if n < 7 then (-1) else 0))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 4) else 0) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 4 else 0)) else 0) else (if n < 28 then (if n < 26 then (if n < 25 then 1 else 0) else (if n < 27 then 0 else 3)) else (if n < 30 then (if n < 29 then 0 else (-1)) else (if n < 31 then 1 else 0))))) else (if n < 48 then (if n < 40 then 0 else (if n < 44 then (if n < 42 then (if n < 41 then 1 else 0) else (if n < 43 then 0 else (-1))) else (if n < 46 then (if n < 45 then 0 else 3) else (if n < 47 then 1 else 0)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then (-1) else 0) else (if n < 51 then 0 else 1)) else (if n < 54 then (if n < 53 then 0 else 1) else (if n < 55 then 3 else 0))) else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 4)))))) else 0
theorem nestingEntries_eq474 (n : Nat) :
    nestingProjection474.numerator[n]! = nestingEntries474 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries474, if_neg (by omega : ¬ n < 64)]

def nestingProjection475 : Projection := ⟨2,6,#[1,0,0,0,0,0,-1,0,0,2,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,1,0,-1,0,0,0,0,0,0,2,0,0,0,0,0,0,-1,0,1,0,0,-1,0,0,0,0,0,1,0,0,0,0,0,0,0,0,2]⟩
theorem nestingLookup475 : projections[475]! = nestingProjection475 := by
  rw [projections_lookup]
  rfl
def nestingEntries475 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else 0) else (if n < 6 then 0 else (if n < 7 then (-1) else 0))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 2) else 0) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 2 else 0)) else 0) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 1)) else (if n < 30 then (if n < 29 then 0 else (-1)) else 0)))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 2 else 0) else 0)) else (if n < 44 then (if n < 42 then 0 else (if n < 43 then 0 else (-1))) else (if n < 46 then (if n < 45 then 0 else 1) else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then (-1) else 0) else 0) else (if n < 54 then 0 else (if n < 55 then 1 else 0))) else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 2)))))) else 0
theorem nestingEntries_eq475 (n : Nat) :
    nestingProjection475.numerator[n]! = nestingEntries475 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries475, if_neg (by omega : ¬ n < 64)]

def nestingProjection476 : Projection := ⟨2,6,#[1,0,0,0,0,0,-1,0,0,2,0,0,0,0,0,0,0,0,1,0,-1,0,0,0,0,0,0,2,0,0,0,0,0,0,-1,0,1,0,0,0,0,0,0,0,0,2,0,0,-1,0,0,0,0,0,1,0,0,0,0,0,0,0,0,2]⟩
theorem nestingLookup476 : projections[476]! = nestingProjection476 := by
  rw [projections_lookup]
  rfl
def nestingEntries476 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else 0) else (if n < 6 then 0 else (if n < 7 then (-1) else 0))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 2) else 0) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 1 else 0)) else (if n < 22 then (if n < 21 then (-1) else 0) else 0)) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 2)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then 0 else (if n < 35 then (-1) else 0)) else (if n < 38 then (if n < 37 then 1 else 0) else 0)) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 2) else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then (-1) else 0) else 0) else (if n < 54 then 0 else (if n < 55 then 1 else 0))) else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 2)))))) else 0
theorem nestingEntries_eq476 (n : Nat) :
    nestingProjection476.numerator[n]! = nestingEntries476 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries476, if_neg (by omega : ¬ n < 64)]

def nestingProjection477 : Projection := ⟨4,6,#[3,0,-1,0,-1,0,-1,0,0,4,0,0,0,0,0,0,-1,0,2,-1,0,-1,-1,0,0,0,-1,3,1,-1,0,0,-1,0,0,1,2,1,-1,0,0,0,-1,-1,1,3,0,0,-1,0,-1,0,-1,0,3,0,0,0,0,0,0,0,0,4]⟩
theorem nestingLookup477 : projections[477]! = nestingProjection477 := by
  rw [projections_lookup]
  rfl
def nestingEntries477 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 0) else (if n < 3 then (-1) else 0)) else (if n < 6 then (if n < 5 then (-1) else 0) else (if n < 7 then (-1) else 0))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 4) else 0) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then (-1) else 0) else (if n < 19 then 2 else (-1))) else (if n < 22 then (if n < 21 then 0 else (-1)) else (if n < 23 then (-1) else 0))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then (-1) else 3)) else (if n < 30 then (if n < 29 then 1 else (-1)) else 0)))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then (-1) else 0) else (if n < 35 then 0 else 1)) else (if n < 38 then (if n < 37 then 2 else 1) else (if n < 39 then (-1) else 0))) else (if n < 44 then (if n < 42 then 0 else (-1)) else (if n < 46 then (if n < 45 then 1 else 3) else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then (-1) else 0) else (if n < 51 then (-1) else 0)) else (if n < 54 then (if n < 53 then (-1) else 0) else (if n < 55 then 3 else 0))) else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 4)))))) else 0
theorem nestingEntries_eq477 (n : Nat) :
    nestingProjection477.numerator[n]! = nestingEntries477 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries477, if_neg (by omega : ¬ n < 64)]

def nestingProjection478 : Projection := ⟨4,6,#[3,0,-1,0,-1,0,-1,0,0,4,0,0,0,0,0,0,-1,0,2,1,0,1,-1,0,0,0,1,3,-1,-1,0,0,-1,0,0,-1,2,-1,-1,0,0,0,1,-1,-1,3,0,0,-1,0,-1,0,-1,0,3,0,0,0,0,0,0,0,0,4]⟩
theorem nestingLookup478 : projections[478]! = nestingProjection478 := by
  rw [projections_lookup]
  rfl
def nestingEntries478 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 0) else (if n < 3 then (-1) else 0)) else (if n < 6 then (if n < 5 then (-1) else 0) else (if n < 7 then (-1) else 0))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 4) else 0) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then (-1) else 0) else (if n < 19 then 2 else 1)) else (if n < 22 then (if n < 21 then 0 else 1) else (if n < 23 then (-1) else 0))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 1 else 3)) else (if n < 30 then (-1) else 0)))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then (-1) else 0) else (if n < 35 then 0 else (-1))) else (if n < 38 then (if n < 37 then 2 else (-1)) else (if n < 39 then (-1) else 0))) else (if n < 44 then (if n < 42 then 0 else (if n < 43 then 1 else (-1))) else (if n < 46 then (if n < 45 then (-1) else 3) else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then (-1) else 0) else (if n < 51 then (-1) else 0)) else (if n < 54 then (if n < 53 then (-1) else 0) else (if n < 55 then 3 else 0))) else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 4)))))) else 0
theorem nestingEntries_eq478 (n : Nat) :
    nestingProjection478.numerator[n]! = nestingEntries478 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries478, if_neg (by omega : ¬ n < 64)]

def nestingProjection479 : Projection := ⟨4,6,#[3,0,1,0,1,0,-1,0,0,4,0,0,0,0,0,0,1,0,2,-1,0,-1,1,0,0,0,-1,3,1,-1,0,0,1,0,0,1,2,1,1,0,0,0,-1,-1,1,3,0,0,-1,0,1,0,1,0,3,0,0,0,0,0,0,0,0,4]⟩
theorem nestingLookup479 : projections[479]! = nestingProjection479 := by
  rw [projections_lookup]
  rfl
def nestingEntries479 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 0) else (if n < 3 then 1 else 0)) else (if n < 6 then (if n < 5 then 1 else 0) else (if n < 7 then (-1) else 0))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 4) else 0) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 1 else 0) else (if n < 19 then 2 else (-1))) else (if n < 22 then (if n < 21 then 0 else (-1)) else (if n < 23 then 1 else 0))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then (-1) else 3)) else (if n < 30 then (if n < 29 then 1 else (-1)) else 0)))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 1 else 0) else (if n < 35 then 0 else 1)) else (if n < 38 then (if n < 37 then 2 else 1) else (if n < 39 then 1 else 0))) else (if n < 44 then (if n < 42 then 0 else (-1)) else (if n < 46 then (if n < 45 then 1 else 3) else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then (-1) else 0) else (if n < 51 then 1 else 0)) else (if n < 54 then (if n < 53 then 1 else 0) else (if n < 55 then 3 else 0))) else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 4)))))) else 0
theorem nestingEntries_eq479 (n : Nat) :
    nestingProjection479.numerator[n]! = nestingEntries479 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries479, if_neg (by omega : ¬ n < 64)]

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def nestingProjection480 : Projection := ⟨4,6,#[3,0,1,0,1,0,-1,0,0,4,0,0,0,0,0,0,1,0,2,1,0,1,1,0,0,0,1,3,-1,-1,0,0,1,0,0,-1,2,-1,1,0,0,0,1,-1,-1,3,0,0,-1,0,1,0,1,0,3,0,0,0,0,0,0,0,0,4]⟩
theorem nestingLookup480 : projections[480]! = nestingProjection480 := by
  rw [projections_lookup]
  rfl
def nestingEntries480 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 0) else (if n < 3 then 1 else 0)) else (if n < 6 then (if n < 5 then 1 else 0) else (if n < 7 then (-1) else 0))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 4) else 0) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 1 else 0) else (if n < 19 then 2 else 1)) else (if n < 22 then (if n < 21 then 0 else 1) else (if n < 23 then 1 else 0))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 1 else 3)) else (if n < 30 then (-1) else 0)))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 1 else 0) else (if n < 35 then 0 else (-1))) else (if n < 38 then (if n < 37 then 2 else (-1)) else (if n < 39 then 1 else 0))) else (if n < 44 then (if n < 42 then 0 else (if n < 43 then 1 else (-1))) else (if n < 46 then (if n < 45 then (-1) else 3) else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then (-1) else 0) else (if n < 51 then 1 else 0)) else (if n < 54 then (if n < 53 then 1 else 0) else (if n < 55 then 3 else 0))) else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 4)))))) else 0
theorem nestingEntries_eq480 (n : Nat) :
    nestingProjection480.numerator[n]! = nestingEntries480 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries480, if_neg (by omega : ¬ n < 64)]

def nestingProjection481 : Projection := ⟨2,6,#[2,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,1,0,1,0,0,0,0,0,0,1,0,-1,0,0,0,0,1,0,1,0,0,0,0,0,0,-1,0,1,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,2]⟩
theorem nestingLookup481 : projections[481]! = nestingProjection481 := by
  rw [projections_lookup]
  rfl
def nestingEntries481 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 2 else 0) else 0) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 2) else 0) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 1 else 0)) else (if n < 22 then (if n < 21 then 1 else 0) else 0)) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 1)) else (if n < 30 then (if n < 29 then 0 else (-1)) else 0)))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then 0 else (if n < 35 then 1 else 0)) else (if n < 38 then (if n < 37 then 1 else 0) else 0)) else (if n < 44 then (if n < 42 then 0 else (if n < 43 then 0 else (-1))) else (if n < 46 then (if n < 45 then 0 else 1) else 0))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 0 else (if n < 55 then 2 else 0))) else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 2)))))) else 0
theorem nestingEntries_eq481 (n : Nat) :
    nestingProjection481.numerator[n]! = nestingEntries481 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries481, if_neg (by omega : ¬ n < 64)]

def nestingProjection482 : Projection := ⟨2,6,#[1,0,0,0,0,0,-1,0,0,2,0,0,0,0,0,0,0,0,1,0,1,0,0,0,0,0,0,2,0,0,0,0,0,0,1,0,1,0,0,0,0,0,0,0,0,2,0,0,-1,0,0,0,0,0,1,0,0,0,0,0,0,0,0,2]⟩
theorem nestingLookup482 : projections[482]! = nestingProjection482 := by
  rw [projections_lookup]
  rfl
def nestingEntries482 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else 0) else (if n < 6 then 0 else (if n < 7 then (-1) else 0))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 2) else 0) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 1 else 0)) else (if n < 22 then (if n < 21 then 1 else 0) else 0)) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 2)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then 0 else (if n < 35 then 1 else 0)) else (if n < 38 then (if n < 37 then 1 else 0) else 0)) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 2) else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then (-1) else 0) else 0) else (if n < 54 then 0 else (if n < 55 then 1 else 0))) else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 2)))))) else 0
theorem nestingEntries_eq482 (n : Nat) :
    nestingProjection482.numerator[n]! = nestingEntries482 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries482, if_neg (by omega : ¬ n < 64)]

def nestingProjection483 : Projection := ⟨4,6,#[3,0,-1,0,1,0,-1,0,0,4,0,0,0,0,0,0,-1,0,2,-1,0,-1,-1,0,0,0,-1,3,-1,-1,0,0,1,0,0,-1,2,-1,1,0,0,0,-1,-1,-1,3,0,0,-1,0,-1,0,1,0,3,0,0,0,0,0,0,0,0,4]⟩
theorem nestingLookup483 : projections[483]! = nestingProjection483 := by
  rw [projections_lookup]
  rfl
def nestingEntries483 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 0) else (if n < 3 then (-1) else 0)) else (if n < 6 then (if n < 5 then 1 else 0) else (if n < 7 then (-1) else 0))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 4) else 0) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then (-1) else 0) else (if n < 19 then 2 else (-1))) else (if n < 22 then (if n < 21 then 0 else (-1)) else (if n < 23 then (-1) else 0))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then (-1) else 3)) else (if n < 30 then (-1) else 0)))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 1 else 0) else (if n < 35 then 0 else (-1))) else (if n < 38 then (if n < 37 then 2 else (-1)) else (if n < 39 then 1 else 0))) else (if n < 44 then (if n < 42 then 0 else (-1)) else (if n < 46 then (if n < 45 then (-1) else 3) else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then (-1) else 0) else (if n < 51 then (-1) else 0)) else (if n < 54 then (if n < 53 then 1 else 0) else (if n < 55 then 3 else 0))) else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 4)))))) else 0
theorem nestingEntries_eq483 (n : Nat) :
    nestingProjection483.numerator[n]! = nestingEntries483 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries483, if_neg (by omega : ¬ n < 64)]

def nestingProjection484 : Projection := ⟨4,6,#[3,0,-1,0,1,0,-1,0,0,4,0,0,0,0,0,0,-1,0,2,1,0,1,-1,0,0,0,1,3,1,-1,0,0,1,0,0,1,2,1,1,0,0,0,1,-1,1,3,0,0,-1,0,-1,0,1,0,3,0,0,0,0,0,0,0,0,4]⟩
theorem nestingLookup484 : projections[484]! = nestingProjection484 := by
  rw [projections_lookup]
  rfl
def nestingEntries484 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 0) else (if n < 3 then (-1) else 0)) else (if n < 6 then (if n < 5 then 1 else 0) else (if n < 7 then (-1) else 0))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 4) else 0) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then (-1) else 0) else (if n < 19 then 2 else 1)) else (if n < 22 then (if n < 21 then 0 else 1) else (if n < 23 then (-1) else 0))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 1 else 3)) else (if n < 30 then (if n < 29 then 1 else (-1)) else 0)))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 1 else 0) else (if n < 35 then 0 else 1)) else (if n < 38 then (if n < 37 then 2 else 1) else (if n < 39 then 1 else 0))) else (if n < 44 then (if n < 42 then 0 else (if n < 43 then 1 else (-1))) else (if n < 46 then (if n < 45 then 1 else 3) else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then (-1) else 0) else (if n < 51 then (-1) else 0)) else (if n < 54 then (if n < 53 then 1 else 0) else (if n < 55 then 3 else 0))) else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 4)))))) else 0
theorem nestingEntries_eq484 (n : Nat) :
    nestingProjection484.numerator[n]! = nestingEntries484 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries484, if_neg (by omega : ¬ n < 64)]

def nestingProjection485 : Projection := ⟨4,6,#[3,0,1,0,-1,0,-1,0,0,4,0,0,0,0,0,0,1,0,2,-1,0,-1,1,0,0,0,-1,3,-1,-1,0,0,-1,0,0,-1,2,-1,-1,0,0,0,-1,-1,-1,3,0,0,-1,0,1,0,-1,0,3,0,0,0,0,0,0,0,0,4]⟩
theorem nestingLookup485 : projections[485]! = nestingProjection485 := by
  rw [projections_lookup]
  rfl
def nestingEntries485 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 0) else (if n < 3 then 1 else 0)) else (if n < 6 then (if n < 5 then (-1) else 0) else (if n < 7 then (-1) else 0))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 4) else 0) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 1 else 0) else (if n < 19 then 2 else (-1))) else (if n < 22 then (if n < 21 then 0 else (-1)) else (if n < 23 then 1 else 0))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then (-1) else 3)) else (if n < 30 then (-1) else 0)))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then (-1) else 0) else (if n < 35 then 0 else (-1))) else (if n < 38 then (if n < 37 then 2 else (-1)) else (if n < 39 then (-1) else 0))) else (if n < 44 then (if n < 42 then 0 else (-1)) else (if n < 46 then (if n < 45 then (-1) else 3) else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then (-1) else 0) else (if n < 51 then 1 else 0)) else (if n < 54 then (if n < 53 then (-1) else 0) else (if n < 55 then 3 else 0))) else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 4)))))) else 0
theorem nestingEntries_eq485 (n : Nat) :
    nestingProjection485.numerator[n]! = nestingEntries485 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries485, if_neg (by omega : ¬ n < 64)]

def nestingProjection486 : Projection := ⟨4,6,#[3,0,1,0,-1,0,-1,0,0,4,0,0,0,0,0,0,1,0,2,1,0,1,1,0,0,0,1,3,1,-1,0,0,-1,0,0,1,2,1,-1,0,0,0,1,-1,1,3,0,0,-1,0,1,0,-1,0,3,0,0,0,0,0,0,0,0,4]⟩
theorem nestingLookup486 : projections[486]! = nestingProjection486 := by
  rw [projections_lookup]
  rfl
def nestingEntries486 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 0) else (if n < 3 then 1 else 0)) else (if n < 6 then (if n < 5 then (-1) else 0) else (if n < 7 then (-1) else 0))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 4) else 0) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 1 else 0) else (if n < 19 then 2 else 1)) else (if n < 22 then (if n < 21 then 0 else 1) else (if n < 23 then 1 else 0))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 1 else 3)) else (if n < 30 then (if n < 29 then 1 else (-1)) else 0)))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then (-1) else 0) else (if n < 35 then 0 else 1)) else (if n < 38 then (if n < 37 then 2 else 1) else (if n < 39 then (-1) else 0))) else (if n < 44 then (if n < 42 then 0 else (if n < 43 then 1 else (-1))) else (if n < 46 then (if n < 45 then 1 else 3) else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then (-1) else 0) else (if n < 51 then 1 else 0)) else (if n < 54 then (if n < 53 then (-1) else 0) else (if n < 55 then 3 else 0))) else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 4)))))) else 0
theorem nestingEntries_eq486 (n : Nat) :
    nestingProjection486.numerator[n]! = nestingEntries486 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries486, if_neg (by omega : ¬ n < 64)]

def nestingProjection487 : Projection := ⟨2,6,#[2,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,1,0,-1,0,0,0,0,0,0,1,0,-1,0,0,0,0,-1,0,1,0,0,0,0,0,0,-1,0,1,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,2]⟩
theorem nestingLookup487 : projections[487]! = nestingProjection487 := by
  rw [projections_lookup]
  rfl
def nestingEntries487 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 2 else 0) else 0) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 2) else 0) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 1 else 0)) else (if n < 22 then (if n < 21 then (-1) else 0) else 0)) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 1)) else (if n < 30 then (if n < 29 then 0 else (-1)) else 0)))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then 0 else (if n < 35 then (-1) else 0)) else (if n < 38 then (if n < 37 then 1 else 0) else 0)) else (if n < 44 then (if n < 42 then 0 else (if n < 43 then 0 else (-1))) else (if n < 46 then (if n < 45 then 0 else 1) else 0))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 0 else (if n < 55 then 2 else 0))) else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 2)))))) else 0
theorem nestingEntries_eq487 (n : Nat) :
    nestingProjection487.numerator[n]! = nestingEntries487 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries487, if_neg (by omega : ¬ n < 64)]

def nestingProjection488 : Projection := ⟨2,6,#[2,0,0,0,0,0,0,0,0,1,0,0,-1,0,0,0,0,0,1,0,0,0,0,-1,0,0,0,2,0,0,0,0,0,-1,0,0,1,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,2,0,0,0,-1,0,0,0,0,1]⟩
theorem nestingLookup488 : projections[488]! = nestingProjection488 := by
  rw [projections_lookup]
  rfl
def nestingEntries488 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 2 else 0) else 0) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else 0) else (if n < 14 then (if n < 13 then (-1) else 0) else 0))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 1 else 0)) else (if n < 22 then 0 else (if n < 23 then 0 else (-1)))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 2)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 0 else (-1)) else 0) else (if n < 38 then (if n < 37 then 1 else 0) else 0)) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 2) else 0))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 0 else (if n < 55 then 2 else 0))) else (if n < 60 then (if n < 58 then 0 else (if n < 59 then (-1) else 0)) else (if n < 62 then 0 else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq488 (n : Nat) :
    nestingProjection488.numerator[n]! = nestingEntries488 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries488, if_neg (by omega : ¬ n < 64)]

def nestingProjection489 : Projection := ⟨4,6,#[3,0,0,-1,0,1,-1,0,0,3,-1,0,-1,0,0,-1,0,-1,3,0,-1,0,0,-1,-1,0,0,3,0,1,-1,0,0,-1,-1,0,3,0,0,-1,1,0,0,1,0,3,1,0,-1,0,0,-1,0,1,3,0,0,-1,-1,0,-1,0,0,3]⟩
theorem nestingLookup489 : projections[489]! = nestingProjection489 := by
  rw [projections_lookup]
  rfl
def nestingEntries489 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 0) else (if n < 3 then 0 else (-1))) else (if n < 6 then (if n < 5 then 0 else 1) else (if n < 7 then (-1) else 0))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 3) else (if n < 11 then (-1) else 0)) else (if n < 14 then (if n < 13 then (-1) else 0) else (if n < 15 then 0 else (-1))))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 0 else (-1)) else (if n < 19 then 3 else 0)) else (if n < 22 then (if n < 21 then (-1) else 0) else (if n < 23 then 0 else (-1)))) else (if n < 28 then (if n < 26 then (if n < 25 then (-1) else 0) else (if n < 27 then 0 else 3)) else (if n < 30 then (if n < 29 then 0 else 1) else (if n < 31 then (-1) else 0))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 0 else (-1)) else (if n < 35 then (-1) else 0)) else (if n < 38 then (if n < 37 then 3 else 0) else (if n < 39 then 0 else (-1)))) else (if n < 44 then (if n < 42 then (if n < 41 then 1 else 0) else (if n < 43 then 0 else 1)) else (if n < 46 then (if n < 45 then 0 else 3) else (if n < 47 then 1 else 0)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then (-1) else 0) else (if n < 51 then 0 else (-1))) else (if n < 54 then (if n < 53 then 0 else 1) else (if n < 55 then 3 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then 0 else (-1)) else (if n < 59 then (-1) else 0)) else (if n < 62 then (if n < 61 then (-1) else 0) else (if n < 63 then 0 else 3)))))) else 0
theorem nestingEntries_eq489 (n : Nat) :
    nestingProjection489.numerator[n]! = nestingEntries489 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries489, if_neg (by omega : ¬ n < 64)]

def nestingProjection490 : Projection := ⟨4,6,#[3,0,0,1,0,1,1,0,0,3,-1,0,-1,0,0,-1,0,-1,3,0,-1,0,0,-1,1,0,0,3,0,-1,-1,0,0,-1,-1,0,3,0,0,-1,1,0,0,-1,0,3,-1,0,1,0,0,-1,0,-1,3,0,0,-1,-1,0,-1,0,0,3]⟩
theorem nestingLookup490 : projections[490]! = nestingProjection490 := by
  rw [projections_lookup]
  rfl
def nestingEntries490 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 0) else (if n < 3 then 0 else 1)) else (if n < 6 then (if n < 5 then 0 else 1) else (if n < 7 then 1 else 0))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 3) else (if n < 11 then (-1) else 0)) else (if n < 14 then (if n < 13 then (-1) else 0) else (if n < 15 then 0 else (-1))))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 0 else (-1)) else (if n < 19 then 3 else 0)) else (if n < 22 then (if n < 21 then (-1) else 0) else (if n < 23 then 0 else (-1)))) else (if n < 28 then (if n < 26 then (if n < 25 then 1 else 0) else (if n < 27 then 0 else 3)) else (if n < 30 then (if n < 29 then 0 else (-1)) else (if n < 31 then (-1) else 0))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 0 else (-1)) else (if n < 35 then (-1) else 0)) else (if n < 38 then (if n < 37 then 3 else 0) else (if n < 39 then 0 else (-1)))) else (if n < 44 then (if n < 42 then (if n < 41 then 1 else 0) else (if n < 43 then 0 else (-1))) else (if n < 46 then (if n < 45 then 0 else 3) else (if n < 47 then (-1) else 0)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 1 else 0) else (if n < 51 then 0 else (-1))) else (if n < 54 then (if n < 53 then 0 else (-1)) else (if n < 55 then 3 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then 0 else (-1)) else (if n < 59 then (-1) else 0)) else (if n < 62 then (if n < 61 then (-1) else 0) else (if n < 63 then 0 else 3)))))) else 0
theorem nestingEntries_eq490 (n : Nat) :
    nestingProjection490.numerator[n]! = nestingEntries490 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries490, if_neg (by omega : ¬ n < 64)]

def nestingProjection491 : Projection := ⟨4,6,#[3,0,0,-1,0,1,-1,0,0,3,1,0,-1,0,0,1,0,1,3,0,1,0,0,-1,-1,0,0,3,0,1,-1,0,0,-1,1,0,3,0,0,1,1,0,0,1,0,3,1,0,-1,0,0,-1,0,1,3,0,0,1,-1,0,1,0,0,3]⟩
theorem nestingLookup491 : projections[491]! = nestingProjection491 := by
  rw [projections_lookup]
  rfl
def nestingEntries491 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 0) else (if n < 3 then 0 else (-1))) else (if n < 6 then (if n < 5 then 0 else 1) else (if n < 7 then (-1) else 0))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 3) else (if n < 11 then 1 else 0)) else (if n < 14 then (if n < 13 then (-1) else 0) else (if n < 15 then 0 else 1)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 0 else 1) else (if n < 19 then 3 else 0)) else (if n < 22 then (if n < 21 then 1 else 0) else (if n < 23 then 0 else (-1)))) else (if n < 28 then (if n < 26 then (if n < 25 then (-1) else 0) else (if n < 27 then 0 else 3)) else (if n < 30 then (if n < 29 then 0 else 1) else (if n < 31 then (-1) else 0))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 0 else (-1)) else (if n < 35 then 1 else 0)) else (if n < 38 then (if n < 37 then 3 else 0) else (if n < 39 then 0 else 1))) else (if n < 44 then (if n < 42 then (if n < 41 then 1 else 0) else (if n < 43 then 0 else 1)) else (if n < 46 then (if n < 45 then 0 else 3) else (if n < 47 then 1 else 0)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then (-1) else 0) else (if n < 51 then 0 else (-1))) else (if n < 54 then (if n < 53 then 0 else 1) else (if n < 55 then 3 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then 0 else 1) else (if n < 59 then (-1) else 0)) else (if n < 62 then (if n < 61 then 1 else 0) else (if n < 63 then 0 else 3)))))) else 0
theorem nestingEntries_eq491 (n : Nat) :
    nestingProjection491.numerator[n]! = nestingEntries491 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries491, if_neg (by omega : ¬ n < 64)]

def nestingProjection492 : Projection := ⟨4,6,#[3,0,0,1,0,1,1,0,0,3,1,0,-1,0,0,1,0,1,3,0,1,0,0,-1,1,0,0,3,0,-1,-1,0,0,-1,1,0,3,0,0,1,1,0,0,-1,0,3,-1,0,1,0,0,-1,0,-1,3,0,0,1,-1,0,1,0,0,3]⟩
theorem nestingLookup492 : projections[492]! = nestingProjection492 := by
  rw [projections_lookup]
  rfl
def nestingEntries492 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 0) else (if n < 3 then 0 else 1)) else (if n < 6 then (if n < 5 then 0 else 1) else (if n < 7 then 1 else 0))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 3) else (if n < 11 then 1 else 0)) else (if n < 14 then (if n < 13 then (-1) else 0) else (if n < 15 then 0 else 1)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 0 else 1) else (if n < 19 then 3 else 0)) else (if n < 22 then (if n < 21 then 1 else 0) else (if n < 23 then 0 else (-1)))) else (if n < 28 then (if n < 26 then (if n < 25 then 1 else 0) else (if n < 27 then 0 else 3)) else (if n < 30 then (if n < 29 then 0 else (-1)) else (if n < 31 then (-1) else 0))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 0 else (-1)) else (if n < 35 then 1 else 0)) else (if n < 38 then (if n < 37 then 3 else 0) else (if n < 39 then 0 else 1))) else (if n < 44 then (if n < 42 then (if n < 41 then 1 else 0) else (if n < 43 then 0 else (-1))) else (if n < 46 then (if n < 45 then 0 else 3) else (if n < 47 then (-1) else 0)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 1 else 0) else (if n < 51 then 0 else (-1))) else (if n < 54 then (if n < 53 then 0 else (-1)) else (if n < 55 then 3 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then 0 else 1) else (if n < 59 then (-1) else 0)) else (if n < 62 then (if n < 61 then 1 else 0) else (if n < 63 then 0 else 3)))))) else 0
theorem nestingEntries_eq492 (n : Nat) :
    nestingProjection492.numerator[n]! = nestingEntries492 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries492, if_neg (by omega : ¬ n < 64)]

def nestingProjection493 : Projection := ⟨2,6,#[1,0,0,0,0,1,0,0,0,2,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,1,0,0,-1,0,0,0,0,0,2,0,0,0,1,0,0,0,0,1,0,0,0,0,0,-1,0,0,1,0,0,0,0,0,0,0,0,2]⟩
theorem nestingLookup493 : projections[493]! = nestingProjection493 := by
  rw [projections_lookup]
  rfl
def nestingEntries493 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else 0) else (if n < 6 then (if n < 5 then 0 else 1) else 0)) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 2) else 0) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 2 else 0)) else 0) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 1)) else (if n < 30 then 0 else (if n < 31 then (-1) else 0))))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 2 else 0) else 0)) else (if n < 44 then (if n < 42 then (if n < 41 then 1 else 0) else 0) else (if n < 46 then (if n < 45 then 0 else 1) else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then 0 else (if n < 51 then 0 else (-1))) else (if n < 54 then 0 else (if n < 55 then 1 else 0))) else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 2)))))) else 0
theorem nestingEntries_eq493 (n : Nat) :
    nestingProjection493.numerator[n]! = nestingEntries493 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries493, if_neg (by omega : ¬ n < 64)]

def nestingProjection494 : Projection := ⟨2,6,#[1,0,0,0,0,1,0,0,0,1,0,0,-1,0,0,0,0,0,2,0,0,0,0,0,0,0,0,2,0,0,0,0,0,-1,0,0,1,0,0,0,1,0,0,0,0,1,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,2]⟩
theorem nestingLookup494 : projections[494]! = nestingProjection494 := by
  rw [projections_lookup]
  rfl
def nestingEntries494 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else 0) else (if n < 6 then (if n < 5 then 0 else 1) else 0)) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else 0) else (if n < 14 then (if n < 13 then (-1) else 0) else 0))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 2 else 0)) else 0) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 2)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 0 else (-1)) else 0) else (if n < 38 then (if n < 37 then 1 else 0) else 0)) else (if n < 44 then (if n < 42 then (if n < 41 then 1 else 0) else 0) else (if n < 46 then (if n < 45 then 0 else 1) else 0))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 0 else (if n < 55 then 2 else 0))) else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 2)))))) else 0
theorem nestingEntries_eq494 (n : Nat) :
    nestingProjection494.numerator[n]! = nestingEntries494 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries494, if_neg (by omega : ¬ n < 64)]

def nestingProjection495 : Projection := ⟨4,6,#[3,-1,0,0,-1,1,0,0,-1,3,0,0,-1,1,0,0,0,0,3,-1,0,0,-1,-1,0,0,-1,3,0,0,-1,-1,-1,-1,0,0,3,1,0,0,1,1,0,0,1,3,0,0,0,0,-1,-1,0,0,3,-1,0,0,-1,-1,0,0,-1,3]⟩
theorem nestingLookup495 : projections[495]! = nestingProjection495 := by
  rw [projections_lookup]
  rfl
def nestingEntries495 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else (-1)) else 0) else (if n < 6 then (if n < 5 then (-1) else 1) else 0)) else (if n < 12 then (if n < 10 then (if n < 9 then (-1) else 3) else 0) else (if n < 14 then (if n < 13 then (-1) else 1) else 0))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 3 else (-1))) else (if n < 22 then 0 else (-1))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then (-1) else 3)) else (if n < 30 then 0 else (-1))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (-1) else 0) else (if n < 38 then (if n < 37 then 3 else 1) else 0)) else (if n < 44 then (if n < 42 then 1 else 0) else (if n < 46 then (if n < 45 then 1 else 3) else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then 0 else (-1)) else (if n < 54 then 0 else (if n < 55 then 3 else (-1)))) else (if n < 60 then (if n < 58 then 0 else (-1)) else (if n < 62 then 0 else (if n < 63 then (-1) else 3)))))) else 0
theorem nestingEntries_eq495 (n : Nat) :
    nestingProjection495.numerator[n]! = nestingEntries495 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries495, if_neg (by omega : ¬ n < 64)]

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def nestingProjection496 : Projection := ⟨4,6,#[3,-1,0,0,-1,1,0,0,-1,3,0,0,-1,1,0,0,0,0,3,1,0,0,1,-1,0,0,1,3,0,0,-1,1,-1,-1,0,0,3,1,0,0,1,1,0,0,1,3,0,0,0,0,1,-1,0,0,3,1,0,0,-1,1,0,0,1,3]⟩
theorem nestingLookup496 : projections[496]! = nestingProjection496 := by
  rw [projections_lookup]
  rfl
def nestingEntries496 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else (-1)) else 0) else (if n < 6 then (if n < 5 then (-1) else 1) else 0)) else (if n < 12 then (if n < 10 then (if n < 9 then (-1) else 3) else 0) else (if n < 14 then (if n < 13 then (-1) else 1) else 0))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 3 else 1)) else (if n < 22 then 0 else (if n < 23 then 1 else (-1)))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 1 else 3)) else (if n < 30 then 0 else (if n < 31 then (-1) else 1))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (-1) else 0) else (if n < 38 then (if n < 37 then 3 else 1) else 0)) else (if n < 44 then (if n < 42 then 1 else 0) else (if n < 46 then (if n < 45 then 1 else 3) else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then 0 else (if n < 51 then 1 else (-1))) else (if n < 54 then 0 else (if n < 55 then 3 else 1))) else (if n < 60 then (if n < 58 then 0 else (if n < 59 then (-1) else 1)) else (if n < 62 then 0 else (if n < 63 then 1 else 3)))))) else 0
theorem nestingEntries_eq496 (n : Nat) :
    nestingProjection496.numerator[n]! = nestingEntries496 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries496, if_neg (by omega : ¬ n < 64)]

def nestingProjection497 : Projection := ⟨4,6,#[3,1,0,0,1,1,0,0,1,3,0,0,-1,-1,0,0,0,0,3,-1,0,0,-1,-1,0,0,-1,3,0,0,-1,-1,1,-1,0,0,3,-1,0,0,1,-1,0,0,-1,3,0,0,0,0,-1,-1,0,0,3,-1,0,0,-1,-1,0,0,-1,3]⟩
theorem nestingLookup497 : projections[497]! = nestingProjection497 := by
  rw [projections_lookup]
  rfl
def nestingEntries497 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 1) else 0) else (if n < 6 then 1 else 0)) else (if n < 12 then (if n < 10 then (if n < 9 then 1 else 3) else 0) else (if n < 14 then (-1) else 0))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 3 else (-1))) else (if n < 22 then 0 else (-1))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then (-1) else 3)) else (if n < 30 then 0 else (-1))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 1 else (-1)) else 0) else (if n < 38 then (if n < 37 then 3 else (-1)) else 0)) else (if n < 44 then (if n < 42 then (if n < 41 then 1 else (-1)) else 0) else (if n < 46 then (if n < 45 then (-1) else 3) else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then 0 else (-1)) else (if n < 54 then 0 else (if n < 55 then 3 else (-1)))) else (if n < 60 then (if n < 58 then 0 else (-1)) else (if n < 62 then 0 else (if n < 63 then (-1) else 3)))))) else 0
theorem nestingEntries_eq497 (n : Nat) :
    nestingProjection497.numerator[n]! = nestingEntries497 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries497, if_neg (by omega : ¬ n < 64)]

def nestingProjection498 : Projection := ⟨4,6,#[3,1,0,0,1,1,0,0,1,3,0,0,-1,-1,0,0,0,0,3,1,0,0,1,-1,0,0,1,3,0,0,-1,1,1,-1,0,0,3,-1,0,0,1,-1,0,0,-1,3,0,0,0,0,1,-1,0,0,3,1,0,0,-1,1,0,0,1,3]⟩
theorem nestingLookup498 : projections[498]! = nestingProjection498 := by
  rw [projections_lookup]
  rfl
def nestingEntries498 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 1) else 0) else (if n < 6 then 1 else 0)) else (if n < 12 then (if n < 10 then (if n < 9 then 1 else 3) else 0) else (if n < 14 then (-1) else 0))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 3 else 1)) else (if n < 22 then 0 else (if n < 23 then 1 else (-1)))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 1 else 3)) else (if n < 30 then 0 else (if n < 31 then (-1) else 1))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 1 else (-1)) else 0) else (if n < 38 then (if n < 37 then 3 else (-1)) else 0)) else (if n < 44 then (if n < 42 then (if n < 41 then 1 else (-1)) else 0) else (if n < 46 then (if n < 45 then (-1) else 3) else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then 0 else (if n < 51 then 1 else (-1))) else (if n < 54 then 0 else (if n < 55 then 3 else 1))) else (if n < 60 then (if n < 58 then 0 else (if n < 59 then (-1) else 1)) else (if n < 62 then 0 else (if n < 63 then 1 else 3)))))) else 0
theorem nestingEntries_eq498 (n : Nat) :
    nestingProjection498.numerator[n]! = nestingEntries498 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries498, if_neg (by omega : ¬ n < 64)]

def nestingProjection499 : Projection := ⟨2,6,#[2,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,1,0,0,0,0,-1,0,0,0,1,0,0,-1,0,0,0,0,0,2,0,0,0,0,0,0,0,0,2,0,0,0,0,0,-1,0,0,1,0,0,0,-1,0,0,0,0,1]⟩
theorem nestingLookup499 : projections[499]! = nestingProjection499 := by
  rw [projections_lookup]
  rfl
def nestingEntries499 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 2 else 0) else 0) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 2) else 0) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 1 else 0)) else (if n < 22 then 0 else (if n < 23 then 0 else (-1)))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 1)) else (if n < 30 then 0 else (if n < 31 then (-1) else 0))))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 2 else 0) else 0)) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 2) else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then 0 else (if n < 51 then 0 else (-1))) else (if n < 54 then 0 else (if n < 55 then 1 else 0))) else (if n < 60 then (if n < 58 then 0 else (if n < 59 then (-1) else 0)) else (if n < 62 then 0 else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq499 (n : Nat) :
    nestingProjection499.numerator[n]! = nestingEntries499 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries499, if_neg (by omega : ¬ n < 64)]

def nestingProjection500 : Projection := ⟨2,6,#[1,0,0,0,0,1,0,0,0,2,0,0,0,0,0,0,0,0,1,0,0,0,0,-1,0,0,0,2,0,0,0,0,0,0,0,0,2,0,0,0,1,0,0,0,0,1,0,0,0,0,0,0,0,0,2,0,0,0,-1,0,0,0,0,1]⟩
theorem nestingLookup500 : projections[500]! = nestingProjection500 := by
  rw [projections_lookup]
  rfl
def nestingEntries500 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else 0) else (if n < 6 then (if n < 5 then 0 else 1) else 0)) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 2) else 0) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 1 else 0)) else (if n < 22 then 0 else (if n < 23 then 0 else (-1)))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 2)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 2 else 0) else 0)) else (if n < 44 then (if n < 42 then (if n < 41 then 1 else 0) else 0) else (if n < 46 then (if n < 45 then 0 else 1) else 0))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 0 else (if n < 55 then 2 else 0))) else (if n < 60 then (if n < 58 then 0 else (if n < 59 then (-1) else 0)) else (if n < 62 then 0 else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq500 (n : Nat) :
    nestingProjection500.numerator[n]! = nestingEntries500 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries500, if_neg (by omega : ¬ n < 64)]

def nestingProjection501 : Projection := ⟨4,6,#[3,0,-1,0,0,1,0,-1,0,3,0,-1,-1,0,-1,0,-1,0,3,0,0,1,0,-1,0,-1,0,3,-1,0,-1,0,0,-1,0,-1,3,0,-1,0,1,0,1,0,0,3,0,1,0,-1,0,-1,-1,0,3,0,-1,0,-1,0,0,1,0,3]⟩
theorem nestingLookup501 : projections[501]! = nestingProjection501 := by
  rw [projections_lookup]
  rfl
def nestingEntries501 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 0) else (if n < 3 then (-1) else 0)) else (if n < 6 then (if n < 5 then 0 else 1) else (if n < 7 then 0 else (-1)))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 3) else (if n < 11 then 0 else (-1))) else (if n < 14 then (if n < 13 then (-1) else 0) else (if n < 15 then (-1) else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then (-1) else 0) else (if n < 19 then 3 else 0)) else (if n < 22 then (if n < 21 then 0 else 1) else (if n < 23 then 0 else (-1)))) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else (-1)) else (if n < 27 then 0 else 3)) else (if n < 30 then (if n < 29 then (-1) else 0) else (if n < 31 then (-1) else 0))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 0 else (-1)) else (if n < 35 then 0 else (-1))) else (if n < 38 then (if n < 37 then 3 else 0) else (if n < 39 then (-1) else 0))) else (if n < 44 then (if n < 42 then (if n < 41 then 1 else 0) else (if n < 43 then 1 else 0)) else (if n < 46 then (if n < 45 then 0 else 3) else (if n < 47 then 0 else 1)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else (-1)) else (if n < 51 then 0 else (-1))) else (if n < 54 then (if n < 53 then (-1) else 0) else (if n < 55 then 3 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then (-1) else 0) else (if n < 59 then (-1) else 0)) else (if n < 62 then (if n < 61 then 0 else 1) else (if n < 63 then 0 else 3)))))) else 0
theorem nestingEntries_eq501 (n : Nat) :
    nestingProjection501.numerator[n]! = nestingEntries501 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries501, if_neg (by omega : ¬ n < 64)]

def nestingProjection502 : Projection := ⟨4,6,#[3,0,-1,0,0,1,0,-1,0,3,0,1,-1,0,1,0,-1,0,3,0,0,1,0,-1,0,1,0,3,1,0,-1,0,0,-1,0,1,3,0,1,0,1,0,1,0,0,3,0,1,0,1,0,-1,1,0,3,0,-1,0,-1,0,0,1,0,3]⟩
theorem nestingLookup502 : projections[502]! = nestingProjection502 := by
  rw [projections_lookup]
  rfl
def nestingEntries502 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 0) else (if n < 3 then (-1) else 0)) else (if n < 6 then (if n < 5 then 0 else 1) else (if n < 7 then 0 else (-1)))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 3) else (if n < 11 then 0 else 1)) else (if n < 14 then (if n < 13 then (-1) else 0) else (if n < 15 then 1 else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then (-1) else 0) else (if n < 19 then 3 else 0)) else (if n < 22 then (if n < 21 then 0 else 1) else (if n < 23 then 0 else (-1)))) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else 1) else (if n < 27 then 0 else 3)) else (if n < 30 then (if n < 29 then 1 else 0) else (if n < 31 then (-1) else 0))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 0 else (-1)) else (if n < 35 then 0 else 1)) else (if n < 38 then (if n < 37 then 3 else 0) else (if n < 39 then 1 else 0))) else (if n < 44 then (if n < 42 then (if n < 41 then 1 else 0) else (if n < 43 then 1 else 0)) else (if n < 46 then (if n < 45 then 0 else 3) else (if n < 47 then 0 else 1)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else 1) else (if n < 51 then 0 else (-1))) else (if n < 54 then (if n < 53 then 1 else 0) else (if n < 55 then 3 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then (-1) else 0) else (if n < 59 then (-1) else 0)) else (if n < 62 then (if n < 61 then 0 else 1) else (if n < 63 then 0 else 3)))))) else 0
theorem nestingEntries_eq502 (n : Nat) :
    nestingProjection502.numerator[n]! = nestingEntries502 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries502, if_neg (by omega : ¬ n < 64)]

def nestingProjection503 : Projection := ⟨4,6,#[3,0,1,0,0,1,0,1,0,3,0,-1,-1,0,-1,0,1,0,3,0,0,-1,0,-1,0,-1,0,3,-1,0,-1,0,0,-1,0,-1,3,0,-1,0,1,0,-1,0,0,3,0,-1,0,-1,0,-1,-1,0,3,0,1,0,-1,0,0,-1,0,3]⟩
theorem nestingLookup503 : projections[503]! = nestingProjection503 := by
  rw [projections_lookup]
  rfl
def nestingEntries503 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 0) else (if n < 3 then 1 else 0)) else (if n < 6 then (if n < 5 then 0 else 1) else (if n < 7 then 0 else 1))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 3) else (if n < 11 then 0 else (-1))) else (if n < 14 then (if n < 13 then (-1) else 0) else (if n < 15 then (-1) else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 1 else 0) else (if n < 19 then 3 else 0)) else (if n < 22 then (if n < 21 then 0 else (-1)) else (if n < 23 then 0 else (-1)))) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else (-1)) else (if n < 27 then 0 else 3)) else (if n < 30 then (if n < 29 then (-1) else 0) else (if n < 31 then (-1) else 0))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 0 else (-1)) else (if n < 35 then 0 else (-1))) else (if n < 38 then (if n < 37 then 3 else 0) else (if n < 39 then (-1) else 0))) else (if n < 44 then (if n < 42 then (if n < 41 then 1 else 0) else (if n < 43 then (-1) else 0)) else (if n < 46 then (if n < 45 then 0 else 3) else (if n < 47 then 0 else (-1))))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else (-1)) else (if n < 51 then 0 else (-1))) else (if n < 54 then (if n < 53 then (-1) else 0) else (if n < 55 then 3 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then 1 else 0) else (if n < 59 then (-1) else 0)) else (if n < 62 then (if n < 61 then 0 else (-1)) else (if n < 63 then 0 else 3)))))) else 0
theorem nestingEntries_eq503 (n : Nat) :
    nestingProjection503.numerator[n]! = nestingEntries503 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries503, if_neg (by omega : ¬ n < 64)]

def nestingProjection504 : Projection := ⟨4,6,#[3,0,1,0,0,1,0,1,0,3,0,1,-1,0,1,0,1,0,3,0,0,-1,0,-1,0,1,0,3,1,0,-1,0,0,-1,0,1,3,0,1,0,1,0,-1,0,0,3,0,-1,0,1,0,-1,1,0,3,0,1,0,-1,0,0,-1,0,3]⟩
theorem nestingLookup504 : projections[504]! = nestingProjection504 := by
  rw [projections_lookup]
  rfl
def nestingEntries504 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 0) else (if n < 3 then 1 else 0)) else (if n < 6 then (if n < 5 then 0 else 1) else (if n < 7 then 0 else 1))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 3) else (if n < 11 then 0 else 1)) else (if n < 14 then (if n < 13 then (-1) else 0) else (if n < 15 then 1 else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 1 else 0) else (if n < 19 then 3 else 0)) else (if n < 22 then (if n < 21 then 0 else (-1)) else (if n < 23 then 0 else (-1)))) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else 1) else (if n < 27 then 0 else 3)) else (if n < 30 then (if n < 29 then 1 else 0) else (if n < 31 then (-1) else 0))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 0 else (-1)) else (if n < 35 then 0 else 1)) else (if n < 38 then (if n < 37 then 3 else 0) else (if n < 39 then 1 else 0))) else (if n < 44 then (if n < 42 then (if n < 41 then 1 else 0) else (if n < 43 then (-1) else 0)) else (if n < 46 then (if n < 45 then 0 else 3) else (if n < 47 then 0 else (-1))))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else 1) else (if n < 51 then 0 else (-1))) else (if n < 54 then (if n < 53 then 1 else 0) else (if n < 55 then 3 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then 1 else 0) else (if n < 59 then (-1) else 0)) else (if n < 62 then (if n < 61 then 0 else (-1)) else (if n < 63 then 0 else 3)))))) else 0
theorem nestingEntries_eq504 (n : Nat) :
    nestingProjection504.numerator[n]! = nestingEntries504 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries504, if_neg (by omega : ¬ n < 64)]

def nestingProjection505 : Projection := ⟨2,6,#[2,0,0,0,0,0,0,0,0,1,0,0,-1,0,0,0,0,0,2,0,0,0,0,0,0,0,0,1,0,0,-1,0,0,-1,0,0,1,0,0,0,0,0,0,0,0,2,0,0,0,0,0,-1,0,0,1,0,0,0,0,0,0,0,0,2]⟩
theorem nestingLookup505 : projections[505]! = nestingProjection505 := by
  rw [projections_lookup]
  rfl
def nestingEntries505 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 2 else 0) else 0) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else 0) else (if n < 14 then (if n < 13 then (-1) else 0) else 0))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 2 else 0)) else 0) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 1)) else (if n < 30 then 0 else (if n < 31 then (-1) else 0))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 0 else (-1)) else 0) else (if n < 38 then (if n < 37 then 1 else 0) else 0)) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 2) else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then 0 else (if n < 51 then 0 else (-1))) else (if n < 54 then 0 else (if n < 55 then 1 else 0))) else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 2)))))) else 0
theorem nestingEntries_eq505 (n : Nat) :
    nestingProjection505.numerator[n]! = nestingEntries505 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries505, if_neg (by omega : ¬ n < 64)]

def nestingProjection506 : Projection := ⟨2,4,#[0,0,0,0,0,0,0,0,0,1,1,0,0,0,0,0,0,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,-1,0,0,0,0,0,2,0,0,0,0,0,0,0,0,2,0,0,0,0,0,-1,0,0,1]⟩
theorem nestingLookup506 : projections[506]! = nestingProjection506 := by
  rw [projections_lookup]
  rfl
def nestingEntries506 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then 0 else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else (if n < 11 then 1 else 0)) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 0 else 1) else (if n < 19 then 1 else 0)) else 0) else 0)) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 1 else 0) else (if n < 39 then 0 else (-1)))) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 2) else 0))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 0 else (if n < 55 then 2 else 0))) else (if n < 60 then 0 else (if n < 62 then (if n < 61 then (-1) else 0) else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq506 (n : Nat) :
    nestingProjection506.numerator[n]! = nestingEntries506 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries506, if_neg (by omega : ¬ n < 64)]

def nestingProjection507 : Projection := ⟨2,4,#[2,0,0,0,0,0,0,0,0,1,-1,0,0,0,0,0,0,-1,1,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,1,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,1]⟩
theorem nestingLookup507 : projections[507]! = nestingProjection507 := by
  rw [projections_lookup]
  rfl
def nestingEntries507 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 2 else 0) else 0) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else (if n < 11 then (-1) else 0)) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 0 else (-1)) else (if n < 19 then 1 else 0)) else 0) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 2)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 1 else 0) else (if n < 39 then 0 else 1))) else 0) else (if n < 56 then 0 else (if n < 60 then 0 else (if n < 62 then (if n < 61 then 1 else 0) else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq507 (n : Nat) :
    nestingProjection507.numerator[n]! = nestingEntries507 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries507, if_neg (by omega : ¬ n < 64)]

def nestingProjection508 : Projection := ⟨4,4,#[2,-1,-1,0,1,0,0,-1,-1,2,0,1,0,1,-1,0,-1,0,2,1,0,-1,1,0,0,1,1,2,1,0,0,-1,1,0,0,1,2,-1,-1,0,0,1,-1,0,-1,2,0,-1,0,-1,1,0,-1,0,2,-1,-1,0,0,-1,0,-1,-1,2]⟩
theorem nestingLookup508 : projections[508]! = nestingProjection508 := by
  rw [projections_lookup]
  rfl
def nestingEntries508 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 2 else (-1)) else (if n < 3 then (-1) else 0)) else (if n < 6 then (if n < 5 then 1 else 0) else (if n < 7 then 0 else (-1)))) else (if n < 12 then (if n < 10 then (if n < 9 then (-1) else 2) else (if n < 11 then 0 else 1)) else (if n < 14 then (if n < 13 then 0 else 1) else (if n < 15 then (-1) else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then (-1) else 0) else (if n < 19 then 2 else 1)) else (if n < 22 then (if n < 21 then 0 else (-1)) else (if n < 23 then 1 else 0))) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else 1) else (if n < 27 then 1 else 2)) else (if n < 30 then (if n < 29 then 1 else 0) else (if n < 31 then 0 else (-1)))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 1 else 0) else (if n < 35 then 0 else 1)) else (if n < 38 then (if n < 37 then 2 else (-1)) else (if n < 39 then (-1) else 0))) else (if n < 44 then (if n < 42 then (if n < 41 then 0 else 1) else (if n < 43 then (-1) else 0)) else (if n < 46 then (if n < 45 then (-1) else 2) else (if n < 47 then 0 else (-1))))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else (-1)) else (if n < 51 then 1 else 0)) else (if n < 54 then (if n < 53 then (-1) else 0) else (if n < 55 then 2 else (-1)))) else (if n < 60 then (if n < 58 then (if n < 57 then (-1) else 0) else (if n < 59 then 0 else (-1))) else (if n < 62 then (if n < 61 then 0 else (-1)) else (if n < 63 then (-1) else 2)))))) else 0
theorem nestingEntries_eq508 (n : Nat) :
    nestingProjection508.numerator[n]! = nestingEntries508 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries508, if_neg (by omega : ¬ n < 64)]

def nestingProjection509 : Projection := ⟨4,4,#[2,1,1,0,-1,0,0,1,1,2,0,-1,0,-1,1,0,1,0,2,-1,0,1,-1,0,0,-1,-1,2,-1,0,0,1,-1,0,0,-1,2,1,1,0,0,-1,1,0,1,2,0,1,0,1,-1,0,1,0,2,1,1,0,0,1,0,1,1,2]⟩
theorem nestingLookup509 : projections[509]! = nestingProjection509 := by
  rw [projections_lookup]
  rfl
def nestingEntries509 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 2 else 1) else (if n < 3 then 1 else 0)) else (if n < 6 then (if n < 5 then (-1) else 0) else (if n < 7 then 0 else 1))) else (if n < 12 then (if n < 10 then (if n < 9 then 1 else 2) else (if n < 11 then 0 else (-1))) else (if n < 14 then (if n < 13 then 0 else (-1)) else (if n < 15 then 1 else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 1 else 0) else (if n < 19 then 2 else (-1))) else (if n < 22 then (if n < 21 then 0 else 1) else (if n < 23 then (-1) else 0))) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else (-1)) else (if n < 27 then (-1) else 2)) else (if n < 30 then (if n < 29 then (-1) else 0) else (if n < 31 then 0 else 1))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then (-1) else 0) else (if n < 35 then 0 else (-1))) else (if n < 38 then (if n < 37 then 2 else 1) else (if n < 39 then 1 else 0))) else (if n < 44 then (if n < 42 then (if n < 41 then 0 else (-1)) else (if n < 43 then 1 else 0)) else (if n < 46 then (if n < 45 then 1 else 2) else (if n < 47 then 0 else 1)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else 1) else (if n < 51 then (-1) else 0)) else (if n < 54 then (if n < 53 then 1 else 0) else (if n < 55 then 2 else 1))) else (if n < 60 then (if n < 58 then (if n < 57 then 1 else 0) else (if n < 59 then 0 else 1)) else (if n < 62 then (if n < 61 then 0 else 1) else (if n < 63 then 1 else 2)))))) else 0
theorem nestingEntries_eq509 (n : Nat) :
    nestingProjection509.numerator[n]! = nestingEntries509 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries509, if_neg (by omega : ¬ n < 64)]

def nestingProjection510 : Projection := ⟨4,7,#[4,0,0,0,0,0,0,0,0,3,-1,0,1,0,0,-1,0,-1,3,0,1,0,0,-1,0,0,0,4,0,0,0,0,0,1,1,0,3,0,0,1,0,0,0,0,0,4,0,0,0,0,0,0,0,0,4,0,0,-1,-1,0,1,0,0,3]⟩
theorem nestingLookup510 : projections[510]! = nestingProjection510 := by
  rw [projections_lookup]
  rfl
def nestingEntries510 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 4 else 0) else 0) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 3) else (if n < 11 then (-1) else 0)) else (if n < 14 then (if n < 13 then 1 else 0) else (if n < 15 then 0 else (-1))))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 0 else (-1)) else (if n < 19 then 3 else 0)) else (if n < 22 then (if n < 21 then 1 else 0) else (if n < 23 then 0 else (-1)))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 4)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 0 else 1) else (if n < 35 then 1 else 0)) else (if n < 38 then (if n < 37 then 3 else 0) else (if n < 39 then 0 else 1))) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 4) else 0))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 0 else (if n < 55 then 4 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then 0 else (-1)) else (if n < 59 then (-1) else 0)) else (if n < 62 then (if n < 61 then 1 else 0) else (if n < 63 then 0 else 3)))))) else 0
theorem nestingEntries_eq510 (n : Nat) :
    nestingProjection510.numerator[n]! = nestingEntries510 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries510, if_neg (by omega : ¬ n < 64)]

def nestingProjection511 : Projection := ⟨4,7,#[4,0,0,0,0,0,0,0,0,3,1,0,1,0,0,1,0,1,3,0,-1,0,0,-1,0,0,0,4,0,0,0,0,0,1,-1,0,3,0,0,-1,0,0,0,0,0,4,0,0,0,0,0,0,0,0,4,0,0,1,-1,0,-1,0,0,3]⟩
theorem nestingLookup511 : projections[511]! = nestingProjection511 := by
  rw [projections_lookup]
  rfl
def nestingEntries511 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 4 else 0) else 0) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 3) else (if n < 11 then 1 else 0)) else (if n < 14 then (if n < 13 then 1 else 0) else (if n < 15 then 0 else 1)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 0 else 1) else (if n < 19 then 3 else 0)) else (if n < 22 then (if n < 21 then (-1) else 0) else (if n < 23 then 0 else (-1)))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 4)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 0 else 1) else (if n < 35 then (-1) else 0)) else (if n < 38 then (if n < 37 then 3 else 0) else (if n < 39 then 0 else (-1)))) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 4) else 0))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 0 else (if n < 55 then 4 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then 0 else 1) else (if n < 59 then (-1) else 0)) else (if n < 62 then (if n < 61 then (-1) else 0) else (if n < 63 then 0 else 3)))))) else 0
theorem nestingEntries_eq511 (n : Nat) :
    nestingProjection511.numerator[n]! = nestingEntries511 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries511, if_neg (by omega : ¬ n < 64)]

end CSL.Construction.PhysicalFramePaths


