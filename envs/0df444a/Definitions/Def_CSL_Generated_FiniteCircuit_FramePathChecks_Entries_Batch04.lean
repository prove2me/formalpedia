-- Prove2me | Definitions.Def_CSL_Generated_FiniteCircuit_FramePathChecks_Entries_Batch04
-- name    : CSL_Generated_FiniteCircuit_FramePathChecks_Entries_Batch04
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T13:37:57.87775+00:00
-- url     : https://prove2.me/theorems/4f575a44-c5b3-4ca2-91d3-2801fa98b9fc
-- title:
--   Coded sorting library: Generated / FiniteCircuit / FramePathChecks / Entries / Batch04
-- statement:
--   Module `CodedSorting.Generated.FiniteCircuit.FramePathChecks.Entries.Batch04` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   Generated physical-frame checks. Uncompiled until a build record exists.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Generated.FiniteCircuit.FramePathChecks.Entries.Batch04

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Generated_FiniteCircuit_FramePathChecks_FunctionBase

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def nestingProjection512 : Projection := ⟨4,7,#[4,0,0,0,0,0,0,0,0,3,-1,0,0,1,1,0,0,-1,3,0,0,1,1,0,0,0,0,4,0,0,0,0,0,0,0,0,4,0,0,0,0,1,1,0,0,3,-1,0,0,1,1,0,0,-1,3,0,0,0,0,0,0,0,0,4]⟩
theorem nestingLookup512 : projections[512]! = nestingProjection512 := by
  rw [projections_lookup]
  rfl
def nestingEntries512 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 4 else 0) else 0) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 3) else (if n < 11 then (-1) else 0)) else (if n < 14 then (if n < 13 then 0 else 1) else (if n < 15 then 1 else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 0 else (-1)) else (if n < 19 then 3 else 0)) else (if n < 22 then (if n < 21 then 0 else 1) else (if n < 23 then 1 else 0))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 4)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 4 else 0) else 0)) else (if n < 44 then (if n < 42 then (if n < 41 then 0 else 1) else (if n < 43 then 1 else 0)) else (if n < 46 then (if n < 45 then 0 else 3) else (if n < 47 then (-1) else 0)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else 1) else (if n < 51 then 1 else 0)) else (if n < 54 then (if n < 53 then 0 else (-1)) else (if n < 55 then 3 else 0))) else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 4)))))) else 0
theorem nestingEntries_eq512 (n : Nat) :
    nestingProjection512.numerator[n]! = nestingEntries512 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries512, if_neg (by omega : ¬ n < 64)]

def nestingProjection513 : Projection := ⟨4,7,#[4,0,0,0,0,0,0,0,0,3,1,0,0,-1,1,0,0,1,3,0,0,1,-1,0,0,0,0,4,0,0,0,0,0,0,0,0,4,0,0,0,0,-1,1,0,0,3,1,0,0,1,-1,0,0,1,3,0,0,0,0,0,0,0,0,4]⟩
theorem nestingLookup513 : projections[513]! = nestingProjection513 := by
  rw [projections_lookup]
  rfl
def nestingEntries513 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 4 else 0) else 0) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 3) else (if n < 11 then 1 else 0)) else (if n < 14 then (if n < 13 then 0 else (-1)) else (if n < 15 then 1 else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 0 else 1) else (if n < 19 then 3 else 0)) else (if n < 22 then (if n < 21 then 0 else 1) else (if n < 23 then (-1) else 0))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 4)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 4 else 0) else 0)) else (if n < 44 then (if n < 42 then (if n < 41 then 0 else (-1)) else (if n < 43 then 1 else 0)) else (if n < 46 then (if n < 45 then 0 else 3) else (if n < 47 then 1 else 0)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else 1) else (if n < 51 then (-1) else 0)) else (if n < 54 then (if n < 53 then 0 else 1) else (if n < 55 then 3 else 0))) else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 4)))))) else 0
theorem nestingEntries_eq513 (n : Nat) :
    nestingProjection513.numerator[n]! = nestingEntries513 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries513, if_neg (by omega : ¬ n < 64)]

def nestingProjection514 : Projection := ⟨4,7,#[4,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,3,-1,-1,-1,0,0,0,0,-1,3,-1,-1,0,0,0,0,-1,-1,3,-1,0,0,0,0,-1,-1,-1,3]⟩
theorem nestingLookup514 : projections[514]! = nestingProjection514 := by
  rw [projections_lookup]
  rfl
def nestingEntries514 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 4 else 0) else 0) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 4) else 0) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 4 else 0)) else 0) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 4)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 3 else (-1)) else (-1))) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then (-1) else 3) else (-1)))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then (-1) else (if n < 55 then 3 else (-1)))) else (if n < 60 then 0 else (if n < 62 then (-1) else (if n < 63 then (-1) else 3)))))) else 0
theorem nestingEntries_eq514 (n : Nat) :
    nestingProjection514.numerator[n]! = nestingEntries514 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries514, if_neg (by omega : ¬ n < 64)]

def nestingProjection515 : Projection := ⟨4,7,#[3,-1,1,-1,0,0,0,0,-1,3,1,-1,0,0,0,0,1,1,3,1,0,0,0,0,-1,-1,1,3,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,4]⟩
theorem nestingLookup515 : projections[515]! = nestingProjection515 := by
  rw [projections_lookup]
  rfl
def nestingEntries515 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else (-1)) else (if n < 3 then 1 else (-1))) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then (-1) else 3) else (if n < 11 then 1 else (-1))) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then 1 else (if n < 19 then 3 else 1)) else 0) else (if n < 28 then (if n < 26 then (-1) else (if n < 27 then 1 else 3)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 4 else 0) else 0)) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 4) else 0))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 0 else (if n < 55 then 4 else 0))) else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 4)))))) else 0
theorem nestingEntries_eq515 (n : Nat) :
    nestingProjection515.numerator[n]! = nestingEntries515 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries515, if_neg (by omega : ¬ n < 64)]

def nestingProjection516 : Projection := ⟨4,7,#[3,0,0,-1,-1,0,0,-1,0,4,0,0,0,0,0,0,0,0,4,0,0,0,0,0,-1,0,0,3,-1,0,0,-1,-1,0,0,-1,3,0,0,-1,0,0,0,0,0,4,0,0,0,0,0,0,0,0,4,0,-1,0,0,-1,-1,0,0,3]⟩
theorem nestingLookup516 : projections[516]! = nestingProjection516 := by
  rw [projections_lookup]
  rfl
def nestingEntries516 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 0) else (if n < 3 then 0 else (-1))) else (if n < 6 then (if n < 5 then (-1) else 0) else (if n < 7 then 0 else (-1)))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 4) else 0) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 4 else 0)) else 0) else (if n < 28 then (if n < 26 then (if n < 25 then (-1) else 0) else (if n < 27 then 0 else 3)) else (if n < 30 then (if n < 29 then (-1) else 0) else (if n < 31 then 0 else (-1)))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then (-1) else 0) else (if n < 35 then 0 else (-1))) else (if n < 38 then (if n < 37 then 3 else 0) else (if n < 39 then 0 else (-1)))) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 4) else 0))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 0 else (if n < 55 then 4 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then (-1) else 0) else (if n < 59 then 0 else (-1))) else (if n < 62 then (if n < 61 then (-1) else 0) else (if n < 63 then 0 else 3)))))) else 0
theorem nestingEntries_eq516 (n : Nat) :
    nestingProjection516.numerator[n]! = nestingEntries516 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries516, if_neg (by omega : ¬ n < 64)]

def nestingProjection517 : Projection := ⟨4,7,#[4,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,3,-1,0,0,-1,1,0,0,-1,3,0,0,-1,1,0,0,0,0,4,0,0,0,0,0,0,0,0,4,0,0,0,0,-1,-1,0,0,3,1,0,0,1,1,0,0,1,3]⟩
theorem nestingLookup517 : projections[517]! = nestingProjection517 := by
  rw [projections_lookup]
  rfl
def nestingEntries517 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 4 else 0) else 0) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 4) else 0) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 3 else (-1))) else (if n < 22 then 0 else (if n < 23 then (-1) else 1))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then (-1) else 3)) else (if n < 30 then 0 else (if n < 31 then (-1) else 1))))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 4 else 0) else 0)) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 4) else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then 0 else (-1)) else (if n < 54 then 0 else (if n < 55 then 3 else 1))) else (if n < 60 then (if n < 58 then 0 else 1) else (if n < 62 then 0 else (if n < 63 then 1 else 3)))))) else 0
theorem nestingEntries_eq517 (n : Nat) :
    nestingProjection517.numerator[n]! = nestingEntries517 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries517, if_neg (by omega : ¬ n < 64)]

def nestingProjection518 : Projection := ⟨4,7,#[4,0,0,0,0,0,0,0,0,3,0,1,0,1,0,1,0,0,4,0,0,0,0,0,0,1,0,3,0,-1,0,-1,0,0,0,0,4,0,0,0,0,1,0,-1,0,3,0,-1,0,0,0,0,0,0,4,0,0,1,0,-1,0,-1,0,3]⟩
theorem nestingLookup518 : projections[518]! = nestingProjection518 := by
  rw [projections_lookup]
  rfl
def nestingEntries518 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 4 else 0) else 0) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 3) else (if n < 11 then 0 else 1)) else (if n < 14 then (if n < 13 then 0 else 1) else (if n < 15 then 0 else 1)))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 4 else 0)) else 0) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else 1) else (if n < 27 then 0 else 3)) else (if n < 30 then (if n < 29 then 0 else (-1)) else (if n < 31 then 0 else (-1)))))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 4 else 0) else 0)) else (if n < 44 then (if n < 42 then (if n < 41 then 0 else 1) else (if n < 43 then 0 else (-1))) else (if n < 46 then (if n < 45 then 0 else 3) else (if n < 47 then 0 else (-1))))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 0 else (if n < 55 then 4 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then 0 else 1) else (if n < 59 then 0 else (-1))) else (if n < 62 then (if n < 61 then 0 else (-1)) else (if n < 63 then 0 else 3)))))) else 0
theorem nestingEntries_eq518 (n : Nat) :
    nestingProjection518.numerator[n]! = nestingEntries518 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries518, if_neg (by omega : ¬ n < 64)]

def nestingProjection519 : Projection := ⟨4,4,#[2,1,1,0,1,0,0,-1,1,2,0,1,0,1,1,0,1,0,2,1,0,-1,-1,0,0,1,1,2,-1,0,0,1,1,0,0,-1,2,1,-1,0,0,1,-1,0,1,2,0,1,0,1,-1,0,-1,0,2,-1,-1,0,0,1,0,1,-1,2]⟩
theorem nestingLookup519 : projections[519]! = nestingProjection519 := by
  rw [projections_lookup]
  rfl
def nestingEntries519 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 2 else 1) else (if n < 3 then 1 else 0)) else (if n < 6 then (if n < 5 then 1 else 0) else (if n < 7 then 0 else (-1)))) else (if n < 12 then (if n < 10 then (if n < 9 then 1 else 2) else (if n < 11 then 0 else 1)) else (if n < 14 then (if n < 13 then 0 else 1) else (if n < 15 then 1 else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 1 else 0) else (if n < 19 then 2 else 1)) else (if n < 22 then (if n < 21 then 0 else (-1)) else (if n < 23 then (-1) else 0))) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else 1) else (if n < 27 then 1 else 2)) else (if n < 30 then (if n < 29 then (-1) else 0) else (if n < 31 then 0 else 1))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 1 else 0) else (if n < 35 then 0 else (-1))) else (if n < 38 then (if n < 37 then 2 else 1) else (if n < 39 then (-1) else 0))) else (if n < 44 then (if n < 42 then (if n < 41 then 0 else 1) else (if n < 43 then (-1) else 0)) else (if n < 46 then (if n < 45 then 1 else 2) else (if n < 47 then 0 else 1)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else 1) else (if n < 51 then (-1) else 0)) else (if n < 54 then (if n < 53 then (-1) else 0) else (if n < 55 then 2 else (-1)))) else (if n < 60 then (if n < 58 then (if n < 57 then (-1) else 0) else (if n < 59 then 0 else 1)) else (if n < 62 then (if n < 61 then 0 else 1) else (if n < 63 then (-1) else 2)))))) else 0
theorem nestingEntries_eq519 (n : Nat) :
    nestingProjection519.numerator[n]! = nestingEntries519 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries519, if_neg (by omega : ¬ n < 64)]

def nestingProjection520 : Projection := ⟨4,4,#[2,-1,-1,0,-1,0,0,1,-1,2,0,-1,0,-1,-1,0,-1,0,2,-1,0,1,1,0,0,-1,-1,2,1,0,0,-1,-1,0,0,1,2,-1,1,0,0,-1,1,0,-1,2,0,-1,0,-1,1,0,1,0,2,1,1,0,0,-1,0,-1,1,2]⟩
theorem nestingLookup520 : projections[520]! = nestingProjection520 := by
  rw [projections_lookup]
  rfl
def nestingEntries520 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 2 else (-1)) else (if n < 3 then (-1) else 0)) else (if n < 6 then (if n < 5 then (-1) else 0) else (if n < 7 then 0 else 1))) else (if n < 12 then (if n < 10 then (if n < 9 then (-1) else 2) else (if n < 11 then 0 else (-1))) else (if n < 14 then (if n < 13 then 0 else (-1)) else (if n < 15 then (-1) else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then (-1) else 0) else (if n < 19 then 2 else (-1))) else (if n < 22 then (if n < 21 then 0 else 1) else (if n < 23 then 1 else 0))) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else (-1)) else (if n < 27 then (-1) else 2)) else (if n < 30 then (if n < 29 then 1 else 0) else (if n < 31 then 0 else (-1)))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then (-1) else 0) else (if n < 35 then 0 else 1)) else (if n < 38 then (if n < 37 then 2 else (-1)) else (if n < 39 then 1 else 0))) else (if n < 44 then (if n < 42 then (if n < 41 then 0 else (-1)) else (if n < 43 then 1 else 0)) else (if n < 46 then (if n < 45 then (-1) else 2) else (if n < 47 then 0 else (-1))))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else (-1)) else (if n < 51 then 1 else 0)) else (if n < 54 then (if n < 53 then 1 else 0) else (if n < 55 then 2 else 1))) else (if n < 60 then (if n < 58 then (if n < 57 then 1 else 0) else (if n < 59 then 0 else (-1))) else (if n < 62 then (if n < 61 then 0 else (-1)) else (if n < 63 then 1 else 2)))))) else 0
theorem nestingEntries_eq520 (n : Nat) :
    nestingProjection520.numerator[n]! = nestingEntries520 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries520, if_neg (by omega : ¬ n < 64)]

def nestingProjection521 : Projection := ⟨2,4,#[1,0,0,0,0,1,0,0,0,1,0,0,-1,0,0,0,0,0,1,0,0,0,0,-1,0,0,0,1,0,0,-1,0,0,-1,0,0,1,0,0,0,1,0,0,0,0,1,0,0,0,0,0,-1,0,0,1,0,0,0,-1,0,0,0,0,1]⟩
theorem nestingLookup521 : projections[521]! = nestingProjection521 := by
  rw [projections_lookup]
  rfl
def nestingEntries521 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else 0) else (if n < 6 then (if n < 5 then 0 else 1) else 0)) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else 0) else (if n < 14 then (if n < 13 then (-1) else 0) else 0))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 1 else 0)) else (if n < 22 then 0 else (if n < 23 then 0 else (-1)))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 1)) else (if n < 30 then 0 else (if n < 31 then (-1) else 0))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 0 else (-1)) else 0) else (if n < 38 then (if n < 37 then 1 else 0) else 0)) else (if n < 44 then (if n < 42 then (if n < 41 then 1 else 0) else 0) else (if n < 46 then (if n < 45 then 0 else 1) else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then 0 else (if n < 51 then 0 else (-1))) else (if n < 54 then 0 else (if n < 55 then 1 else 0))) else (if n < 60 then (if n < 58 then 0 else (if n < 59 then (-1) else 0)) else (if n < 62 then 0 else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq521 (n : Nat) :
    nestingProjection521.numerator[n]! = nestingEntries521 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries521, if_neg (by omega : ¬ n < 64)]

def nestingProjection522 : Projection := ⟨2,4,#[1,0,0,0,0,0,-1,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,0,1,0,0,-1,0,0,0,0,0,1,0,0,0,0,0,0,0,0,2]⟩
theorem nestingLookup522 : projections[522]! = nestingProjection522 := by
  rw [projections_lookup]
  rfl
def nestingEntries522 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else 0) else (if n < 6 then 0 else (if n < 7 then (-1) else 0))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 2) else 0) else 0)) else (if n < 24 then 0 else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 1)) else (if n < 30 then (if n < 29 then 0 else (-1)) else 0)))) else (if n < 48 then (if n < 40 then 0 else (if n < 44 then (if n < 42 then 0 else (if n < 43 then 0 else (-1))) else (if n < 46 then (if n < 45 then 0 else 1) else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then (-1) else 0) else 0) else (if n < 54 then 0 else (if n < 55 then 1 else 0))) else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 2)))))) else 0
theorem nestingEntries_eq522 (n : Nat) :
    nestingProjection522.numerator[n]! = nestingEntries522 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries522, if_neg (by omega : ¬ n < 64)]

def nestingProjection523 : Projection := ⟨2,4,#[1,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,1,0,1,0,0,0,0,0,0,2,0,0,0,0,0,0,1,0,1,0,0,1,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0]⟩
theorem nestingLookup523 : projections[523]! = nestingProjection523 := by
  rw [projections_lookup]
  rfl
def nestingEntries523 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else 0) else (if n < 6 then 0 else (if n < 7 then 1 else 0))) else 0) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 2 else 0)) else 0) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 1)) else (if n < 30 then (if n < 29 then 0 else 1) else 0)))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 2 else 0) else 0)) else (if n < 44 then (if n < 42 then 0 else (if n < 43 then 0 else 1)) else (if n < 46 then (if n < 45 then 0 else 1) else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 1 else 0) else 0) else (if n < 54 then 0 else (if n < 55 then 1 else 0))) else 0))) else 0
theorem nestingEntries_eq523 (n : Nat) :
    nestingProjection523.numerator[n]! = nestingEntries523 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries523, if_neg (by omega : ¬ n < 64)]

def nestingProjection524 : Projection := ⟨2,4,#[1,0,0,0,0,-1,0,0,0,1,0,0,1,0,0,0,0,0,1,0,0,0,0,1,0,0,0,1,0,0,1,0,0,1,0,0,1,0,0,0,-1,0,0,0,0,1,0,0,0,0,0,1,0,0,1,0,0,0,1,0,0,0,0,1]⟩
theorem nestingLookup524 : projections[524]! = nestingProjection524 := by
  rw [projections_lookup]
  rfl
def nestingEntries524 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else 0) else (if n < 6 then (if n < 5 then 0 else (-1)) else 0)) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else 0) else (if n < 14 then (if n < 13 then 1 else 0) else 0))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 1 else 0)) else (if n < 22 then 0 else (if n < 23 then 0 else 1))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 1)) else (if n < 30 then 0 else (if n < 31 then 1 else 0))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 0 else 1) else 0) else (if n < 38 then (if n < 37 then 1 else 0) else 0)) else (if n < 44 then (if n < 42 then (if n < 41 then (-1) else 0) else 0) else (if n < 46 then (if n < 45 then 0 else 1) else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then 0 else (if n < 51 then 0 else 1)) else (if n < 54 then 0 else (if n < 55 then 1 else 0))) else (if n < 60 then (if n < 58 then 0 else (if n < 59 then 1 else 0)) else (if n < 62 then 0 else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq524 (n : Nat) :
    nestingProjection524.numerator[n]! = nestingEntries524 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries524, if_neg (by omega : ¬ n < 64)]

def nestingProjection525 : Projection := ⟨1,7,#[0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,1]⟩
theorem nestingLookup525 : projections[525]! = nestingProjection525 := by
  rw [projections_lookup]
  rfl
def nestingEntries525 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then 0 else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else 0) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 1 else 0)) else 0) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 1)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 1 else 0) else 0)) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 1) else 0))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 0 else (if n < 55 then 1 else 0))) else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq525 (n : Nat) :
    nestingProjection525.numerator[n]! = nestingEntries525 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries525, if_neg (by omega : ¬ n < 64)]

def nestingProjection526 : Projection := ⟨1,7,#[1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,1]⟩
theorem nestingLookup526 : projections[526]! = nestingProjection526 := by
  rw [projections_lookup]
  rfl
def nestingEntries526 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else 0) else 0) else 0) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 1 else 0)) else 0) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 1)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 1 else 0) else 0)) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 1) else 0))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 0 else (if n < 55 then 1 else 0))) else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq526 (n : Nat) :
    nestingProjection526.numerator[n]! = nestingEntries526 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries526, if_neg (by omega : ¬ n < 64)]

def nestingProjection527 : Projection := ⟨1,7,#[1,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,1]⟩
theorem nestingLookup527 : projections[527]! = nestingProjection527 := by
  rw [projections_lookup]
  rfl
def nestingEntries527 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else 0) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else 0) else 0)) else (if n < 24 then 0 else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 1)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 1 else 0) else 0)) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 1) else 0))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 0 else (if n < 55 then 1 else 0))) else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq527 (n : Nat) :
    nestingProjection527.numerator[n]! = nestingEntries527 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries527, if_neg (by omega : ¬ n < 64)]

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def nestingProjection528 : Projection := ⟨1,7,#[1,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,1]⟩
theorem nestingLookup528 : projections[528]! = nestingProjection528 := by
  rw [projections_lookup]
  rfl
def nestingEntries528 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else 0) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else 0) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 1 else 0)) else 0) else 0)) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 1 else 0) else 0)) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 1) else 0))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 0 else (if n < 55 then 1 else 0))) else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq528 (n : Nat) :
    nestingProjection528.numerator[n]! = nestingEntries528 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries528, if_neg (by omega : ¬ n < 64)]

def nestingProjection529 : Projection := ⟨1,7,#[1,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,1]⟩
theorem nestingLookup529 : projections[529]! = nestingProjection529 := by
  rw [projections_lookup]
  rfl
def nestingEntries529 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else 0) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else 0) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 1 else 0)) else 0) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 1)) else 0))) else (if n < 48 then (if n < 40 then 0 else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 1) else 0))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 0 else (if n < 55 then 1 else 0))) else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq529 (n : Nat) :
    nestingProjection529.numerator[n]! = nestingEntries529 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries529, if_neg (by omega : ¬ n < 64)]

def nestingProjection530 : Projection := ⟨1,7,#[1,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,1]⟩
theorem nestingLookup530 : projections[530]! = nestingProjection530 := by
  rw [projections_lookup]
  rfl
def nestingEntries530 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else 0) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else 0) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 1 else 0)) else 0) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 1)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 1 else 0) else 0)) else 0) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 0 else (if n < 55 then 1 else 0))) else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq530 (n : Nat) :
    nestingProjection530.numerator[n]! = nestingEntries530 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries530, if_neg (by omega : ¬ n < 64)]

def nestingProjection531 : Projection := ⟨1,7,#[1,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1]⟩
theorem nestingLookup531 : projections[531]! = nestingProjection531 := by
  rw [projections_lookup]
  rfl
def nestingEntries531 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else 0) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else 0) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 1 else 0)) else 0) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 1)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 1 else 0) else 0)) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 1) else 0))) else (if n < 56 then 0 else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq531 (n : Nat) :
    nestingProjection531.numerator[n]! = nestingEntries531 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries531, if_neg (by omega : ¬ n < 64)]

def nestingProjection532 : Projection := ⟨1,7,#[1,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0]⟩
theorem nestingLookup532 : projections[532]! = nestingProjection532 := by
  rw [projections_lookup]
  rfl
def nestingEntries532 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else 0) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else 0) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 1 else 0)) else 0) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 1)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 1 else 0) else 0)) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 1) else 0))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 0 else (if n < 55 then 1 else 0))) else 0))) else 0
theorem nestingEntries_eq532 (n : Nat) :
    nestingProjection532.numerator[n]! = nestingEntries532 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries532, if_neg (by omega : ¬ n < 64)]

def nestingProjection533 : Projection := ⟨4,7,#[4,0,0,0,0,0,0,0,0,3,-1,0,-1,0,0,-1,0,-1,3,0,-1,0,0,-1,0,0,0,4,0,0,0,0,0,-1,-1,0,3,0,0,-1,0,0,0,0,0,4,0,0,0,0,0,0,0,0,4,0,0,-1,-1,0,-1,0,0,3]⟩
theorem nestingLookup533 : projections[533]! = nestingProjection533 := by
  rw [projections_lookup]
  rfl
def nestingEntries533 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 4 else 0) else 0) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 3) else (if n < 11 then (-1) else 0)) else (if n < 14 then (if n < 13 then (-1) else 0) else (if n < 15 then 0 else (-1))))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 0 else (-1)) else (if n < 19 then 3 else 0)) else (if n < 22 then (if n < 21 then (-1) else 0) else (if n < 23 then 0 else (-1)))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 4)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 0 else (-1)) else (if n < 35 then (-1) else 0)) else (if n < 38 then (if n < 37 then 3 else 0) else (if n < 39 then 0 else (-1)))) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 4) else 0))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 0 else (if n < 55 then 4 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then 0 else (-1)) else (if n < 59 then (-1) else 0)) else (if n < 62 then (if n < 61 then (-1) else 0) else (if n < 63 then 0 else 3)))))) else 0
theorem nestingEntries_eq533 (n : Nat) :
    nestingProjection533.numerator[n]! = nestingEntries533 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries533, if_neg (by omega : ¬ n < 64)]

def nestingProjection534 : Projection := ⟨4,7,#[4,0,0,0,0,0,0,0,0,3,-1,0,-1,0,0,1,0,-1,3,0,-1,0,0,1,0,0,0,4,0,0,0,0,0,-1,-1,0,3,0,0,1,0,0,0,0,0,4,0,0,0,0,0,0,0,0,4,0,0,1,1,0,1,0,0,3]⟩
theorem nestingLookup534 : projections[534]! = nestingProjection534 := by
  rw [projections_lookup]
  rfl
def nestingEntries534 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 4 else 0) else 0) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 3) else (if n < 11 then (-1) else 0)) else (if n < 14 then (if n < 13 then (-1) else 0) else (if n < 15 then 0 else 1)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 0 else (-1)) else (if n < 19 then 3 else 0)) else (if n < 22 then (if n < 21 then (-1) else 0) else (if n < 23 then 0 else 1))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 4)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 0 else (-1)) else (if n < 35 then (-1) else 0)) else (if n < 38 then (if n < 37 then 3 else 0) else (if n < 39 then 0 else 1))) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 4) else 0))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 0 else (if n < 55 then 4 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then 0 else 1) else (if n < 59 then 1 else 0)) else (if n < 62 then (if n < 61 then 1 else 0) else (if n < 63 then 0 else 3)))))) else 0
theorem nestingEntries_eq534 (n : Nat) :
    nestingProjection534.numerator[n]! = nestingEntries534 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries534, if_neg (by omega : ¬ n < 64)]

def nestingProjection535 : Projection := ⟨4,7,#[4,0,0,0,0,0,0,0,0,3,-1,0,1,0,0,1,0,-1,3,0,1,0,0,1,0,0,0,4,0,0,0,0,0,1,1,0,3,0,0,-1,0,0,0,0,0,4,0,0,0,0,0,0,0,0,4,0,0,1,1,0,-1,0,0,3]⟩
theorem nestingLookup535 : projections[535]! = nestingProjection535 := by
  rw [projections_lookup]
  rfl
def nestingEntries535 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 4 else 0) else 0) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 3) else (if n < 11 then (-1) else 0)) else (if n < 14 then (if n < 13 then 1 else 0) else (if n < 15 then 0 else 1)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 0 else (-1)) else (if n < 19 then 3 else 0)) else (if n < 22 then (if n < 21 then 1 else 0) else (if n < 23 then 0 else 1))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 4)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 0 else 1) else (if n < 35 then 1 else 0)) else (if n < 38 then (if n < 37 then 3 else 0) else (if n < 39 then 0 else (-1)))) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 4) else 0))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 0 else (if n < 55 then 4 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then 0 else 1) else (if n < 59 then 1 else 0)) else (if n < 62 then (if n < 61 then (-1) else 0) else (if n < 63 then 0 else 3)))))) else 0
theorem nestingEntries_eq535 (n : Nat) :
    nestingProjection535.numerator[n]! = nestingEntries535 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries535, if_neg (by omega : ¬ n < 64)]

def nestingProjection536 : Projection := ⟨4,7,#[4,0,0,0,0,0,0,0,0,3,1,0,-1,0,0,-1,0,1,3,0,1,0,0,1,0,0,0,4,0,0,0,0,0,-1,1,0,3,0,0,-1,0,0,0,0,0,4,0,0,0,0,0,0,0,0,4,0,0,-1,1,0,-1,0,0,3]⟩
theorem nestingLookup536 : projections[536]! = nestingProjection536 := by
  rw [projections_lookup]
  rfl
def nestingEntries536 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 4 else 0) else 0) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 3) else (if n < 11 then 1 else 0)) else (if n < 14 then (if n < 13 then (-1) else 0) else (if n < 15 then 0 else (-1))))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 0 else 1) else (if n < 19 then 3 else 0)) else (if n < 22 then (if n < 21 then 1 else 0) else (if n < 23 then 0 else 1))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 4)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 0 else (-1)) else (if n < 35 then 1 else 0)) else (if n < 38 then (if n < 37 then 3 else 0) else (if n < 39 then 0 else (-1)))) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 4) else 0))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 0 else (if n < 55 then 4 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then 0 else (-1)) else (if n < 59 then 1 else 0)) else (if n < 62 then (if n < 61 then (-1) else 0) else (if n < 63 then 0 else 3)))))) else 0
theorem nestingEntries_eq536 (n : Nat) :
    nestingProjection536.numerator[n]! = nestingEntries536 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries536, if_neg (by omega : ¬ n < 64)]

def nestingProjection537 : Projection := ⟨4,7,#[4,0,0,0,0,0,0,0,0,3,1,0,-1,0,0,1,0,1,3,0,1,0,0,-1,0,0,0,4,0,0,0,0,0,-1,1,0,3,0,0,1,0,0,0,0,0,4,0,0,0,0,0,0,0,0,4,0,0,1,-1,0,1,0,0,3]⟩
theorem nestingLookup537 : projections[537]! = nestingProjection537 := by
  rw [projections_lookup]
  rfl
def nestingEntries537 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 4 else 0) else 0) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 3) else (if n < 11 then 1 else 0)) else (if n < 14 then (if n < 13 then (-1) else 0) else (if n < 15 then 0 else 1)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 0 else 1) else (if n < 19 then 3 else 0)) else (if n < 22 then (if n < 21 then 1 else 0) else (if n < 23 then 0 else (-1)))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 4)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 0 else (-1)) else (if n < 35 then 1 else 0)) else (if n < 38 then (if n < 37 then 3 else 0) else (if n < 39 then 0 else 1))) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 4) else 0))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 0 else (if n < 55 then 4 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then 0 else 1) else (if n < 59 then (-1) else 0)) else (if n < 62 then (if n < 61 then 1 else 0) else (if n < 63 then 0 else 3)))))) else 0
theorem nestingEntries_eq537 (n : Nat) :
    nestingProjection537.numerator[n]! = nestingEntries537 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries537, if_neg (by omega : ¬ n < 64)]

def nestingProjection538 : Projection := ⟨4,7,#[4,0,0,0,0,0,0,0,0,3,1,0,1,0,0,-1,0,1,3,0,-1,0,0,1,0,0,0,4,0,0,0,0,0,1,-1,0,3,0,0,1,0,0,0,0,0,4,0,0,0,0,0,0,0,0,4,0,0,-1,1,0,1,0,0,3]⟩
theorem nestingLookup538 : projections[538]! = nestingProjection538 := by
  rw [projections_lookup]
  rfl
def nestingEntries538 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 4 else 0) else 0) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 3) else (if n < 11 then 1 else 0)) else (if n < 14 then (if n < 13 then 1 else 0) else (if n < 15 then 0 else (-1))))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 0 else 1) else (if n < 19 then 3 else 0)) else (if n < 22 then (if n < 21 then (-1) else 0) else (if n < 23 then 0 else 1))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 4)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 0 else 1) else (if n < 35 then (-1) else 0)) else (if n < 38 then (if n < 37 then 3 else 0) else (if n < 39 then 0 else 1))) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 4) else 0))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 0 else (if n < 55 then 4 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then 0 else (-1)) else (if n < 59 then 1 else 0)) else (if n < 62 then (if n < 61 then 1 else 0) else (if n < 63 then 0 else 3)))))) else 0
theorem nestingEntries_eq538 (n : Nat) :
    nestingProjection538.numerator[n]! = nestingEntries538 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries538, if_neg (by omega : ¬ n < 64)]

def nestingProjection539 : Projection := ⟨4,7,#[3,0,-1,0,-1,0,-1,0,0,4,0,0,0,0,0,0,-1,0,3,0,-1,0,-1,0,0,0,0,4,0,0,0,0,-1,0,-1,0,3,0,-1,0,0,0,0,0,0,4,0,0,-1,0,-1,0,-1,0,3,0,0,0,0,0,0,0,0,4]⟩
theorem nestingLookup539 : projections[539]! = nestingProjection539 := by
  rw [projections_lookup]
  rfl
def nestingEntries539 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 0) else (if n < 3 then (-1) else 0)) else (if n < 6 then (if n < 5 then (-1) else 0) else (if n < 7 then (-1) else 0))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 4) else 0) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then (-1) else 0) else (if n < 19 then 3 else 0)) else (if n < 22 then (if n < 21 then (-1) else 0) else (if n < 23 then (-1) else 0))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 4)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then (-1) else 0) else (if n < 35 then (-1) else 0)) else (if n < 38 then (if n < 37 then 3 else 0) else (if n < 39 then (-1) else 0))) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 4) else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then (-1) else 0) else (if n < 51 then (-1) else 0)) else (if n < 54 then (if n < 53 then (-1) else 0) else (if n < 55 then 3 else 0))) else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 4)))))) else 0
theorem nestingEntries_eq539 (n : Nat) :
    nestingProjection539.numerator[n]! = nestingEntries539 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries539, if_neg (by omega : ¬ n < 64)]

def nestingProjection540 : Projection := ⟨4,7,#[3,0,-1,0,-1,0,1,0,0,4,0,0,0,0,0,0,-1,0,3,0,-1,0,1,0,0,0,0,4,0,0,0,0,-1,0,-1,0,3,0,1,0,0,0,0,0,0,4,0,0,1,0,1,0,1,0,3,0,0,0,0,0,0,0,0,4]⟩
theorem nestingLookup540 : projections[540]! = nestingProjection540 := by
  rw [projections_lookup]
  rfl
def nestingEntries540 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 0) else (if n < 3 then (-1) else 0)) else (if n < 6 then (if n < 5 then (-1) else 0) else (if n < 7 then 1 else 0))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 4) else 0) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then (-1) else 0) else (if n < 19 then 3 else 0)) else (if n < 22 then (if n < 21 then (-1) else 0) else (if n < 23 then 1 else 0))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 4)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then (-1) else 0) else (if n < 35 then (-1) else 0)) else (if n < 38 then (if n < 37 then 3 else 0) else (if n < 39 then 1 else 0))) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 4) else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 1 else 0) else (if n < 51 then 1 else 0)) else (if n < 54 then (if n < 53 then 1 else 0) else (if n < 55 then 3 else 0))) else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 4)))))) else 0
theorem nestingEntries_eq540 (n : Nat) :
    nestingProjection540.numerator[n]! = nestingEntries540 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries540, if_neg (by omega : ¬ n < 64)]

def nestingProjection541 : Projection := ⟨4,7,#[3,0,-1,0,1,0,-1,0,0,4,0,0,0,0,0,0,-1,0,3,0,1,0,-1,0,0,0,0,4,0,0,0,0,1,0,1,0,3,0,1,0,0,0,0,0,0,4,0,0,-1,0,-1,0,1,0,3,0,0,0,0,0,0,0,0,4]⟩
theorem nestingLookup541 : projections[541]! = nestingProjection541 := by
  rw [projections_lookup]
  rfl
def nestingEntries541 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 0) else (if n < 3 then (-1) else 0)) else (if n < 6 then (if n < 5 then 1 else 0) else (if n < 7 then (-1) else 0))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 4) else 0) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then (-1) else 0) else (if n < 19 then 3 else 0)) else (if n < 22 then (if n < 21 then 1 else 0) else (if n < 23 then (-1) else 0))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 4)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 1 else 0) else (if n < 35 then 1 else 0)) else (if n < 38 then (if n < 37 then 3 else 0) else (if n < 39 then 1 else 0))) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 4) else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then (-1) else 0) else (if n < 51 then (-1) else 0)) else (if n < 54 then (if n < 53 then 1 else 0) else (if n < 55 then 3 else 0))) else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 4)))))) else 0
theorem nestingEntries_eq541 (n : Nat) :
    nestingProjection541.numerator[n]! = nestingEntries541 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries541, if_neg (by omega : ¬ n < 64)]

def nestingProjection542 : Projection := ⟨4,7,#[3,0,-1,0,1,0,1,0,0,4,0,0,0,0,0,0,-1,0,3,0,1,0,1,0,0,0,0,4,0,0,0,0,1,0,1,0,3,0,-1,0,0,0,0,0,0,4,0,0,1,0,1,0,-1,0,3,0,0,0,0,0,0,0,0,4]⟩
theorem nestingLookup542 : projections[542]! = nestingProjection542 := by
  rw [projections_lookup]
  rfl
def nestingEntries542 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 0) else (if n < 3 then (-1) else 0)) else (if n < 6 then (if n < 5 then 1 else 0) else (if n < 7 then 1 else 0))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 4) else 0) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then (-1) else 0) else (if n < 19 then 3 else 0)) else (if n < 22 then (if n < 21 then 1 else 0) else (if n < 23 then 1 else 0))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 4)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 1 else 0) else (if n < 35 then 1 else 0)) else (if n < 38 then (if n < 37 then 3 else 0) else (if n < 39 then (-1) else 0))) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 4) else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 1 else 0) else (if n < 51 then 1 else 0)) else (if n < 54 then (if n < 53 then (-1) else 0) else (if n < 55 then 3 else 0))) else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 4)))))) else 0
theorem nestingEntries_eq542 (n : Nat) :
    nestingProjection542.numerator[n]! = nestingEntries542 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries542, if_neg (by omega : ¬ n < 64)]

def nestingProjection543 : Projection := ⟨4,7,#[3,0,1,0,-1,0,-1,0,0,4,0,0,0,0,0,0,1,0,3,0,1,0,1,0,0,0,0,4,0,0,0,0,-1,0,1,0,3,0,-1,0,0,0,0,0,0,4,0,0,-1,0,1,0,-1,0,3,0,0,0,0,0,0,0,0,4]⟩
theorem nestingLookup543 : projections[543]! = nestingProjection543 := by
  rw [projections_lookup]
  rfl
def nestingEntries543 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 0) else (if n < 3 then 1 else 0)) else (if n < 6 then (if n < 5 then (-1) else 0) else (if n < 7 then (-1) else 0))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 4) else 0) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 1 else 0) else (if n < 19 then 3 else 0)) else (if n < 22 then (if n < 21 then 1 else 0) else (if n < 23 then 1 else 0))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 4)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then (-1) else 0) else (if n < 35 then 1 else 0)) else (if n < 38 then (if n < 37 then 3 else 0) else (if n < 39 then (-1) else 0))) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 4) else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then (-1) else 0) else (if n < 51 then 1 else 0)) else (if n < 54 then (if n < 53 then (-1) else 0) else (if n < 55 then 3 else 0))) else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 4)))))) else 0
theorem nestingEntries_eq543 (n : Nat) :
    nestingProjection543.numerator[n]! = nestingEntries543 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries543, if_neg (by omega : ¬ n < 64)]

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def nestingProjection544 : Projection := ⟨4,7,#[3,0,1,0,-1,0,1,0,0,4,0,0,0,0,0,0,1,0,3,0,1,0,-1,0,0,0,0,4,0,0,0,0,-1,0,1,0,3,0,1,0,0,0,0,0,0,4,0,0,1,0,-1,0,1,0,3,0,0,0,0,0,0,0,0,4]⟩
theorem nestingLookup544 : projections[544]! = nestingProjection544 := by
  rw [projections_lookup]
  rfl
def nestingEntries544 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 0) else (if n < 3 then 1 else 0)) else (if n < 6 then (if n < 5 then (-1) else 0) else (if n < 7 then 1 else 0))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 4) else 0) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 1 else 0) else (if n < 19 then 3 else 0)) else (if n < 22 then (if n < 21 then 1 else 0) else (if n < 23 then (-1) else 0))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 4)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then (-1) else 0) else (if n < 35 then 1 else 0)) else (if n < 38 then (if n < 37 then 3 else 0) else (if n < 39 then 1 else 0))) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 4) else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 1 else 0) else (if n < 51 then (-1) else 0)) else (if n < 54 then (if n < 53 then 1 else 0) else (if n < 55 then 3 else 0))) else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 4)))))) else 0
theorem nestingEntries_eq544 (n : Nat) :
    nestingProjection544.numerator[n]! = nestingEntries544 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries544, if_neg (by omega : ¬ n < 64)]

def nestingProjection545 : Projection := ⟨4,7,#[3,0,1,0,1,0,-1,0,0,4,0,0,0,0,0,0,1,0,3,0,-1,0,1,0,0,0,0,4,0,0,0,0,1,0,-1,0,3,0,1,0,0,0,0,0,0,4,0,0,-1,0,1,0,1,0,3,0,0,0,0,0,0,0,0,4]⟩
theorem nestingLookup545 : projections[545]! = nestingProjection545 := by
  rw [projections_lookup]
  rfl
def nestingEntries545 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 0) else (if n < 3 then 1 else 0)) else (if n < 6 then (if n < 5 then 1 else 0) else (if n < 7 then (-1) else 0))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 4) else 0) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 1 else 0) else (if n < 19 then 3 else 0)) else (if n < 22 then (if n < 21 then (-1) else 0) else (if n < 23 then 1 else 0))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 4)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 1 else 0) else (if n < 35 then (-1) else 0)) else (if n < 38 then (if n < 37 then 3 else 0) else (if n < 39 then 1 else 0))) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 4) else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then (-1) else 0) else (if n < 51 then 1 else 0)) else (if n < 54 then (if n < 53 then 1 else 0) else (if n < 55 then 3 else 0))) else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 4)))))) else 0
theorem nestingEntries_eq545 (n : Nat) :
    nestingProjection545.numerator[n]! = nestingEntries545 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries545, if_neg (by omega : ¬ n < 64)]

def nestingProjection546 : Projection := ⟨4,7,#[3,0,1,0,1,0,1,0,0,4,0,0,0,0,0,0,1,0,3,0,-1,0,-1,0,0,0,0,4,0,0,0,0,1,0,-1,0,3,0,-1,0,0,0,0,0,0,4,0,0,1,0,-1,0,-1,0,3,0,0,0,0,0,0,0,0,4]⟩
theorem nestingLookup546 : projections[546]! = nestingProjection546 := by
  rw [projections_lookup]
  rfl
def nestingEntries546 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 0) else (if n < 3 then 1 else 0)) else (if n < 6 then (if n < 5 then 1 else 0) else (if n < 7 then 1 else 0))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 4) else 0) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 1 else 0) else (if n < 19 then 3 else 0)) else (if n < 22 then (if n < 21 then (-1) else 0) else (if n < 23 then (-1) else 0))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 4)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 1 else 0) else (if n < 35 then (-1) else 0)) else (if n < 38 then (if n < 37 then 3 else 0) else (if n < 39 then (-1) else 0))) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 4) else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 1 else 0) else (if n < 51 then (-1) else 0)) else (if n < 54 then (if n < 53 then (-1) else 0) else (if n < 55 then 3 else 0))) else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 4)))))) else 0
theorem nestingEntries_eq546 (n : Nat) :
    nestingProjection546.numerator[n]! = nestingEntries546 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries546, if_neg (by omega : ¬ n < 64)]

def nestingProjection547 : Projection := ⟨4,7,#[3,-1,0,0,0,0,-1,-1,-1,3,0,0,0,0,-1,-1,0,0,4,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,4,0,0,-1,-1,0,0,0,0,3,-1,-1,-1,0,0,0,0,-1,3]⟩
theorem nestingLookup547 : projections[547]! = nestingProjection547 := by
  rw [projections_lookup]
  rfl
def nestingEntries547 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else (-1)) else 0) else (if n < 6 then 0 else (-1))) else (if n < 12 then (if n < 10 then (if n < 9 then (-1) else 3) else 0) else (if n < 14 then 0 else (-1)))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 4 else 0)) else 0) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 4)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 4 else 0) else 0)) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 4) else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then (-1) else 0) else (if n < 54 then 0 else (if n < 55 then 3 else (-1)))) else (if n < 60 then (if n < 58 then (-1) else 0) else (if n < 62 then 0 else (if n < 63 then (-1) else 3)))))) else 0
theorem nestingEntries_eq547 (n : Nat) :
    nestingProjection547.numerator[n]! = nestingEntries547 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries547, if_neg (by omega : ¬ n < 64)]

def nestingProjection548 : Projection := ⟨4,7,#[3,-1,0,0,0,0,-1,1,-1,3,0,0,0,0,-1,1,0,0,4,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,4,0,0,-1,-1,0,0,0,0,3,1,1,1,0,0,0,0,1,3]⟩
theorem nestingLookup548 : projections[548]! = nestingProjection548 := by
  rw [projections_lookup]
  rfl
def nestingEntries548 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else (-1)) else 0) else (if n < 6 then 0 else (if n < 7 then (-1) else 1))) else (if n < 12 then (if n < 10 then (if n < 9 then (-1) else 3) else 0) else (if n < 14 then 0 else (if n < 15 then (-1) else 1)))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 4 else 0)) else 0) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 4)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 4 else 0) else 0)) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 4) else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then (-1) else 0) else (if n < 54 then 0 else (if n < 55 then 3 else 1))) else (if n < 60 then (if n < 58 then 1 else 0) else (if n < 62 then 0 else (if n < 63 then 1 else 3)))))) else 0
theorem nestingEntries_eq548 (n : Nat) :
    nestingProjection548.numerator[n]! = nestingEntries548 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries548, if_neg (by omega : ¬ n < 64)]

def nestingProjection549 : Projection := ⟨4,7,#[3,-1,0,0,0,0,1,-1,-1,3,0,0,0,0,1,-1,0,0,4,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,4,0,0,1,1,0,0,0,0,3,1,-1,-1,0,0,0,0,1,3]⟩
theorem nestingLookup549 : projections[549]! = nestingProjection549 := by
  rw [projections_lookup]
  rfl
def nestingEntries549 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else (-1)) else 0) else (if n < 6 then 0 else (if n < 7 then 1 else (-1)))) else (if n < 12 then (if n < 10 then (if n < 9 then (-1) else 3) else 0) else (if n < 14 then 0 else (if n < 15 then 1 else (-1))))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 4 else 0)) else 0) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 4)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 4 else 0) else 0)) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 4) else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then 1 else 0) else (if n < 54 then 0 else (if n < 55 then 3 else 1))) else (if n < 60 then (if n < 58 then (-1) else 0) else (if n < 62 then 0 else (if n < 63 then 1 else 3)))))) else 0
theorem nestingEntries_eq549 (n : Nat) :
    nestingProjection549.numerator[n]! = nestingEntries549 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries549, if_neg (by omega : ¬ n < 64)]

def nestingProjection550 : Projection := ⟨4,7,#[3,-1,0,0,0,0,1,1,-1,3,0,0,0,0,1,1,0,0,4,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,4,0,0,1,1,0,0,0,0,3,-1,1,1,0,0,0,0,-1,3]⟩
theorem nestingLookup550 : projections[550]! = nestingProjection550 := by
  rw [projections_lookup]
  rfl
def nestingEntries550 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else (-1)) else 0) else (if n < 6 then 0 else 1)) else (if n < 12 then (if n < 10 then (if n < 9 then (-1) else 3) else 0) else (if n < 14 then 0 else 1))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 4 else 0)) else 0) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 4)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 4 else 0) else 0)) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 4) else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then 1 else 0) else (if n < 54 then 0 else (if n < 55 then 3 else (-1)))) else (if n < 60 then (if n < 58 then 1 else 0) else (if n < 62 then 0 else (if n < 63 then (-1) else 3)))))) else 0
theorem nestingEntries_eq550 (n : Nat) :
    nestingProjection550.numerator[n]! = nestingEntries550 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries550, if_neg (by omega : ¬ n < 64)]

def nestingProjection551 : Projection := ⟨4,7,#[3,1,0,0,0,0,-1,-1,1,3,0,0,0,0,1,1,0,0,4,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,4,0,0,-1,1,0,0,0,0,3,-1,-1,1,0,0,0,0,-1,3]⟩
theorem nestingLookup551 : projections[551]! = nestingProjection551 := by
  rw [projections_lookup]
  rfl
def nestingEntries551 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 1) else 0) else (if n < 6 then 0 else (-1))) else (if n < 12 then (if n < 10 then (if n < 9 then 1 else 3) else 0) else (if n < 14 then 0 else 1))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 4 else 0)) else 0) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 4)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 4 else 0) else 0)) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 4) else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then (-1) else 1) else 0) else (if n < 54 then 0 else (if n < 55 then 3 else (-1)))) else (if n < 60 then (if n < 58 then (if n < 57 then (-1) else 1) else 0) else (if n < 62 then 0 else (if n < 63 then (-1) else 3)))))) else 0
theorem nestingEntries_eq551 (n : Nat) :
    nestingProjection551.numerator[n]! = nestingEntries551 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries551, if_neg (by omega : ¬ n < 64)]

def nestingProjection552 : Projection := ⟨4,7,#[3,1,0,0,0,0,-1,1,1,3,0,0,0,0,1,-1,0,0,4,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,4,0,0,-1,1,0,0,0,0,3,1,1,-1,0,0,0,0,1,3]⟩
theorem nestingLookup552 : projections[552]! = nestingProjection552 := by
  rw [projections_lookup]
  rfl
def nestingEntries552 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 1) else 0) else (if n < 6 then 0 else (if n < 7 then (-1) else 1))) else (if n < 12 then (if n < 10 then (if n < 9 then 1 else 3) else 0) else (if n < 14 then 0 else (if n < 15 then 1 else (-1))))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 4 else 0)) else 0) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 4)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 4 else 0) else 0)) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 4) else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then (-1) else 1) else 0) else (if n < 54 then 0 else (if n < 55 then 3 else 1))) else (if n < 60 then (if n < 58 then (if n < 57 then 1 else (-1)) else 0) else (if n < 62 then 0 else (if n < 63 then 1 else 3)))))) else 0
theorem nestingEntries_eq552 (n : Nat) :
    nestingProjection552.numerator[n]! = nestingEntries552 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries552, if_neg (by omega : ¬ n < 64)]

def nestingProjection553 : Projection := ⟨4,7,#[3,1,0,0,0,0,1,-1,1,3,0,0,0,0,-1,1,0,0,4,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,4,0,0,1,-1,0,0,0,0,3,1,-1,1,0,0,0,0,1,3]⟩
theorem nestingLookup553 : projections[553]! = nestingProjection553 := by
  rw [projections_lookup]
  rfl
def nestingEntries553 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 1) else 0) else (if n < 6 then 0 else (if n < 7 then 1 else (-1)))) else (if n < 12 then (if n < 10 then (if n < 9 then 1 else 3) else 0) else (if n < 14 then 0 else (if n < 15 then (-1) else 1)))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 4 else 0)) else 0) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 4)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 4 else 0) else 0)) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 4) else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 1 else (-1)) else 0) else (if n < 54 then 0 else (if n < 55 then 3 else 1))) else (if n < 60 then (if n < 58 then (if n < 57 then (-1) else 1) else 0) else (if n < 62 then 0 else (if n < 63 then 1 else 3)))))) else 0
theorem nestingEntries_eq553 (n : Nat) :
    nestingProjection553.numerator[n]! = nestingEntries553 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries553, if_neg (by omega : ¬ n < 64)]

def nestingProjection554 : Projection := ⟨4,7,#[3,1,0,0,0,0,1,1,1,3,0,0,0,0,-1,-1,0,0,4,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,4,0,0,1,-1,0,0,0,0,3,-1,1,-1,0,0,0,0,-1,3]⟩
theorem nestingLookup554 : projections[554]! = nestingProjection554 := by
  rw [projections_lookup]
  rfl
def nestingEntries554 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 1) else 0) else (if n < 6 then 0 else 1)) else (if n < 12 then (if n < 10 then (if n < 9 then 1 else 3) else 0) else (if n < 14 then 0 else (-1)))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 4 else 0)) else 0) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 4)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 4 else 0) else 0)) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 4) else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 1 else (-1)) else 0) else (if n < 54 then 0 else (if n < 55 then 3 else (-1)))) else (if n < 60 then (if n < 58 then (if n < 57 then 1 else (-1)) else 0) else (if n < 62 then 0 else (if n < 63 then (-1) else 3)))))) else 0
theorem nestingEntries_eq554 (n : Nat) :
    nestingProjection554.numerator[n]! = nestingEntries554 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries554, if_neg (by omega : ¬ n < 64)]

def nestingProjection555 : Projection := ⟨4,7,#[3,-1,0,0,-1,-1,0,0,-1,3,0,0,-1,-1,0,0,0,0,4,0,0,0,0,0,0,0,0,4,0,0,0,0,-1,-1,0,0,3,-1,0,0,-1,-1,0,0,-1,3,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,4]⟩
theorem nestingLookup555 : projections[555]! = nestingProjection555 := by
  rw [projections_lookup]
  rfl
def nestingEntries555 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else (-1)) else 0) else (if n < 6 then (-1) else 0)) else (if n < 12 then (if n < 10 then (if n < 9 then (-1) else 3) else 0) else (if n < 14 then (-1) else 0))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 4 else 0)) else 0) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 4)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (-1) else 0) else (if n < 38 then (if n < 37 then 3 else (-1)) else 0)) else (if n < 44 then (if n < 42 then (-1) else 0) else (if n < 46 then (if n < 45 then (-1) else 3) else 0))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 0 else (if n < 55 then 4 else 0))) else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 4)))))) else 0
theorem nestingEntries_eq555 (n : Nat) :
    nestingProjection555.numerator[n]! = nestingEntries555 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries555, if_neg (by omega : ¬ n < 64)]

def nestingProjection556 : Projection := ⟨4,7,#[3,-1,0,0,-1,1,0,0,-1,3,0,0,-1,1,0,0,0,0,4,0,0,0,0,0,0,0,0,4,0,0,0,0,-1,-1,0,0,3,1,0,0,1,1,0,0,1,3,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,4]⟩
theorem nestingLookup556 : projections[556]! = nestingProjection556 := by
  rw [projections_lookup]
  rfl
def nestingEntries556 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else (-1)) else 0) else (if n < 6 then (if n < 5 then (-1) else 1) else 0)) else (if n < 12 then (if n < 10 then (if n < 9 then (-1) else 3) else 0) else (if n < 14 then (if n < 13 then (-1) else 1) else 0))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 4 else 0)) else 0) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 4)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (-1) else 0) else (if n < 38 then (if n < 37 then 3 else 1) else 0)) else (if n < 44 then (if n < 42 then 1 else 0) else (if n < 46 then (if n < 45 then 1 else 3) else 0))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 0 else (if n < 55 then 4 else 0))) else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 4)))))) else 0
theorem nestingEntries_eq556 (n : Nat) :
    nestingProjection556.numerator[n]! = nestingEntries556 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries556, if_neg (by omega : ¬ n < 64)]

def nestingProjection557 : Projection := ⟨4,7,#[3,-1,0,0,1,-1,0,0,-1,3,0,0,1,-1,0,0,0,0,4,0,0,0,0,0,0,0,0,4,0,0,0,0,1,1,0,0,3,1,0,0,-1,-1,0,0,1,3,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,4]⟩
theorem nestingLookup557 : projections[557]! = nestingProjection557 := by
  rw [projections_lookup]
  rfl
def nestingEntries557 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else (-1)) else 0) else (if n < 6 then (if n < 5 then 1 else (-1)) else 0)) else (if n < 12 then (if n < 10 then (if n < 9 then (-1) else 3) else 0) else (if n < 14 then (if n < 13 then 1 else (-1)) else 0))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 4 else 0)) else 0) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 4)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then 1 else 0) else (if n < 38 then (if n < 37 then 3 else 1) else 0)) else (if n < 44 then (if n < 42 then (-1) else 0) else (if n < 46 then (if n < 45 then 1 else 3) else 0))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 0 else (if n < 55 then 4 else 0))) else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 4)))))) else 0
theorem nestingEntries_eq557 (n : Nat) :
    nestingProjection557.numerator[n]! = nestingEntries557 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries557, if_neg (by omega : ¬ n < 64)]

def nestingProjection558 : Projection := ⟨4,7,#[3,-1,0,0,1,1,0,0,-1,3,0,0,1,1,0,0,0,0,4,0,0,0,0,0,0,0,0,4,0,0,0,0,1,1,0,0,3,-1,0,0,1,1,0,0,-1,3,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,4]⟩
theorem nestingLookup558 : projections[558]! = nestingProjection558 := by
  rw [projections_lookup]
  rfl
def nestingEntries558 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else (-1)) else 0) else (if n < 6 then 1 else 0)) else (if n < 12 then (if n < 10 then (if n < 9 then (-1) else 3) else 0) else (if n < 14 then 1 else 0))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 4 else 0)) else 0) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 4)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then 1 else 0) else (if n < 38 then (if n < 37 then 3 else (-1)) else 0)) else (if n < 44 then (if n < 42 then 1 else 0) else (if n < 46 then (if n < 45 then (-1) else 3) else 0))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 0 else (if n < 55 then 4 else 0))) else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 4)))))) else 0
theorem nestingEntries_eq558 (n : Nat) :
    nestingProjection558.numerator[n]! = nestingEntries558 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries558, if_neg (by omega : ¬ n < 64)]

def nestingProjection559 : Projection := ⟨4,7,#[3,1,0,0,-1,-1,0,0,1,3,0,0,1,1,0,0,0,0,4,0,0,0,0,0,0,0,0,4,0,0,0,0,-1,1,0,0,3,-1,0,0,-1,1,0,0,-1,3,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,4]⟩
theorem nestingLookup559 : projections[559]! = nestingProjection559 := by
  rw [projections_lookup]
  rfl
def nestingEntries559 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 1) else 0) else (if n < 6 then (-1) else 0)) else (if n < 12 then (if n < 10 then (if n < 9 then 1 else 3) else 0) else (if n < 14 then 1 else 0))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 4 else 0)) else 0) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 4)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then (-1) else 1) else 0) else (if n < 38 then (if n < 37 then 3 else (-1)) else 0)) else (if n < 44 then (if n < 42 then (if n < 41 then (-1) else 1) else 0) else (if n < 46 then (if n < 45 then (-1) else 3) else 0))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 0 else (if n < 55 then 4 else 0))) else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 4)))))) else 0
theorem nestingEntries_eq559 (n : Nat) :
    nestingProjection559.numerator[n]! = nestingEntries559 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries559, if_neg (by omega : ¬ n < 64)]

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def nestingProjection560 : Projection := ⟨4,7,#[3,1,0,0,-1,1,0,0,1,3,0,0,1,-1,0,0,0,0,4,0,0,0,0,0,0,0,0,4,0,0,0,0,-1,1,0,0,3,1,0,0,1,-1,0,0,1,3,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,4]⟩
theorem nestingLookup560 : projections[560]! = nestingProjection560 := by
  rw [projections_lookup]
  rfl
def nestingEntries560 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 1) else 0) else (if n < 6 then (if n < 5 then (-1) else 1) else 0)) else (if n < 12 then (if n < 10 then (if n < 9 then 1 else 3) else 0) else (if n < 14 then (if n < 13 then 1 else (-1)) else 0))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 4 else 0)) else 0) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 4)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then (-1) else 1) else 0) else (if n < 38 then (if n < 37 then 3 else 1) else 0)) else (if n < 44 then (if n < 42 then (if n < 41 then 1 else (-1)) else 0) else (if n < 46 then (if n < 45 then 1 else 3) else 0))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 0 else (if n < 55 then 4 else 0))) else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 4)))))) else 0
theorem nestingEntries_eq560 (n : Nat) :
    nestingProjection560.numerator[n]! = nestingEntries560 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries560, if_neg (by omega : ¬ n < 64)]

def nestingProjection561 : Projection := ⟨4,7,#[3,1,0,0,1,-1,0,0,1,3,0,0,-1,1,0,0,0,0,4,0,0,0,0,0,0,0,0,4,0,0,0,0,1,-1,0,0,3,1,0,0,-1,1,0,0,1,3,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,4]⟩
theorem nestingLookup561 : projections[561]! = nestingProjection561 := by
  rw [projections_lookup]
  rfl
def nestingEntries561 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 1) else 0) else (if n < 6 then (if n < 5 then 1 else (-1)) else 0)) else (if n < 12 then (if n < 10 then (if n < 9 then 1 else 3) else 0) else (if n < 14 then (if n < 13 then (-1) else 1) else 0))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 4 else 0)) else 0) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 4)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 1 else (-1)) else 0) else (if n < 38 then (if n < 37 then 3 else 1) else 0)) else (if n < 44 then (if n < 42 then (if n < 41 then (-1) else 1) else 0) else (if n < 46 then (if n < 45 then 1 else 3) else 0))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 0 else (if n < 55 then 4 else 0))) else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 4)))))) else 0
theorem nestingEntries_eq561 (n : Nat) :
    nestingProjection561.numerator[n]! = nestingEntries561 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries561, if_neg (by omega : ¬ n < 64)]

def nestingProjection562 : Projection := ⟨4,7,#[3,1,0,0,1,1,0,0,1,3,0,0,-1,-1,0,0,0,0,4,0,0,0,0,0,0,0,0,4,0,0,0,0,1,-1,0,0,3,-1,0,0,1,-1,0,0,-1,3,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,4]⟩
theorem nestingLookup562 : projections[562]! = nestingProjection562 := by
  rw [projections_lookup]
  rfl
def nestingEntries562 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 1) else 0) else (if n < 6 then 1 else 0)) else (if n < 12 then (if n < 10 then (if n < 9 then 1 else 3) else 0) else (if n < 14 then (-1) else 0))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 4 else 0)) else 0) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 4)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 1 else (-1)) else 0) else (if n < 38 then (if n < 37 then 3 else (-1)) else 0)) else (if n < 44 then (if n < 42 then (if n < 41 then 1 else (-1)) else 0) else (if n < 46 then (if n < 45 then (-1) else 3) else 0))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 0 else (if n < 55 then 4 else 0))) else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 4)))))) else 0
theorem nestingEntries_eq562 (n : Nat) :
    nestingProjection562.numerator[n]! = nestingEntries562 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries562, if_neg (by omega : ¬ n < 64)]

def nestingProjection563 : Projection := ⟨4,7,#[3,0,-1,0,0,-1,0,-1,0,4,0,0,0,0,0,0,-1,0,3,0,0,-1,0,-1,0,0,0,4,0,0,0,0,0,0,0,0,4,0,0,0,-1,0,-1,0,0,3,0,-1,0,0,0,0,0,0,4,0,-1,0,-1,0,0,-1,0,3]⟩
theorem nestingLookup563 : projections[563]! = nestingProjection563 := by
  rw [projections_lookup]
  rfl
def nestingEntries563 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 0) else (if n < 3 then (-1) else 0)) else (if n < 6 then (if n < 5 then 0 else (-1)) else (if n < 7 then 0 else (-1)))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 4) else 0) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then (-1) else 0) else (if n < 19 then 3 else 0)) else (if n < 22 then (if n < 21 then 0 else (-1)) else (if n < 23 then 0 else (-1)))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 4)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 4 else 0) else 0)) else (if n < 44 then (if n < 42 then (if n < 41 then (-1) else 0) else (if n < 43 then (-1) else 0)) else (if n < 46 then (if n < 45 then 0 else 3) else (if n < 47 then 0 else (-1))))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 0 else (if n < 55 then 4 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then (-1) else 0) else (if n < 59 then (-1) else 0)) else (if n < 62 then (if n < 61 then 0 else (-1)) else (if n < 63 then 0 else 3)))))) else 0
theorem nestingEntries_eq563 (n : Nat) :
    nestingProjection563.numerator[n]! = nestingEntries563 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries563, if_neg (by omega : ¬ n < 64)]

def nestingProjection564 : Projection := ⟨4,7,#[3,0,-1,0,0,-1,0,1,0,4,0,0,0,0,0,0,-1,0,3,0,0,-1,0,1,0,0,0,4,0,0,0,0,0,0,0,0,4,0,0,0,-1,0,-1,0,0,3,0,1,0,0,0,0,0,0,4,0,1,0,1,0,0,1,0,3]⟩
theorem nestingLookup564 : projections[564]! = nestingProjection564 := by
  rw [projections_lookup]
  rfl
def nestingEntries564 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 0) else (if n < 3 then (-1) else 0)) else (if n < 6 then (if n < 5 then 0 else (-1)) else (if n < 7 then 0 else 1))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 4) else 0) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then (-1) else 0) else (if n < 19 then 3 else 0)) else (if n < 22 then (if n < 21 then 0 else (-1)) else (if n < 23 then 0 else 1))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 4)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 4 else 0) else 0)) else (if n < 44 then (if n < 42 then (if n < 41 then (-1) else 0) else (if n < 43 then (-1) else 0)) else (if n < 46 then (if n < 45 then 0 else 3) else (if n < 47 then 0 else 1)))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 0 else (if n < 55 then 4 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then 1 else 0) else (if n < 59 then 1 else 0)) else (if n < 62 then (if n < 61 then 0 else 1) else (if n < 63 then 0 else 3)))))) else 0
theorem nestingEntries_eq564 (n : Nat) :
    nestingProjection564.numerator[n]! = nestingEntries564 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries564, if_neg (by omega : ¬ n < 64)]

def nestingProjection565 : Projection := ⟨4,7,#[3,0,-1,0,0,1,0,-1,0,4,0,0,0,0,0,0,-1,0,3,0,0,1,0,-1,0,0,0,4,0,0,0,0,0,0,0,0,4,0,0,0,1,0,1,0,0,3,0,1,0,0,0,0,0,0,4,0,-1,0,-1,0,0,1,0,3]⟩
theorem nestingLookup565 : projections[565]! = nestingProjection565 := by
  rw [projections_lookup]
  rfl
def nestingEntries565 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 0) else (if n < 3 then (-1) else 0)) else (if n < 6 then (if n < 5 then 0 else 1) else (if n < 7 then 0 else (-1)))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 4) else 0) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then (-1) else 0) else (if n < 19 then 3 else 0)) else (if n < 22 then (if n < 21 then 0 else 1) else (if n < 23 then 0 else (-1)))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 4)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 4 else 0) else 0)) else (if n < 44 then (if n < 42 then (if n < 41 then 1 else 0) else (if n < 43 then 1 else 0)) else (if n < 46 then (if n < 45 then 0 else 3) else (if n < 47 then 0 else 1)))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 0 else (if n < 55 then 4 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then (-1) else 0) else (if n < 59 then (-1) else 0)) else (if n < 62 then (if n < 61 then 0 else 1) else (if n < 63 then 0 else 3)))))) else 0
theorem nestingEntries_eq565 (n : Nat) :
    nestingProjection565.numerator[n]! = nestingEntries565 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries565, if_neg (by omega : ¬ n < 64)]

def nestingProjection566 : Projection := ⟨4,7,#[3,0,-1,0,0,1,0,1,0,4,0,0,0,0,0,0,-1,0,3,0,0,1,0,1,0,0,0,4,0,0,0,0,0,0,0,0,4,0,0,0,1,0,1,0,0,3,0,-1,0,0,0,0,0,0,4,0,1,0,1,0,0,-1,0,3]⟩
theorem nestingLookup566 : projections[566]! = nestingProjection566 := by
  rw [projections_lookup]
  rfl
def nestingEntries566 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 0) else (if n < 3 then (-1) else 0)) else (if n < 6 then (if n < 5 then 0 else 1) else (if n < 7 then 0 else 1))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 4) else 0) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then (-1) else 0) else (if n < 19 then 3 else 0)) else (if n < 22 then (if n < 21 then 0 else 1) else (if n < 23 then 0 else 1))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 4)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 4 else 0) else 0)) else (if n < 44 then (if n < 42 then (if n < 41 then 1 else 0) else (if n < 43 then 1 else 0)) else (if n < 46 then (if n < 45 then 0 else 3) else (if n < 47 then 0 else (-1))))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 0 else (if n < 55 then 4 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then 1 else 0) else (if n < 59 then 1 else 0)) else (if n < 62 then (if n < 61 then 0 else (-1)) else (if n < 63 then 0 else 3)))))) else 0
theorem nestingEntries_eq566 (n : Nat) :
    nestingProjection566.numerator[n]! = nestingEntries566 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries566, if_neg (by omega : ¬ n < 64)]

def nestingProjection567 : Projection := ⟨4,7,#[3,0,1,0,0,-1,0,-1,0,4,0,0,0,0,0,0,1,0,3,0,0,1,0,1,0,0,0,4,0,0,0,0,0,0,0,0,4,0,0,0,-1,0,1,0,0,3,0,-1,0,0,0,0,0,0,4,0,-1,0,1,0,0,-1,0,3]⟩
theorem nestingLookup567 : projections[567]! = nestingProjection567 := by
  rw [projections_lookup]
  rfl
def nestingEntries567 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 0) else (if n < 3 then 1 else 0)) else (if n < 6 then (if n < 5 then 0 else (-1)) else (if n < 7 then 0 else (-1)))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 4) else 0) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 1 else 0) else (if n < 19 then 3 else 0)) else (if n < 22 then (if n < 21 then 0 else 1) else (if n < 23 then 0 else 1))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 4)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 4 else 0) else 0)) else (if n < 44 then (if n < 42 then (if n < 41 then (-1) else 0) else (if n < 43 then 1 else 0)) else (if n < 46 then (if n < 45 then 0 else 3) else (if n < 47 then 0 else (-1))))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 0 else (if n < 55 then 4 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then (-1) else 0) else (if n < 59 then 1 else 0)) else (if n < 62 then (if n < 61 then 0 else (-1)) else (if n < 63 then 0 else 3)))))) else 0
theorem nestingEntries_eq567 (n : Nat) :
    nestingProjection567.numerator[n]! = nestingEntries567 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries567, if_neg (by omega : ¬ n < 64)]

def nestingProjection568 : Projection := ⟨4,7,#[3,0,1,0,0,-1,0,1,0,4,0,0,0,0,0,0,1,0,3,0,0,1,0,-1,0,0,0,4,0,0,0,0,0,0,0,0,4,0,0,0,-1,0,1,0,0,3,0,1,0,0,0,0,0,0,4,0,1,0,-1,0,0,1,0,3]⟩
theorem nestingLookup568 : projections[568]! = nestingProjection568 := by
  rw [projections_lookup]
  rfl
def nestingEntries568 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 0) else (if n < 3 then 1 else 0)) else (if n < 6 then (if n < 5 then 0 else (-1)) else (if n < 7 then 0 else 1))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 4) else 0) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 1 else 0) else (if n < 19 then 3 else 0)) else (if n < 22 then (if n < 21 then 0 else 1) else (if n < 23 then 0 else (-1)))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 4)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 4 else 0) else 0)) else (if n < 44 then (if n < 42 then (if n < 41 then (-1) else 0) else (if n < 43 then 1 else 0)) else (if n < 46 then (if n < 45 then 0 else 3) else (if n < 47 then 0 else 1)))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 0 else (if n < 55 then 4 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then 1 else 0) else (if n < 59 then (-1) else 0)) else (if n < 62 then (if n < 61 then 0 else 1) else (if n < 63 then 0 else 3)))))) else 0
theorem nestingEntries_eq568 (n : Nat) :
    nestingProjection568.numerator[n]! = nestingEntries568 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries568, if_neg (by omega : ¬ n < 64)]

def nestingProjection569 : Projection := ⟨4,7,#[3,0,1,0,0,1,0,-1,0,4,0,0,0,0,0,0,1,0,3,0,0,-1,0,1,0,0,0,4,0,0,0,0,0,0,0,0,4,0,0,0,1,0,-1,0,0,3,0,1,0,0,0,0,0,0,4,0,-1,0,1,0,0,1,0,3]⟩
theorem nestingLookup569 : projections[569]! = nestingProjection569 := by
  rw [projections_lookup]
  rfl
def nestingEntries569 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 0) else (if n < 3 then 1 else 0)) else (if n < 6 then (if n < 5 then 0 else 1) else (if n < 7 then 0 else (-1)))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 4) else 0) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 1 else 0) else (if n < 19 then 3 else 0)) else (if n < 22 then (if n < 21 then 0 else (-1)) else (if n < 23 then 0 else 1))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 4)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 4 else 0) else 0)) else (if n < 44 then (if n < 42 then (if n < 41 then 1 else 0) else (if n < 43 then (-1) else 0)) else (if n < 46 then (if n < 45 then 0 else 3) else (if n < 47 then 0 else 1)))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 0 else (if n < 55 then 4 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then (-1) else 0) else (if n < 59 then 1 else 0)) else (if n < 62 then (if n < 61 then 0 else 1) else (if n < 63 then 0 else 3)))))) else 0
theorem nestingEntries_eq569 (n : Nat) :
    nestingProjection569.numerator[n]! = nestingEntries569 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries569, if_neg (by omega : ¬ n < 64)]

def nestingProjection570 : Projection := ⟨4,7,#[3,0,1,0,0,1,0,1,0,4,0,0,0,0,0,0,1,0,3,0,0,-1,0,-1,0,0,0,4,0,0,0,0,0,0,0,0,4,0,0,0,1,0,-1,0,0,3,0,-1,0,0,0,0,0,0,4,0,1,0,-1,0,0,-1,0,3]⟩
theorem nestingLookup570 : projections[570]! = nestingProjection570 := by
  rw [projections_lookup]
  rfl
def nestingEntries570 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 0) else (if n < 3 then 1 else 0)) else (if n < 6 then (if n < 5 then 0 else 1) else (if n < 7 then 0 else 1))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 4) else 0) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 1 else 0) else (if n < 19 then 3 else 0)) else (if n < 22 then (if n < 21 then 0 else (-1)) else (if n < 23 then 0 else (-1)))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 4)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 4 else 0) else 0)) else (if n < 44 then (if n < 42 then (if n < 41 then 1 else 0) else (if n < 43 then (-1) else 0)) else (if n < 46 then (if n < 45 then 0 else 3) else (if n < 47 then 0 else (-1))))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 0 else (if n < 55 then 4 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then 1 else 0) else (if n < 59 then (-1) else 0)) else (if n < 62 then (if n < 61 then 0 else (-1)) else (if n < 63 then 0 else 3)))))) else 0
theorem nestingEntries_eq570 (n : Nat) :
    nestingProjection570.numerator[n]! = nestingEntries570 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries570, if_neg (by omega : ¬ n < 64)]

def nestingProjection571 : Projection := ⟨4,7,#[4,0,0,0,0,0,0,0,0,3,-1,0,0,-1,-1,0,0,-1,3,0,0,-1,-1,0,0,0,0,4,0,0,0,0,0,0,0,0,4,0,0,0,0,-1,-1,0,0,3,-1,0,0,-1,-1,0,0,-1,3,0,0,0,0,0,0,0,0,4]⟩
theorem nestingLookup571 : projections[571]! = nestingProjection571 := by
  rw [projections_lookup]
  rfl
def nestingEntries571 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 4 else 0) else 0) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 3) else (if n < 11 then (-1) else 0)) else (if n < 14 then (if n < 13 then 0 else (-1)) else (if n < 15 then (-1) else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 0 else (-1)) else (if n < 19 then 3 else 0)) else (if n < 22 then (if n < 21 then 0 else (-1)) else (if n < 23 then (-1) else 0))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 4)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 4 else 0) else 0)) else (if n < 44 then (if n < 42 then (if n < 41 then 0 else (-1)) else (if n < 43 then (-1) else 0)) else (if n < 46 then (if n < 45 then 0 else 3) else (if n < 47 then (-1) else 0)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else (-1)) else (if n < 51 then (-1) else 0)) else (if n < 54 then (if n < 53 then 0 else (-1)) else (if n < 55 then 3 else 0))) else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 4)))))) else 0
theorem nestingEntries_eq571 (n : Nat) :
    nestingProjection571.numerator[n]! = nestingEntries571 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries571, if_neg (by omega : ¬ n < 64)]

def nestingProjection572 : Projection := ⟨4,7,#[4,0,0,0,0,0,0,0,0,3,-1,0,0,-1,1,0,0,-1,3,0,0,-1,1,0,0,0,0,4,0,0,0,0,0,0,0,0,4,0,0,0,0,-1,-1,0,0,3,1,0,0,1,1,0,0,1,3,0,0,0,0,0,0,0,0,4]⟩
theorem nestingLookup572 : projections[572]! = nestingProjection572 := by
  rw [projections_lookup]
  rfl
def nestingEntries572 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 4 else 0) else 0) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 3) else (if n < 11 then (-1) else 0)) else (if n < 14 then (if n < 13 then 0 else (-1)) else (if n < 15 then 1 else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 0 else (-1)) else (if n < 19 then 3 else 0)) else (if n < 22 then (if n < 21 then 0 else (-1)) else (if n < 23 then 1 else 0))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 4)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 4 else 0) else 0)) else (if n < 44 then (if n < 42 then (if n < 41 then 0 else (-1)) else (if n < 43 then (-1) else 0)) else (if n < 46 then (if n < 45 then 0 else 3) else (if n < 47 then 1 else 0)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else 1) else (if n < 51 then 1 else 0)) else (if n < 54 then (if n < 53 then 0 else 1) else (if n < 55 then 3 else 0))) else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 4)))))) else 0
theorem nestingEntries_eq572 (n : Nat) :
    nestingProjection572.numerator[n]! = nestingEntries572 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries572, if_neg (by omega : ¬ n < 64)]

def nestingProjection573 : Projection := ⟨4,7,#[4,0,0,0,0,0,0,0,0,3,-1,0,0,1,-1,0,0,-1,3,0,0,1,-1,0,0,0,0,4,0,0,0,0,0,0,0,0,4,0,0,0,0,1,1,0,0,3,1,0,0,-1,-1,0,0,1,3,0,0,0,0,0,0,0,0,4]⟩
theorem nestingLookup573 : projections[573]! = nestingProjection573 := by
  rw [projections_lookup]
  rfl
def nestingEntries573 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 4 else 0) else 0) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 3) else (if n < 11 then (-1) else 0)) else (if n < 14 then (if n < 13 then 0 else 1) else (if n < 15 then (-1) else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 0 else (-1)) else (if n < 19 then 3 else 0)) else (if n < 22 then (if n < 21 then 0 else 1) else (if n < 23 then (-1) else 0))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 4)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 4 else 0) else 0)) else (if n < 44 then (if n < 42 then (if n < 41 then 0 else 1) else (if n < 43 then 1 else 0)) else (if n < 46 then (if n < 45 then 0 else 3) else (if n < 47 then 1 else 0)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else (-1)) else (if n < 51 then (-1) else 0)) else (if n < 54 then (if n < 53 then 0 else 1) else (if n < 55 then 3 else 0))) else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 4)))))) else 0
theorem nestingEntries_eq573 (n : Nat) :
    nestingProjection573.numerator[n]! = nestingEntries573 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries573, if_neg (by omega : ¬ n < 64)]

def nestingProjection574 : Projection := ⟨4,7,#[4,0,0,0,0,0,0,0,0,3,1,0,0,-1,-1,0,0,1,3,0,0,1,1,0,0,0,0,4,0,0,0,0,0,0,0,0,4,0,0,0,0,-1,1,0,0,3,-1,0,0,-1,1,0,0,-1,3,0,0,0,0,0,0,0,0,4]⟩
theorem nestingLookup574 : projections[574]! = nestingProjection574 := by
  rw [projections_lookup]
  rfl
def nestingEntries574 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 4 else 0) else 0) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 3) else (if n < 11 then 1 else 0)) else (if n < 14 then (if n < 13 then 0 else (-1)) else (if n < 15 then (-1) else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 0 else 1) else (if n < 19 then 3 else 0)) else (if n < 22 then (if n < 21 then 0 else 1) else (if n < 23 then 1 else 0))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 4)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 4 else 0) else 0)) else (if n < 44 then (if n < 42 then (if n < 41 then 0 else (-1)) else (if n < 43 then 1 else 0)) else (if n < 46 then (if n < 45 then 0 else 3) else (if n < 47 then (-1) else 0)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else (-1)) else (if n < 51 then 1 else 0)) else (if n < 54 then (if n < 53 then 0 else (-1)) else (if n < 55 then 3 else 0))) else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 4)))))) else 0
theorem nestingEntries_eq574 (n : Nat) :
    nestingProjection574.numerator[n]! = nestingEntries574 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries574, if_neg (by omega : ¬ n < 64)]

def nestingProjection575 : Projection := ⟨4,7,#[4,0,0,0,0,0,0,0,0,3,1,0,0,1,-1,0,0,1,3,0,0,-1,1,0,0,0,0,4,0,0,0,0,0,0,0,0,4,0,0,0,0,1,-1,0,0,3,1,0,0,-1,1,0,0,1,3,0,0,0,0,0,0,0,0,4]⟩
theorem nestingLookup575 : projections[575]! = nestingProjection575 := by
  rw [projections_lookup]
  rfl
def nestingEntries575 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 4 else 0) else 0) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 3) else (if n < 11 then 1 else 0)) else (if n < 14 then (if n < 13 then 0 else 1) else (if n < 15 then (-1) else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 0 else 1) else (if n < 19 then 3 else 0)) else (if n < 22 then (if n < 21 then 0 else (-1)) else (if n < 23 then 1 else 0))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 4)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 4 else 0) else 0)) else (if n < 44 then (if n < 42 then (if n < 41 then 0 else 1) else (if n < 43 then (-1) else 0)) else (if n < 46 then (if n < 45 then 0 else 3) else (if n < 47 then 1 else 0)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else (-1)) else (if n < 51 then 1 else 0)) else (if n < 54 then (if n < 53 then 0 else 1) else (if n < 55 then 3 else 0))) else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 4)))))) else 0
theorem nestingEntries_eq575 (n : Nat) :
    nestingProjection575.numerator[n]! = nestingEntries575 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries575, if_neg (by omega : ¬ n < 64)]

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def nestingProjection576 : Projection := ⟨4,7,#[4,0,0,0,0,0,0,0,0,3,1,0,0,1,1,0,0,1,3,0,0,-1,-1,0,0,0,0,4,0,0,0,0,0,0,0,0,4,0,0,0,0,1,-1,0,0,3,-1,0,0,1,-1,0,0,-1,3,0,0,0,0,0,0,0,0,4]⟩
theorem nestingLookup576 : projections[576]! = nestingProjection576 := by
  rw [projections_lookup]
  rfl
def nestingEntries576 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 4 else 0) else 0) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 3) else (if n < 11 then 1 else 0)) else (if n < 14 then (if n < 13 then 0 else 1) else (if n < 15 then 1 else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 0 else 1) else (if n < 19 then 3 else 0)) else (if n < 22 then (if n < 21 then 0 else (-1)) else (if n < 23 then (-1) else 0))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 4)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 4 else 0) else 0)) else (if n < 44 then (if n < 42 then (if n < 41 then 0 else 1) else (if n < 43 then (-1) else 0)) else (if n < 46 then (if n < 45 then 0 else 3) else (if n < 47 then (-1) else 0)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else 1) else (if n < 51 then (-1) else 0)) else (if n < 54 then (if n < 53 then 0 else (-1)) else (if n < 55 then 3 else 0))) else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 4)))))) else 0
theorem nestingEntries_eq576 (n : Nat) :
    nestingProjection576.numerator[n]! = nestingEntries576 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries576, if_neg (by omega : ¬ n < 64)]

def nestingProjection577 : Projection := ⟨4,7,#[4,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,3,-1,-1,1,0,0,0,0,-1,3,-1,1,0,0,0,0,-1,-1,3,1,0,0,0,0,1,1,1,3]⟩
theorem nestingLookup577 : projections[577]! = nestingProjection577 := by
  rw [projections_lookup]
  rfl
def nestingEntries577 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 4 else 0) else 0) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 4) else 0) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 4 else 0)) else 0) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 4)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 3 else (-1)) else (if n < 39 then (-1) else 1))) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then (-1) else 3) else (if n < 47 then (-1) else 1)))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then (-1) else (if n < 55 then 3 else 1))) else (if n < 60 then 0 else (if n < 62 then 1 else (if n < 63 then 1 else 3)))))) else 0
theorem nestingEntries_eq577 (n : Nat) :
    nestingProjection577.numerator[n]! = nestingEntries577 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries577, if_neg (by omega : ¬ n < 64)]

def nestingProjection578 : Projection := ⟨4,7,#[4,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,3,-1,1,-1,0,0,0,0,-1,3,1,-1,0,0,0,0,1,1,3,1,0,0,0,0,-1,-1,1,3]⟩
theorem nestingLookup578 : projections[578]! = nestingProjection578 := by
  rw [projections_lookup]
  rfl
def nestingEntries578 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 4 else 0) else 0) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 4) else 0) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 4 else 0)) else 0) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 4)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 3 else (-1)) else (if n < 39 then 1 else (-1)))) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then (-1) else 3) else (if n < 47 then 1 else (-1))))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 1 else (if n < 55 then 3 else 1))) else (if n < 60 then 0 else (if n < 62 then (-1) else (if n < 63 then 1 else 3)))))) else 0
theorem nestingEntries_eq578 (n : Nat) :
    nestingProjection578.numerator[n]! = nestingEntries578 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries578, if_neg (by omega : ¬ n < 64)]

def nestingProjection579 : Projection := ⟨4,7,#[4,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,3,-1,1,1,0,0,0,0,-1,3,1,1,0,0,0,0,1,1,3,-1,0,0,0,0,1,1,-1,3]⟩
theorem nestingLookup579 : projections[579]! = nestingProjection579 := by
  rw [projections_lookup]
  rfl
def nestingEntries579 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 4 else 0) else 0) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 4) else 0) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 4 else 0)) else 0) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 4)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 3 else (-1)) else 1)) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then (-1) else 3) else 1))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 1 else (if n < 55 then 3 else (-1)))) else (if n < 60 then 0 else (if n < 62 then 1 else (if n < 63 then (-1) else 3)))))) else 0
theorem nestingEntries_eq579 (n : Nat) :
    nestingProjection579.numerator[n]! = nestingEntries579 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries579, if_neg (by omega : ¬ n < 64)]

def nestingProjection580 : Projection := ⟨4,7,#[4,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,3,1,-1,-1,0,0,0,0,1,3,1,1,0,0,0,0,-1,1,3,-1,0,0,0,0,-1,1,-1,3]⟩
theorem nestingLookup580 : projections[580]! = nestingProjection580 := by
  rw [projections_lookup]
  rfl
def nestingEntries580 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 4 else 0) else 0) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 4) else 0) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 4 else 0)) else 0) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 4)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 3 else 1) else (-1))) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 1 else 3) else 1))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then (if n < 53 then (-1) else 1) else (if n < 55 then 3 else (-1)))) else (if n < 60 then 0 else (if n < 62 then (if n < 61 then (-1) else 1) else (if n < 63 then (-1) else 3)))))) else 0
theorem nestingEntries_eq580 (n : Nat) :
    nestingProjection580.numerator[n]! = nestingEntries580 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries580, if_neg (by omega : ¬ n < 64)]

def nestingProjection581 : Projection := ⟨4,7,#[4,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,3,1,-1,1,0,0,0,0,1,3,1,-1,0,0,0,0,-1,1,3,1,0,0,0,0,1,-1,1,3]⟩
theorem nestingLookup581 : projections[581]! = nestingProjection581 := by
  rw [projections_lookup]
  rfl
def nestingEntries581 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 4 else 0) else 0) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 4) else 0) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 4 else 0)) else 0) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 4)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 3 else 1) else (if n < 39 then (-1) else 1))) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 1 else 3) else (if n < 47 then 1 else (-1))))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then (if n < 53 then (-1) else 1) else (if n < 55 then 3 else 1))) else (if n < 60 then 0 else (if n < 62 then (if n < 61 then 1 else (-1)) else (if n < 63 then 1 else 3)))))) else 0
theorem nestingEntries_eq581 (n : Nat) :
    nestingProjection581.numerator[n]! = nestingEntries581 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries581, if_neg (by omega : ¬ n < 64)]

def nestingProjection582 : Projection := ⟨4,7,#[4,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,3,1,1,-1,0,0,0,0,1,3,-1,1,0,0,0,0,1,-1,3,1,0,0,0,0,-1,1,1,3]⟩
theorem nestingLookup582 : projections[582]! = nestingProjection582 := by
  rw [projections_lookup]
  rfl
def nestingEntries582 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 4 else 0) else 0) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 4) else 0) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 4 else 0)) else 0) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 4)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 3 else 1) else (if n < 39 then 1 else (-1)))) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 1 else 3) else (if n < 47 then (-1) else 1)))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then (if n < 53 then 1 else (-1)) else (if n < 55 then 3 else 1))) else (if n < 60 then 0 else (if n < 62 then (if n < 61 then (-1) else 1) else (if n < 63 then 1 else 3)))))) else 0
theorem nestingEntries_eq582 (n : Nat) :
    nestingProjection582.numerator[n]! = nestingEntries582 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries582, if_neg (by omega : ¬ n < 64)]

def nestingProjection583 : Projection := ⟨4,7,#[4,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,3,1,1,1,0,0,0,0,1,3,-1,-1,0,0,0,0,1,-1,3,-1,0,0,0,0,1,-1,-1,3]⟩
theorem nestingLookup583 : projections[583]! = nestingProjection583 := by
  rw [projections_lookup]
  rfl
def nestingEntries583 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 4 else 0) else 0) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 4) else 0) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 4 else 0)) else 0) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 4)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 3 else 1) else 1)) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 1 else 3) else (-1)))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then (if n < 53 then 1 else (-1)) else (if n < 55 then 3 else (-1)))) else (if n < 60 then 0 else (if n < 62 then (if n < 61 then 1 else (-1)) else (if n < 63 then (-1) else 3)))))) else 0
theorem nestingEntries_eq583 (n : Nat) :
    nestingProjection583.numerator[n]! = nestingEntries583 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries583, if_neg (by omega : ¬ n < 64)]

def nestingProjection584 : Projection := ⟨4,7,#[3,-1,-1,-1,0,0,0,0,-1,3,-1,-1,0,0,0,0,-1,-1,3,-1,0,0,0,0,-1,-1,-1,3,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,4]⟩
theorem nestingLookup584 : projections[584]! = nestingProjection584 := by
  rw [projections_lookup]
  rfl
def nestingEntries584 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else (-1)) else (-1)) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then (-1) else 3) else (-1)) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then (-1) else (if n < 19 then 3 else (-1))) else 0) else (if n < 28 then (if n < 26 then (-1) else (if n < 27 then (-1) else 3)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 4 else 0) else 0)) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 4) else 0))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 0 else (if n < 55 then 4 else 0))) else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 4)))))) else 0
theorem nestingEntries_eq584 (n : Nat) :
    nestingProjection584.numerator[n]! = nestingEntries584 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries584, if_neg (by omega : ¬ n < 64)]

def nestingProjection585 : Projection := ⟨4,7,#[3,-1,-1,1,0,0,0,0,-1,3,-1,1,0,0,0,0,-1,-1,3,1,0,0,0,0,1,1,1,3,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,4]⟩
theorem nestingLookup585 : projections[585]! = nestingProjection585 := by
  rw [projections_lookup]
  rfl
def nestingEntries585 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else (-1)) else (if n < 3 then (-1) else 1)) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then (-1) else 3) else (if n < 11 then (-1) else 1)) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then (-1) else (if n < 19 then 3 else 1)) else 0) else (if n < 28 then (if n < 26 then 1 else (if n < 27 then 1 else 3)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 4 else 0) else 0)) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 4) else 0))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 0 else (if n < 55 then 4 else 0))) else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 4)))))) else 0
theorem nestingEntries_eq585 (n : Nat) :
    nestingProjection585.numerator[n]! = nestingEntries585 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries585, if_neg (by omega : ¬ n < 64)]

def nestingProjection586 : Projection := ⟨4,7,#[3,-1,1,1,0,0,0,0,-1,3,1,1,0,0,0,0,1,1,3,-1,0,0,0,0,1,1,-1,3,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,4]⟩
theorem nestingLookup586 : projections[586]! = nestingProjection586 := by
  rw [projections_lookup]
  rfl
def nestingEntries586 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else (-1)) else 1) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then (-1) else 3) else 1) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then 1 else (if n < 19 then 3 else (-1))) else 0) else (if n < 28 then (if n < 26 then 1 else (if n < 27 then (-1) else 3)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 4 else 0) else 0)) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 4) else 0))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 0 else (if n < 55 then 4 else 0))) else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 4)))))) else 0
theorem nestingEntries_eq586 (n : Nat) :
    nestingProjection586.numerator[n]! = nestingEntries586 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries586, if_neg (by omega : ¬ n < 64)]

def nestingProjection587 : Projection := ⟨4,7,#[3,1,-1,-1,0,0,0,0,1,3,1,1,0,0,0,0,-1,1,3,-1,0,0,0,0,-1,1,-1,3,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,4]⟩
theorem nestingLookup587 : projections[587]! = nestingProjection587 := by
  rw [projections_lookup]
  rfl
def nestingEntries587 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 1) else (-1)) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 1 else 3) else 1) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then (-1) else 1) else (if n < 19 then 3 else (-1))) else 0) else (if n < 28 then (if n < 26 then (if n < 25 then (-1) else 1) else (if n < 27 then (-1) else 3)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 4 else 0) else 0)) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 4) else 0))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 0 else (if n < 55 then 4 else 0))) else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 4)))))) else 0
theorem nestingEntries_eq587 (n : Nat) :
    nestingProjection587.numerator[n]! = nestingEntries587 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries587, if_neg (by omega : ¬ n < 64)]

def nestingProjection588 : Projection := ⟨4,7,#[3,1,-1,1,0,0,0,0,1,3,1,-1,0,0,0,0,-1,1,3,1,0,0,0,0,1,-1,1,3,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,4]⟩
theorem nestingLookup588 : projections[588]! = nestingProjection588 := by
  rw [projections_lookup]
  rfl
def nestingEntries588 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 1) else (if n < 3 then (-1) else 1)) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 1 else 3) else (if n < 11 then 1 else (-1))) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then (-1) else 1) else (if n < 19 then 3 else 1)) else 0) else (if n < 28 then (if n < 26 then (if n < 25 then 1 else (-1)) else (if n < 27 then 1 else 3)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 4 else 0) else 0)) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 4) else 0))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 0 else (if n < 55 then 4 else 0))) else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 4)))))) else 0
theorem nestingEntries_eq588 (n : Nat) :
    nestingProjection588.numerator[n]! = nestingEntries588 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries588, if_neg (by omega : ¬ n < 64)]

def nestingProjection589 : Projection := ⟨4,7,#[3,1,1,-1,0,0,0,0,1,3,-1,1,0,0,0,0,1,-1,3,1,0,0,0,0,-1,1,1,3,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,4]⟩
theorem nestingLookup589 : projections[589]! = nestingProjection589 := by
  rw [projections_lookup]
  rfl
def nestingEntries589 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 1) else (if n < 3 then 1 else (-1))) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 1 else 3) else (if n < 11 then (-1) else 1)) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 1 else (-1)) else (if n < 19 then 3 else 1)) else 0) else (if n < 28 then (if n < 26 then (if n < 25 then (-1) else 1) else (if n < 27 then 1 else 3)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 4 else 0) else 0)) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 4) else 0))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 0 else (if n < 55 then 4 else 0))) else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 4)))))) else 0
theorem nestingEntries_eq589 (n : Nat) :
    nestingProjection589.numerator[n]! = nestingEntries589 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries589, if_neg (by omega : ¬ n < 64)]

def nestingProjection590 : Projection := ⟨4,7,#[3,1,1,1,0,0,0,0,1,3,-1,-1,0,0,0,0,1,-1,3,-1,0,0,0,0,1,-1,-1,3,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,4]⟩
theorem nestingLookup590 : projections[590]! = nestingProjection590 := by
  rw [projections_lookup]
  rfl
def nestingEntries590 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 1) else 1) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 1 else 3) else (-1)) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 1 else (-1)) else (if n < 19 then 3 else (-1))) else 0) else (if n < 28 then (if n < 26 then (if n < 25 then 1 else (-1)) else (if n < 27 then (-1) else 3)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 4 else 0) else 0)) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 4) else 0))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 0 else (if n < 55 then 4 else 0))) else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 4)))))) else 0
theorem nestingEntries_eq590 (n : Nat) :
    nestingProjection590.numerator[n]! = nestingEntries590 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries590, if_neg (by omega : ¬ n < 64)]

def nestingProjection591 : Projection := ⟨4,7,#[3,0,0,-1,-1,0,0,1,0,4,0,0,0,0,0,0,0,0,4,0,0,0,0,0,-1,0,0,3,-1,0,0,1,-1,0,0,-1,3,0,0,1,0,0,0,0,0,4,0,0,0,0,0,0,0,0,4,0,1,0,0,1,1,0,0,3]⟩
theorem nestingLookup591 : projections[591]! = nestingProjection591 := by
  rw [projections_lookup]
  rfl
def nestingEntries591 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 0) else (if n < 3 then 0 else (-1))) else (if n < 6 then (if n < 5 then (-1) else 0) else (if n < 7 then 0 else 1))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 4) else 0) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 4 else 0)) else 0) else (if n < 28 then (if n < 26 then (if n < 25 then (-1) else 0) else (if n < 27 then 0 else 3)) else (if n < 30 then (if n < 29 then (-1) else 0) else (if n < 31 then 0 else 1))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then (-1) else 0) else (if n < 35 then 0 else (-1))) else (if n < 38 then (if n < 37 then 3 else 0) else (if n < 39 then 0 else 1))) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 4) else 0))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 0 else (if n < 55 then 4 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then 1 else 0) else (if n < 59 then 0 else 1)) else (if n < 62 then (if n < 61 then 1 else 0) else (if n < 63 then 0 else 3)))))) else 0
theorem nestingEntries_eq591 (n : Nat) :
    nestingProjection591.numerator[n]! = nestingEntries591 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries591, if_neg (by omega : ¬ n < 64)]

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def nestingProjection592 : Projection := ⟨4,7,#[3,0,0,-1,1,0,0,-1,0,4,0,0,0,0,0,0,0,0,4,0,0,0,0,0,-1,0,0,3,1,0,0,-1,1,0,0,1,3,0,0,1,0,0,0,0,0,4,0,0,0,0,0,0,0,0,4,0,-1,0,0,-1,1,0,0,3]⟩
theorem nestingLookup592 : projections[592]! = nestingProjection592 := by
  rw [projections_lookup]
  rfl
def nestingEntries592 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 0) else (if n < 3 then 0 else (-1))) else (if n < 6 then (if n < 5 then 1 else 0) else (if n < 7 then 0 else (-1)))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 4) else 0) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 4 else 0)) else 0) else (if n < 28 then (if n < 26 then (if n < 25 then (-1) else 0) else (if n < 27 then 0 else 3)) else (if n < 30 then (if n < 29 then 1 else 0) else (if n < 31 then 0 else (-1)))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 1 else 0) else (if n < 35 then 0 else 1)) else (if n < 38 then (if n < 37 then 3 else 0) else (if n < 39 then 0 else 1))) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 4) else 0))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 0 else (if n < 55 then 4 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then (-1) else 0) else (if n < 59 then 0 else (-1))) else (if n < 62 then (if n < 61 then 1 else 0) else (if n < 63 then 0 else 3)))))) else 0
theorem nestingEntries_eq592 (n : Nat) :
    nestingProjection592.numerator[n]! = nestingEntries592 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries592, if_neg (by omega : ¬ n < 64)]

def nestingProjection593 : Projection := ⟨4,7,#[3,0,0,-1,1,0,0,1,0,4,0,0,0,0,0,0,0,0,4,0,0,0,0,0,-1,0,0,3,1,0,0,1,1,0,0,1,3,0,0,-1,0,0,0,0,0,4,0,0,0,0,0,0,0,0,4,0,1,0,0,1,-1,0,0,3]⟩
theorem nestingLookup593 : projections[593]! = nestingProjection593 := by
  rw [projections_lookup]
  rfl
def nestingEntries593 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 0) else (if n < 3 then 0 else (-1))) else (if n < 6 then (if n < 5 then 1 else 0) else (if n < 7 then 0 else 1))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 4) else 0) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 4 else 0)) else 0) else (if n < 28 then (if n < 26 then (if n < 25 then (-1) else 0) else (if n < 27 then 0 else 3)) else (if n < 30 then (if n < 29 then 1 else 0) else (if n < 31 then 0 else 1))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 1 else 0) else (if n < 35 then 0 else 1)) else (if n < 38 then (if n < 37 then 3 else 0) else (if n < 39 then 0 else (-1)))) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 4) else 0))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 0 else (if n < 55 then 4 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then 1 else 0) else (if n < 59 then 0 else 1)) else (if n < 62 then (if n < 61 then (-1) else 0) else (if n < 63 then 0 else 3)))))) else 0
theorem nestingEntries_eq593 (n : Nat) :
    nestingProjection593.numerator[n]! = nestingEntries593 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries593, if_neg (by omega : ¬ n < 64)]

def nestingProjection594 : Projection := ⟨4,7,#[3,0,0,1,-1,0,0,-1,0,4,0,0,0,0,0,0,0,0,4,0,0,0,0,0,1,0,0,3,1,0,0,1,-1,0,0,1,3,0,0,-1,0,0,0,0,0,4,0,0,0,0,0,0,0,0,4,0,-1,0,0,1,-1,0,0,3]⟩
theorem nestingLookup594 : projections[594]! = nestingProjection594 := by
  rw [projections_lookup]
  rfl
def nestingEntries594 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 0) else (if n < 3 then 0 else 1)) else (if n < 6 then (if n < 5 then (-1) else 0) else (if n < 7 then 0 else (-1)))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 4) else 0) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 4 else 0)) else 0) else (if n < 28 then (if n < 26 then (if n < 25 then 1 else 0) else (if n < 27 then 0 else 3)) else (if n < 30 then (if n < 29 then 1 else 0) else (if n < 31 then 0 else 1))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then (-1) else 0) else (if n < 35 then 0 else 1)) else (if n < 38 then (if n < 37 then 3 else 0) else (if n < 39 then 0 else (-1)))) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 4) else 0))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 0 else (if n < 55 then 4 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then (-1) else 0) else (if n < 59 then 0 else 1)) else (if n < 62 then (if n < 61 then (-1) else 0) else (if n < 63 then 0 else 3)))))) else 0
theorem nestingEntries_eq594 (n : Nat) :
    nestingProjection594.numerator[n]! = nestingEntries594 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries594, if_neg (by omega : ¬ n < 64)]

def nestingProjection595 : Projection := ⟨4,7,#[3,0,0,1,-1,0,0,1,0,4,0,0,0,0,0,0,0,0,4,0,0,0,0,0,1,0,0,3,1,0,0,-1,-1,0,0,1,3,0,0,1,0,0,0,0,0,4,0,0,0,0,0,0,0,0,4,0,1,0,0,-1,1,0,0,3]⟩
theorem nestingLookup595 : projections[595]! = nestingProjection595 := by
  rw [projections_lookup]
  rfl
def nestingEntries595 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 0) else (if n < 3 then 0 else 1)) else (if n < 6 then (if n < 5 then (-1) else 0) else (if n < 7 then 0 else 1))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 4) else 0) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 4 else 0)) else 0) else (if n < 28 then (if n < 26 then (if n < 25 then 1 else 0) else (if n < 27 then 0 else 3)) else (if n < 30 then (if n < 29 then 1 else 0) else (if n < 31 then 0 else (-1)))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then (-1) else 0) else (if n < 35 then 0 else 1)) else (if n < 38 then (if n < 37 then 3 else 0) else (if n < 39 then 0 else 1))) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 4) else 0))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 0 else (if n < 55 then 4 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then 1 else 0) else (if n < 59 then 0 else (-1))) else (if n < 62 then (if n < 61 then 1 else 0) else (if n < 63 then 0 else 3)))))) else 0
theorem nestingEntries_eq595 (n : Nat) :
    nestingProjection595.numerator[n]! = nestingEntries595 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries595, if_neg (by omega : ¬ n < 64)]

def nestingProjection596 : Projection := ⟨4,7,#[3,0,0,1,1,0,0,-1,0,4,0,0,0,0,0,0,0,0,4,0,0,0,0,0,1,0,0,3,-1,0,0,1,1,0,0,-1,3,0,0,1,0,0,0,0,0,4,0,0,0,0,0,0,0,0,4,0,-1,0,0,1,1,0,0,3]⟩
theorem nestingLookup596 : projections[596]! = nestingProjection596 := by
  rw [projections_lookup]
  rfl
def nestingEntries596 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 0) else (if n < 3 then 0 else 1)) else (if n < 6 then (if n < 5 then 1 else 0) else (if n < 7 then 0 else (-1)))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 4) else 0) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 4 else 0)) else 0) else (if n < 28 then (if n < 26 then (if n < 25 then 1 else 0) else (if n < 27 then 0 else 3)) else (if n < 30 then (if n < 29 then (-1) else 0) else (if n < 31 then 0 else 1))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 1 else 0) else (if n < 35 then 0 else (-1))) else (if n < 38 then (if n < 37 then 3 else 0) else (if n < 39 then 0 else 1))) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 4) else 0))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 0 else (if n < 55 then 4 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then (-1) else 0) else (if n < 59 then 0 else 1)) else (if n < 62 then (if n < 61 then 1 else 0) else (if n < 63 then 0 else 3)))))) else 0
theorem nestingEntries_eq596 (n : Nat) :
    nestingProjection596.numerator[n]! = nestingEntries596 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries596, if_neg (by omega : ¬ n < 64)]

def nestingProjection597 : Projection := ⟨4,7,#[3,0,0,1,1,0,0,1,0,4,0,0,0,0,0,0,0,0,4,0,0,0,0,0,1,0,0,3,-1,0,0,-1,1,0,0,-1,3,0,0,-1,0,0,0,0,0,4,0,0,0,0,0,0,0,0,4,0,1,0,0,-1,-1,0,0,3]⟩
theorem nestingLookup597 : projections[597]! = nestingProjection597 := by
  rw [projections_lookup]
  rfl
def nestingEntries597 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 0) else (if n < 3 then 0 else 1)) else (if n < 6 then (if n < 5 then 1 else 0) else (if n < 7 then 0 else 1))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 4) else 0) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 4 else 0)) else 0) else (if n < 28 then (if n < 26 then (if n < 25 then 1 else 0) else (if n < 27 then 0 else 3)) else (if n < 30 then (if n < 29 then (-1) else 0) else (if n < 31 then 0 else (-1)))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 1 else 0) else (if n < 35 then 0 else (-1))) else (if n < 38 then (if n < 37 then 3 else 0) else (if n < 39 then 0 else (-1)))) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 4) else 0))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 0 else (if n < 55 then 4 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then 1 else 0) else (if n < 59 then 0 else (-1))) else (if n < 62 then (if n < 61 then (-1) else 0) else (if n < 63 then 0 else 3)))))) else 0
theorem nestingEntries_eq597 (n : Nat) :
    nestingProjection597.numerator[n]! = nestingEntries597 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries597, if_neg (by omega : ¬ n < 64)]

def nestingProjection598 : Projection := ⟨4,7,#[4,0,0,0,0,0,0,0,0,3,0,-1,-1,0,-1,0,0,0,4,0,0,0,0,0,0,-1,0,3,-1,0,-1,0,0,-1,0,-1,3,0,-1,0,0,0,0,0,0,4,0,0,0,-1,0,-1,-1,0,3,0,0,0,0,0,0,0,0,4]⟩
theorem nestingLookup598 : projections[598]! = nestingProjection598 := by
  rw [projections_lookup]
  rfl
def nestingEntries598 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 4 else 0) else 0) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 3) else (if n < 11 then 0 else (-1))) else (if n < 14 then (if n < 13 then (-1) else 0) else (if n < 15 then (-1) else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 4 else 0)) else 0) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else (-1)) else (if n < 27 then 0 else 3)) else (if n < 30 then (if n < 29 then (-1) else 0) else (if n < 31 then (-1) else 0))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 0 else (-1)) else (if n < 35 then 0 else (-1))) else (if n < 38 then (if n < 37 then 3 else 0) else (if n < 39 then (-1) else 0))) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 4) else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else (-1)) else (if n < 51 then 0 else (-1))) else (if n < 54 then (if n < 53 then (-1) else 0) else (if n < 55 then 3 else 0))) else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 4)))))) else 0
theorem nestingEntries_eq598 (n : Nat) :
    nestingProjection598.numerator[n]! = nestingEntries598 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries598, if_neg (by omega : ¬ n < 64)]

def nestingProjection599 : Projection := ⟨4,7,#[4,0,0,0,0,0,0,0,0,3,0,-1,-1,0,1,0,0,0,4,0,0,0,0,0,0,-1,0,3,-1,0,1,0,0,-1,0,-1,3,0,1,0,0,0,0,0,0,4,0,0,0,1,0,1,1,0,3,0,0,0,0,0,0,0,0,4]⟩
theorem nestingLookup599 : projections[599]! = nestingProjection599 := by
  rw [projections_lookup]
  rfl
def nestingEntries599 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 4 else 0) else 0) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 3) else (if n < 11 then 0 else (-1))) else (if n < 14 then (if n < 13 then (-1) else 0) else (if n < 15 then 1 else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 4 else 0)) else 0) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else (-1)) else (if n < 27 then 0 else 3)) else (if n < 30 then (if n < 29 then (-1) else 0) else (if n < 31 then 1 else 0))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 0 else (-1)) else (if n < 35 then 0 else (-1))) else (if n < 38 then (if n < 37 then 3 else 0) else (if n < 39 then 1 else 0))) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 4) else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else 1) else (if n < 51 then 0 else 1)) else (if n < 54 then (if n < 53 then 1 else 0) else (if n < 55 then 3 else 0))) else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 4)))))) else 0
theorem nestingEntries_eq599 (n : Nat) :
    nestingProjection599.numerator[n]! = nestingEntries599 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries599, if_neg (by omega : ¬ n < 64)]

def nestingProjection600 : Projection := ⟨4,7,#[4,0,0,0,0,0,0,0,0,3,0,-1,1,0,-1,0,0,0,4,0,0,0,0,0,0,-1,0,3,1,0,-1,0,0,1,0,1,3,0,1,0,0,0,0,0,0,4,0,0,0,-1,0,-1,1,0,3,0,0,0,0,0,0,0,0,4]⟩
theorem nestingLookup600 : projections[600]! = nestingProjection600 := by
  rw [projections_lookup]
  rfl
def nestingEntries600 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 4 else 0) else 0) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 3) else (if n < 11 then 0 else (-1))) else (if n < 14 then (if n < 13 then 1 else 0) else (if n < 15 then (-1) else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 4 else 0)) else 0) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else (-1)) else (if n < 27 then 0 else 3)) else (if n < 30 then (if n < 29 then 1 else 0) else (if n < 31 then (-1) else 0))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 0 else 1) else (if n < 35 then 0 else 1)) else (if n < 38 then (if n < 37 then 3 else 0) else (if n < 39 then 1 else 0))) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 4) else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else (-1)) else (if n < 51 then 0 else (-1))) else (if n < 54 then (if n < 53 then 1 else 0) else (if n < 55 then 3 else 0))) else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 4)))))) else 0
theorem nestingEntries_eq600 (n : Nat) :
    nestingProjection600.numerator[n]! = nestingEntries600 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries600, if_neg (by omega : ¬ n < 64)]

def nestingProjection601 : Projection := ⟨4,7,#[4,0,0,0,0,0,0,0,0,3,0,-1,1,0,1,0,0,0,4,0,0,0,0,0,0,-1,0,3,1,0,1,0,0,1,0,1,3,0,-1,0,0,0,0,0,0,4,0,0,0,1,0,1,-1,0,3,0,0,0,0,0,0,0,0,4]⟩
theorem nestingLookup601 : projections[601]! = nestingProjection601 := by
  rw [projections_lookup]
  rfl
def nestingEntries601 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 4 else 0) else 0) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 3) else (if n < 11 then 0 else (-1))) else (if n < 14 then (if n < 13 then 1 else 0) else (if n < 15 then 1 else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 4 else 0)) else 0) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else (-1)) else (if n < 27 then 0 else 3)) else (if n < 30 then (if n < 29 then 1 else 0) else (if n < 31 then 1 else 0))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 0 else 1) else (if n < 35 then 0 else 1)) else (if n < 38 then (if n < 37 then 3 else 0) else (if n < 39 then (-1) else 0))) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 4) else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else 1) else (if n < 51 then 0 else 1)) else (if n < 54 then (if n < 53 then (-1) else 0) else (if n < 55 then 3 else 0))) else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 4)))))) else 0
theorem nestingEntries_eq601 (n : Nat) :
    nestingProjection601.numerator[n]! = nestingEntries601 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries601, if_neg (by omega : ¬ n < 64)]

def nestingProjection602 : Projection := ⟨4,7,#[4,0,0,0,0,0,0,0,0,3,0,1,-1,0,-1,0,0,0,4,0,0,0,0,0,0,1,0,3,1,0,1,0,0,-1,0,1,3,0,-1,0,0,0,0,0,0,4,0,0,0,-1,0,1,-1,0,3,0,0,0,0,0,0,0,0,4]⟩
theorem nestingLookup602 : projections[602]! = nestingProjection602 := by
  rw [projections_lookup]
  rfl
def nestingEntries602 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 4 else 0) else 0) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 3) else (if n < 11 then 0 else 1)) else (if n < 14 then (if n < 13 then (-1) else 0) else (if n < 15 then (-1) else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 4 else 0)) else 0) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else 1) else (if n < 27 then 0 else 3)) else (if n < 30 then (if n < 29 then 1 else 0) else (if n < 31 then 1 else 0))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 0 else (-1)) else (if n < 35 then 0 else 1)) else (if n < 38 then (if n < 37 then 3 else 0) else (if n < 39 then (-1) else 0))) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 4) else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else (-1)) else (if n < 51 then 0 else 1)) else (if n < 54 then (if n < 53 then (-1) else 0) else (if n < 55 then 3 else 0))) else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 4)))))) else 0
theorem nestingEntries_eq602 (n : Nat) :
    nestingProjection602.numerator[n]! = nestingEntries602 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries602, if_neg (by omega : ¬ n < 64)]

def nestingProjection603 : Projection := ⟨4,7,#[4,0,0,0,0,0,0,0,0,3,0,1,-1,0,1,0,0,0,4,0,0,0,0,0,0,1,0,3,1,0,-1,0,0,-1,0,1,3,0,1,0,0,0,0,0,0,4,0,0,0,1,0,-1,1,0,3,0,0,0,0,0,0,0,0,4]⟩
theorem nestingLookup603 : projections[603]! = nestingProjection603 := by
  rw [projections_lookup]
  rfl
def nestingEntries603 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 4 else 0) else 0) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 3) else (if n < 11 then 0 else 1)) else (if n < 14 then (if n < 13 then (-1) else 0) else (if n < 15 then 1 else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 4 else 0)) else 0) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else 1) else (if n < 27 then 0 else 3)) else (if n < 30 then (if n < 29 then 1 else 0) else (if n < 31 then (-1) else 0))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 0 else (-1)) else (if n < 35 then 0 else 1)) else (if n < 38 then (if n < 37 then 3 else 0) else (if n < 39 then 1 else 0))) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 4) else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else 1) else (if n < 51 then 0 else (-1))) else (if n < 54 then (if n < 53 then 1 else 0) else (if n < 55 then 3 else 0))) else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 4)))))) else 0
theorem nestingEntries_eq603 (n : Nat) :
    nestingProjection603.numerator[n]! = nestingEntries603 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries603, if_neg (by omega : ¬ n < 64)]

def nestingProjection604 : Projection := ⟨4,7,#[4,0,0,0,0,0,0,0,0,3,0,1,1,0,-1,0,0,0,4,0,0,0,0,0,0,1,0,3,-1,0,1,0,0,1,0,-1,3,0,1,0,0,0,0,0,0,4,0,0,0,-1,0,1,1,0,3,0,0,0,0,0,0,0,0,4]⟩
theorem nestingLookup604 : projections[604]! = nestingProjection604 := by
  rw [projections_lookup]
  rfl
def nestingEntries604 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 4 else 0) else 0) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 3) else (if n < 11 then 0 else 1)) else (if n < 14 then (if n < 13 then 1 else 0) else (if n < 15 then (-1) else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 4 else 0)) else 0) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else 1) else (if n < 27 then 0 else 3)) else (if n < 30 then (if n < 29 then (-1) else 0) else (if n < 31 then 1 else 0))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 0 else 1) else (if n < 35 then 0 else (-1))) else (if n < 38 then (if n < 37 then 3 else 0) else (if n < 39 then 1 else 0))) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 4) else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else (-1)) else (if n < 51 then 0 else 1)) else (if n < 54 then (if n < 53 then 1 else 0) else (if n < 55 then 3 else 0))) else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 4)))))) else 0
theorem nestingEntries_eq604 (n : Nat) :
    nestingProjection604.numerator[n]! = nestingEntries604 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries604, if_neg (by omega : ¬ n < 64)]

def nestingProjection605 : Projection := ⟨4,7,#[4,0,0,0,0,0,0,0,0,3,0,1,1,0,1,0,0,0,4,0,0,0,0,0,0,1,0,3,-1,0,-1,0,0,1,0,-1,3,0,-1,0,0,0,0,0,0,4,0,0,0,1,0,-1,-1,0,3,0,0,0,0,0,0,0,0,4]⟩
theorem nestingLookup605 : projections[605]! = nestingProjection605 := by
  rw [projections_lookup]
  rfl
def nestingEntries605 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 4 else 0) else 0) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 3) else (if n < 11 then 0 else 1)) else (if n < 14 then (if n < 13 then 1 else 0) else (if n < 15 then 1 else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 4 else 0)) else 0) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else 1) else (if n < 27 then 0 else 3)) else (if n < 30 then (if n < 29 then (-1) else 0) else (if n < 31 then (-1) else 0))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 0 else 1) else (if n < 35 then 0 else (-1))) else (if n < 38 then (if n < 37 then 3 else 0) else (if n < 39 then (-1) else 0))) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 4) else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else 1) else (if n < 51 then 0 else (-1))) else (if n < 54 then (if n < 53 then (-1) else 0) else (if n < 55 then 3 else 0))) else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 4)))))) else 0
theorem nestingEntries_eq605 (n : Nat) :
    nestingProjection605.numerator[n]! = nestingEntries605 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries605, if_neg (by omega : ¬ n < 64)]

def nestingProjection606 : Projection := ⟨4,7,#[4,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,3,-1,0,0,-1,-1,0,0,-1,3,0,0,-1,-1,0,0,0,0,4,0,0,0,0,0,0,0,0,4,0,0,0,0,-1,-1,0,0,3,-1,0,0,-1,-1,0,0,-1,3]⟩
theorem nestingLookup606 : projections[606]! = nestingProjection606 := by
  rw [projections_lookup]
  rfl
def nestingEntries606 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 4 else 0) else 0) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 4) else 0) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 3 else (-1))) else (if n < 22 then 0 else (-1))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then (-1) else 3)) else (if n < 30 then 0 else (-1))))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 4 else 0) else 0)) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 4) else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then 0 else (-1)) else (if n < 54 then 0 else (if n < 55 then 3 else (-1)))) else (if n < 60 then (if n < 58 then 0 else (-1)) else (if n < 62 then 0 else (if n < 63 then (-1) else 3)))))) else 0
theorem nestingEntries_eq606 (n : Nat) :
    nestingProjection606.numerator[n]! = nestingEntries606 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries606, if_neg (by omega : ¬ n < 64)]

def nestingProjection607 : Projection := ⟨4,7,#[4,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,3,-1,0,0,1,-1,0,0,-1,3,0,0,1,-1,0,0,0,0,4,0,0,0,0,0,0,0,0,4,0,0,0,0,1,1,0,0,3,1,0,0,-1,-1,0,0,1,3]⟩
theorem nestingLookup607 : projections[607]! = nestingProjection607 := by
  rw [projections_lookup]
  rfl
def nestingEntries607 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 4 else 0) else 0) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 4) else 0) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 3 else (-1))) else (if n < 22 then 0 else (if n < 23 then 1 else (-1)))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then (-1) else 3)) else (if n < 30 then 0 else (if n < 31 then 1 else (-1)))))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 4 else 0) else 0)) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 4) else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then 0 else 1) else (if n < 54 then 0 else (if n < 55 then 3 else 1))) else (if n < 60 then (if n < 58 then 0 else (-1)) else (if n < 62 then 0 else (if n < 63 then 1 else 3)))))) else 0
theorem nestingEntries_eq607 (n : Nat) :
    nestingProjection607.numerator[n]! = nestingEntries607 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries607, if_neg (by omega : ¬ n < 64)]

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def nestingProjection608 : Projection := ⟨4,7,#[4,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,3,-1,0,0,1,1,0,0,-1,3,0,0,1,1,0,0,0,0,4,0,0,0,0,0,0,0,0,4,0,0,0,0,1,1,0,0,3,-1,0,0,1,1,0,0,-1,3]⟩
theorem nestingLookup608 : projections[608]! = nestingProjection608 := by
  rw [projections_lookup]
  rfl
def nestingEntries608 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 4 else 0) else 0) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 4) else 0) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 3 else (-1))) else (if n < 22 then 0 else 1)) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then (-1) else 3)) else (if n < 30 then 0 else 1)))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 4 else 0) else 0)) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 4) else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then 0 else 1) else (if n < 54 then 0 else (if n < 55 then 3 else (-1)))) else (if n < 60 then (if n < 58 then 0 else 1) else (if n < 62 then 0 else (if n < 63 then (-1) else 3)))))) else 0
theorem nestingEntries_eq608 (n : Nat) :
    nestingProjection608.numerator[n]! = nestingEntries608 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries608, if_neg (by omega : ¬ n < 64)]

def nestingProjection609 : Projection := ⟨4,7,#[4,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,3,1,0,0,-1,-1,0,0,1,3,0,0,1,1,0,0,0,0,4,0,0,0,0,0,0,0,0,4,0,0,0,0,-1,1,0,0,3,-1,0,0,-1,1,0,0,-1,3]⟩
theorem nestingLookup609 : projections[609]! = nestingProjection609 := by
  rw [projections_lookup]
  rfl
def nestingEntries609 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 4 else 0) else 0) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 4) else 0) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 3 else 1)) else (if n < 22 then 0 else (-1))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 1 else 3)) else (if n < 30 then 0 else 1)))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 4 else 0) else 0)) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 4) else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then 0 else (if n < 51 then (-1) else 1)) else (if n < 54 then 0 else (if n < 55 then 3 else (-1)))) else (if n < 60 then (if n < 58 then 0 else (if n < 59 then (-1) else 1)) else (if n < 62 then 0 else (if n < 63 then (-1) else 3)))))) else 0
theorem nestingEntries_eq609 (n : Nat) :
    nestingProjection609.numerator[n]! = nestingEntries609 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries609, if_neg (by omega : ¬ n < 64)]

def nestingProjection610 : Projection := ⟨4,7,#[4,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,3,1,0,0,-1,1,0,0,1,3,0,0,1,-1,0,0,0,0,4,0,0,0,0,0,0,0,0,4,0,0,0,0,-1,1,0,0,3,1,0,0,1,-1,0,0,1,3]⟩
theorem nestingLookup610 : projections[610]! = nestingProjection610 := by
  rw [projections_lookup]
  rfl
def nestingEntries610 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 4 else 0) else 0) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 4) else 0) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 3 else 1)) else (if n < 22 then 0 else (if n < 23 then (-1) else 1))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 1 else 3)) else (if n < 30 then 0 else (if n < 31 then 1 else (-1)))))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 4 else 0) else 0)) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 4) else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then 0 else (if n < 51 then (-1) else 1)) else (if n < 54 then 0 else (if n < 55 then 3 else 1))) else (if n < 60 then (if n < 58 then 0 else (if n < 59 then 1 else (-1))) else (if n < 62 then 0 else (if n < 63 then 1 else 3)))))) else 0
theorem nestingEntries_eq610 (n : Nat) :
    nestingProjection610.numerator[n]! = nestingEntries610 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries610, if_neg (by omega : ¬ n < 64)]

def nestingProjection611 : Projection := ⟨4,7,#[4,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,3,1,0,0,1,-1,0,0,1,3,0,0,-1,1,0,0,0,0,4,0,0,0,0,0,0,0,0,4,0,0,0,0,1,-1,0,0,3,1,0,0,-1,1,0,0,1,3]⟩
theorem nestingLookup611 : projections[611]! = nestingProjection611 := by
  rw [projections_lookup]
  rfl
def nestingEntries611 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 4 else 0) else 0) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 4) else 0) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 3 else 1)) else (if n < 22 then 0 else (if n < 23 then 1 else (-1)))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 1 else 3)) else (if n < 30 then 0 else (if n < 31 then (-1) else 1))))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 4 else 0) else 0)) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 4) else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then 0 else (if n < 51 then 1 else (-1))) else (if n < 54 then 0 else (if n < 55 then 3 else 1))) else (if n < 60 then (if n < 58 then 0 else (if n < 59 then (-1) else 1)) else (if n < 62 then 0 else (if n < 63 then 1 else 3)))))) else 0
theorem nestingEntries_eq611 (n : Nat) :
    nestingProjection611.numerator[n]! = nestingEntries611 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries611, if_neg (by omega : ¬ n < 64)]

def nestingProjection612 : Projection := ⟨4,7,#[4,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,3,1,0,0,1,1,0,0,1,3,0,0,-1,-1,0,0,0,0,4,0,0,0,0,0,0,0,0,4,0,0,0,0,1,-1,0,0,3,-1,0,0,1,-1,0,0,-1,3]⟩
theorem nestingLookup612 : projections[612]! = nestingProjection612 := by
  rw [projections_lookup]
  rfl
def nestingEntries612 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 4 else 0) else 0) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 4) else 0) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 3 else 1)) else (if n < 22 then 0 else 1)) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 1 else 3)) else (if n < 30 then 0 else (-1))))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 4 else 0) else 0)) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 4) else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then 0 else (if n < 51 then 1 else (-1))) else (if n < 54 then 0 else (if n < 55 then 3 else (-1)))) else (if n < 60 then (if n < 58 then 0 else (if n < 59 then 1 else (-1))) else (if n < 62 then 0 else (if n < 63 then (-1) else 3)))))) else 0
theorem nestingEntries_eq612 (n : Nat) :
    nestingProjection612.numerator[n]! = nestingEntries612 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries612, if_neg (by omega : ¬ n < 64)]

def nestingProjection613 : Projection := ⟨4,7,#[4,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,3,-1,-1,-1,0,0,0,0,-1,3,-1,-1,0,0,0,0,-1,-1,3,-1,0,0,0,0,-1,-1,-1,3,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,4]⟩
theorem nestingLookup613 : projections[613]! = nestingProjection613 := by
  rw [projections_lookup]
  rfl
def nestingEntries613 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 4 else 0) else 0) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 4) else 0) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 3 else (-1))) else (if n < 22 then (-1) else 0)) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then (-1) else 3)) else (if n < 30 then (-1) else 0)))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then 0 else (-1)) else (if n < 38 then (if n < 37 then 3 else (-1)) else 0)) else (if n < 44 then (if n < 42 then 0 else (-1)) else (if n < 46 then (if n < 45 then (-1) else 3) else 0))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 0 else (if n < 55 then 4 else 0))) else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 4)))))) else 0
theorem nestingEntries_eq613 (n : Nat) :
    nestingProjection613.numerator[n]! = nestingEntries613 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries613, if_neg (by omega : ¬ n < 64)]

def nestingProjection614 : Projection := ⟨4,7,#[4,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,3,-1,-1,1,0,0,0,0,-1,3,-1,1,0,0,0,0,-1,-1,3,1,0,0,0,0,1,1,1,3,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,4]⟩
theorem nestingLookup614 : projections[614]! = nestingProjection614 := by
  rw [projections_lookup]
  rfl
def nestingEntries614 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 4 else 0) else 0) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 4) else 0) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 3 else (-1))) else (if n < 22 then (if n < 21 then (-1) else 1) else 0)) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then (-1) else 3)) else (if n < 30 then (if n < 29 then (-1) else 1) else 0)))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then 0 else (-1)) else (if n < 38 then (if n < 37 then 3 else 1) else 0)) else (if n < 44 then (if n < 42 then 0 else 1) else (if n < 46 then (if n < 45 then 1 else 3) else 0))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 0 else (if n < 55 then 4 else 0))) else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 4)))))) else 0
theorem nestingEntries_eq614 (n : Nat) :
    nestingProjection614.numerator[n]! = nestingEntries614 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries614, if_neg (by omega : ¬ n < 64)]

def nestingProjection615 : Projection := ⟨4,7,#[4,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,3,-1,1,-1,0,0,0,0,-1,3,1,-1,0,0,0,0,1,1,3,1,0,0,0,0,-1,-1,1,3,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,4]⟩
theorem nestingLookup615 : projections[615]! = nestingProjection615 := by
  rw [projections_lookup]
  rfl
def nestingEntries615 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 4 else 0) else 0) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 4) else 0) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 3 else (-1))) else (if n < 22 then (if n < 21 then 1 else (-1)) else 0)) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then (-1) else 3)) else (if n < 30 then (if n < 29 then 1 else (-1)) else 0)))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then 0 else 1) else (if n < 38 then (if n < 37 then 3 else 1) else 0)) else (if n < 44 then (if n < 42 then 0 else (-1)) else (if n < 46 then (if n < 45 then 1 else 3) else 0))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 0 else (if n < 55 then 4 else 0))) else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 4)))))) else 0
theorem nestingEntries_eq615 (n : Nat) :
    nestingProjection615.numerator[n]! = nestingEntries615 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries615, if_neg (by omega : ¬ n < 64)]

def nestingProjection616 : Projection := ⟨4,7,#[4,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,3,-1,1,1,0,0,0,0,-1,3,1,1,0,0,0,0,1,1,3,-1,0,0,0,0,1,1,-1,3,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,4]⟩
theorem nestingLookup616 : projections[616]! = nestingProjection616 := by
  rw [projections_lookup]
  rfl
def nestingEntries616 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 4 else 0) else 0) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 4) else 0) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 3 else (-1))) else (if n < 22 then 1 else 0)) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then (-1) else 3)) else (if n < 30 then 1 else 0)))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then 0 else 1) else (if n < 38 then (if n < 37 then 3 else (-1)) else 0)) else (if n < 44 then (if n < 42 then 0 else 1) else (if n < 46 then (if n < 45 then (-1) else 3) else 0))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 0 else (if n < 55 then 4 else 0))) else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 4)))))) else 0
theorem nestingEntries_eq616 (n : Nat) :
    nestingProjection616.numerator[n]! = nestingEntries616 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries616, if_neg (by omega : ¬ n < 64)]

def nestingProjection617 : Projection := ⟨4,7,#[4,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,3,1,-1,-1,0,0,0,0,1,3,1,1,0,0,0,0,-1,1,3,-1,0,0,0,0,-1,1,-1,3,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,4]⟩
theorem nestingLookup617 : projections[617]! = nestingProjection617 := by
  rw [projections_lookup]
  rfl
def nestingEntries617 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 4 else 0) else 0) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 4) else 0) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 3 else 1)) else (if n < 22 then (-1) else 0)) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 1 else 3)) else (if n < 30 then 1 else 0)))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then 0 else (if n < 35 then (-1) else 1)) else (if n < 38 then (if n < 37 then 3 else (-1)) else 0)) else (if n < 44 then (if n < 42 then 0 else (if n < 43 then (-1) else 1)) else (if n < 46 then (if n < 45 then (-1) else 3) else 0))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 0 else (if n < 55 then 4 else 0))) else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 4)))))) else 0
theorem nestingEntries_eq617 (n : Nat) :
    nestingProjection617.numerator[n]! = nestingEntries617 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries617, if_neg (by omega : ¬ n < 64)]

def nestingProjection618 : Projection := ⟨4,7,#[4,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,3,1,-1,1,0,0,0,0,1,3,1,-1,0,0,0,0,-1,1,3,1,0,0,0,0,1,-1,1,3,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,4]⟩
theorem nestingLookup618 : projections[618]! = nestingProjection618 := by
  rw [projections_lookup]
  rfl
def nestingEntries618 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 4 else 0) else 0) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 4) else 0) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 3 else 1)) else (if n < 22 then (if n < 21 then (-1) else 1) else 0)) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 1 else 3)) else (if n < 30 then (if n < 29 then 1 else (-1)) else 0)))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then 0 else (if n < 35 then (-1) else 1)) else (if n < 38 then (if n < 37 then 3 else 1) else 0)) else (if n < 44 then (if n < 42 then 0 else (if n < 43 then 1 else (-1))) else (if n < 46 then (if n < 45 then 1 else 3) else 0))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 0 else (if n < 55 then 4 else 0))) else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 4)))))) else 0
theorem nestingEntries_eq618 (n : Nat) :
    nestingProjection618.numerator[n]! = nestingEntries618 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries618, if_neg (by omega : ¬ n < 64)]

def nestingProjection619 : Projection := ⟨4,7,#[4,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,3,1,1,-1,0,0,0,0,1,3,-1,1,0,0,0,0,1,-1,3,1,0,0,0,0,-1,1,1,3,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,4]⟩
theorem nestingLookup619 : projections[619]! = nestingProjection619 := by
  rw [projections_lookup]
  rfl
def nestingEntries619 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 4 else 0) else 0) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 4) else 0) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 3 else 1)) else (if n < 22 then (if n < 21 then 1 else (-1)) else 0)) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 1 else 3)) else (if n < 30 then (if n < 29 then (-1) else 1) else 0)))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then 0 else (if n < 35 then 1 else (-1))) else (if n < 38 then (if n < 37 then 3 else 1) else 0)) else (if n < 44 then (if n < 42 then 0 else (if n < 43 then (-1) else 1)) else (if n < 46 then (if n < 45 then 1 else 3) else 0))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 0 else (if n < 55 then 4 else 0))) else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 4)))))) else 0
theorem nestingEntries_eq619 (n : Nat) :
    nestingProjection619.numerator[n]! = nestingEntries619 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries619, if_neg (by omega : ¬ n < 64)]

def nestingProjection620 : Projection := ⟨4,7,#[4,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,3,1,1,1,0,0,0,0,1,3,-1,-1,0,0,0,0,1,-1,3,-1,0,0,0,0,1,-1,-1,3,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,4]⟩
theorem nestingLookup620 : projections[620]! = nestingProjection620 := by
  rw [projections_lookup]
  rfl
def nestingEntries620 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 4 else 0) else 0) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 4) else 0) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 3 else 1)) else (if n < 22 then 1 else 0)) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 1 else 3)) else (if n < 30 then (-1) else 0)))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then 0 else (if n < 35 then 1 else (-1))) else (if n < 38 then (if n < 37 then 3 else (-1)) else 0)) else (if n < 44 then (if n < 42 then 0 else (if n < 43 then 1 else (-1))) else (if n < 46 then (if n < 45 then (-1) else 3) else 0))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 0 else (if n < 55 then 4 else 0))) else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 4)))))) else 0
theorem nestingEntries_eq620 (n : Nat) :
    nestingProjection620.numerator[n]! = nestingEntries620 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries620, if_neg (by omega : ¬ n < 64)]

def nestingProjection621 : Projection := ⟨4,7,#[4,0,0,0,0,0,0,0,0,3,0,-1,0,-1,0,-1,0,0,4,0,0,0,0,0,0,-1,0,3,0,-1,0,-1,0,0,0,0,4,0,0,0,0,-1,0,-1,0,3,0,-1,0,0,0,0,0,0,4,0,0,-1,0,-1,0,-1,0,3]⟩
theorem nestingLookup621 : projections[621]! = nestingProjection621 := by
  rw [projections_lookup]
  rfl
def nestingEntries621 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 4 else 0) else 0) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 3) else (if n < 11 then 0 else (-1))) else (if n < 14 then (if n < 13 then 0 else (-1)) else (if n < 15 then 0 else (-1))))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 4 else 0)) else 0) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else (-1)) else (if n < 27 then 0 else 3)) else (if n < 30 then (if n < 29 then 0 else (-1)) else (if n < 31 then 0 else (-1)))))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 4 else 0) else 0)) else (if n < 44 then (if n < 42 then (if n < 41 then 0 else (-1)) else (if n < 43 then 0 else (-1))) else (if n < 46 then (if n < 45 then 0 else 3) else (if n < 47 then 0 else (-1))))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 0 else (if n < 55 then 4 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then 0 else (-1)) else (if n < 59 then 0 else (-1))) else (if n < 62 then (if n < 61 then 0 else (-1)) else (if n < 63 then 0 else 3)))))) else 0
theorem nestingEntries_eq621 (n : Nat) :
    nestingProjection621.numerator[n]! = nestingEntries621 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries621, if_neg (by omega : ¬ n < 64)]

def nestingProjection622 : Projection := ⟨4,7,#[4,0,0,0,0,0,0,0,0,3,0,-1,0,-1,0,1,0,0,4,0,0,0,0,0,0,-1,0,3,0,-1,0,1,0,0,0,0,4,0,0,0,0,-1,0,-1,0,3,0,1,0,0,0,0,0,0,4,0,0,1,0,1,0,1,0,3]⟩
theorem nestingLookup622 : projections[622]! = nestingProjection622 := by
  rw [projections_lookup]
  rfl
def nestingEntries622 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 4 else 0) else 0) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 3) else (if n < 11 then 0 else (-1))) else (if n < 14 then (if n < 13 then 0 else (-1)) else (if n < 15 then 0 else 1)))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 4 else 0)) else 0) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else (-1)) else (if n < 27 then 0 else 3)) else (if n < 30 then (if n < 29 then 0 else (-1)) else (if n < 31 then 0 else 1))))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 4 else 0) else 0)) else (if n < 44 then (if n < 42 then (if n < 41 then 0 else (-1)) else (if n < 43 then 0 else (-1))) else (if n < 46 then (if n < 45 then 0 else 3) else (if n < 47 then 0 else 1)))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 0 else (if n < 55 then 4 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then 0 else 1) else (if n < 59 then 0 else 1)) else (if n < 62 then (if n < 61 then 0 else 1) else (if n < 63 then 0 else 3)))))) else 0
theorem nestingEntries_eq622 (n : Nat) :
    nestingProjection622.numerator[n]! = nestingEntries622 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries622, if_neg (by omega : ¬ n < 64)]

def nestingProjection623 : Projection := ⟨4,7,#[4,0,0,0,0,0,0,0,0,3,0,-1,0,1,0,-1,0,0,4,0,0,0,0,0,0,-1,0,3,0,1,0,-1,0,0,0,0,4,0,0,0,0,1,0,1,0,3,0,1,0,0,0,0,0,0,4,0,0,-1,0,-1,0,1,0,3]⟩
theorem nestingLookup623 : projections[623]! = nestingProjection623 := by
  rw [projections_lookup]
  rfl
def nestingEntries623 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 4 else 0) else 0) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 3) else (if n < 11 then 0 else (-1))) else (if n < 14 then (if n < 13 then 0 else 1) else (if n < 15 then 0 else (-1))))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 4 else 0)) else 0) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else (-1)) else (if n < 27 then 0 else 3)) else (if n < 30 then (if n < 29 then 0 else 1) else (if n < 31 then 0 else (-1)))))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 4 else 0) else 0)) else (if n < 44 then (if n < 42 then (if n < 41 then 0 else 1) else (if n < 43 then 0 else 1)) else (if n < 46 then (if n < 45 then 0 else 3) else (if n < 47 then 0 else 1)))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 0 else (if n < 55 then 4 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then 0 else (-1)) else (if n < 59 then 0 else (-1))) else (if n < 62 then (if n < 61 then 0 else 1) else (if n < 63 then 0 else 3)))))) else 0
theorem nestingEntries_eq623 (n : Nat) :
    nestingProjection623.numerator[n]! = nestingEntries623 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries623, if_neg (by omega : ¬ n < 64)]

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def nestingProjection624 : Projection := ⟨4,7,#[4,0,0,0,0,0,0,0,0,3,0,-1,0,1,0,1,0,0,4,0,0,0,0,0,0,-1,0,3,0,1,0,1,0,0,0,0,4,0,0,0,0,1,0,1,0,3,0,-1,0,0,0,0,0,0,4,0,0,1,0,1,0,-1,0,3]⟩
theorem nestingLookup624 : projections[624]! = nestingProjection624 := by
  rw [projections_lookup]
  rfl
def nestingEntries624 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 4 else 0) else 0) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 3) else (if n < 11 then 0 else (-1))) else (if n < 14 then (if n < 13 then 0 else 1) else (if n < 15 then 0 else 1)))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 4 else 0)) else 0) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else (-1)) else (if n < 27 then 0 else 3)) else (if n < 30 then (if n < 29 then 0 else 1) else (if n < 31 then 0 else 1))))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 4 else 0) else 0)) else (if n < 44 then (if n < 42 then (if n < 41 then 0 else 1) else (if n < 43 then 0 else 1)) else (if n < 46 then (if n < 45 then 0 else 3) else (if n < 47 then 0 else (-1))))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 0 else (if n < 55 then 4 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then 0 else 1) else (if n < 59 then 0 else 1)) else (if n < 62 then (if n < 61 then 0 else (-1)) else (if n < 63 then 0 else 3)))))) else 0
theorem nestingEntries_eq624 (n : Nat) :
    nestingProjection624.numerator[n]! = nestingEntries624 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries624, if_neg (by omega : ¬ n < 64)]

def nestingProjection625 : Projection := ⟨4,7,#[4,0,0,0,0,0,0,0,0,3,0,1,0,-1,0,-1,0,0,4,0,0,0,0,0,0,1,0,3,0,1,0,1,0,0,0,0,4,0,0,0,0,-1,0,1,0,3,0,-1,0,0,0,0,0,0,4,0,0,-1,0,1,0,-1,0,3]⟩
theorem nestingLookup625 : projections[625]! = nestingProjection625 := by
  rw [projections_lookup]
  rfl
def nestingEntries625 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 4 else 0) else 0) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 3) else (if n < 11 then 0 else 1)) else (if n < 14 then (if n < 13 then 0 else (-1)) else (if n < 15 then 0 else (-1))))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 4 else 0)) else 0) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else 1) else (if n < 27 then 0 else 3)) else (if n < 30 then (if n < 29 then 0 else 1) else (if n < 31 then 0 else 1))))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 4 else 0) else 0)) else (if n < 44 then (if n < 42 then (if n < 41 then 0 else (-1)) else (if n < 43 then 0 else 1)) else (if n < 46 then (if n < 45 then 0 else 3) else (if n < 47 then 0 else (-1))))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 0 else (if n < 55 then 4 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then 0 else (-1)) else (if n < 59 then 0 else 1)) else (if n < 62 then (if n < 61 then 0 else (-1)) else (if n < 63 then 0 else 3)))))) else 0
theorem nestingEntries_eq625 (n : Nat) :
    nestingProjection625.numerator[n]! = nestingEntries625 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries625, if_neg (by omega : ¬ n < 64)]

def nestingProjection626 : Projection := ⟨4,7,#[4,0,0,0,0,0,0,0,0,3,0,1,0,-1,0,1,0,0,4,0,0,0,0,0,0,1,0,3,0,1,0,-1,0,0,0,0,4,0,0,0,0,-1,0,1,0,3,0,1,0,0,0,0,0,0,4,0,0,1,0,-1,0,1,0,3]⟩
theorem nestingLookup626 : projections[626]! = nestingProjection626 := by
  rw [projections_lookup]
  rfl
def nestingEntries626 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 4 else 0) else 0) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 3) else (if n < 11 then 0 else 1)) else (if n < 14 then (if n < 13 then 0 else (-1)) else (if n < 15 then 0 else 1)))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 4 else 0)) else 0) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else 1) else (if n < 27 then 0 else 3)) else (if n < 30 then (if n < 29 then 0 else 1) else (if n < 31 then 0 else (-1)))))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 4 else 0) else 0)) else (if n < 44 then (if n < 42 then (if n < 41 then 0 else (-1)) else (if n < 43 then 0 else 1)) else (if n < 46 then (if n < 45 then 0 else 3) else (if n < 47 then 0 else 1)))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 0 else (if n < 55 then 4 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then 0 else 1) else (if n < 59 then 0 else (-1))) else (if n < 62 then (if n < 61 then 0 else 1) else (if n < 63 then 0 else 3)))))) else 0
theorem nestingEntries_eq626 (n : Nat) :
    nestingProjection626.numerator[n]! = nestingEntries626 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries626, if_neg (by omega : ¬ n < 64)]

def nestingProjection627 : Projection := ⟨4,7,#[4,0,0,0,0,0,0,0,0,3,0,1,0,1,0,-1,0,0,4,0,0,0,0,0,0,1,0,3,0,-1,0,1,0,0,0,0,4,0,0,0,0,1,0,-1,0,3,0,1,0,0,0,0,0,0,4,0,0,-1,0,1,0,1,0,3]⟩
theorem nestingLookup627 : projections[627]! = nestingProjection627 := by
  rw [projections_lookup]
  rfl
def nestingEntries627 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 4 else 0) else 0) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 3) else (if n < 11 then 0 else 1)) else (if n < 14 then (if n < 13 then 0 else 1) else (if n < 15 then 0 else (-1))))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 4 else 0)) else 0) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else 1) else (if n < 27 then 0 else 3)) else (if n < 30 then (if n < 29 then 0 else (-1)) else (if n < 31 then 0 else 1))))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 4 else 0) else 0)) else (if n < 44 then (if n < 42 then (if n < 41 then 0 else 1) else (if n < 43 then 0 else (-1))) else (if n < 46 then (if n < 45 then 0 else 3) else (if n < 47 then 0 else 1)))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 0 else (if n < 55 then 4 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then 0 else (-1)) else (if n < 59 then 0 else 1)) else (if n < 62 then (if n < 61 then 0 else 1) else (if n < 63 then 0 else 3)))))) else 0
theorem nestingEntries_eq627 (n : Nat) :
    nestingProjection627.numerator[n]! = nestingEntries627 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries627, if_neg (by omega : ¬ n < 64)]

def nestingProjection628 : Projection := ⟨4,7,#[3,0,0,-1,0,-1,-1,0,0,4,0,0,0,0,0,0,0,0,4,0,0,0,0,0,-1,0,0,3,0,-1,-1,0,0,0,0,0,4,0,0,0,-1,0,0,-1,0,3,-1,0,-1,0,0,-1,0,-1,3,0,0,0,0,0,0,0,0,4]⟩
theorem nestingLookup628 : projections[628]! = nestingProjection628 := by
  rw [projections_lookup]
  rfl
def nestingEntries628 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 0) else (if n < 3 then 0 else (-1))) else (if n < 6 then (if n < 5 then 0 else (-1)) else (if n < 7 then (-1) else 0))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 4) else 0) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 4 else 0)) else 0) else (if n < 28 then (if n < 26 then (if n < 25 then (-1) else 0) else (if n < 27 then 0 else 3)) else (if n < 30 then (if n < 29 then 0 else (-1)) else (if n < 31 then (-1) else 0))))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 4 else 0) else 0)) else (if n < 44 then (if n < 42 then (if n < 41 then (-1) else 0) else (if n < 43 then 0 else (-1))) else (if n < 46 then (if n < 45 then 0 else 3) else (if n < 47 then (-1) else 0)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then (-1) else 0) else (if n < 51 then 0 else (-1))) else (if n < 54 then (if n < 53 then 0 else (-1)) else (if n < 55 then 3 else 0))) else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 4)))))) else 0
theorem nestingEntries_eq628 (n : Nat) :
    nestingProjection628.numerator[n]! = nestingEntries628 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries628, if_neg (by omega : ¬ n < 64)]

def nestingProjection629 : Projection := ⟨4,7,#[3,0,0,-1,0,-1,1,0,0,4,0,0,0,0,0,0,0,0,4,0,0,0,0,0,-1,0,0,3,0,-1,1,0,0,0,0,0,4,0,0,0,-1,0,0,-1,0,3,1,0,1,0,0,1,0,1,3,0,0,0,0,0,0,0,0,4]⟩
theorem nestingLookup629 : projections[629]! = nestingProjection629 := by
  rw [projections_lookup]
  rfl
def nestingEntries629 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 0) else (if n < 3 then 0 else (-1))) else (if n < 6 then (if n < 5 then 0 else (-1)) else (if n < 7 then 1 else 0))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 4) else 0) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 4 else 0)) else 0) else (if n < 28 then (if n < 26 then (if n < 25 then (-1) else 0) else (if n < 27 then 0 else 3)) else (if n < 30 then (if n < 29 then 0 else (-1)) else (if n < 31 then 1 else 0))))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 4 else 0) else 0)) else (if n < 44 then (if n < 42 then (if n < 41 then (-1) else 0) else (if n < 43 then 0 else (-1))) else (if n < 46 then (if n < 45 then 0 else 3) else (if n < 47 then 1 else 0)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 1 else 0) else (if n < 51 then 0 else 1)) else (if n < 54 then (if n < 53 then 0 else 1) else (if n < 55 then 3 else 0))) else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 4)))))) else 0
theorem nestingEntries_eq629 (n : Nat) :
    nestingProjection629.numerator[n]! = nestingEntries629 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries629, if_neg (by omega : ¬ n < 64)]

def nestingProjection630 : Projection := ⟨4,7,#[3,0,0,-1,0,1,-1,0,0,4,0,0,0,0,0,0,0,0,4,0,0,0,0,0,-1,0,0,3,0,1,-1,0,0,0,0,0,4,0,0,0,1,0,0,1,0,3,1,0,-1,0,0,-1,0,1,3,0,0,0,0,0,0,0,0,4]⟩
theorem nestingLookup630 : projections[630]! = nestingProjection630 := by
  rw [projections_lookup]
  rfl
def nestingEntries630 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 0) else (if n < 3 then 0 else (-1))) else (if n < 6 then (if n < 5 then 0 else 1) else (if n < 7 then (-1) else 0))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 4) else 0) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 4 else 0)) else 0) else (if n < 28 then (if n < 26 then (if n < 25 then (-1) else 0) else (if n < 27 then 0 else 3)) else (if n < 30 then (if n < 29 then 0 else 1) else (if n < 31 then (-1) else 0))))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 4 else 0) else 0)) else (if n < 44 then (if n < 42 then (if n < 41 then 1 else 0) else (if n < 43 then 0 else 1)) else (if n < 46 then (if n < 45 then 0 else 3) else (if n < 47 then 1 else 0)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then (-1) else 0) else (if n < 51 then 0 else (-1))) else (if n < 54 then (if n < 53 then 0 else 1) else (if n < 55 then 3 else 0))) else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 4)))))) else 0
theorem nestingEntries_eq630 (n : Nat) :
    nestingProjection630.numerator[n]! = nestingEntries630 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries630, if_neg (by omega : ¬ n < 64)]

def nestingProjection631 : Projection := ⟨4,7,#[3,0,0,-1,0,1,1,0,0,4,0,0,0,0,0,0,0,0,4,0,0,0,0,0,-1,0,0,3,0,1,1,0,0,0,0,0,4,0,0,0,1,0,0,1,0,3,-1,0,1,0,0,1,0,-1,3,0,0,0,0,0,0,0,0,4]⟩
theorem nestingLookup631 : projections[631]! = nestingProjection631 := by
  rw [projections_lookup]
  rfl
def nestingEntries631 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 0) else (if n < 3 then 0 else (-1))) else (if n < 6 then (if n < 5 then 0 else 1) else (if n < 7 then 1 else 0))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 4) else 0) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 4 else 0)) else 0) else (if n < 28 then (if n < 26 then (if n < 25 then (-1) else 0) else (if n < 27 then 0 else 3)) else (if n < 30 then (if n < 29 then 0 else 1) else (if n < 31 then 1 else 0))))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 4 else 0) else 0)) else (if n < 44 then (if n < 42 then (if n < 41 then 1 else 0) else (if n < 43 then 0 else 1)) else (if n < 46 then (if n < 45 then 0 else 3) else (if n < 47 then (-1) else 0)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 1 else 0) else (if n < 51 then 0 else 1)) else (if n < 54 then (if n < 53 then 0 else (-1)) else (if n < 55 then 3 else 0))) else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 4)))))) else 0
theorem nestingEntries_eq631 (n : Nat) :
    nestingProjection631.numerator[n]! = nestingEntries631 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries631, if_neg (by omega : ¬ n < 64)]

def nestingProjection632 : Projection := ⟨4,7,#[3,0,0,1,0,-1,-1,0,0,4,0,0,0,0,0,0,0,0,4,0,0,0,0,0,1,0,0,3,0,1,1,0,0,0,0,0,4,0,0,0,-1,0,0,1,0,3,-1,0,-1,0,0,1,0,-1,3,0,0,0,0,0,0,0,0,4]⟩
theorem nestingLookup632 : projections[632]! = nestingProjection632 := by
  rw [projections_lookup]
  rfl
def nestingEntries632 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 0) else (if n < 3 then 0 else 1)) else (if n < 6 then (if n < 5 then 0 else (-1)) else (if n < 7 then (-1) else 0))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 4) else 0) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 4 else 0)) else 0) else (if n < 28 then (if n < 26 then (if n < 25 then 1 else 0) else (if n < 27 then 0 else 3)) else (if n < 30 then (if n < 29 then 0 else 1) else (if n < 31 then 1 else 0))))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 4 else 0) else 0)) else (if n < 44 then (if n < 42 then (if n < 41 then (-1) else 0) else (if n < 43 then 0 else 1)) else (if n < 46 then (if n < 45 then 0 else 3) else (if n < 47 then (-1) else 0)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then (-1) else 0) else (if n < 51 then 0 else 1)) else (if n < 54 then (if n < 53 then 0 else (-1)) else (if n < 55 then 3 else 0))) else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 4)))))) else 0
theorem nestingEntries_eq632 (n : Nat) :
    nestingProjection632.numerator[n]! = nestingEntries632 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries632, if_neg (by omega : ¬ n < 64)]

def nestingProjection633 : Projection := ⟨4,7,#[3,0,0,1,0,-1,1,0,0,4,0,0,0,0,0,0,0,0,4,0,0,0,0,0,1,0,0,3,0,1,-1,0,0,0,0,0,4,0,0,0,-1,0,0,1,0,3,1,0,1,0,0,-1,0,1,3,0,0,0,0,0,0,0,0,4]⟩
theorem nestingLookup633 : projections[633]! = nestingProjection633 := by
  rw [projections_lookup]
  rfl
def nestingEntries633 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 0) else (if n < 3 then 0 else 1)) else (if n < 6 then (if n < 5 then 0 else (-1)) else (if n < 7 then 1 else 0))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 4) else 0) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 4 else 0)) else 0) else (if n < 28 then (if n < 26 then (if n < 25 then 1 else 0) else (if n < 27 then 0 else 3)) else (if n < 30 then (if n < 29 then 0 else 1) else (if n < 31 then (-1) else 0))))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 4 else 0) else 0)) else (if n < 44 then (if n < 42 then (if n < 41 then (-1) else 0) else (if n < 43 then 0 else 1)) else (if n < 46 then (if n < 45 then 0 else 3) else (if n < 47 then 1 else 0)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 1 else 0) else (if n < 51 then 0 else (-1))) else (if n < 54 then (if n < 53 then 0 else 1) else (if n < 55 then 3 else 0))) else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 4)))))) else 0
theorem nestingEntries_eq633 (n : Nat) :
    nestingProjection633.numerator[n]! = nestingEntries633 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries633, if_neg (by omega : ¬ n < 64)]

def nestingProjection634 : Projection := ⟨4,7,#[3,0,0,1,0,1,-1,0,0,4,0,0,0,0,0,0,0,0,4,0,0,0,0,0,1,0,0,3,0,-1,1,0,0,0,0,0,4,0,0,0,1,0,0,-1,0,3,1,0,-1,0,0,1,0,1,3,0,0,0,0,0,0,0,0,4]⟩
theorem nestingLookup634 : projections[634]! = nestingProjection634 := by
  rw [projections_lookup]
  rfl
def nestingEntries634 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 0) else (if n < 3 then 0 else 1)) else (if n < 6 then (if n < 5 then 0 else 1) else (if n < 7 then (-1) else 0))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 4) else 0) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 4 else 0)) else 0) else (if n < 28 then (if n < 26 then (if n < 25 then 1 else 0) else (if n < 27 then 0 else 3)) else (if n < 30 then (if n < 29 then 0 else (-1)) else (if n < 31 then 1 else 0))))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 4 else 0) else 0)) else (if n < 44 then (if n < 42 then (if n < 41 then 1 else 0) else (if n < 43 then 0 else (-1))) else (if n < 46 then (if n < 45 then 0 else 3) else (if n < 47 then 1 else 0)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then (-1) else 0) else (if n < 51 then 0 else 1)) else (if n < 54 then (if n < 53 then 0 else 1) else (if n < 55 then 3 else 0))) else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 4)))))) else 0
theorem nestingEntries_eq634 (n : Nat) :
    nestingProjection634.numerator[n]! = nestingEntries634 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries634, if_neg (by omega : ¬ n < 64)]

def nestingProjection635 : Projection := ⟨4,7,#[3,0,0,1,0,1,1,0,0,4,0,0,0,0,0,0,0,0,4,0,0,0,0,0,1,0,0,3,0,-1,-1,0,0,0,0,0,4,0,0,0,1,0,0,-1,0,3,-1,0,1,0,0,-1,0,-1,3,0,0,0,0,0,0,0,0,4]⟩
theorem nestingLookup635 : projections[635]! = nestingProjection635 := by
  rw [projections_lookup]
  rfl
def nestingEntries635 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 0) else (if n < 3 then 0 else 1)) else (if n < 6 then (if n < 5 then 0 else 1) else (if n < 7 then 1 else 0))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 4) else 0) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 4 else 0)) else 0) else (if n < 28 then (if n < 26 then (if n < 25 then 1 else 0) else (if n < 27 then 0 else 3)) else (if n < 30 then (if n < 29 then 0 else (-1)) else (if n < 31 then (-1) else 0))))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 4 else 0) else 0)) else (if n < 44 then (if n < 42 then (if n < 41 then 1 else 0) else (if n < 43 then 0 else (-1))) else (if n < 46 then (if n < 45 then 0 else 3) else (if n < 47 then (-1) else 0)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 1 else 0) else (if n < 51 then 0 else (-1))) else (if n < 54 then (if n < 53 then 0 else (-1)) else (if n < 55 then 3 else 0))) else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 4)))))) else 0
theorem nestingEntries_eq635 (n : Nat) :
    nestingProjection635.numerator[n]! = nestingEntries635 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries635, if_neg (by omega : ¬ n < 64)]

end CSL.Construction.PhysicalFramePaths


