-- Prove2me | Definitions.Def_CSL_Generated_FiniteCircuit_FramePathChecks_Entries_Batch01
-- name    : CSL_Generated_FiniteCircuit_FramePathChecks_Entries_Batch01
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T13:38:35.625549+00:00
-- url     : https://prove2.me/theorems/1b1d82a1-5638-41b8-94e3-3f48887293f6
-- title:
--   Coded sorting library: Generated / FiniteCircuit / FramePathChecks / Entries / Batch01
-- statement:
--   Module `CodedSorting.Generated.FiniteCircuit.FramePathChecks.Entries.Batch01` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   Generated physical-frame checks. Uncompiled until a build record exists.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Generated.FiniteCircuit.FramePathChecks.Entries.Batch01

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Generated_FiniteCircuit_FramePathChecks_FunctionBase

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def nestingProjection128 : Projection := ⟨4,2,#[2,-1,1,0,1,0,0,1,-1,1,-1,-1,0,0,0,0,1,-1,1,1,0,0,0,0,0,-1,1,2,-1,0,0,-1,1,0,0,-1,1,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,-1,1,0,0,1]⟩
theorem nestingLookup128 : projections[128]! = nestingProjection128 := by
  rw [projections_lookup]
  rfl
def nestingEntries128 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 2 else (-1)) else (if n < 3 then 1 else 0)) else (if n < 6 then (if n < 5 then 1 else 0) else (if n < 7 then 0 else 1))) else (if n < 12 then (if n < 10 then (if n < 9 then (-1) else 1) else (-1)) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 1 else (-1)) else 1) else 0) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else (-1)) else (if n < 27 then 1 else 2)) else (if n < 30 then (if n < 29 then (-1) else 0) else (if n < 31 then 0 else (-1)))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 1 else 0) else (if n < 35 then 0 else (-1))) else (if n < 38 then (if n < 37 then 1 else 0) else (if n < 39 then 0 else 1))) else 0) else (if n < 56 then 0 else (if n < 60 then (if n < 58 then (if n < 57 then 1 else 0) else (if n < 59 then 0 else (-1))) else (if n < 62 then (if n < 61 then 1 else 0) else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq128 (n : Nat) :
    nestingProjection128.numerator[n]! = nestingEntries128 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries128, if_neg (by omega : ¬ n < 64)]

def nestingProjection129 : Projection := ⟨4,2,#[2,-1,1,0,-1,0,0,-1,-1,1,-1,-1,0,0,0,0,1,-1,1,1,0,0,0,0,0,-1,1,2,1,0,0,1,-1,0,0,1,1,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,0,0,1,1,0,0,1]⟩
theorem nestingLookup129 : projections[129]! = nestingProjection129 := by
  rw [projections_lookup]
  rfl
def nestingEntries129 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 2 else (-1)) else (if n < 3 then 1 else 0)) else (if n < 6 then (if n < 5 then (-1) else 0) else (if n < 7 then 0 else (-1)))) else (if n < 12 then (if n < 10 then (if n < 9 then (-1) else 1) else (-1)) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 1 else (-1)) else 1) else 0) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else (-1)) else (if n < 27 then 1 else 2)) else (if n < 30 then (if n < 29 then 1 else 0) else (if n < 31 then 0 else 1))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then (-1) else 0) else (if n < 35 then 0 else 1)) else (if n < 38 then (if n < 37 then 1 else 0) else (if n < 39 then 0 else 1))) else 0) else (if n < 56 then 0 else (if n < 60 then (if n < 58 then (if n < 57 then (-1) else 0) else (if n < 59 then 0 else 1)) else (if n < 62 then (if n < 61 then 1 else 0) else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq129 (n : Nat) :
    nestingProjection129.numerator[n]! = nestingEntries129 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries129, if_neg (by omega : ¬ n < 64)]

def nestingProjection130 : Projection := ⟨2,2,#[1,0,0,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,0,0,1,0,0,0,0,0,0,0,0,1,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,1]⟩
theorem nestingLookup130 : projections[130]! = nestingProjection130 := by
  rw [projections_lookup]
  rfl
def nestingEntries130 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else (if n < 3 then 0 else (-1))) else 0) else 0) else (if n < 24 then 0 else (if n < 28 then (if n < 26 then (if n < 25 then (-1) else 0) else (if n < 27 then 0 else 1)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 1 else 0) else (if n < 39 then 0 else 1))) else 0) else (if n < 56 then 0 else (if n < 60 then 0 else (if n < 62 then (if n < 61 then 1 else 0) else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq130 (n : Nat) :
    nestingProjection130.numerator[n]! = nestingEntries130 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries130, if_neg (by omega : ¬ n < 64)]

def nestingProjection131 : Projection := ⟨2,2,#[1,0,0,-1,0,0,0,0,0,1,-1,0,0,0,0,0,0,-1,1,0,0,0,0,0,-1,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]⟩
theorem nestingLookup131 : projections[131]! = nestingProjection131 := by
  rw [projections_lookup]
  rfl
def nestingEntries131 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else (if n < 3 then 0 else (-1))) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else (if n < 11 then (-1) else 0)) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 0 else (-1)) else (if n < 19 then 1 else 0)) else 0) else (if n < 28 then (if n < 26 then (if n < 25 then (-1) else 0) else (if n < 27 then 0 else 1)) else 0))) else 0) else 0
theorem nestingEntries_eq131 (n : Nat) :
    nestingProjection131.numerator[n]! = nestingEntries131 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries131, if_neg (by omega : ¬ n < 64)]

def nestingProjection132 : Projection := ⟨4,2,#[2,1,-1,0,-1,0,0,-1,1,1,-1,-1,0,0,0,0,-1,-1,1,1,0,0,0,0,0,-1,1,2,-1,0,0,-1,-1,0,0,-1,1,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,0,0,-1,1,0,0,1]⟩
theorem nestingLookup132 : projections[132]! = nestingProjection132 := by
  rw [projections_lookup]
  rfl
def nestingEntries132 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 2 else 1) else (if n < 3 then (-1) else 0)) else (if n < 6 then (if n < 5 then (-1) else 0) else (if n < 7 then 0 else (-1)))) else (if n < 12 then (if n < 10 then 1 else (-1)) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then (-1) else 1) else 0) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else (-1)) else (if n < 27 then 1 else 2)) else (if n < 30 then (if n < 29 then (-1) else 0) else (if n < 31 then 0 else (-1)))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then (-1) else 0) else (if n < 35 then 0 else (-1))) else (if n < 38 then (if n < 37 then 1 else 0) else (if n < 39 then 0 else 1))) else 0) else (if n < 56 then 0 else (if n < 60 then (if n < 58 then (if n < 57 then (-1) else 0) else (if n < 59 then 0 else (-1))) else (if n < 62 then (if n < 61 then 1 else 0) else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq132 (n : Nat) :
    nestingProjection132.numerator[n]! = nestingEntries132 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries132, if_neg (by omega : ¬ n < 64)]

def nestingProjection133 : Projection := ⟨4,2,#[2,-1,1,0,-1,0,0,-1,-1,1,-1,1,0,0,0,0,1,-1,1,-1,0,0,0,0,0,1,-1,2,-1,0,0,-1,-1,0,0,-1,1,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,0,0,-1,1,0,0,1]⟩
theorem nestingLookup133 : projections[133]! = nestingProjection133 := by
  rw [projections_lookup]
  rfl
def nestingEntries133 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 2 else (-1)) else (if n < 3 then 1 else 0)) else (if n < 6 then (if n < 5 then (-1) else 0) else (if n < 7 then 0 else (-1)))) else (if n < 12 then (if n < 10 then (if n < 9 then (-1) else 1) else (if n < 11 then (-1) else 1)) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 1 else (-1)) else (if n < 19 then 1 else (-1))) else 0) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else 1) else (if n < 27 then (-1) else 2)) else (if n < 30 then (if n < 29 then (-1) else 0) else (if n < 31 then 0 else (-1)))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then (-1) else 0) else (if n < 35 then 0 else (-1))) else (if n < 38 then (if n < 37 then 1 else 0) else (if n < 39 then 0 else 1))) else 0) else (if n < 56 then 0 else (if n < 60 then (if n < 58 then (if n < 57 then (-1) else 0) else (if n < 59 then 0 else (-1))) else (if n < 62 then (if n < 61 then 1 else 0) else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq133 (n : Nat) :
    nestingProjection133.numerator[n]! = nestingEntries133 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries133, if_neg (by omega : ¬ n < 64)]

def nestingProjection134 : Projection := ⟨4,2,#[2,1,1,0,1,0,0,-1,1,1,0,0,0,0,1,-1,1,0,1,0,1,0,-1,0,0,0,0,0,0,0,0,0,1,0,1,0,1,0,-1,0,0,0,0,0,0,0,0,0,0,1,-1,0,-1,0,2,-1,-1,-1,0,0,0,0,-1,1]⟩
theorem nestingLookup134 : projections[134]! = nestingProjection134 := by
  rw [projections_lookup]
  rfl
def nestingEntries134 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 2 else 1) else (if n < 3 then 1 else 0)) else (if n < 6 then (if n < 5 then 1 else 0) else (if n < 7 then 0 else (-1)))) else (if n < 12 then (if n < 10 then 1 else 0) else (if n < 14 then 0 else (if n < 15 then 1 else (-1))))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 1 else 0) else (if n < 19 then 1 else 0)) else (if n < 22 then (if n < 21 then 1 else 0) else (if n < 23 then (-1) else 0))) else 0)) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 1 else 0) else (if n < 35 then 1 else 0)) else (if n < 38 then (if n < 37 then 1 else 0) else (if n < 39 then (-1) else 0))) else 0) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else 1) else (if n < 51 then (-1) else 0)) else (if n < 54 then (if n < 53 then (-1) else 0) else (if n < 55 then 2 else (-1)))) else (if n < 60 then (if n < 58 then (-1) else 0) else (if n < 62 then 0 else (if n < 63 then (-1) else 1)))))) else 0
theorem nestingEntries_eq134 (n : Nat) :
    nestingProjection134.numerator[n]! = nestingEntries134 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries134, if_neg (by omega : ¬ n < 64)]

def nestingProjection135 : Projection := ⟨4,2,#[1,0,1,0,1,0,-1,0,0,0,0,0,0,0,0,0,1,0,2,1,0,-1,-1,0,0,0,1,1,-1,-1,0,0,1,0,0,-1,2,1,-1,0,0,0,-1,-1,1,1,0,0,-1,0,-1,0,-1,0,1,0,0,0,0,0,0,0,0,0]⟩
theorem nestingLookup135 : projections[135]! = nestingProjection135 := by
  rw [projections_lookup]
  rfl
def nestingEntries135 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else (if n < 3 then 1 else 0)) else (if n < 6 then (if n < 5 then 1 else 0) else (if n < 7 then (-1) else 0))) else 0) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 1 else 0) else (if n < 19 then 2 else 1)) else (if n < 22 then (if n < 21 then 0 else (-1)) else (if n < 23 then (-1) else 0))) else (if n < 28 then (if n < 26 then 0 else 1) else (if n < 30 then (-1) else 0)))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 1 else 0) else (if n < 35 then 0 else (-1))) else (if n < 38 then (if n < 37 then 2 else 1) else (if n < 39 then (-1) else 0))) else (if n < 44 then (if n < 42 then 0 else (-1)) else (if n < 46 then 1 else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then (-1) else 0) else (if n < 51 then (-1) else 0)) else (if n < 54 then (if n < 53 then (-1) else 0) else (if n < 55 then 1 else 0))) else 0))) else 0
theorem nestingEntries_eq135 (n : Nat) :
    nestingProjection135.numerator[n]! = nestingEntries135 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries135, if_neg (by omega : ¬ n < 64)]

def nestingProjection136 : Projection := ⟨4,2,#[1,0,1,0,1,0,-1,0,0,1,0,1,0,1,0,1,1,0,1,0,1,0,-1,0,0,1,0,1,0,1,0,1,1,0,1,0,1,0,-1,0,0,1,0,1,0,1,0,1,-1,0,-1,0,-1,0,1,0,0,1,0,1,0,1,0,1]⟩
theorem nestingLookup136 : projections[136]! = nestingProjection136 := by
  rw [projections_lookup]
  rfl
def nestingEntries136 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else (if n < 3 then 1 else 0)) else (if n < 6 then (if n < 5 then 1 else 0) else (if n < 7 then (-1) else 0))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else (if n < 11 then 0 else 1)) else (if n < 14 then (if n < 13 then 0 else 1) else (if n < 15 then 0 else 1)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 1 else 0) else (if n < 19 then 1 else 0)) else (if n < 22 then (if n < 21 then 1 else 0) else (if n < 23 then (-1) else 0))) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else 1) else (if n < 27 then 0 else 1)) else (if n < 30 then (if n < 29 then 0 else 1) else (if n < 31 then 0 else 1))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 1 else 0) else (if n < 35 then 1 else 0)) else (if n < 38 then (if n < 37 then 1 else 0) else (if n < 39 then (-1) else 0))) else (if n < 44 then (if n < 42 then (if n < 41 then 0 else 1) else (if n < 43 then 0 else 1)) else (if n < 46 then (if n < 45 then 0 else 1) else (if n < 47 then 0 else 1)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then (-1) else 0) else (if n < 51 then (-1) else 0)) else (if n < 54 then (if n < 53 then (-1) else 0) else (if n < 55 then 1 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then 0 else 1) else (if n < 59 then 0 else 1)) else (if n < 62 then (if n < 61 then 0 else 1) else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq136 (n : Nat) :
    nestingProjection136.numerator[n]! = nestingEntries136 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries136, if_neg (by omega : ¬ n < 64)]

def nestingProjection137 : Projection := ⟨4,2,#[1,1,0,0,0,0,1,-1,1,1,0,0,0,0,1,-1,0,0,1,1,-1,-1,0,0,0,0,1,1,-1,-1,0,0,0,0,-1,-1,1,1,0,0,0,0,-1,-1,1,1,0,0,1,1,0,0,0,0,1,-1,-1,-1,0,0,0,0,-1,1]⟩
theorem nestingLookup137 : projections[137]! = nestingProjection137 := by
  rw [projections_lookup]
  rfl
def nestingEntries137 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then 1 else 0) else (if n < 6 then 0 else (if n < 7 then 1 else (-1)))) else (if n < 12 then (if n < 10 then 1 else 0) else (if n < 14 then 0 else (if n < 15 then 1 else (-1))))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else 1) else (if n < 22 then (-1) else 0)) else (if n < 28 then (if n < 26 then 0 else 1) else (if n < 30 then (-1) else 0)))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then 0 else (-1)) else (if n < 38 then 1 else 0)) else (if n < 44 then (if n < 42 then 0 else (-1)) else (if n < 46 then 1 else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then 1 else 0) else (if n < 54 then 0 else (if n < 55 then 1 else (-1)))) else (if n < 60 then (if n < 58 then (-1) else 0) else (if n < 62 then 0 else (if n < 63 then (-1) else 1)))))) else 0
theorem nestingEntries_eq137 (n : Nat) :
    nestingProjection137.numerator[n]! = nestingEntries137 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries137, if_neg (by omega : ¬ n < 64)]

def nestingProjection138 : Projection := ⟨4,2,#[1,1,0,0,0,0,1,-1,1,2,0,1,0,1,1,0,0,0,0,0,0,0,0,0,0,1,0,1,0,1,0,1,0,0,0,0,0,0,0,0,0,1,0,1,0,1,0,1,1,1,0,0,0,0,1,-1,-1,0,0,1,0,1,-1,2]⟩
theorem nestingLookup138 : projections[138]! = nestingProjection138 := by
  rw [projections_lookup]
  rfl
def nestingEntries138 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then 1 else 0) else (if n < 6 then 0 else (if n < 7 then 1 else (-1)))) else (if n < 12 then (if n < 10 then (if n < 9 then 1 else 2) else (if n < 11 then 0 else 1)) else (if n < 14 then (if n < 13 then 0 else 1) else (if n < 15 then 1 else 0)))) else (if n < 24 then 0 else (if n < 28 then (if n < 26 then (if n < 25 then 0 else 1) else (if n < 27 then 0 else 1)) else (if n < 30 then (if n < 29 then 0 else 1) else (if n < 31 then 0 else 1))))) else (if n < 48 then (if n < 40 then 0 else (if n < 44 then (if n < 42 then (if n < 41 then 0 else 1) else (if n < 43 then 0 else 1)) else (if n < 46 then (if n < 45 then 0 else 1) else (if n < 47 then 0 else 1)))) else (if n < 56 then (if n < 52 then (if n < 50 then 1 else 0) else (if n < 54 then 0 else (if n < 55 then 1 else (-1)))) else (if n < 60 then (if n < 58 then (if n < 57 then (-1) else 0) else (if n < 59 then 0 else 1)) else (if n < 62 then (if n < 61 then 0 else 1) else (if n < 63 then (-1) else 2)))))) else 0
theorem nestingEntries_eq138 (n : Nat) :
    nestingProjection138.numerator[n]! = nestingEntries138 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries138, if_neg (by omega : ¬ n < 64)]

def nestingProjection139 : Projection := ⟨4,2,#[0,0,0,0,0,0,0,0,0,1,0,1,0,1,0,1,0,0,1,1,-1,-1,0,0,0,1,1,2,-1,0,0,1,0,0,-1,-1,1,1,0,0,0,1,-1,0,1,2,0,1,0,0,0,0,0,0,0,0,0,1,0,1,0,1,0,1]⟩
theorem nestingLookup139 : projections[139]! = nestingProjection139 := by
  rw [projections_lookup]
  rfl
def nestingEntries139 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then 0 else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else (if n < 11 then 0 else 1)) else (if n < 14 then (if n < 13 then 0 else 1) else (if n < 15 then 0 else 1)))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else 1) else (if n < 22 then (-1) else 0)) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else 1) else (if n < 27 then 1 else 2)) else (if n < 30 then (if n < 29 then (-1) else 0) else (if n < 31 then 0 else 1))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then 0 else (-1)) else (if n < 38 then 1 else 0)) else (if n < 44 then (if n < 42 then (if n < 41 then 0 else 1) else (if n < 43 then (-1) else 0)) else (if n < 46 then (if n < 45 then 1 else 2) else (if n < 47 then 0 else 1)))) else (if n < 56 then 0 else (if n < 60 then (if n < 58 then (if n < 57 then 0 else 1) else (if n < 59 then 0 else 1)) else (if n < 62 then (if n < 61 then 0 else 1) else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq139 (n : Nat) :
    nestingProjection139.numerator[n]! = nestingEntries139 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries139, if_neg (by omega : ¬ n < 64)]

def nestingProjection140 : Projection := ⟨4,2,#[2,1,1,0,1,0,0,-1,1,1,0,0,1,1,0,0,1,0,1,0,0,-1,0,-1,0,0,0,0,0,0,0,0,1,1,0,0,1,1,0,0,0,1,-1,0,1,2,0,1,0,0,0,0,0,0,0,0,-1,0,-1,0,0,1,0,1]⟩
theorem nestingLookup140 : projections[140]! = nestingProjection140 := by
  rw [projections_lookup]
  rfl
def nestingEntries140 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 2 else 1) else (if n < 3 then 1 else 0)) else (if n < 6 then (if n < 5 then 1 else 0) else (if n < 7 then 0 else (-1)))) else (if n < 12 then (if n < 10 then 1 else 0) else (if n < 14 then 1 else 0))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 1 else 0) else (if n < 19 then 1 else 0)) else (if n < 22 then (if n < 21 then 0 else (-1)) else (if n < 23 then 0 else (-1)))) else 0)) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then 1 else 0) else (if n < 38 then 1 else 0)) else (if n < 44 then (if n < 42 then (if n < 41 then 0 else 1) else (if n < 43 then (-1) else 0)) else (if n < 46 then (if n < 45 then 1 else 2) else (if n < 47 then 0 else 1)))) else (if n < 56 then 0 else (if n < 60 then (if n < 58 then (if n < 57 then (-1) else 0) else (if n < 59 then (-1) else 0)) else (if n < 62 then (if n < 61 then 0 else 1) else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq140 (n : Nat) :
    nestingProjection140.numerator[n]! = nestingEntries140 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries140, if_neg (by omega : ¬ n < 64)]

def nestingProjection141 : Projection := ⟨4,2,#[1,1,0,0,1,1,0,0,1,2,0,1,0,1,1,0,0,0,0,0,0,0,0,0,0,1,0,1,-1,0,1,0,1,0,0,-1,2,1,-1,0,1,1,0,0,1,1,0,0,0,1,0,1,-1,0,1,0,0,0,0,0,0,0,0,0]⟩
theorem nestingLookup141 : projections[141]! = nestingProjection141 := by
  rw [projections_lookup]
  rfl
def nestingEntries141 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then 1 else 0) else (if n < 6 then 1 else 0)) else (if n < 12 then (if n < 10 then (if n < 9 then 1 else 2) else (if n < 11 then 0 else 1)) else (if n < 14 then (if n < 13 then 0 else 1) else (if n < 15 then 1 else 0)))) else (if n < 24 then 0 else (if n < 28 then (if n < 26 then (if n < 25 then 0 else 1) else (if n < 27 then 0 else 1)) else (if n < 30 then (if n < 29 then (-1) else 0) else (if n < 31 then 1 else 0))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 1 else 0) else (if n < 35 then 0 else (-1))) else (if n < 38 then (if n < 37 then 2 else 1) else (if n < 39 then (-1) else 0))) else (if n < 44 then (if n < 42 then 1 else 0) else (if n < 46 then 1 else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else 1) else (if n < 51 then 0 else 1)) else (if n < 54 then (if n < 53 then (-1) else 0) else (if n < 55 then 1 else 0))) else 0))) else 0
theorem nestingEntries_eq141 (n : Nat) :
    nestingProjection141.numerator[n]! = nestingEntries141 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries141, if_neg (by omega : ¬ n < 64)]

def nestingProjection142 : Projection := ⟨4,2,#[1,1,0,0,1,1,0,0,1,1,0,0,1,1,0,0,0,0,1,1,0,0,-1,1,0,0,1,1,0,0,-1,1,1,1,0,0,1,1,0,0,1,1,0,0,1,1,0,0,0,0,-1,-1,0,0,1,-1,0,0,1,1,0,0,-1,1]⟩
theorem nestingLookup142 : projections[142]! = nestingProjection142 := by
  rw [projections_lookup]
  rfl
def nestingEntries142 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then 1 else 0) else (if n < 6 then 1 else 0)) else (if n < 12 then (if n < 10 then 1 else 0) else (if n < 14 then 1 else 0))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else 1) else (if n < 22 then 0 else (if n < 23 then (-1) else 1))) else (if n < 28 then (if n < 26 then 0 else 1) else (if n < 30 then 0 else (if n < 31 then (-1) else 1))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then 1 else 0) else (if n < 38 then 1 else 0)) else (if n < 44 then (if n < 42 then 1 else 0) else (if n < 46 then 1 else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then 0 else (-1)) else (if n < 54 then 0 else (if n < 55 then 1 else (-1)))) else (if n < 60 then (if n < 58 then 0 else 1) else (if n < 62 then 0 else (if n < 63 then (-1) else 1)))))) else 0
theorem nestingEntries_eq142 (n : Nat) :
    nestingProjection142.numerator[n]! = nestingEntries142 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries142, if_neg (by omega : ¬ n < 64)]

def nestingProjection143 : Projection := ⟨4,2,#[1,0,1,0,0,-1,0,-1,0,1,0,1,-1,0,1,0,1,0,1,0,0,-1,0,-1,0,1,0,1,-1,0,1,0,0,-1,0,-1,1,0,-1,0,-1,0,-1,0,0,1,0,1,0,1,0,1,-1,0,1,0,-1,0,-1,0,0,1,0,1]⟩
theorem nestingLookup143 : projections[143]! = nestingProjection143 := by
  rw [projections_lookup]
  rfl
def nestingEntries143 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else (if n < 3 then 1 else 0)) else (if n < 6 then (if n < 5 then 0 else (-1)) else (if n < 7 then 0 else (-1)))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else (if n < 11 then 0 else 1)) else (if n < 14 then (if n < 13 then (-1) else 0) else (if n < 15 then 1 else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 1 else 0) else (if n < 19 then 1 else 0)) else (if n < 22 then (if n < 21 then 0 else (-1)) else (if n < 23 then 0 else (-1)))) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else 1) else (if n < 27 then 0 else 1)) else (if n < 30 then (if n < 29 then (-1) else 0) else (if n < 31 then 1 else 0))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 0 else (-1)) else (if n < 35 then 0 else (-1))) else (if n < 38 then (if n < 37 then 1 else 0) else (if n < 39 then (-1) else 0))) else (if n < 44 then (if n < 42 then (if n < 41 then (-1) else 0) else (if n < 43 then (-1) else 0)) else (if n < 46 then (if n < 45 then 0 else 1) else (if n < 47 then 0 else 1)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else 1) else (if n < 51 then 0 else 1)) else (if n < 54 then (if n < 53 then (-1) else 0) else (if n < 55 then 1 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then (-1) else 0) else (if n < 59 then (-1) else 0)) else (if n < 62 then (if n < 61 then 0 else 1) else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq143 (n : Nat) :
    nestingProjection143.numerator[n]! = nestingEntries143 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries143, if_neg (by omega : ¬ n < 64)]

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def nestingProjection144 : Projection := ⟨4,2,#[1,0,1,0,0,-1,0,-1,0,0,0,0,0,0,0,0,1,0,2,1,0,-1,-1,0,0,0,1,1,0,0,-1,1,0,0,0,0,0,0,0,0,-1,0,-1,0,0,1,0,1,0,0,-1,-1,0,0,1,-1,-1,0,0,1,0,1,-1,2]⟩
theorem nestingLookup144 : projections[144]! = nestingProjection144 := by
  rw [projections_lookup]
  rfl
def nestingEntries144 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else (if n < 3 then 1 else 0)) else (if n < 6 then (if n < 5 then 0 else (-1)) else (if n < 7 then 0 else (-1)))) else 0) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 1 else 0) else (if n < 19 then 2 else 1)) else (if n < 22 then (if n < 21 then 0 else (-1)) else (if n < 23 then (-1) else 0))) else (if n < 28 then (if n < 26 then 0 else 1) else (if n < 30 then 0 else (if n < 31 then (-1) else 1))))) else (if n < 48 then (if n < 40 then 0 else (if n < 44 then (if n < 42 then (if n < 41 then (-1) else 0) else (if n < 43 then (-1) else 0)) else (if n < 46 then (if n < 45 then 0 else 1) else (if n < 47 then 0 else 1)))) else (if n < 56 then (if n < 52 then (if n < 50 then 0 else (-1)) else (if n < 54 then 0 else (if n < 55 then 1 else (-1)))) else (if n < 60 then (if n < 58 then (if n < 57 then (-1) else 0) else (if n < 59 then 0 else 1)) else (if n < 62 then (if n < 61 then 0 else 1) else (if n < 63 then (-1) else 2)))))) else 0
theorem nestingEntries_eq144 (n : Nat) :
    nestingProjection144.numerator[n]! = nestingEntries144 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries144, if_neg (by omega : ¬ n < 64)]

def nestingProjection145 : Projection := ⟨4,2,#[0,0,0,0,0,0,0,0,0,1,0,1,-1,0,1,0,0,0,1,1,0,0,-1,1,0,1,1,2,-1,0,0,1,0,-1,0,-1,1,0,-1,0,0,0,0,0,0,0,0,0,0,1,-1,0,-1,0,2,-1,0,0,1,1,0,0,-1,1]⟩
theorem nestingLookup145 : projections[145]! = nestingProjection145 := by
  rw [projections_lookup]
  rfl
def nestingEntries145 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then 0 else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else (if n < 11 then 0 else 1)) else (if n < 14 then (if n < 13 then (-1) else 0) else (if n < 15 then 1 else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else 1) else (if n < 22 then 0 else (if n < 23 then (-1) else 1))) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else 1) else (if n < 27 then 1 else 2)) else (if n < 30 then (if n < 29 then (-1) else 0) else (if n < 31 then 0 else 1))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 0 else (-1)) else (if n < 35 then 0 else (-1))) else (if n < 38 then (if n < 37 then 1 else 0) else (if n < 39 then (-1) else 0))) else 0) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else 1) else (if n < 51 then (-1) else 0)) else (if n < 54 then (if n < 53 then (-1) else 0) else (if n < 55 then 2 else (-1)))) else (if n < 60 then (if n < 58 then 0 else 1) else (if n < 62 then 0 else (if n < 63 then (-1) else 1)))))) else 0
theorem nestingEntries_eq145 (n : Nat) :
    nestingProjection145.numerator[n]! = nestingEntries145 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries145, if_neg (by omega : ¬ n < 64)]

def nestingProjection146 : Projection := ⟨4,2,#[0,0,0,0,0,0,0,0,0,1,-1,0,0,1,1,0,0,-1,1,0,0,-1,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,1,1,-1,1,0,1,-1,0,1,2,0,1,0,1,-1,0,-1,0,2,-1,0,0,0,0,1,1,-1,1]⟩
theorem nestingLookup146 : projections[146]! = nestingProjection146 := by
  rw [projections_lookup]
  rfl
def nestingEntries146 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then 0 else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else (if n < 11 then (-1) else 0)) else (if n < 14 then (if n < 13 then 0 else 1) else (if n < 15 then 1 else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 0 else (-1)) else (if n < 19 then 1 else 0)) else (if n < 22 then (if n < 21 then 0 else (-1)) else (if n < 23 then (-1) else 0))) else 0)) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then 1 else (if n < 39 then (-1) else 1))) else (if n < 44 then (if n < 42 then (if n < 41 then 0 else 1) else (if n < 43 then (-1) else 0)) else (if n < 46 then (if n < 45 then 1 else 2) else (if n < 47 then 0 else 1)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else 1) else (if n < 51 then (-1) else 0)) else (if n < 54 then (if n < 53 then (-1) else 0) else (if n < 55 then 2 else (-1)))) else (if n < 60 then 0 else (if n < 62 then 1 else (if n < 63 then (-1) else 1)))))) else 0
theorem nestingEntries_eq146 (n : Nat) :
    nestingProjection146.numerator[n]! = nestingEntries146 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries146, if_neg (by omega : ¬ n < 64)]

def nestingProjection147 : Projection := ⟨4,2,#[1,1,1,1,0,0,0,0,1,2,0,1,0,1,1,0,1,0,2,1,0,-1,-1,0,1,1,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,1,-1,0,0,1,1,0,0,1,-1,0,0,1,1,0,0,0,0,0,0,0,0,0]⟩
theorem nestingLookup147 : projections[147]! = nestingProjection147 := by
  rw [projections_lookup]
  rfl
def nestingEntries147 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then 1 else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 1 else 2) else (if n < 11 then 0 else 1)) else (if n < 14 then (if n < 13 then 0 else 1) else (if n < 15 then 1 else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 1 else 0) else (if n < 19 then 2 else 1)) else (if n < 22 then (if n < 21 then 0 else (-1)) else (if n < 23 then (-1) else 0))) else (if n < 28 then 1 else 0))) else (if n < 48 then (if n < 40 then 0 else (if n < 44 then (if n < 42 then (if n < 41 then 0 else 1) else (if n < 43 then (-1) else 0)) else (if n < 46 then (if n < 45 then 0 else 1) else (if n < 47 then 1 else 0)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else 1) else (if n < 51 then (-1) else 0)) else (if n < 54 then (if n < 53 then 0 else 1) else (if n < 55 then 1 else 0))) else 0))) else 0
theorem nestingEntries_eq147 (n : Nat) :
    nestingProjection147.numerator[n]! = nestingEntries147 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries147, if_neg (by omega : ¬ n < 64)]

def nestingProjection148 : Projection := ⟨4,2,#[1,0,0,-1,1,0,0,-1,0,1,-1,0,0,1,1,0,0,-1,1,0,0,-1,-1,0,-1,0,0,1,-1,0,0,1,1,0,0,-1,1,0,0,-1,0,1,-1,0,0,1,1,0,0,1,-1,0,0,1,1,0,-1,0,0,1,-1,0,0,1]⟩
theorem nestingLookup148 : projections[148]! = nestingProjection148 := by
  rw [projections_lookup]
  rfl
def nestingEntries148 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else (if n < 3 then 0 else (-1))) else (if n < 6 then (if n < 5 then 1 else 0) else (if n < 7 then 0 else (-1)))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else (if n < 11 then (-1) else 0)) else (if n < 14 then (if n < 13 then 0 else 1) else (if n < 15 then 1 else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 0 else (-1)) else (if n < 19 then 1 else 0)) else (if n < 22 then (if n < 21 then 0 else (-1)) else (if n < 23 then (-1) else 0))) else (if n < 28 then (if n < 26 then (if n < 25 then (-1) else 0) else (if n < 27 then 0 else 1)) else (if n < 30 then (if n < 29 then (-1) else 0) else (if n < 31 then 0 else 1))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 1 else 0) else (if n < 35 then 0 else (-1))) else (if n < 38 then (if n < 37 then 1 else 0) else (if n < 39 then 0 else (-1)))) else (if n < 44 then (if n < 42 then (if n < 41 then 0 else 1) else (if n < 43 then (-1) else 0)) else (if n < 46 then (if n < 45 then 0 else 1) else (if n < 47 then 1 else 0)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else 1) else (if n < 51 then (-1) else 0)) else (if n < 54 then (if n < 53 then 0 else 1) else (if n < 55 then 1 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then (-1) else 0) else (if n < 59 then 0 else 1)) else (if n < 62 then (if n < 61 then (-1) else 0) else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq148 (n : Nat) :
    nestingProjection148.numerator[n]! = nestingEntries148 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries148, if_neg (by omega : ¬ n < 64)]

def nestingProjection149 : Projection := ⟨4,2,#[1,1,1,1,0,0,0,0,1,1,1,1,0,0,0,0,1,1,1,1,0,0,0,0,1,1,1,1,0,0,0,0,0,0,0,0,1,1,-1,1,0,0,0,0,1,1,-1,1,0,0,0,0,-1,-1,1,-1,0,0,0,0,1,1,-1,1]⟩
theorem nestingLookup149 : projections[149]! = nestingProjection149 := by
  rw [projections_lookup]
  rfl
def nestingEntries149 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then 1 else 0) else (if n < 12 then 1 else 0)) else (if n < 24 then (if n < 20 then 1 else 0) else (if n < 28 then 1 else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then 1 else (if n < 39 then (-1) else 1))) else (if n < 44 then 0 else (if n < 46 then 1 else (if n < 47 then (-1) else 1)))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then (-1) else (if n < 55 then 1 else (-1)))) else (if n < 60 then 0 else (if n < 62 then 1 else (if n < 63 then (-1) else 1)))))) else 0
theorem nestingEntries_eq149 (n : Nat) :
    nestingProjection149.numerator[n]! = nestingEntries149 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries149, if_neg (by omega : ¬ n < 64)]

def nestingProjection150 : Projection := ⟨4,2,#[1,0,0,-1,1,0,0,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,0,0,1,-1,0,0,1,1,0,0,-1,2,1,-1,0,0,0,0,0,1,1,-1,1,0,0,0,0,-1,-1,1,-1,-1,0,0,1,0,1,-1,2]⟩
theorem nestingLookup150 : projections[150]! = nestingProjection150 := by
  rw [projections_lookup]
  rfl
def nestingEntries150 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else (if n < 3 then 0 else (-1))) else (if n < 6 then (if n < 5 then 1 else 0) else (if n < 7 then 0 else (-1)))) else 0) else (if n < 24 then 0 else (if n < 28 then (if n < 26 then (if n < 25 then (-1) else 0) else (if n < 27 then 0 else 1)) else (if n < 30 then (if n < 29 then (-1) else 0) else (if n < 31 then 0 else 1))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 1 else 0) else (if n < 35 then 0 else (-1))) else (if n < 38 then (if n < 37 then 2 else 1) else (if n < 39 then (-1) else 0))) else (if n < 44 then 0 else (if n < 46 then 1 else (if n < 47 then (-1) else 1)))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then (-1) else (if n < 55 then 1 else (-1)))) else (if n < 60 then (if n < 58 then (if n < 57 then (-1) else 0) else (if n < 59 then 0 else 1)) else (if n < 62 then (if n < 61 then 0 else 1) else (if n < 63 then (-1) else 2)))))) else 0
theorem nestingEntries_eq150 (n : Nat) :
    nestingProjection150.numerator[n]! = nestingEntries150 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries150, if_neg (by omega : ¬ n < 64)]

def nestingProjection151 : Projection := ⟨4,2,#[2,1,1,0,1,0,0,-1,1,1,1,1,0,0,0,0,1,1,1,1,0,0,0,0,0,1,1,2,-1,0,0,1,1,0,0,-1,1,0,0,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,0,0,1,-1,0,0,1]⟩
theorem nestingLookup151 : projections[151]! = nestingProjection151 := by
  rw [projections_lookup]
  rfl
def nestingEntries151 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 2 else 1) else (if n < 3 then 1 else 0)) else (if n < 6 then (if n < 5 then 1 else 0) else (if n < 7 then 0 else (-1)))) else (if n < 12 then 1 else 0)) else (if n < 24 then (if n < 20 then 1 else 0) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else 1) else (if n < 27 then 1 else 2)) else (if n < 30 then (if n < 29 then (-1) else 0) else (if n < 31 then 0 else 1))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 1 else 0) else (if n < 35 then 0 else (-1))) else (if n < 38 then (if n < 37 then 1 else 0) else (if n < 39 then 0 else (-1)))) else 0) else (if n < 56 then 0 else (if n < 60 then (if n < 58 then (if n < 57 then (-1) else 0) else (if n < 59 then 0 else 1)) else (if n < 62 then (if n < 61 then (-1) else 0) else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq151 (n : Nat) :
    nestingProjection151.numerator[n]! = nestingEntries151 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries151, if_neg (by omega : ¬ n < 64)]

def nestingProjection152 : Projection := ⟨4,2,#[2,-1,-1,0,1,0,0,-1,-1,1,0,0,0,0,-1,1,-1,0,1,0,-1,0,1,0,0,0,0,0,0,0,0,0,1,0,-1,0,1,0,-1,0,0,0,0,0,0,0,0,0,0,-1,1,0,-1,0,2,-1,-1,1,0,0,0,0,-1,1]⟩
theorem nestingLookup152 : projections[152]! = nestingProjection152 := by
  rw [projections_lookup]
  rfl
def nestingEntries152 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 2 else (-1)) else (if n < 3 then (-1) else 0)) else (if n < 6 then (if n < 5 then 1 else 0) else (if n < 7 then 0 else (-1)))) else (if n < 12 then (if n < 10 then (if n < 9 then (-1) else 1) else 0) else (if n < 14 then 0 else (if n < 15 then (-1) else 1)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then (-1) else 0) else (if n < 19 then 1 else 0)) else (if n < 22 then (if n < 21 then (-1) else 0) else (if n < 23 then 1 else 0))) else 0)) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 1 else 0) else (if n < 35 then (-1) else 0)) else (if n < 38 then (if n < 37 then 1 else 0) else (if n < 39 then (-1) else 0))) else 0) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else (-1)) else (if n < 51 then 1 else 0)) else (if n < 54 then (if n < 53 then (-1) else 0) else (if n < 55 then 2 else (-1)))) else (if n < 60 then (if n < 58 then (if n < 57 then (-1) else 1) else 0) else (if n < 62 then 0 else (if n < 63 then (-1) else 1)))))) else 0
theorem nestingEntries_eq152 (n : Nat) :
    nestingProjection152.numerator[n]! = nestingEntries152 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries152, if_neg (by omega : ¬ n < 64)]

def nestingProjection153 : Projection := ⟨4,2,#[1,0,-1,0,1,0,-1,0,0,0,0,0,0,0,0,0,-1,0,2,1,0,-1,1,0,0,0,1,1,1,-1,0,0,1,0,0,1,2,-1,-1,0,0,0,-1,-1,-1,1,0,0,-1,0,1,0,-1,0,1,0,0,0,0,0,0,0,0,0]⟩
theorem nestingLookup153 : projections[153]! = nestingProjection153 := by
  rw [projections_lookup]
  rfl
def nestingEntries153 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else (if n < 3 then (-1) else 0)) else (if n < 6 then (if n < 5 then 1 else 0) else (if n < 7 then (-1) else 0))) else 0) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then (-1) else 0) else (if n < 19 then 2 else 1)) else (if n < 22 then (if n < 21 then 0 else (-1)) else (if n < 23 then 1 else 0))) else (if n < 28 then (if n < 26 then 0 else 1) else (if n < 30 then (if n < 29 then 1 else (-1)) else 0)))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 1 else 0) else (if n < 35 then 0 else 1)) else (if n < 38 then (if n < 37 then 2 else (-1)) else (if n < 39 then (-1) else 0))) else (if n < 44 then (if n < 42 then 0 else (-1)) else (if n < 46 then (if n < 45 then (-1) else 1) else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then (-1) else 0) else (if n < 51 then 1 else 0)) else (if n < 54 then (if n < 53 then (-1) else 0) else (if n < 55 then 1 else 0))) else 0))) else 0
theorem nestingEntries_eq153 (n : Nat) :
    nestingProjection153.numerator[n]! = nestingEntries153 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries153, if_neg (by omega : ¬ n < 64)]

def nestingProjection154 : Projection := ⟨4,2,#[1,0,-1,0,1,0,-1,0,0,1,0,1,0,1,0,-1,-1,0,1,0,-1,0,1,0,0,1,0,1,0,1,0,-1,1,0,-1,0,1,0,-1,0,0,1,0,1,0,1,0,-1,-1,0,1,0,-1,0,1,0,0,-1,0,-1,0,-1,0,1]⟩
theorem nestingLookup154 : projections[154]! = nestingProjection154 := by
  rw [projections_lookup]
  rfl
def nestingEntries154 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else (if n < 3 then (-1) else 0)) else (if n < 6 then (if n < 5 then 1 else 0) else (if n < 7 then (-1) else 0))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else (if n < 11 then 0 else 1)) else (if n < 14 then (if n < 13 then 0 else 1) else (if n < 15 then 0 else (-1))))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then (-1) else 0) else (if n < 19 then 1 else 0)) else (if n < 22 then (if n < 21 then (-1) else 0) else (if n < 23 then 1 else 0))) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else 1) else (if n < 27 then 0 else 1)) else (if n < 30 then (if n < 29 then 0 else 1) else (if n < 31 then 0 else (-1)))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 1 else 0) else (if n < 35 then (-1) else 0)) else (if n < 38 then (if n < 37 then 1 else 0) else (if n < 39 then (-1) else 0))) else (if n < 44 then (if n < 42 then (if n < 41 then 0 else 1) else (if n < 43 then 0 else 1)) else (if n < 46 then (if n < 45 then 0 else 1) else (if n < 47 then 0 else (-1))))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then (-1) else 0) else (if n < 51 then 1 else 0)) else (if n < 54 then (if n < 53 then (-1) else 0) else (if n < 55 then 1 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then 0 else (-1)) else (if n < 59 then 0 else (-1))) else (if n < 62 then (if n < 61 then 0 else (-1)) else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq154 (n : Nat) :
    nestingProjection154.numerator[n]! = nestingEntries154 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries154, if_neg (by omega : ¬ n < 64)]

def nestingProjection155 : Projection := ⟨4,2,#[1,-1,0,0,0,0,1,-1,-1,1,0,0,0,0,-1,1,0,0,1,1,1,-1,0,0,0,0,1,1,1,-1,0,0,0,0,1,1,1,-1,0,0,0,0,-1,-1,-1,1,0,0,1,-1,0,0,0,0,1,-1,-1,1,0,0,0,0,-1,1]⟩
theorem nestingLookup155 : projections[155]! = nestingProjection155 := by
  rw [projections_lookup]
  rfl
def nestingEntries155 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else (-1)) else 0) else (if n < 6 then 0 else (if n < 7 then 1 else (-1)))) else (if n < 12 then (if n < 10 then (if n < 9 then (-1) else 1) else 0) else (if n < 14 then 0 else (if n < 15 then (-1) else 1)))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else 1) else (if n < 22 then (if n < 21 then 1 else (-1)) else 0)) else (if n < 28 then (if n < 26 then 0 else 1) else (if n < 30 then (if n < 29 then 1 else (-1)) else 0)))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then 0 else 1) else (if n < 38 then (if n < 37 then 1 else (-1)) else 0)) else (if n < 44 then (if n < 42 then 0 else (-1)) else (if n < 46 then (if n < 45 then (-1) else 1) else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 1 else (-1)) else 0) else (if n < 54 then 0 else (if n < 55 then 1 else (-1)))) else (if n < 60 then (if n < 58 then (if n < 57 then (-1) else 1) else 0) else (if n < 62 then 0 else (if n < 63 then (-1) else 1)))))) else 0
theorem nestingEntries_eq155 (n : Nat) :
    nestingProjection155.numerator[n]! = nestingEntries155 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries155, if_neg (by omega : ¬ n < 64)]

def nestingProjection156 : Projection := ⟨4,2,#[1,-1,0,0,0,0,1,-1,-1,2,0,1,0,1,-1,0,0,0,0,0,0,0,0,0,0,1,0,1,0,1,0,-1,0,0,0,0,0,0,0,0,0,1,0,1,0,1,0,-1,1,-1,0,0,0,0,1,-1,-1,0,0,-1,0,-1,-1,2]⟩
theorem nestingLookup156 : projections[156]! = nestingProjection156 := by
  rw [projections_lookup]
  rfl
def nestingEntries156 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else (-1)) else 0) else (if n < 6 then 0 else (if n < 7 then 1 else (-1)))) else (if n < 12 then (if n < 10 then (if n < 9 then (-1) else 2) else (if n < 11 then 0 else 1)) else (if n < 14 then (if n < 13 then 0 else 1) else (if n < 15 then (-1) else 0)))) else (if n < 24 then 0 else (if n < 28 then (if n < 26 then (if n < 25 then 0 else 1) else (if n < 27 then 0 else 1)) else (if n < 30 then (if n < 29 then 0 else 1) else (if n < 31 then 0 else (-1)))))) else (if n < 48 then (if n < 40 then 0 else (if n < 44 then (if n < 42 then (if n < 41 then 0 else 1) else (if n < 43 then 0 else 1)) else (if n < 46 then (if n < 45 then 0 else 1) else (if n < 47 then 0 else (-1))))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 1 else (-1)) else 0) else (if n < 54 then 0 else (if n < 55 then 1 else (-1)))) else (if n < 60 then (if n < 58 then (if n < 57 then (-1) else 0) else (if n < 59 then 0 else (-1))) else (if n < 62 then (if n < 61 then 0 else (-1)) else (if n < 63 then (-1) else 2)))))) else 0
theorem nestingEntries_eq156 (n : Nat) :
    nestingProjection156.numerator[n]! = nestingEntries156 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries156, if_neg (by omega : ¬ n < 64)]

def nestingProjection157 : Projection := ⟨4,2,#[0,0,0,0,0,0,0,0,0,1,0,1,0,1,0,-1,0,0,1,1,1,-1,0,0,0,1,1,2,1,0,0,-1,0,0,1,1,1,-1,0,0,0,1,-1,0,-1,2,0,-1,0,0,0,0,0,0,0,0,0,-1,0,-1,0,-1,0,1]⟩
theorem nestingLookup157 : projections[157]! = nestingProjection157 := by
  rw [projections_lookup]
  rfl
def nestingEntries157 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then 0 else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else (if n < 11 then 0 else 1)) else (if n < 14 then (if n < 13 then 0 else 1) else (if n < 15 then 0 else (-1))))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else 1) else (if n < 22 then (if n < 21 then 1 else (-1)) else 0)) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else 1) else (if n < 27 then 1 else 2)) else (if n < 30 then (if n < 29 then 1 else 0) else (if n < 31 then 0 else (-1)))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then 0 else 1) else (if n < 38 then (if n < 37 then 1 else (-1)) else 0)) else (if n < 44 then (if n < 42 then (if n < 41 then 0 else 1) else (if n < 43 then (-1) else 0)) else (if n < 46 then (if n < 45 then (-1) else 2) else (if n < 47 then 0 else (-1))))) else (if n < 56 then 0 else (if n < 60 then (if n < 58 then (if n < 57 then 0 else (-1)) else (if n < 59 then 0 else (-1))) else (if n < 62 then (if n < 61 then 0 else (-1)) else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq157 (n : Nat) :
    nestingProjection157.numerator[n]! = nestingEntries157 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries157, if_neg (by omega : ¬ n < 64)]

def nestingProjection158 : Projection := ⟨4,2,#[2,-1,-1,0,1,0,0,-1,-1,1,0,0,-1,1,0,0,-1,0,1,0,0,-1,0,1,0,0,0,0,0,0,0,0,1,-1,0,0,1,-1,0,0,0,1,-1,0,-1,2,0,-1,0,0,0,0,0,0,0,0,-1,0,1,0,0,-1,0,1]⟩
theorem nestingLookup158 : projections[158]! = nestingProjection158 := by
  rw [projections_lookup]
  rfl
def nestingEntries158 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 2 else (-1)) else (if n < 3 then (-1) else 0)) else (if n < 6 then (if n < 5 then 1 else 0) else (if n < 7 then 0 else (-1)))) else (if n < 12 then (if n < 10 then (if n < 9 then (-1) else 1) else 0) else (if n < 14 then (if n < 13 then (-1) else 1) else 0))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then (-1) else 0) else (if n < 19 then 1 else 0)) else (if n < 22 then (if n < 21 then 0 else (-1)) else (if n < 23 then 0 else 1))) else 0)) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 1 else (-1)) else 0) else (if n < 38 then (if n < 37 then 1 else (-1)) else 0)) else (if n < 44 then (if n < 42 then (if n < 41 then 0 else 1) else (if n < 43 then (-1) else 0)) else (if n < 46 then (if n < 45 then (-1) else 2) else (if n < 47 then 0 else (-1))))) else (if n < 56 then 0 else (if n < 60 then (if n < 58 then (if n < 57 then (-1) else 0) else (if n < 59 then 1 else 0)) else (if n < 62 then (if n < 61 then 0 else (-1)) else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq158 (n : Nat) :
    nestingProjection158.numerator[n]! = nestingEntries158 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries158, if_neg (by omega : ¬ n < 64)]

def nestingProjection159 : Projection := ⟨4,2,#[1,-1,0,0,1,-1,0,0,-1,2,0,1,0,1,-1,0,0,0,0,0,0,0,0,0,0,1,0,1,1,0,-1,0,1,0,0,1,2,-1,-1,0,-1,1,0,0,-1,1,0,0,0,-1,0,-1,-1,0,1,0,0,0,0,0,0,0,0,0]⟩
theorem nestingLookup159 : projections[159]! = nestingProjection159 := by
  rw [projections_lookup]
  rfl
def nestingEntries159 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else (-1)) else 0) else (if n < 6 then (if n < 5 then 1 else (-1)) else 0)) else (if n < 12 then (if n < 10 then (if n < 9 then (-1) else 2) else (if n < 11 then 0 else 1)) else (if n < 14 then (if n < 13 then 0 else 1) else (if n < 15 then (-1) else 0)))) else (if n < 24 then 0 else (if n < 28 then (if n < 26 then (if n < 25 then 0 else 1) else (if n < 27 then 0 else 1)) else (if n < 30 then (if n < 29 then 1 else 0) else (if n < 31 then (-1) else 0))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 1 else 0) else (if n < 35 then 0 else 1)) else (if n < 38 then (if n < 37 then 2 else (-1)) else (if n < 39 then (-1) else 0))) else (if n < 44 then (if n < 42 then (if n < 41 then (-1) else 1) else 0) else (if n < 46 then (if n < 45 then (-1) else 1) else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else (-1)) else (if n < 51 then 0 else (-1))) else (if n < 54 then (if n < 53 then (-1) else 0) else (if n < 55 then 1 else 0))) else 0))) else 0
theorem nestingEntries_eq159 (n : Nat) :
    nestingProjection159.numerator[n]! = nestingEntries159 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries159, if_neg (by omega : ¬ n < 64)]

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def nestingProjection160 : Projection := ⟨4,2,#[1,0,-1,0,0,1,0,-1,0,1,0,1,1,0,-1,0,-1,0,1,0,0,-1,0,1,0,1,0,1,1,0,-1,0,0,1,0,1,1,0,-1,0,1,0,-1,0,0,1,0,-1,0,-1,0,-1,-1,0,1,0,-1,0,1,0,0,-1,0,1]⟩
theorem nestingLookup160 : projections[160]! = nestingProjection160 := by
  rw [projections_lookup]
  rfl
def nestingEntries160 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else (if n < 3 then (-1) else 0)) else (if n < 6 then (if n < 5 then 0 else 1) else (if n < 7 then 0 else (-1)))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else (if n < 11 then 0 else 1)) else (if n < 14 then (if n < 13 then 1 else 0) else (if n < 15 then (-1) else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then (-1) else 0) else (if n < 19 then 1 else 0)) else (if n < 22 then (if n < 21 then 0 else (-1)) else (if n < 23 then 0 else 1))) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else 1) else (if n < 27 then 0 else 1)) else (if n < 30 then (if n < 29 then 1 else 0) else (if n < 31 then (-1) else 0))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 0 else 1) else (if n < 35 then 0 else 1)) else (if n < 38 then (if n < 37 then 1 else 0) else (if n < 39 then (-1) else 0))) else (if n < 44 then (if n < 42 then (if n < 41 then 1 else 0) else (if n < 43 then (-1) else 0)) else (if n < 46 then (if n < 45 then 0 else 1) else (if n < 47 then 0 else (-1))))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else (-1)) else (if n < 51 then 0 else (-1))) else (if n < 54 then (if n < 53 then (-1) else 0) else (if n < 55 then 1 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then (-1) else 0) else (if n < 59 then 1 else 0)) else (if n < 62 then (if n < 61 then 0 else (-1)) else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq160 (n : Nat) :
    nestingProjection160.numerator[n]! = nestingEntries160 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries160, if_neg (by omega : ¬ n < 64)]

def nestingProjection161 : Projection := ⟨4,2,#[1,-1,-1,-1,0,0,0,0,-1,1,1,1,0,0,0,0,-1,1,1,1,0,0,0,0,-1,1,1,1,0,0,0,0,0,0,0,0,1,-1,-1,1,0,0,0,0,-1,1,1,-1,0,0,0,0,-1,1,1,-1,0,0,0,0,1,-1,-1,1]⟩
theorem nestingLookup161 : projections[161]! = nestingProjection161 := by
  rw [projections_lookup]
  rfl
def nestingEntries161 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else (-1)) else (-1)) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then (-1) else 1) else 1) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then (-1) else 1) else 1) else 0) else (if n < 28 then (if n < 26 then (if n < 25 then (-1) else 1) else 1) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 1 else (-1)) else (if n < 39 then (-1) else 1))) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then (-1) else 1) else (if n < 47 then 1 else (-1))))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then (if n < 53 then (-1) else 1) else (if n < 55 then 1 else (-1)))) else (if n < 60 then 0 else (if n < 62 then (if n < 61 then 1 else (-1)) else (if n < 63 then (-1) else 1)))))) else 0
theorem nestingEntries_eq161 (n : Nat) :
    nestingProjection161.numerator[n]! = nestingEntries161 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries161, if_neg (by omega : ¬ n < 64)]

def nestingProjection162 : Projection := ⟨4,2,#[1,0,0,1,1,0,0,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,1,1,0,0,-1,1,0,0,1,2,-1,-1,0,0,0,0,0,-1,1,1,-1,0,0,0,0,-1,1,1,-1,-1,0,0,-1,0,-1,-1,2]⟩
theorem nestingLookup162 : projections[162]! = nestingProjection162 := by
  rw [projections_lookup]
  rfl
def nestingEntries162 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else (if n < 3 then 0 else 1)) else (if n < 6 then (if n < 5 then 1 else 0) else (if n < 7 then 0 else (-1)))) else 0) else (if n < 24 then 0 else (if n < 28 then (if n < 26 then (if n < 25 then 1 else 0) else (if n < 27 then 0 else 1)) else (if n < 30 then (if n < 29 then 1 else 0) else (if n < 31 then 0 else (-1)))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 1 else 0) else (if n < 35 then 0 else 1)) else (if n < 38 then (if n < 37 then 2 else (-1)) else (if n < 39 then (-1) else 0))) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then (-1) else 1) else (if n < 47 then 1 else (-1))))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then (if n < 53 then (-1) else 1) else (if n < 55 then 1 else (-1)))) else (if n < 60 then (if n < 58 then (if n < 57 then (-1) else 0) else (if n < 59 then 0 else (-1))) else (if n < 62 then (if n < 61 then 0 else (-1)) else (if n < 63 then (-1) else 2)))))) else 0
theorem nestingEntries_eq162 (n : Nat) :
    nestingProjection162.numerator[n]! = nestingEntries162 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries162, if_neg (by omega : ¬ n < 64)]

def nestingProjection163 : Projection := ⟨4,2,#[2,-1,-1,0,1,0,0,-1,-1,1,1,1,0,0,0,0,-1,1,1,1,0,0,0,0,0,1,1,2,1,0,0,-1,1,0,0,1,1,0,0,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,0,0,-1,-1,0,0,1]⟩
theorem nestingLookup163 : projections[163]! = nestingProjection163 := by
  rw [projections_lookup]
  rfl
def nestingEntries163 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 2 else (-1)) else (if n < 3 then (-1) else 0)) else (if n < 6 then (if n < 5 then 1 else 0) else (if n < 7 then 0 else (-1)))) else (if n < 12 then (if n < 10 then (if n < 9 then (-1) else 1) else 1) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then (-1) else 1) else 1) else 0) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else 1) else (if n < 27 then 1 else 2)) else (if n < 30 then (if n < 29 then 1 else 0) else (if n < 31 then 0 else (-1)))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 1 else 0) else (if n < 35 then 0 else 1)) else (if n < 38 then (if n < 37 then 1 else 0) else (if n < 39 then 0 else (-1)))) else 0) else (if n < 56 then 0 else (if n < 60 then (if n < 58 then (if n < 57 then (-1) else 0) else (if n < 59 then 0 else (-1))) else (if n < 62 then (if n < 61 then (-1) else 0) else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq163 (n : Nat) :
    nestingProjection163.numerator[n]! = nestingEntries163 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries163, if_neg (by omega : ¬ n < 64)]

def nestingProjection164 : Projection := ⟨4,2,#[2,-1,-1,0,-1,0,0,1,-1,1,0,0,0,0,-1,-1,-1,0,1,0,1,0,1,0,0,0,0,0,0,0,0,0,-1,0,1,0,1,0,1,0,0,0,0,0,0,0,0,0,0,-1,1,0,1,0,2,1,1,-1,0,0,0,0,1,1]⟩
theorem nestingLookup164 : projections[164]! = nestingProjection164 := by
  rw [projections_lookup]
  rfl
def nestingEntries164 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 2 else (-1)) else (if n < 3 then (-1) else 0)) else (if n < 6 then (if n < 5 then (-1) else 0) else (if n < 7 then 0 else 1))) else (if n < 12 then (if n < 10 then (if n < 9 then (-1) else 1) else 0) else (if n < 14 then 0 else (-1)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then (-1) else 0) else (if n < 19 then 1 else 0)) else (if n < 22 then (if n < 21 then 1 else 0) else (if n < 23 then 1 else 0))) else 0)) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then (-1) else 0) else (if n < 35 then 1 else 0)) else (if n < 38 then (if n < 37 then 1 else 0) else (if n < 39 then 1 else 0))) else 0) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else (-1)) else (if n < 51 then 1 else 0)) else (if n < 54 then (if n < 53 then 1 else 0) else (if n < 55 then 2 else 1))) else (if n < 60 then (if n < 58 then (if n < 57 then 1 else (-1)) else 0) else (if n < 62 then 0 else 1))))) else 0
theorem nestingEntries_eq164 (n : Nat) :
    nestingProjection164.numerator[n]! = nestingEntries164 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries164, if_neg (by omega : ¬ n < 64)]

def nestingProjection165 : Projection := ⟨4,2,#[1,0,-1,0,-1,0,-1,0,0,0,0,0,0,0,0,0,-1,0,2,-1,0,1,1,0,0,0,-1,1,1,-1,0,0,-1,0,0,1,2,-1,1,0,0,0,1,-1,-1,1,0,0,-1,0,1,0,1,0,1,0,0,0,0,0,0,0,0,0]⟩
theorem nestingLookup165 : projections[165]! = nestingProjection165 := by
  rw [projections_lookup]
  rfl
def nestingEntries165 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else (if n < 3 then (-1) else 0)) else (if n < 6 then (if n < 5 then (-1) else 0) else (if n < 7 then (-1) else 0))) else 0) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then (-1) else 0) else (if n < 19 then 2 else (-1))) else (if n < 22 then (if n < 21 then 0 else 1) else (if n < 23 then 1 else 0))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then (-1) else 1)) else (if n < 30 then (if n < 29 then 1 else (-1)) else 0)))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then (-1) else 0) else (if n < 35 then 0 else 1)) else (if n < 38 then (if n < 37 then 2 else (-1)) else (if n < 39 then 1 else 0))) else (if n < 44 then (if n < 42 then 0 else (if n < 43 then 1 else (-1))) else (if n < 46 then (if n < 45 then (-1) else 1) else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then (-1) else 0) else (if n < 51 then 1 else 0)) else (if n < 54 then (if n < 53 then 1 else 0) else (if n < 55 then 1 else 0))) else 0))) else 0
theorem nestingEntries_eq165 (n : Nat) :
    nestingProjection165.numerator[n]! = nestingEntries165 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries165, if_neg (by omega : ¬ n < 64)]

def nestingProjection166 : Projection := ⟨4,2,#[1,0,-1,0,-1,0,-1,0,0,1,0,-1,0,-1,0,1,-1,0,1,0,1,0,1,0,0,-1,0,1,0,1,0,-1,-1,0,1,0,1,0,1,0,0,-1,0,1,0,1,0,-1,-1,0,1,0,1,0,1,0,0,1,0,-1,0,-1,0,1]⟩
theorem nestingLookup166 : projections[166]! = nestingProjection166 := by
  rw [projections_lookup]
  rfl
def nestingEntries166 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else (if n < 3 then (-1) else 0)) else (if n < 6 then (if n < 5 then (-1) else 0) else (if n < 7 then (-1) else 0))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else (if n < 11 then 0 else (-1))) else (if n < 14 then (if n < 13 then 0 else (-1)) else (if n < 15 then 0 else 1)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then (-1) else 0) else (if n < 19 then 1 else 0)) else (if n < 22 then (if n < 21 then 1 else 0) else (if n < 23 then 1 else 0))) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else (-1)) else (if n < 27 then 0 else 1)) else (if n < 30 then (if n < 29 then 0 else 1) else (if n < 31 then 0 else (-1)))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then (-1) else 0) else (if n < 35 then 1 else 0)) else (if n < 38 then (if n < 37 then 1 else 0) else (if n < 39 then 1 else 0))) else (if n < 44 then (if n < 42 then (if n < 41 then 0 else (-1)) else (if n < 43 then 0 else 1)) else (if n < 46 then (if n < 45 then 0 else 1) else (if n < 47 then 0 else (-1))))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then (-1) else 0) else (if n < 51 then 1 else 0)) else (if n < 54 then (if n < 53 then 1 else 0) else (if n < 55 then 1 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then 0 else 1) else (if n < 59 then 0 else (-1))) else (if n < 62 then (if n < 61 then 0 else (-1)) else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq166 (n : Nat) :
    nestingProjection166.numerator[n]! = nestingEntries166 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries166, if_neg (by omega : ¬ n < 64)]

def nestingProjection167 : Projection := ⟨4,2,#[1,-1,0,0,0,0,1,1,-1,1,0,0,0,0,-1,-1,0,0,1,-1,-1,1,0,0,0,0,-1,1,1,-1,0,0,0,0,-1,1,1,-1,0,0,0,0,1,-1,-1,1,0,0,1,-1,0,0,0,0,1,1,1,-1,0,0,0,0,1,1]⟩
theorem nestingLookup167 : projections[167]! = nestingProjection167 := by
  rw [projections_lookup]
  rfl
def nestingEntries167 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else (-1)) else 0) else (if n < 6 then 0 else 1)) else (if n < 12 then (if n < 10 then (if n < 9 then (-1) else 1) else 0) else (if n < 14 then 0 else (-1)))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 1 else (-1))) else (if n < 22 then (if n < 21 then (-1) else 1) else 0)) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then (-1) else 1)) else (if n < 30 then (if n < 29 then 1 else (-1)) else 0)))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then 0 else (if n < 35 then (-1) else 1)) else (if n < 38 then (if n < 37 then 1 else (-1)) else 0)) else (if n < 44 then (if n < 42 then 0 else (if n < 43 then 1 else (-1))) else (if n < 46 then (if n < 45 then (-1) else 1) else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 1 else (-1)) else 0) else (if n < 54 then 0 else 1)) else (if n < 60 then (if n < 58 then (if n < 57 then 1 else (-1)) else 0) else (if n < 62 then 0 else 1))))) else 0
theorem nestingEntries_eq167 (n : Nat) :
    nestingProjection167.numerator[n]! = nestingEntries167 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries167, if_neg (by omega : ¬ n < 64)]

def nestingProjection168 : Projection := ⟨4,2,#[1,-1,0,0,0,0,1,1,-1,2,0,-1,0,-1,-1,0,0,0,0,0,0,0,0,0,0,-1,0,1,0,1,0,-1,0,0,0,0,0,0,0,0,0,-1,0,1,0,1,0,-1,1,-1,0,0,0,0,1,1,1,0,0,-1,0,-1,1,2]⟩
theorem nestingLookup168 : projections[168]! = nestingProjection168 := by
  rw [projections_lookup]
  rfl
def nestingEntries168 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else (-1)) else 0) else (if n < 6 then 0 else 1)) else (if n < 12 then (if n < 10 then (if n < 9 then (-1) else 2) else (if n < 11 then 0 else (-1))) else (if n < 14 then (if n < 13 then 0 else (-1)) else (if n < 15 then (-1) else 0)))) else (if n < 24 then 0 else (if n < 28 then (if n < 26 then (if n < 25 then 0 else (-1)) else (if n < 27 then 0 else 1)) else (if n < 30 then (if n < 29 then 0 else 1) else (if n < 31 then 0 else (-1)))))) else (if n < 48 then (if n < 40 then 0 else (if n < 44 then (if n < 42 then (if n < 41 then 0 else (-1)) else (if n < 43 then 0 else 1)) else (if n < 46 then (if n < 45 then 0 else 1) else (if n < 47 then 0 else (-1))))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 1 else (-1)) else 0) else (if n < 54 then 0 else 1)) else (if n < 60 then (if n < 58 then (if n < 57 then 1 else 0) else (if n < 59 then 0 else (-1))) else (if n < 62 then (if n < 61 then 0 else (-1)) else (if n < 63 then 1 else 2)))))) else 0
theorem nestingEntries_eq168 (n : Nat) :
    nestingProjection168.numerator[n]! = nestingEntries168 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries168, if_neg (by omega : ¬ n < 64)]

def nestingProjection169 : Projection := ⟨4,2,#[0,0,0,0,0,0,0,0,0,1,0,-1,0,-1,0,1,0,0,1,-1,-1,1,0,0,0,-1,-1,2,1,0,0,-1,0,0,-1,1,1,-1,0,0,0,-1,1,0,-1,2,0,-1,0,0,0,0,0,0,0,0,0,1,0,-1,0,-1,0,1]⟩
theorem nestingLookup169 : projections[169]! = nestingProjection169 := by
  rw [projections_lookup]
  rfl
def nestingEntries169 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then 0 else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else (if n < 11 then 0 else (-1))) else (if n < 14 then (if n < 13 then 0 else (-1)) else (if n < 15 then 0 else 1)))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 1 else (-1))) else (if n < 22 then (if n < 21 then (-1) else 1) else 0)) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else (-1)) else (if n < 27 then (-1) else 2)) else (if n < 30 then (if n < 29 then 1 else 0) else (if n < 31 then 0 else (-1)))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then 0 else (if n < 35 then (-1) else 1)) else (if n < 38 then (if n < 37 then 1 else (-1)) else 0)) else (if n < 44 then (if n < 42 then (if n < 41 then 0 else (-1)) else (if n < 43 then 1 else 0)) else (if n < 46 then (if n < 45 then (-1) else 2) else (if n < 47 then 0 else (-1))))) else (if n < 56 then 0 else (if n < 60 then (if n < 58 then (if n < 57 then 0 else 1) else (if n < 59 then 0 else (-1))) else (if n < 62 then (if n < 61 then 0 else (-1)) else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq169 (n : Nat) :
    nestingProjection169.numerator[n]! = nestingEntries169 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries169, if_neg (by omega : ¬ n < 64)]

def nestingProjection170 : Projection := ⟨4,2,#[2,-1,-1,0,-1,0,0,1,-1,1,0,0,1,-1,0,0,-1,0,1,0,0,1,0,-1,0,0,0,0,0,0,0,0,-1,1,0,0,1,-1,0,0,0,-1,1,0,-1,2,0,-1,0,0,0,0,0,0,0,0,1,0,-1,0,0,-1,0,1]⟩
theorem nestingLookup170 : projections[170]! = nestingProjection170 := by
  rw [projections_lookup]
  rfl
def nestingEntries170 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 2 else (-1)) else (if n < 3 then (-1) else 0)) else (if n < 6 then (if n < 5 then (-1) else 0) else (if n < 7 then 0 else 1))) else (if n < 12 then (if n < 10 then (if n < 9 then (-1) else 1) else 0) else (if n < 14 then (if n < 13 then 1 else (-1)) else 0))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then (-1) else 0) else (if n < 19 then 1 else 0)) else (if n < 22 then (if n < 21 then 0 else 1) else (if n < 23 then 0 else (-1)))) else 0)) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then (-1) else 1) else 0) else (if n < 38 then (if n < 37 then 1 else (-1)) else 0)) else (if n < 44 then (if n < 42 then (if n < 41 then 0 else (-1)) else (if n < 43 then 1 else 0)) else (if n < 46 then (if n < 45 then (-1) else 2) else (if n < 47 then 0 else (-1))))) else (if n < 56 then 0 else (if n < 60 then (if n < 58 then (if n < 57 then 1 else 0) else (if n < 59 then (-1) else 0)) else (if n < 62 then (if n < 61 then 0 else (-1)) else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq170 (n : Nat) :
    nestingProjection170.numerator[n]! = nestingEntries170 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries170, if_neg (by omega : ¬ n < 64)]

def nestingProjection171 : Projection := ⟨4,2,#[1,-1,0,0,-1,1,0,0,-1,2,0,-1,0,-1,-1,0,0,0,0,0,0,0,0,0,0,-1,0,1,1,0,1,0,-1,0,0,1,2,-1,1,0,1,-1,0,0,-1,1,0,0,0,-1,0,1,1,0,1,0,0,0,0,0,0,0,0,0]⟩
theorem nestingLookup171 : projections[171]! = nestingProjection171 := by
  rw [projections_lookup]
  rfl
def nestingEntries171 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else (-1)) else 0) else (if n < 6 then (if n < 5 then (-1) else 1) else 0)) else (if n < 12 then (if n < 10 then (if n < 9 then (-1) else 2) else (if n < 11 then 0 else (-1))) else (if n < 14 then (if n < 13 then 0 else (-1)) else (if n < 15 then (-1) else 0)))) else (if n < 24 then 0 else (if n < 28 then (if n < 26 then (if n < 25 then 0 else (-1)) else (if n < 27 then 0 else 1)) else (if n < 30 then (if n < 29 then 1 else 0) else (if n < 31 then 1 else 0))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then (-1) else 0) else (if n < 35 then 0 else 1)) else (if n < 38 then (if n < 37 then 2 else (-1)) else (if n < 39 then 1 else 0))) else (if n < 44 then (if n < 42 then (if n < 41 then 1 else (-1)) else 0) else (if n < 46 then (if n < 45 then (-1) else 1) else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else (-1)) else (if n < 51 then 0 else 1)) else (if n < 54 then (if n < 53 then 1 else 0) else (if n < 55 then 1 else 0))) else 0))) else 0
theorem nestingEntries_eq171 (n : Nat) :
    nestingProjection171.numerator[n]! = nestingEntries171 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries171, if_neg (by omega : ¬ n < 64)]

def nestingProjection172 : Projection := ⟨4,2,#[1,-1,0,0,-1,1,0,0,-1,1,0,0,1,-1,0,0,0,0,1,-1,0,0,1,1,0,0,-1,1,0,0,-1,-1,-1,1,0,0,1,-1,0,0,1,-1,0,0,-1,1,0,0,0,0,1,-1,0,0,1,1,0,0,1,-1,0,0,1,1]⟩
theorem nestingLookup172 : projections[172]! = nestingProjection172 := by
  rw [projections_lookup]
  rfl
def nestingEntries172 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else (-1)) else 0) else (if n < 6 then (if n < 5 then (-1) else 1) else 0)) else (if n < 12 then (if n < 10 then (if n < 9 then (-1) else 1) else 0) else (if n < 14 then (if n < 13 then 1 else (-1)) else 0))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 1 else (-1))) else (if n < 22 then 0 else 1)) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then (-1) else 1)) else (if n < 30 then 0 else (-1))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then (-1) else 1) else 0) else (if n < 38 then (if n < 37 then 1 else (-1)) else 0)) else (if n < 44 then (if n < 42 then (if n < 41 then 1 else (-1)) else 0) else (if n < 46 then (if n < 45 then (-1) else 1) else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then 0 else (if n < 51 then 1 else (-1))) else (if n < 54 then 0 else 1)) else (if n < 60 then (if n < 58 then 0 else (if n < 59 then 1 else (-1))) else (if n < 62 then 0 else 1))))) else 0
theorem nestingEntries_eq172 (n : Nat) :
    nestingProjection172.numerator[n]! = nestingEntries172 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries172, if_neg (by omega : ¬ n < 64)]

def nestingProjection173 : Projection := ⟨4,2,#[1,0,-1,0,0,-1,0,1,0,1,0,-1,-1,0,-1,0,-1,0,1,0,0,1,0,-1,0,-1,0,1,1,0,1,0,0,-1,0,1,1,0,1,0,-1,0,1,0,0,1,0,-1,0,-1,0,1,1,0,1,0,1,0,-1,0,0,-1,0,1]⟩
theorem nestingLookup173 : projections[173]! = nestingProjection173 := by
  rw [projections_lookup]
  rfl
def nestingEntries173 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else (if n < 3 then (-1) else 0)) else (if n < 6 then (if n < 5 then 0 else (-1)) else (if n < 7 then 0 else 1))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else (if n < 11 then 0 else (-1))) else (if n < 14 then (if n < 13 then (-1) else 0) else (if n < 15 then (-1) else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then (-1) else 0) else (if n < 19 then 1 else 0)) else (if n < 22 then (if n < 21 then 0 else 1) else (if n < 23 then 0 else (-1)))) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else (-1)) else (if n < 27 then 0 else 1)) else (if n < 30 then (if n < 29 then 1 else 0) else (if n < 31 then 1 else 0))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 0 else (-1)) else (if n < 35 then 0 else 1)) else (if n < 38 then (if n < 37 then 1 else 0) else (if n < 39 then 1 else 0))) else (if n < 44 then (if n < 42 then (if n < 41 then (-1) else 0) else (if n < 43 then 1 else 0)) else (if n < 46 then (if n < 45 then 0 else 1) else (if n < 47 then 0 else (-1))))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else (-1)) else (if n < 51 then 0 else 1)) else (if n < 54 then (if n < 53 then 1 else 0) else (if n < 55 then 1 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then 1 else 0) else (if n < 59 then (-1) else 0)) else (if n < 62 then (if n < 61 then 0 else (-1)) else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq173 (n : Nat) :
    nestingProjection173.numerator[n]! = nestingEntries173 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries173, if_neg (by omega : ¬ n < 64)]

def nestingProjection174 : Projection := ⟨4,2,#[1,0,-1,0,0,-1,0,1,0,0,0,0,0,0,0,0,-1,0,2,-1,0,1,1,0,0,0,-1,1,0,0,-1,-1,0,0,0,0,0,0,0,0,-1,0,1,0,0,1,0,-1,0,0,1,-1,0,0,1,1,1,0,0,-1,0,-1,1,2]⟩
theorem nestingLookup174 : projections[174]! = nestingProjection174 := by
  rw [projections_lookup]
  rfl
def nestingEntries174 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else (if n < 3 then (-1) else 0)) else (if n < 6 then (if n < 5 then 0 else (-1)) else (if n < 7 then 0 else 1))) else 0) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then (-1) else 0) else (if n < 19 then 2 else (-1))) else (if n < 22 then (if n < 21 then 0 else 1) else (if n < 23 then 1 else 0))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then (-1) else 1)) else (if n < 30 then 0 else (-1))))) else (if n < 48 then (if n < 40 then 0 else (if n < 44 then (if n < 42 then (if n < 41 then (-1) else 0) else (if n < 43 then 1 else 0)) else (if n < 46 then (if n < 45 then 0 else 1) else (if n < 47 then 0 else (-1))))) else (if n < 56 then (if n < 52 then (if n < 50 then 0 else (if n < 51 then 1 else (-1))) else (if n < 54 then 0 else 1)) else (if n < 60 then (if n < 58 then (if n < 57 then 1 else 0) else (if n < 59 then 0 else (-1))) else (if n < 62 then (if n < 61 then 0 else (-1)) else (if n < 63 then 1 else 2)))))) else 0
theorem nestingEntries_eq174 (n : Nat) :
    nestingProjection174.numerator[n]! = nestingEntries174 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries174, if_neg (by omega : ¬ n < 64)]

def nestingProjection175 : Projection := ⟨4,2,#[0,0,0,0,0,0,0,0,0,1,0,-1,-1,0,-1,0,0,0,1,-1,0,0,1,1,0,-1,-1,2,1,0,0,-1,0,-1,0,1,1,0,1,0,0,0,0,0,0,0,0,0,0,-1,1,0,1,0,2,1,0,0,1,-1,0,0,1,1]⟩
theorem nestingLookup175 : projections[175]! = nestingProjection175 := by
  rw [projections_lookup]
  rfl
def nestingEntries175 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then 0 else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else (if n < 11 then 0 else (-1))) else (if n < 14 then (if n < 13 then (-1) else 0) else (if n < 15 then (-1) else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 1 else (-1))) else (if n < 22 then 0 else 1)) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else (-1)) else (if n < 27 then (-1) else 2)) else (if n < 30 then (if n < 29 then 1 else 0) else (if n < 31 then 0 else (-1)))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 0 else (-1)) else (if n < 35 then 0 else 1)) else (if n < 38 then (if n < 37 then 1 else 0) else (if n < 39 then 1 else 0))) else 0) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else (-1)) else (if n < 51 then 1 else 0)) else (if n < 54 then (if n < 53 then 1 else 0) else (if n < 55 then 2 else 1))) else (if n < 60 then (if n < 58 then 0 else (if n < 59 then 1 else (-1))) else (if n < 62 then 0 else 1))))) else 0
theorem nestingEntries_eq175 (n : Nat) :
    nestingProjection175.numerator[n]! = nestingEntries175 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries175, if_neg (by omega : ¬ n < 64)]

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def nestingProjection176 : Projection := ⟨4,2,#[0,0,0,0,0,0,0,0,0,1,-1,0,0,-1,-1,0,0,-1,1,0,0,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,1,-1,1,1,0,-1,1,0,-1,2,0,-1,0,-1,1,0,1,0,2,1,0,0,0,0,1,-1,1,1]⟩
theorem nestingLookup176 : projections[176]! = nestingProjection176 := by
  rw [projections_lookup]
  rfl
def nestingEntries176 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then 0 else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else (if n < 11 then (-1) else 0)) else (if n < 14 then (if n < 13 then 0 else (-1)) else (if n < 15 then (-1) else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 0 else (-1)) else (if n < 19 then 1 else 0)) else (if n < 22 then (if n < 21 then 0 else 1) else (if n < 23 then 1 else 0))) else 0)) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 1 else (-1)) else 1)) else (if n < 44 then (if n < 42 then (if n < 41 then 0 else (-1)) else (if n < 43 then 1 else 0)) else (if n < 46 then (if n < 45 then (-1) else 2) else (if n < 47 then 0 else (-1))))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else (-1)) else (if n < 51 then 1 else 0)) else (if n < 54 then (if n < 53 then 1 else 0) else (if n < 55 then 2 else 1))) else (if n < 60 then 0 else (if n < 62 then (if n < 61 then 1 else (-1)) else 1))))) else 0
theorem nestingEntries_eq176 (n : Nat) :
    nestingProjection176.numerator[n]! = nestingEntries176 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries176, if_neg (by omega : ¬ n < 64)]

def nestingProjection177 : Projection := ⟨4,2,#[1,-1,-1,1,0,0,0,0,-1,2,0,-1,0,-1,-1,0,-1,0,2,-1,0,1,1,0,1,-1,-1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,1,0,0,1,1,0,0,-1,1,0,0,1,1,0,0,0,0,0,0,0,0,0]⟩
theorem nestingLookup177 : projections[177]! = nestingProjection177 := by
  rw [projections_lookup]
  rfl
def nestingEntries177 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else (-1)) else (if n < 3 then (-1) else 1)) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then (-1) else 2) else (if n < 11 then 0 else (-1))) else (if n < 14 then (if n < 13 then 0 else (-1)) else (if n < 15 then (-1) else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then (-1) else 0) else (if n < 19 then 2 else (-1))) else (if n < 22 then (if n < 21 then 0 else 1) else (if n < 23 then 1 else 0))) else (if n < 28 then (if n < 26 then (if n < 25 then 1 else (-1)) else (if n < 27 then (-1) else 1)) else 0))) else (if n < 48 then (if n < 40 then 0 else (if n < 44 then (if n < 42 then (if n < 41 then 0 else (-1)) else (if n < 43 then 1 else 0)) else (if n < 46 then (if n < 45 then 0 else 1) else (if n < 47 then 1 else 0)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else (-1)) else (if n < 51 then 1 else 0)) else (if n < 54 then (if n < 53 then 0 else 1) else (if n < 55 then 1 else 0))) else 0))) else 0
theorem nestingEntries_eq177 (n : Nat) :
    nestingProjection177.numerator[n]! = nestingEntries177 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries177, if_neg (by omega : ¬ n < 64)]

def nestingProjection178 : Projection := ⟨4,2,#[1,0,0,-1,-1,0,0,1,0,1,-1,0,0,-1,-1,0,0,-1,1,0,0,1,1,0,-1,0,0,1,1,0,0,-1,-1,0,0,1,1,0,0,-1,0,-1,1,0,0,1,1,0,0,-1,1,0,0,1,1,0,1,0,0,-1,-1,0,0,1]⟩
theorem nestingLookup178 : projections[178]! = nestingProjection178 := by
  rw [projections_lookup]
  rfl
def nestingEntries178 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else (if n < 3 then 0 else (-1))) else (if n < 6 then (if n < 5 then (-1) else 0) else (if n < 7 then 0 else 1))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else (if n < 11 then (-1) else 0)) else (if n < 14 then (if n < 13 then 0 else (-1)) else (if n < 15 then (-1) else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 0 else (-1)) else (if n < 19 then 1 else 0)) else (if n < 22 then (if n < 21 then 0 else 1) else (if n < 23 then 1 else 0))) else (if n < 28 then (if n < 26 then (if n < 25 then (-1) else 0) else (if n < 27 then 0 else 1)) else (if n < 30 then (if n < 29 then 1 else 0) else (if n < 31 then 0 else (-1)))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then (-1) else 0) else (if n < 35 then 0 else 1)) else (if n < 38 then (if n < 37 then 1 else 0) else (if n < 39 then 0 else (-1)))) else (if n < 44 then (if n < 42 then (if n < 41 then 0 else (-1)) else (if n < 43 then 1 else 0)) else (if n < 46 then (if n < 45 then 0 else 1) else (if n < 47 then 1 else 0)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else (-1)) else (if n < 51 then 1 else 0)) else (if n < 54 then (if n < 53 then 0 else 1) else (if n < 55 then 1 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then 1 else 0) else (if n < 59 then 0 else (-1))) else (if n < 62 then (if n < 61 then (-1) else 0) else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq178 (n : Nat) :
    nestingProjection178.numerator[n]! = nestingEntries178 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries178, if_neg (by omega : ¬ n < 64)]

def nestingProjection179 : Projection := ⟨4,2,#[1,-1,-1,1,0,0,0,0,-1,1,1,-1,0,0,0,0,-1,1,1,-1,0,0,0,0,1,-1,-1,1,0,0,0,0,0,0,0,0,1,-1,1,1,0,0,0,0,-1,1,-1,-1,0,0,0,0,1,-1,1,1,0,0,0,0,1,-1,1,1]⟩
theorem nestingLookup179 : projections[179]! = nestingProjection179 := by
  rw [projections_lookup]
  rfl
def nestingEntries179 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else (-1)) else (if n < 3 then (-1) else 1)) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then (-1) else 1) else (if n < 11 then 1 else (-1))) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then (-1) else 1) else (if n < 19 then 1 else (-1))) else 0) else (if n < 28 then (if n < 26 then (if n < 25 then 1 else (-1)) else (if n < 27 then (-1) else 1)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 1 else (-1)) else 1)) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then (-1) else 1) else (-1)))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then (if n < 53 then 1 else (-1)) else 1)) else (if n < 60 then 0 else (if n < 62 then (if n < 61 then 1 else (-1)) else 1))))) else 0
theorem nestingEntries_eq179 (n : Nat) :
    nestingProjection179.numerator[n]! = nestingEntries179 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries179, if_neg (by omega : ¬ n < 64)]

def nestingProjection180 : Projection := ⟨4,2,#[1,0,0,-1,-1,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,0,0,1,1,0,0,-1,-1,0,0,1,2,-1,1,0,0,0,0,0,-1,1,-1,-1,0,0,0,0,1,-1,1,1,1,0,0,-1,0,-1,1,2]⟩
theorem nestingLookup180 : projections[180]! = nestingProjection180 := by
  rw [projections_lookup]
  rfl
def nestingEntries180 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else (if n < 3 then 0 else (-1))) else (if n < 6 then (if n < 5 then (-1) else 0) else (if n < 7 then 0 else 1))) else 0) else (if n < 24 then 0 else (if n < 28 then (if n < 26 then (if n < 25 then (-1) else 0) else (if n < 27 then 0 else 1)) else (if n < 30 then (if n < 29 then 1 else 0) else (if n < 31 then 0 else (-1)))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then (-1) else 0) else (if n < 35 then 0 else 1)) else (if n < 38 then (if n < 37 then 2 else (-1)) else (if n < 39 then 1 else 0))) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then (-1) else 1) else (-1)))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then (if n < 53 then 1 else (-1)) else 1)) else (if n < 60 then (if n < 58 then (if n < 57 then 1 else 0) else (if n < 59 then 0 else (-1))) else (if n < 62 then (if n < 61 then 0 else (-1)) else (if n < 63 then 1 else 2)))))) else 0
theorem nestingEntries_eq180 (n : Nat) :
    nestingProjection180.numerator[n]! = nestingEntries180 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries180, if_neg (by omega : ¬ n < 64)]

def nestingProjection181 : Projection := ⟨4,2,#[2,-1,-1,0,-1,0,0,1,-1,1,1,-1,0,0,0,0,-1,1,1,-1,0,0,0,0,0,-1,-1,2,1,0,0,-1,-1,0,0,1,1,0,0,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,-1,-1,0,0,1]⟩
theorem nestingLookup181 : projections[181]! = nestingProjection181 := by
  rw [projections_lookup]
  rfl
def nestingEntries181 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 2 else (-1)) else (if n < 3 then (-1) else 0)) else (if n < 6 then (if n < 5 then (-1) else 0) else (if n < 7 then 0 else 1))) else (if n < 12 then (if n < 10 then (if n < 9 then (-1) else 1) else (if n < 11 then 1 else (-1))) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then (-1) else 1) else (if n < 19 then 1 else (-1))) else 0) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else (-1)) else (if n < 27 then (-1) else 2)) else (if n < 30 then (if n < 29 then 1 else 0) else (if n < 31 then 0 else (-1)))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then (-1) else 0) else (if n < 35 then 0 else 1)) else (if n < 38 then (if n < 37 then 1 else 0) else (if n < 39 then 0 else (-1)))) else 0) else (if n < 56 then 0 else (if n < 60 then (if n < 58 then (if n < 57 then 1 else 0) else (if n < 59 then 0 else (-1))) else (if n < 62 then (if n < 61 then (-1) else 0) else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq181 (n : Nat) :
    nestingProjection181.numerator[n]! = nestingEntries181 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries181, if_neg (by omega : ¬ n < 64)]

def nestingProjection182 : Projection := ⟨4,2,#[2,1,1,0,-1,0,0,1,1,1,0,0,0,0,1,1,1,0,1,0,-1,0,-1,0,0,0,0,0,0,0,0,0,-1,0,-1,0,1,0,1,0,0,0,0,0,0,0,0,0,0,1,-1,0,1,0,2,1,1,1,0,0,0,0,1,1]⟩
theorem nestingLookup182 : projections[182]! = nestingProjection182 := by
  rw [projections_lookup]
  rfl
def nestingEntries182 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 2 else 1) else (if n < 3 then 1 else 0)) else (if n < 6 then (if n < 5 then (-1) else 0) else (if n < 7 then 0 else 1))) else (if n < 12 then (if n < 10 then 1 else 0) else (if n < 14 then 0 else 1))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 1 else 0) else (if n < 19 then 1 else 0)) else (if n < 22 then (if n < 21 then (-1) else 0) else (if n < 23 then (-1) else 0))) else 0)) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then (-1) else 0) else (if n < 35 then (-1) else 0)) else (if n < 38 then (if n < 37 then 1 else 0) else (if n < 39 then 1 else 0))) else 0) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else 1) else (if n < 51 then (-1) else 0)) else (if n < 54 then (if n < 53 then 1 else 0) else (if n < 55 then 2 else 1))) else (if n < 60 then (if n < 58 then 1 else 0) else (if n < 62 then 0 else 1))))) else 0
theorem nestingEntries_eq182 (n : Nat) :
    nestingProjection182.numerator[n]! = nestingEntries182 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries182, if_neg (by omega : ¬ n < 64)]

def nestingProjection183 : Projection := ⟨4,2,#[1,0,1,0,-1,0,-1,0,0,0,0,0,0,0,0,0,1,0,2,-1,0,1,-1,0,0,0,-1,1,-1,-1,0,0,-1,0,0,-1,2,1,1,0,0,0,1,-1,1,1,0,0,-1,0,-1,0,1,0,1,0,0,0,0,0,0,0,0,0]⟩
theorem nestingLookup183 : projections[183]! = nestingProjection183 := by
  rw [projections_lookup]
  rfl
def nestingEntries183 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else (if n < 3 then 1 else 0)) else (if n < 6 then (if n < 5 then (-1) else 0) else (if n < 7 then (-1) else 0))) else 0) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 1 else 0) else (if n < 19 then 2 else (-1))) else (if n < 22 then (if n < 21 then 0 else 1) else (if n < 23 then (-1) else 0))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then (-1) else 1)) else (if n < 30 then (-1) else 0)))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then (-1) else 0) else (if n < 35 then 0 else (-1))) else (if n < 38 then (if n < 37 then 2 else 1) else (if n < 39 then 1 else 0))) else (if n < 44 then (if n < 42 then 0 else (if n < 43 then 1 else (-1))) else (if n < 46 then 1 else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then (-1) else 0) else (if n < 51 then (-1) else 0)) else (if n < 54 then (if n < 53 then 1 else 0) else (if n < 55 then 1 else 0))) else 0))) else 0
theorem nestingEntries_eq183 (n : Nat) :
    nestingProjection183.numerator[n]! = nestingEntries183 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries183, if_neg (by omega : ¬ n < 64)]

def nestingProjection184 : Projection := ⟨4,2,#[1,1,0,0,0,0,1,1,1,1,0,0,0,0,1,1,0,0,1,-1,1,1,0,0,0,0,-1,1,-1,-1,0,0,0,0,1,-1,1,1,0,0,0,0,1,-1,1,1,0,0,1,1,0,0,0,0,1,1,1,1,0,0,0,0,1,1]⟩
theorem nestingLookup184 : projections[184]! = nestingProjection184 := by
  rw [projections_lookup]
  rfl
def nestingEntries184 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then 1 else 0) else (if n < 6 then 0 else 1)) else (if n < 12 then (if n < 10 then 1 else 0) else (if n < 14 then 0 else 1))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 1 else (-1))) else (if n < 22 then 1 else 0)) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then (-1) else 1)) else (if n < 30 then (-1) else 0)))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then 0 else (if n < 35 then 1 else (-1))) else (if n < 38 then 1 else 0)) else (if n < 44 then (if n < 42 then 0 else (if n < 43 then 1 else (-1))) else (if n < 46 then 1 else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then 1 else 0) else (if n < 54 then 0 else 1)) else (if n < 60 then (if n < 58 then 1 else 0) else (if n < 62 then 0 else 1))))) else 0
theorem nestingEntries_eq184 (n : Nat) :
    nestingProjection184.numerator[n]! = nestingEntries184 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries184, if_neg (by omega : ¬ n < 64)]

def nestingProjection185 : Projection := ⟨4,2,#[2,1,1,0,-1,0,0,1,1,1,0,0,-1,-1,0,0,1,0,1,0,0,1,0,1,0,0,0,0,0,0,0,0,-1,-1,0,0,1,1,0,0,0,-1,1,0,1,2,0,1,0,0,0,0,0,0,0,0,1,0,1,0,0,1,0,1]⟩
theorem nestingLookup185 : projections[185]! = nestingProjection185 := by
  rw [projections_lookup]
  rfl
def nestingEntries185 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 2 else 1) else (if n < 3 then 1 else 0)) else (if n < 6 then (if n < 5 then (-1) else 0) else (if n < 7 then 0 else 1))) else (if n < 12 then (if n < 10 then 1 else 0) else (if n < 14 then (-1) else 0))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 1 else 0) else (if n < 19 then 1 else 0)) else (if n < 22 then (if n < 21 then 0 else 1) else (if n < 23 then 0 else 1))) else 0)) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (-1) else 0) else (if n < 38 then 1 else 0)) else (if n < 44 then (if n < 42 then (if n < 41 then 0 else (-1)) else (if n < 43 then 1 else 0)) else (if n < 46 then (if n < 45 then 1 else 2) else (if n < 47 then 0 else 1)))) else (if n < 56 then 0 else (if n < 60 then (if n < 58 then (if n < 57 then 1 else 0) else (if n < 59 then 1 else 0)) else (if n < 62 then (if n < 61 then 0 else 1) else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq185 (n : Nat) :
    nestingProjection185.numerator[n]! = nestingEntries185 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries185, if_neg (by omega : ¬ n < 64)]

def nestingProjection186 : Projection := ⟨4,2,#[1,1,0,0,-1,-1,0,0,1,2,0,-1,0,-1,1,0,0,0,0,0,0,0,0,0,0,-1,0,1,-1,0,-1,0,-1,0,0,-1,2,1,1,0,-1,-1,0,0,1,1,0,0,0,1,0,-1,1,0,1,0,0,0,0,0,0,0,0,0]⟩
theorem nestingLookup186 : projections[186]! = nestingProjection186 := by
  rw [projections_lookup]
  rfl
def nestingEntries186 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then 1 else 0) else (if n < 6 then (-1) else 0)) else (if n < 12 then (if n < 10 then (if n < 9 then 1 else 2) else (if n < 11 then 0 else (-1))) else (if n < 14 then (if n < 13 then 0 else (-1)) else (if n < 15 then 1 else 0)))) else (if n < 24 then 0 else (if n < 28 then (if n < 26 then (if n < 25 then 0 else (-1)) else (if n < 27 then 0 else 1)) else (if n < 30 then (if n < 29 then (-1) else 0) else (if n < 31 then (-1) else 0))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then (-1) else 0) else (if n < 35 then 0 else (-1))) else (if n < 38 then (if n < 37 then 2 else 1) else (if n < 39 then 1 else 0))) else (if n < 44 then (if n < 42 then (-1) else 0) else (if n < 46 then 1 else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else 1) else (if n < 51 then 0 else (-1))) else (if n < 54 then (if n < 53 then 1 else 0) else (if n < 55 then 1 else 0))) else 0))) else 0
theorem nestingEntries_eq186 (n : Nat) :
    nestingProjection186.numerator[n]! = nestingEntries186 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries186, if_neg (by omega : ¬ n < 64)]

def nestingProjection187 : Projection := ⟨4,2,#[1,1,0,0,-1,-1,0,0,1,1,0,0,-1,-1,0,0,0,0,1,-1,0,0,-1,-1,0,0,-1,1,0,0,1,1,-1,-1,0,0,1,1,0,0,-1,-1,0,0,1,1,0,0,0,0,-1,1,0,0,1,1,0,0,-1,1,0,0,1,1]⟩
theorem nestingLookup187 : projections[187]! = nestingProjection187 := by
  rw [projections_lookup]
  rfl
def nestingEntries187 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then 1 else 0) else (if n < 6 then (-1) else 0)) else (if n < 12 then (if n < 10 then 1 else 0) else (if n < 14 then (-1) else 0))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 1 else (-1))) else (if n < 22 then 0 else (-1))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then (-1) else 1)) else (if n < 30 then 0 else 1)))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (-1) else 0) else (if n < 38 then 1 else 0)) else (if n < 44 then (if n < 42 then (-1) else 0) else (if n < 46 then 1 else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then 0 else (if n < 51 then (-1) else 1)) else (if n < 54 then 0 else 1)) else (if n < 60 then (if n < 58 then 0 else (if n < 59 then (-1) else 1)) else (if n < 62 then 0 else 1))))) else 0
theorem nestingEntries_eq187 (n : Nat) :
    nestingProjection187.numerator[n]! = nestingEntries187 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries187, if_neg (by omega : ¬ n < 64)]

def nestingProjection188 : Projection := ⟨4,2,#[1,0,1,0,0,1,0,1,0,1,0,-1,1,0,1,0,1,0,1,0,0,1,0,1,0,-1,0,1,-1,0,-1,0,0,1,0,-1,1,0,1,0,1,0,1,0,0,1,0,1,0,1,0,-1,1,0,1,0,1,0,1,0,0,1,0,1]⟩
theorem nestingLookup188 : projections[188]! = nestingProjection188 := by
  rw [projections_lookup]
  rfl
def nestingEntries188 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else (if n < 3 then 1 else 0)) else (if n < 6 then (if n < 5 then 0 else 1) else (if n < 7 then 0 else 1))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else (if n < 11 then 0 else (-1))) else (if n < 14 then (if n < 13 then 1 else 0) else (if n < 15 then 1 else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 1 else 0) else (if n < 19 then 1 else 0)) else (if n < 22 then (if n < 21 then 0 else 1) else (if n < 23 then 0 else 1))) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else (-1)) else (if n < 27 then 0 else 1)) else (if n < 30 then (if n < 29 then (-1) else 0) else (if n < 31 then (-1) else 0))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 0 else 1) else (if n < 35 then 0 else (-1))) else (if n < 38 then (if n < 37 then 1 else 0) else (if n < 39 then 1 else 0))) else (if n < 44 then (if n < 42 then (if n < 41 then 1 else 0) else (if n < 43 then 1 else 0)) else (if n < 46 then (if n < 45 then 0 else 1) else (if n < 47 then 0 else 1)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else 1) else (if n < 51 then 0 else (-1))) else (if n < 54 then (if n < 53 then 1 else 0) else (if n < 55 then 1 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then 1 else 0) else (if n < 59 then 1 else 0)) else (if n < 62 then (if n < 61 then 0 else 1) else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq188 (n : Nat) :
    nestingProjection188.numerator[n]! = nestingEntries188 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries188, if_neg (by omega : ¬ n < 64)]

def nestingProjection189 : Projection := ⟨4,2,#[1,0,1,0,0,1,0,1,0,0,0,0,0,0,0,0,1,0,2,-1,0,1,-1,0,0,0,-1,1,0,0,1,1,0,0,0,0,0,0,0,0,1,0,1,0,0,1,0,1,0,0,-1,1,0,0,1,1,1,0,0,1,0,1,1,2]⟩
theorem nestingLookup189 : projections[189]! = nestingProjection189 := by
  rw [projections_lookup]
  rfl
def nestingEntries189 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else (if n < 3 then 1 else 0)) else (if n < 6 then (if n < 5 then 0 else 1) else (if n < 7 then 0 else 1))) else 0) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 1 else 0) else (if n < 19 then 2 else (-1))) else (if n < 22 then (if n < 21 then 0 else 1) else (if n < 23 then (-1) else 0))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then (-1) else 1)) else (if n < 30 then 0 else 1)))) else (if n < 48 then (if n < 40 then 0 else (if n < 44 then (if n < 42 then (if n < 41 then 1 else 0) else (if n < 43 then 1 else 0)) else (if n < 46 then (if n < 45 then 0 else 1) else (if n < 47 then 0 else 1)))) else (if n < 56 then (if n < 52 then (if n < 50 then 0 else (if n < 51 then (-1) else 1)) else (if n < 54 then 0 else 1)) else (if n < 60 then (if n < 58 then (if n < 57 then 1 else 0) else (if n < 59 then 0 else 1)) else (if n < 62 then (if n < 61 then 0 else 1) else (if n < 63 then 1 else 2)))))) else 0
theorem nestingEntries_eq189 (n : Nat) :
    nestingProjection189.numerator[n]! = nestingEntries189 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries189, if_neg (by omega : ¬ n < 64)]

def nestingProjection190 : Projection := ⟨4,2,#[0,0,0,0,0,0,0,0,0,1,0,-1,1,0,1,0,0,0,1,-1,0,0,-1,-1,0,-1,-1,2,-1,0,0,1,0,1,0,-1,1,0,1,0,0,0,0,0,0,0,0,0,0,1,-1,0,1,0,2,1,0,0,-1,1,0,0,1,1]⟩
theorem nestingLookup190 : projections[190]! = nestingProjection190 := by
  rw [projections_lookup]
  rfl
def nestingEntries190 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then 0 else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else (if n < 11 then 0 else (-1))) else (if n < 14 then (if n < 13 then 1 else 0) else (if n < 15 then 1 else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 1 else (-1))) else (if n < 22 then 0 else (-1))) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else (-1)) else (if n < 27 then (-1) else 2)) else (if n < 30 then (if n < 29 then (-1) else 0) else (if n < 31 then 0 else 1))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 0 else 1) else (if n < 35 then 0 else (-1))) else (if n < 38 then (if n < 37 then 1 else 0) else (if n < 39 then 1 else 0))) else 0) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else 1) else (if n < 51 then (-1) else 0)) else (if n < 54 then (if n < 53 then 1 else 0) else (if n < 55 then 2 else 1))) else (if n < 60 then (if n < 58 then 0 else (if n < 59 then (-1) else 1)) else (if n < 62 then 0 else 1))))) else 0
theorem nestingEntries_eq190 (n : Nat) :
    nestingProjection190.numerator[n]! = nestingEntries190 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries190, if_neg (by omega : ¬ n < 64)]

def nestingProjection191 : Projection := ⟨4,2,#[1,1,1,-1,0,0,0,0,1,2,0,-1,0,-1,1,0,1,0,2,-1,0,1,-1,0,-1,-1,-1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,1,0,0,1,-1,0,0,1,-1,0,0,-1,1,0,0,0,0,0,0,0,0,0]⟩
theorem nestingLookup191 : projections[191]! = nestingProjection191 := by
  rw [projections_lookup]
  rfl
def nestingEntries191 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then 1 else (if n < 3 then 1 else (-1))) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 1 else 2) else (if n < 11 then 0 else (-1))) else (if n < 14 then (if n < 13 then 0 else (-1)) else (if n < 15 then 1 else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 1 else 0) else (if n < 19 then 2 else (-1))) else (if n < 22 then (if n < 21 then 0 else 1) else (if n < 23 then (-1) else 0))) else (if n < 28 then (if n < 26 then (-1) else (if n < 27 then (-1) else 1)) else 0))) else (if n < 48 then (if n < 40 then 0 else (if n < 44 then (if n < 42 then (if n < 41 then 0 else (-1)) else (if n < 43 then 1 else 0)) else (if n < 46 then (if n < 45 then 0 else 1) else (if n < 47 then (-1) else 0)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else 1) else (if n < 51 then (-1) else 0)) else (if n < 54 then (if n < 53 then 0 else (-1)) else (if n < 55 then 1 else 0))) else 0))) else 0
theorem nestingEntries_eq191 (n : Nat) :
    nestingProjection191.numerator[n]! = nestingEntries191 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries191, if_neg (by omega : ¬ n < 64)]

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def nestingProjection192 : Projection := ⟨4,2,#[1,0,0,1,-1,0,0,1,0,1,-1,0,0,-1,1,0,0,-1,1,0,0,1,-1,0,1,0,0,1,-1,0,0,1,-1,0,0,-1,1,0,0,-1,0,-1,1,0,0,1,-1,0,0,1,-1,0,0,-1,1,0,1,0,0,1,-1,0,0,1]⟩
theorem nestingLookup192 : projections[192]! = nestingProjection192 := by
  rw [projections_lookup]
  rfl
def nestingEntries192 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else (if n < 3 then 0 else 1)) else (if n < 6 then (if n < 5 then (-1) else 0) else (if n < 7 then 0 else 1))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else (if n < 11 then (-1) else 0)) else (if n < 14 then (if n < 13 then 0 else (-1)) else (if n < 15 then 1 else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 0 else (-1)) else (if n < 19 then 1 else 0)) else (if n < 22 then (if n < 21 then 0 else 1) else (if n < 23 then (-1) else 0))) else (if n < 28 then (if n < 26 then (if n < 25 then 1 else 0) else (if n < 27 then 0 else 1)) else (if n < 30 then (if n < 29 then (-1) else 0) else (if n < 31 then 0 else 1))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then (-1) else 0) else (if n < 35 then 0 else (-1))) else (if n < 38 then (if n < 37 then 1 else 0) else (if n < 39 then 0 else (-1)))) else (if n < 44 then (if n < 42 then (if n < 41 then 0 else (-1)) else (if n < 43 then 1 else 0)) else (if n < 46 then (if n < 45 then 0 else 1) else (if n < 47 then (-1) else 0)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else 1) else (if n < 51 then (-1) else 0)) else (if n < 54 then (if n < 53 then 0 else (-1)) else (if n < 55 then 1 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then 1 else 0) else (if n < 59 then 0 else 1)) else (if n < 62 then (if n < 61 then (-1) else 0) else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq192 (n : Nat) :
    nestingProjection192.numerator[n]! = nestingEntries192 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries192, if_neg (by omega : ¬ n < 64)]

def nestingProjection193 : Projection := ⟨4,2,#[2,1,1,0,-1,0,0,1,1,1,1,-1,0,0,0,0,1,1,1,-1,0,0,0,0,0,-1,-1,2,-1,0,0,1,-1,0,0,-1,1,0,0,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,1,-1,0,0,1]⟩
theorem nestingLookup193 : projections[193]! = nestingProjection193 := by
  rw [projections_lookup]
  rfl
def nestingEntries193 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 2 else 1) else (if n < 3 then 1 else 0)) else (if n < 6 then (if n < 5 then (-1) else 0) else (if n < 7 then 0 else 1))) else (if n < 12 then (if n < 10 then 1 else (if n < 11 then 1 else (-1))) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then 1 else (if n < 19 then 1 else (-1))) else 0) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else (-1)) else (if n < 27 then (-1) else 2)) else (if n < 30 then (if n < 29 then (-1) else 0) else (if n < 31 then 0 else 1))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then (-1) else 0) else (if n < 35 then 0 else (-1))) else (if n < 38 then (if n < 37 then 1 else 0) else (if n < 39 then 0 else (-1)))) else 0) else (if n < 56 then 0 else (if n < 60 then (if n < 58 then (if n < 57 then 1 else 0) else (if n < 59 then 0 else 1)) else (if n < 62 then (if n < 61 then (-1) else 0) else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq193 (n : Nat) :
    nestingProjection193.numerator[n]! = nestingEntries193 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries193, if_neg (by omega : ¬ n < 64)]

def nestingProjection194 : Projection := ⟨2,2,#[0,0,0,0,0,0,0,0,0,1,0,0,-1,0,0,0,0,0,1,0,0,0,0,-1,0,0,0,0,0,0,0,0,0,-1,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,0,0,0,0,1]⟩
theorem nestingLookup194 : projections[194]! = nestingProjection194 := by
  rw [projections_lookup]
  rfl
def nestingEntries194 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then 0 else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else 0) else (if n < 14 then (if n < 13 then (-1) else 0) else 0))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 1 else 0)) else (if n < 22 then 0 else (if n < 23 then 0 else (-1)))) else 0)) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 0 else (-1)) else 0) else (if n < 38 then (if n < 37 then 1 else 0) else 0)) else 0) else (if n < 56 then 0 else (if n < 60 then (if n < 58 then 0 else (if n < 59 then (-1) else 0)) else (if n < 62 then 0 else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq194 (n : Nat) :
    nestingProjection194.numerator[n]! = nestingEntries194 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries194, if_neg (by omega : ¬ n < 64)]

def nestingProjection195 : Projection := ⟨4,2,#[1,0,0,1,0,1,-1,0,0,1,1,0,-1,0,0,-1,0,1,1,0,-1,0,0,-1,1,0,0,1,0,1,-1,0,0,-1,-1,0,1,0,0,1,1,0,0,1,0,1,-1,0,-1,0,0,-1,0,-1,1,0,0,-1,-1,0,1,0,0,1]⟩
theorem nestingLookup195 : projections[195]! = nestingProjection195 := by
  rw [projections_lookup]
  rfl
def nestingEntries195 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else (if n < 3 then 0 else 1)) else (if n < 6 then (if n < 5 then 0 else 1) else (if n < 7 then (-1) else 0))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else (if n < 11 then 1 else 0)) else (if n < 14 then (if n < 13 then (-1) else 0) else (if n < 15 then 0 else (-1))))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 0 else 1) else (if n < 19 then 1 else 0)) else (if n < 22 then (if n < 21 then (-1) else 0) else (if n < 23 then 0 else (-1)))) else (if n < 28 then (if n < 26 then (if n < 25 then 1 else 0) else (if n < 27 then 0 else 1)) else (if n < 30 then (if n < 29 then 0 else 1) else (if n < 31 then (-1) else 0))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 0 else (-1)) else (if n < 35 then (-1) else 0)) else (if n < 38 then (if n < 37 then 1 else 0) else (if n < 39 then 0 else 1))) else (if n < 44 then (if n < 42 then (if n < 41 then 1 else 0) else (if n < 43 then 0 else 1)) else (if n < 46 then (if n < 45 then 0 else 1) else (if n < 47 then (-1) else 0)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then (-1) else 0) else (if n < 51 then 0 else (-1))) else (if n < 54 then (if n < 53 then 0 else (-1)) else (if n < 55 then 1 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then 0 else (-1)) else (if n < 59 then (-1) else 0)) else (if n < 62 then (if n < 61 then 1 else 0) else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq195 (n : Nat) :
    nestingProjection195.numerator[n]! = nestingEntries195 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries195, if_neg (by omega : ¬ n < 64)]

def nestingProjection196 : Projection := ⟨4,2,#[1,0,0,-1,0,1,1,0,0,1,1,0,-1,0,0,-1,0,1,1,0,-1,0,0,-1,-1,0,0,1,0,-1,-1,0,0,-1,-1,0,1,0,0,1,1,0,0,-1,0,1,1,0,1,0,0,-1,0,1,1,0,0,-1,-1,0,1,0,0,1]⟩
theorem nestingLookup196 : projections[196]! = nestingProjection196 := by
  rw [projections_lookup]
  rfl
def nestingEntries196 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else (if n < 3 then 0 else (-1))) else (if n < 6 then (if n < 5 then 0 else 1) else (if n < 7 then 1 else 0))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else (if n < 11 then 1 else 0)) else (if n < 14 then (if n < 13 then (-1) else 0) else (if n < 15 then 0 else (-1))))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 0 else 1) else (if n < 19 then 1 else 0)) else (if n < 22 then (if n < 21 then (-1) else 0) else (if n < 23 then 0 else (-1)))) else (if n < 28 then (if n < 26 then (if n < 25 then (-1) else 0) else (if n < 27 then 0 else 1)) else (if n < 30 then (if n < 29 then 0 else (-1)) else (if n < 31 then (-1) else 0))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 0 else (-1)) else (if n < 35 then (-1) else 0)) else (if n < 38 then (if n < 37 then 1 else 0) else (if n < 39 then 0 else 1))) else (if n < 44 then (if n < 42 then (if n < 41 then 1 else 0) else (if n < 43 then 0 else (-1))) else (if n < 46 then (if n < 45 then 0 else 1) else (if n < 47 then 1 else 0)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 1 else 0) else (if n < 51 then 0 else (-1))) else (if n < 54 then (if n < 53 then 0 else 1) else (if n < 55 then 1 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then 0 else (-1)) else (if n < 59 then (-1) else 0)) else (if n < 62 then (if n < 61 then 1 else 0) else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq196 (n : Nat) :
    nestingProjection196.numerator[n]! = nestingEntries196 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries196, if_neg (by omega : ¬ n < 64)]

def nestingProjection197 : Projection := ⟨4,2,#[1,0,0,1,0,1,-1,0,0,1,-1,0,-1,0,0,1,0,-1,1,0,1,0,0,-1,1,0,0,1,0,1,-1,0,0,-1,1,0,1,0,0,-1,1,0,0,1,0,1,-1,0,-1,0,0,-1,0,-1,1,0,0,1,-1,0,-1,0,0,1]⟩
theorem nestingLookup197 : projections[197]! = nestingProjection197 := by
  rw [projections_lookup]
  rfl
def nestingEntries197 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else (if n < 3 then 0 else 1)) else (if n < 6 then (if n < 5 then 0 else 1) else (if n < 7 then (-1) else 0))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else (if n < 11 then (-1) else 0)) else (if n < 14 then (if n < 13 then (-1) else 0) else (if n < 15 then 0 else 1)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 0 else (-1)) else (if n < 19 then 1 else 0)) else (if n < 22 then (if n < 21 then 1 else 0) else (if n < 23 then 0 else (-1)))) else (if n < 28 then (if n < 26 then (if n < 25 then 1 else 0) else (if n < 27 then 0 else 1)) else (if n < 30 then (if n < 29 then 0 else 1) else (if n < 31 then (-1) else 0))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 0 else (-1)) else (if n < 35 then 1 else 0)) else (if n < 38 then (if n < 37 then 1 else 0) else (if n < 39 then 0 else (-1)))) else (if n < 44 then (if n < 42 then (if n < 41 then 1 else 0) else (if n < 43 then 0 else 1)) else (if n < 46 then (if n < 45 then 0 else 1) else (if n < 47 then (-1) else 0)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then (-1) else 0) else (if n < 51 then 0 else (-1))) else (if n < 54 then (if n < 53 then 0 else (-1)) else (if n < 55 then 1 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then 0 else 1) else (if n < 59 then (-1) else 0)) else (if n < 62 then (if n < 61 then (-1) else 0) else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq197 (n : Nat) :
    nestingProjection197.numerator[n]! = nestingEntries197 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries197, if_neg (by omega : ¬ n < 64)]

def nestingProjection198 : Projection := ⟨4,2,#[1,0,0,-1,0,1,1,0,0,1,-1,0,-1,0,0,1,0,-1,1,0,1,0,0,-1,-1,0,0,1,0,-1,-1,0,0,-1,1,0,1,0,0,-1,1,0,0,-1,0,1,1,0,1,0,0,-1,0,1,1,0,0,1,-1,0,-1,0,0,1]⟩
theorem nestingLookup198 : projections[198]! = nestingProjection198 := by
  rw [projections_lookup]
  rfl
def nestingEntries198 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else (if n < 3 then 0 else (-1))) else (if n < 6 then (if n < 5 then 0 else 1) else (if n < 7 then 1 else 0))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else (if n < 11 then (-1) else 0)) else (if n < 14 then (if n < 13 then (-1) else 0) else (if n < 15 then 0 else 1)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 0 else (-1)) else (if n < 19 then 1 else 0)) else (if n < 22 then (if n < 21 then 1 else 0) else (if n < 23 then 0 else (-1)))) else (if n < 28 then (if n < 26 then (if n < 25 then (-1) else 0) else (if n < 27 then 0 else 1)) else (if n < 30 then (if n < 29 then 0 else (-1)) else (if n < 31 then (-1) else 0))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 0 else (-1)) else (if n < 35 then 1 else 0)) else (if n < 38 then (if n < 37 then 1 else 0) else (if n < 39 then 0 else (-1)))) else (if n < 44 then (if n < 42 then (if n < 41 then 1 else 0) else (if n < 43 then 0 else (-1))) else (if n < 46 then (if n < 45 then 0 else 1) else (if n < 47 then 1 else 0)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 1 else 0) else (if n < 51 then 0 else (-1))) else (if n < 54 then (if n < 53 then 0 else 1) else (if n < 55 then 1 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then 0 else 1) else (if n < 59 then (-1) else 0)) else (if n < 62 then (if n < 61 then (-1) else 0) else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq198 (n : Nat) :
    nestingProjection198.numerator[n]! = nestingEntries198 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries198, if_neg (by omega : ¬ n < 64)]

def nestingProjection199 : Projection := ⟨2,2,#[1,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,-1,0,0,0,0,0,0,0,0,0,1,0,0,0,0,1,0,0,0,0,0,-1,0,0,1,0,0,0,0,0,0,0,0,0]⟩
theorem nestingLookup199 : projections[199]! = nestingProjection199 := by
  rw [projections_lookup]
  rfl
def nestingEntries199 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else 0) else (if n < 6 then (if n < 5 then 0 else 1) else 0)) else 0) else (if n < 24 then 0 else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 1)) else (if n < 30 then 0 else (if n < 31 then (-1) else 0))))) else (if n < 48 then (if n < 40 then 0 else (if n < 44 then (if n < 42 then (if n < 41 then 1 else 0) else 0) else (if n < 46 then (if n < 45 then 0 else 1) else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then 0 else (if n < 51 then 0 else (-1))) else (if n < 54 then 0 else (if n < 55 then 1 else 0))) else 0))) else 0
theorem nestingEntries_eq199 (n : Nat) :
    nestingProjection199.numerator[n]! = nestingEntries199 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries199, if_neg (by omega : ¬ n < 64)]

def nestingProjection200 : Projection := ⟨2,2,#[1,0,0,0,0,1,0,0,0,1,0,0,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,0,0,1,0,0,0,1,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]⟩
theorem nestingLookup200 : projections[200]! = nestingProjection200 := by
  rw [projections_lookup]
  rfl
def nestingEntries200 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else 0) else (if n < 6 then (if n < 5 then 0 else 1) else 0)) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else 0) else (if n < 14 then (if n < 13 then (-1) else 0) else 0))) else 0) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 0 else (-1)) else 0) else (if n < 38 then (if n < 37 then 1 else 0) else 0)) else (if n < 44 then (if n < 42 then (if n < 41 then 1 else 0) else 0) else (if n < 46 then (if n < 45 then 0 else 1) else 0))) else 0)) else 0
theorem nestingEntries_eq200 (n : Nat) :
    nestingProjection200.numerator[n]! = nestingEntries200 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries200, if_neg (by omega : ¬ n < 64)]

def nestingProjection201 : Projection := ⟨4,2,#[1,1,0,0,-1,1,0,0,1,1,0,0,-1,1,0,0,0,0,1,1,0,0,-1,-1,0,0,1,1,0,0,-1,-1,-1,-1,0,0,1,-1,0,0,1,1,0,0,-1,1,0,0,0,0,-1,-1,0,0,1,1,0,0,-1,-1,0,0,1,1]⟩
theorem nestingLookup201 : projections[201]! = nestingProjection201 := by
  rw [projections_lookup]
  rfl
def nestingEntries201 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then 1 else 0) else (if n < 6 then (if n < 5 then (-1) else 1) else 0)) else (if n < 12 then (if n < 10 then 1 else 0) else (if n < 14 then (if n < 13 then (-1) else 1) else 0))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else 1) else (if n < 22 then 0 else (-1))) else (if n < 28 then (if n < 26 then 0 else 1) else (if n < 30 then 0 else (-1))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (-1) else 0) else (if n < 38 then (if n < 37 then 1 else (-1)) else 0)) else (if n < 44 then (if n < 42 then 1 else 0) else (if n < 46 then (if n < 45 then (-1) else 1) else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then 0 else (-1)) else (if n < 54 then 0 else 1)) else (if n < 60 then (if n < 58 then 0 else (-1)) else (if n < 62 then 0 else 1))))) else 0
theorem nestingEntries_eq201 (n : Nat) :
    nestingProjection201.numerator[n]! = nestingEntries201 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries201, if_neg (by omega : ¬ n < 64)]

def nestingProjection202 : Projection := ⟨4,2,#[1,1,0,0,-1,1,0,0,1,1,0,0,-1,1,0,0,0,0,1,-1,0,0,1,-1,0,0,-1,1,0,0,-1,1,-1,-1,0,0,1,-1,0,0,1,1,0,0,-1,1,0,0,0,0,1,-1,0,0,1,-1,0,0,-1,1,0,0,-1,1]⟩
theorem nestingLookup202 : projections[202]! = nestingProjection202 := by
  rw [projections_lookup]
  rfl
def nestingEntries202 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then 1 else 0) else (if n < 6 then (if n < 5 then (-1) else 1) else 0)) else (if n < 12 then (if n < 10 then 1 else 0) else (if n < 14 then (if n < 13 then (-1) else 1) else 0))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 1 else (-1))) else (if n < 22 then 0 else (if n < 23 then 1 else (-1)))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then (-1) else 1)) else (if n < 30 then 0 else (if n < 31 then (-1) else 1))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (-1) else 0) else (if n < 38 then (if n < 37 then 1 else (-1)) else 0)) else (if n < 44 then (if n < 42 then 1 else 0) else (if n < 46 then (if n < 45 then (-1) else 1) else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then 0 else (if n < 51 then 1 else (-1))) else (if n < 54 then 0 else (if n < 55 then 1 else (-1)))) else (if n < 60 then (if n < 58 then 0 else (if n < 59 then (-1) else 1)) else (if n < 62 then 0 else (if n < 63 then (-1) else 1)))))) else 0
theorem nestingEntries_eq202 (n : Nat) :
    nestingProjection202.numerator[n]! = nestingEntries202 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries202, if_neg (by omega : ¬ n < 64)]

def nestingProjection203 : Projection := ⟨4,2,#[1,-1,0,0,1,1,0,0,-1,1,0,0,-1,-1,0,0,0,0,1,1,0,0,-1,-1,0,0,1,1,0,0,-1,-1,1,-1,0,0,1,1,0,0,1,-1,0,0,1,1,0,0,0,0,-1,-1,0,0,1,1,0,0,-1,-1,0,0,1,1]⟩
theorem nestingLookup203 : projections[203]! = nestingProjection203 := by
  rw [projections_lookup]
  rfl
def nestingEntries203 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else (-1)) else 0) else (if n < 6 then 1 else 0)) else (if n < 12 then (if n < 10 then (if n < 9 then (-1) else 1) else 0) else (if n < 14 then (-1) else 0))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else 1) else (if n < 22 then 0 else (-1))) else (if n < 28 then (if n < 26 then 0 else 1) else (if n < 30 then 0 else (-1))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 1 else (-1)) else 0) else (if n < 38 then 1 else 0)) else (if n < 44 then (if n < 42 then (if n < 41 then 1 else (-1)) else 0) else (if n < 46 then 1 else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then 0 else (-1)) else (if n < 54 then 0 else 1)) else (if n < 60 then (if n < 58 then 0 else (-1)) else (if n < 62 then 0 else 1))))) else 0
theorem nestingEntries_eq203 (n : Nat) :
    nestingProjection203.numerator[n]! = nestingEntries203 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries203, if_neg (by omega : ¬ n < 64)]

def nestingProjection204 : Projection := ⟨4,2,#[1,-1,0,0,1,1,0,0,-1,1,0,0,-1,-1,0,0,0,0,1,-1,0,0,1,-1,0,0,-1,1,0,0,-1,1,1,-1,0,0,1,1,0,0,1,-1,0,0,1,1,0,0,0,0,1,-1,0,0,1,-1,0,0,-1,1,0,0,-1,1]⟩
theorem nestingLookup204 : projections[204]! = nestingProjection204 := by
  rw [projections_lookup]
  rfl
def nestingEntries204 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else (-1)) else 0) else (if n < 6 then 1 else 0)) else (if n < 12 then (if n < 10 then (if n < 9 then (-1) else 1) else 0) else (if n < 14 then (-1) else 0))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 1 else (-1))) else (if n < 22 then 0 else (if n < 23 then 1 else (-1)))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then (-1) else 1)) else (if n < 30 then 0 else (if n < 31 then (-1) else 1))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 1 else (-1)) else 0) else (if n < 38 then 1 else 0)) else (if n < 44 then (if n < 42 then (if n < 41 then 1 else (-1)) else 0) else (if n < 46 then 1 else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then 0 else (if n < 51 then 1 else (-1))) else (if n < 54 then 0 else (if n < 55 then 1 else (-1)))) else (if n < 60 then (if n < 58 then 0 else (if n < 59 then (-1) else 1)) else (if n < 62 then 0 else (if n < 63 then (-1) else 1)))))) else 0
theorem nestingEntries_eq204 (n : Nat) :
    nestingProjection204.numerator[n]! = nestingEntries204 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries204, if_neg (by omega : ¬ n < 64)]

def nestingProjection205 : Projection := ⟨2,2,#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,-1,0,0,0,1,0,0,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,0,0,1,0,0,0,-1,0,0,0,0,1]⟩
theorem nestingLookup205 : projections[205]! = nestingProjection205 := by
  rw [projections_lookup]
  rfl
def nestingEntries205 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then 0 else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 1 else 0)) else (if n < 22 then 0 else (if n < 23 then 0 else (-1)))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 1)) else (if n < 30 then 0 else (if n < 31 then (-1) else 0))))) else (if n < 48 then 0 else (if n < 56 then (if n < 52 then (if n < 50 then 0 else (if n < 51 then 0 else (-1))) else (if n < 54 then 0 else (if n < 55 then 1 else 0))) else (if n < 60 then (if n < 58 then 0 else (if n < 59 then (-1) else 0)) else (if n < 62 then 0 else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq205 (n : Nat) :
    nestingProjection205.numerator[n]! = nestingEntries205 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries205, if_neg (by omega : ¬ n < 64)]

def nestingProjection206 : Projection := ⟨2,2,#[1,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,-1,0,0,0,0,1]⟩
theorem nestingLookup206 : projections[206]! = nestingProjection206 := by
  rw [projections_lookup]
  rfl
def nestingEntries206 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else 0) else (if n < 6 then (if n < 5 then 0 else 1) else 0)) else 0) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 1 else 0)) else (if n < 22 then 0 else (if n < 23 then 0 else (-1)))) else 0)) else (if n < 48 then (if n < 40 then 0 else (if n < 44 then (if n < 42 then (if n < 41 then 1 else 0) else 0) else (if n < 46 then (if n < 45 then 0 else 1) else 0))) else (if n < 56 then 0 else (if n < 60 then (if n < 58 then 0 else (if n < 59 then (-1) else 0)) else (if n < 62 then 0 else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq206 (n : Nat) :
    nestingProjection206.numerator[n]! = nestingEntries206 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries206, if_neg (by omega : ¬ n < 64)]

def nestingProjection207 : Projection := ⟨4,2,#[1,0,1,0,0,1,0,-1,0,1,0,1,-1,0,-1,0,1,0,1,0,0,1,0,-1,0,1,0,1,-1,0,-1,0,0,-1,0,-1,1,0,1,0,1,0,1,0,0,1,0,-1,0,-1,0,-1,1,0,1,0,-1,0,-1,0,0,-1,0,1]⟩
theorem nestingLookup207 : projections[207]! = nestingProjection207 := by
  rw [projections_lookup]
  rfl
def nestingEntries207 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else (if n < 3 then 1 else 0)) else (if n < 6 then (if n < 5 then 0 else 1) else (if n < 7 then 0 else (-1)))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else (if n < 11 then 0 else 1)) else (if n < 14 then (if n < 13 then (-1) else 0) else (if n < 15 then (-1) else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 1 else 0) else (if n < 19 then 1 else 0)) else (if n < 22 then (if n < 21 then 0 else 1) else (if n < 23 then 0 else (-1)))) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else 1) else (if n < 27 then 0 else 1)) else (if n < 30 then (if n < 29 then (-1) else 0) else (if n < 31 then (-1) else 0))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 0 else (-1)) else (if n < 35 then 0 else (-1))) else (if n < 38 then (if n < 37 then 1 else 0) else (if n < 39 then 1 else 0))) else (if n < 44 then (if n < 42 then (if n < 41 then 1 else 0) else (if n < 43 then 1 else 0)) else (if n < 46 then (if n < 45 then 0 else 1) else (if n < 47 then 0 else (-1))))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else (-1)) else (if n < 51 then 0 else (-1))) else (if n < 54 then (if n < 53 then 1 else 0) else (if n < 55 then 1 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then (-1) else 0) else (if n < 59 then (-1) else 0)) else (if n < 62 then (if n < 61 then 0 else (-1)) else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq207 (n : Nat) :
    nestingProjection207.numerator[n]! = nestingEntries207 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries207, if_neg (by omega : ¬ n < 64)]

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def nestingProjection208 : Projection := ⟨4,2,#[1,0,1,0,0,1,0,-1,0,1,0,-1,-1,0,1,0,1,0,1,0,0,1,0,-1,0,-1,0,1,1,0,-1,0,0,-1,0,1,1,0,-1,0,1,0,1,0,0,1,0,-1,0,1,0,-1,-1,0,1,0,-1,0,-1,0,0,-1,0,1]⟩
theorem nestingLookup208 : projections[208]! = nestingProjection208 := by
  rw [projections_lookup]
  rfl
def nestingEntries208 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else (if n < 3 then 1 else 0)) else (if n < 6 then (if n < 5 then 0 else 1) else (if n < 7 then 0 else (-1)))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else (if n < 11 then 0 else (-1))) else (if n < 14 then (if n < 13 then (-1) else 0) else (if n < 15 then 1 else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 1 else 0) else (if n < 19 then 1 else 0)) else (if n < 22 then (if n < 21 then 0 else 1) else (if n < 23 then 0 else (-1)))) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else (-1)) else (if n < 27 then 0 else 1)) else (if n < 30 then (if n < 29 then 1 else 0) else (if n < 31 then (-1) else 0))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 0 else (-1)) else (if n < 35 then 0 else 1)) else (if n < 38 then (if n < 37 then 1 else 0) else (if n < 39 then (-1) else 0))) else (if n < 44 then (if n < 42 then (if n < 41 then 1 else 0) else (if n < 43 then 1 else 0)) else (if n < 46 then (if n < 45 then 0 else 1) else (if n < 47 then 0 else (-1))))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else 1) else (if n < 51 then 0 else (-1))) else (if n < 54 then (if n < 53 then (-1) else 0) else (if n < 55 then 1 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then (-1) else 0) else (if n < 59 then (-1) else 0)) else (if n < 62 then (if n < 61 then 0 else (-1)) else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq208 (n : Nat) :
    nestingProjection208.numerator[n]! = nestingEntries208 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries208, if_neg (by omega : ¬ n < 64)]

def nestingProjection209 : Projection := ⟨4,2,#[1,0,-1,0,0,1,0,1,0,1,0,1,-1,0,-1,0,-1,0,1,0,0,-1,0,-1,0,1,0,1,-1,0,-1,0,0,-1,0,-1,1,0,1,0,1,0,-1,0,0,1,0,1,0,-1,0,-1,1,0,1,0,1,0,-1,0,0,1,0,1]⟩
theorem nestingLookup209 : projections[209]! = nestingProjection209 := by
  rw [projections_lookup]
  rfl
def nestingEntries209 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else (if n < 3 then (-1) else 0)) else (if n < 6 then (if n < 5 then 0 else 1) else (if n < 7 then 0 else 1))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else (if n < 11 then 0 else 1)) else (if n < 14 then (if n < 13 then (-1) else 0) else (if n < 15 then (-1) else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then (-1) else 0) else (if n < 19 then 1 else 0)) else (if n < 22 then (if n < 21 then 0 else (-1)) else (if n < 23 then 0 else (-1)))) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else 1) else (if n < 27 then 0 else 1)) else (if n < 30 then (if n < 29 then (-1) else 0) else (if n < 31 then (-1) else 0))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 0 else (-1)) else (if n < 35 then 0 else (-1))) else (if n < 38 then (if n < 37 then 1 else 0) else (if n < 39 then 1 else 0))) else (if n < 44 then (if n < 42 then (if n < 41 then 1 else 0) else (if n < 43 then (-1) else 0)) else (if n < 46 then (if n < 45 then 0 else 1) else (if n < 47 then 0 else 1)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else (-1)) else (if n < 51 then 0 else (-1))) else (if n < 54 then (if n < 53 then 1 else 0) else (if n < 55 then 1 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then 1 else 0) else (if n < 59 then (-1) else 0)) else (if n < 62 then (if n < 61 then 0 else 1) else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq209 (n : Nat) :
    nestingProjection209.numerator[n]! = nestingEntries209 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries209, if_neg (by omega : ¬ n < 64)]

def nestingProjection210 : Projection := ⟨4,2,#[1,0,-1,0,0,1,0,1,0,1,0,-1,-1,0,1,0,-1,0,1,0,0,-1,0,-1,0,-1,0,1,1,0,-1,0,0,-1,0,1,1,0,-1,0,1,0,-1,0,0,1,0,1,0,1,0,-1,-1,0,1,0,1,0,-1,0,0,1,0,1]⟩
theorem nestingLookup210 : projections[210]! = nestingProjection210 := by
  rw [projections_lookup]
  rfl
def nestingEntries210 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else (if n < 3 then (-1) else 0)) else (if n < 6 then (if n < 5 then 0 else 1) else (if n < 7 then 0 else 1))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else (if n < 11 then 0 else (-1))) else (if n < 14 then (if n < 13 then (-1) else 0) else (if n < 15 then 1 else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then (-1) else 0) else (if n < 19 then 1 else 0)) else (if n < 22 then (if n < 21 then 0 else (-1)) else (if n < 23 then 0 else (-1)))) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else (-1)) else (if n < 27 then 0 else 1)) else (if n < 30 then (if n < 29 then 1 else 0) else (if n < 31 then (-1) else 0))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 0 else (-1)) else (if n < 35 then 0 else 1)) else (if n < 38 then (if n < 37 then 1 else 0) else (if n < 39 then (-1) else 0))) else (if n < 44 then (if n < 42 then (if n < 41 then 1 else 0) else (if n < 43 then (-1) else 0)) else (if n < 46 then (if n < 45 then 0 else 1) else (if n < 47 then 0 else 1)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else 1) else (if n < 51 then 0 else (-1))) else (if n < 54 then (if n < 53 then (-1) else 0) else (if n < 55 then 1 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then 1 else 0) else (if n < 59 then (-1) else 0)) else (if n < 62 then (if n < 61 then 0 else 1) else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq210 (n : Nat) :
    nestingProjection210.numerator[n]! = nestingEntries210 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries210, if_neg (by omega : ¬ n < 64)]

def nestingProjection211 : Projection := ⟨2,2,#[0,0,0,0,0,0,0,0,0,1,0,0,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,-1,0,0,-1,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,0,0,1,0,0,0,0,0,0,0,0,0]⟩
theorem nestingLookup211 : projections[211]! = nestingProjection211 := by
  rw [projections_lookup]
  rfl
def nestingEntries211 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then 0 else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else 0) else (if n < 14 then (if n < 13 then (-1) else 0) else 0))) else (if n < 24 then 0 else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 1)) else (if n < 30 then 0 else (if n < 31 then (-1) else 0))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 0 else (-1)) else 0) else (if n < 38 then (if n < 37 then 1 else 0) else 0)) else 0) else (if n < 56 then (if n < 52 then (if n < 50 then 0 else (if n < 51 then 0 else (-1))) else (if n < 54 then 0 else (if n < 55 then 1 else 0))) else 0))) else 0
theorem nestingEntries_eq211 (n : Nat) :
    nestingProjection211.numerator[n]! = nestingEntries211 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries211, if_neg (by omega : ¬ n < 64)]

def nestingProjection212 : Projection := ⟨1,2,#[0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1]⟩
theorem nestingLookup212 : projections[212]! = nestingProjection212 := by
  rw [projections_lookup]
  rfl
def nestingEntries212 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then 0 else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else 0) else 0)) else 0) else (if n < 48 then 0 else (if n < 56 then 0 else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq212 (n : Nat) :
    nestingProjection212.numerator[n]! = nestingEntries212 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries212, if_neg (by omega : ¬ n < 64)]

def nestingProjection213 : Projection := ⟨4,2,#[1,0,0,1,0,-1,-1,0,0,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,1,0,-1,-1,0,0,0,0,0,0,0,0,0,-1,0,0,-1,0,1,1,0,-1,0,0,-1,0,1,1,0,0,0,0,0,0,0,0,0]⟩
theorem nestingLookup213 : projections[213]! = nestingProjection213 := by
  rw [projections_lookup]
  rfl
def nestingEntries213 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else (if n < 3 then 0 else 1)) else (if n < 6 then (if n < 5 then 0 else (-1)) else (if n < 7 then (-1) else 0))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 4) else 0) else 0)) else (if n < 24 then 0 else (if n < 28 then (if n < 26 then (if n < 25 then 1 else 0) else (if n < 27 then 0 else 1)) else (if n < 30 then (if n < 29 then 0 else (-1)) else (if n < 31 then (-1) else 0))))) else (if n < 48 then (if n < 40 then 0 else (if n < 44 then (if n < 42 then (if n < 41 then (-1) else 0) else (if n < 43 then 0 else (-1))) else (if n < 46 then (if n < 45 then 0 else 1) else (if n < 47 then 1 else 0)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then (-1) else 0) else (if n < 51 then 0 else (-1))) else (if n < 54 then (if n < 53 then 0 else 1) else (if n < 55 then 1 else 0))) else 0))) else 0
theorem nestingEntries_eq213 (n : Nat) :
    nestingProjection213.numerator[n]! = nestingEntries213 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries213, if_neg (by omega : ¬ n < 64)]

def nestingProjection214 : Projection := ⟨4,2,#[1,0,0,-1,0,1,-1,0,0,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,0,0,1,0,-1,1,0,0,0,0,0,0,0,0,0,1,0,0,-1,0,1,-1,0,-1,0,0,1,0,-1,1,0,0,0,0,0,0,0,0,0]⟩
theorem nestingLookup214 : projections[214]! = nestingProjection214 := by
  rw [projections_lookup]
  rfl
def nestingEntries214 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else (if n < 3 then 0 else (-1))) else (if n < 6 then (if n < 5 then 0 else 1) else (if n < 7 then (-1) else 0))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 4) else 0) else 0)) else (if n < 24 then 0 else (if n < 28 then (if n < 26 then (if n < 25 then (-1) else 0) else (if n < 27 then 0 else 1)) else (if n < 30 then (if n < 29 then 0 else (-1)) else (if n < 31 then 1 else 0))))) else (if n < 48 then (if n < 40 then 0 else (if n < 44 then (if n < 42 then (if n < 41 then 1 else 0) else (if n < 43 then 0 else (-1))) else (if n < 46 then (if n < 45 then 0 else 1) else (if n < 47 then (-1) else 0)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then (-1) else 0) else (if n < 51 then 0 else 1)) else (if n < 54 then (if n < 53 then 0 else (-1)) else (if n < 55 then 1 else 0))) else 0))) else 0
theorem nestingEntries_eq214 (n : Nat) :
    nestingProjection214.numerator[n]! = nestingEntries214 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries214, if_neg (by omega : ¬ n < 64)]

def nestingProjection215 : Projection := ⟨4,2,#[1,0,0,1,0,-1,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,1,0,-1,-1,0,0,0,0,0,0,0,0,0,-1,0,0,-1,0,1,1,0,-1,0,0,-1,0,1,1,0,0,0,0,0,0,0,0,4]⟩
theorem nestingLookup215 : projections[215]! = nestingProjection215 := by
  rw [projections_lookup]
  rfl
def nestingEntries215 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else (if n < 3 then 0 else 1)) else (if n < 6 then (if n < 5 then 0 else (-1)) else (if n < 7 then (-1) else 0))) else 0) else (if n < 24 then 0 else (if n < 28 then (if n < 26 then (if n < 25 then 1 else 0) else (if n < 27 then 0 else 1)) else (if n < 30 then (if n < 29 then 0 else (-1)) else (if n < 31 then (-1) else 0))))) else (if n < 48 then (if n < 40 then 0 else (if n < 44 then (if n < 42 then (if n < 41 then (-1) else 0) else (if n < 43 then 0 else (-1))) else (if n < 46 then (if n < 45 then 0 else 1) else (if n < 47 then 1 else 0)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then (-1) else 0) else (if n < 51 then 0 else (-1))) else (if n < 54 then (if n < 53 then 0 else 1) else (if n < 55 then 1 else 0))) else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 4)))))) else 0
theorem nestingEntries_eq215 (n : Nat) :
    nestingProjection215.numerator[n]! = nestingEntries215 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries215, if_neg (by omega : ¬ n < 64)]

def nestingProjection216 : Projection := ⟨4,2,#[1,0,0,-1,0,1,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,0,0,1,0,-1,1,0,0,0,0,0,0,0,0,0,1,0,0,-1,0,1,-1,0,-1,0,0,1,0,-1,1,0,0,0,0,0,0,0,0,4]⟩
theorem nestingLookup216 : projections[216]! = nestingProjection216 := by
  rw [projections_lookup]
  rfl
def nestingEntries216 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else (if n < 3 then 0 else (-1))) else (if n < 6 then (if n < 5 then 0 else 1) else (if n < 7 then (-1) else 0))) else 0) else (if n < 24 then 0 else (if n < 28 then (if n < 26 then (if n < 25 then (-1) else 0) else (if n < 27 then 0 else 1)) else (if n < 30 then (if n < 29 then 0 else (-1)) else (if n < 31 then 1 else 0))))) else (if n < 48 then (if n < 40 then 0 else (if n < 44 then (if n < 42 then (if n < 41 then 1 else 0) else (if n < 43 then 0 else (-1))) else (if n < 46 then (if n < 45 then 0 else 1) else (if n < 47 then (-1) else 0)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then (-1) else 0) else (if n < 51 then 0 else 1)) else (if n < 54 then (if n < 53 then 0 else (-1)) else (if n < 55 then 1 else 0))) else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 4)))))) else 0
theorem nestingEntries_eq216 (n : Nat) :
    nestingProjection216.numerator[n]! = nestingEntries216 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries216, if_neg (by omega : ¬ n < 64)]

def nestingProjection217 : Projection := ⟨2,2,#[1,0,0,0,0,0,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,0,1,0,0,-1,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0]⟩
theorem nestingLookup217 : projections[217]! = nestingProjection217 := by
  rw [projections_lookup]
  rfl
def nestingEntries217 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else 0) else (if n < 6 then 0 else (if n < 7 then (-1) else 0))) else 0) else (if n < 24 then 0 else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 1)) else (if n < 30 then (if n < 29 then 0 else (-1)) else 0)))) else (if n < 48 then (if n < 40 then 0 else (if n < 44 then (if n < 42 then 0 else (if n < 43 then 0 else (-1))) else (if n < 46 then (if n < 45 then 0 else 1) else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then (-1) else 0) else 0) else (if n < 54 then 0 else (if n < 55 then 1 else 0))) else 0))) else 0
theorem nestingEntries_eq217 (n : Nat) :
    nestingProjection217.numerator[n]! = nestingEntries217 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries217, if_neg (by omega : ¬ n < 64)]

def nestingProjection218 : Projection := ⟨2,2,#[1,0,0,0,0,0,-1,0,0,1,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,0,0,0,0,0,1,0,0,1,0,0,0,0,0,1]⟩
theorem nestingLookup218 : projections[218]! = nestingProjection218 := by
  rw [projections_lookup]
  rfl
def nestingEntries218 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else 0) else (if n < 6 then 0 else (if n < 7 then (-1) else 0))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else 0) else (if n < 14 then 0 else (if n < 15 then 0 else 1)))) else 0) else (if n < 48 then 0 else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then (-1) else 0) else 0) else (if n < 54 then 0 else (if n < 55 then 1 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then 0 else 1) else 0) else (if n < 62 then 0 else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq218 (n : Nat) :
    nestingProjection218.numerator[n]! = nestingEntries218 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries218, if_neg (by omega : ¬ n < 64)]

def nestingProjection219 : Projection := ⟨4,2,#[1,1,0,0,0,0,-1,1,1,2,0,1,0,-1,-1,0,0,0,0,0,0,0,0,0,0,1,0,1,0,-1,0,-1,0,0,0,0,0,0,0,0,0,-1,0,-1,0,1,0,1,-1,-1,0,0,0,0,1,-1,1,0,0,-1,0,1,-1,2]⟩
theorem nestingLookup219 : projections[219]! = nestingProjection219 := by
  rw [projections_lookup]
  rfl
def nestingEntries219 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then 1 else 0) else (if n < 6 then 0 else (if n < 7 then (-1) else 1))) else (if n < 12 then (if n < 10 then (if n < 9 then 1 else 2) else (if n < 11 then 0 else 1)) else (if n < 14 then (if n < 13 then 0 else (-1)) else (if n < 15 then (-1) else 0)))) else (if n < 24 then 0 else (if n < 28 then (if n < 26 then (if n < 25 then 0 else 1) else (if n < 27 then 0 else 1)) else (if n < 30 then (if n < 29 then 0 else (-1)) else (if n < 31 then 0 else (-1)))))) else (if n < 48 then (if n < 40 then 0 else (if n < 44 then (if n < 42 then (if n < 41 then 0 else (-1)) else (if n < 43 then 0 else (-1))) else (if n < 46 then (if n < 45 then 0 else 1) else (if n < 47 then 0 else 1)))) else (if n < 56 then (if n < 52 then (if n < 50 then (-1) else 0) else (if n < 54 then 0 else (if n < 55 then 1 else (-1)))) else (if n < 60 then (if n < 58 then (if n < 57 then 1 else 0) else (if n < 59 then 0 else (-1))) else (if n < 62 then (if n < 61 then 0 else 1) else (if n < 63 then (-1) else 2)))))) else 0
theorem nestingEntries_eq219 (n : Nat) :
    nestingProjection219.numerator[n]! = nestingEntries219 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries219, if_neg (by omega : ¬ n < 64)]

def nestingProjection220 : Projection := ⟨4,2,#[1,1,0,0,0,0,-1,1,1,2,0,-1,0,1,-1,0,0,0,0,0,0,0,0,0,0,-1,0,1,0,-1,0,1,0,0,0,0,0,0,0,0,0,1,0,-1,0,1,0,-1,-1,-1,0,0,0,0,1,-1,1,0,0,1,0,-1,-1,2]⟩
theorem nestingLookup220 : projections[220]! = nestingProjection220 := by
  rw [projections_lookup]
  rfl
def nestingEntries220 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then 1 else 0) else (if n < 6 then 0 else (if n < 7 then (-1) else 1))) else (if n < 12 then (if n < 10 then (if n < 9 then 1 else 2) else (if n < 11 then 0 else (-1))) else (if n < 14 then (if n < 13 then 0 else 1) else (if n < 15 then (-1) else 0)))) else (if n < 24 then 0 else (if n < 28 then (if n < 26 then (if n < 25 then 0 else (-1)) else (if n < 27 then 0 else 1)) else (if n < 30 then (if n < 29 then 0 else (-1)) else (if n < 31 then 0 else 1))))) else (if n < 48 then (if n < 40 then 0 else (if n < 44 then (if n < 42 then (if n < 41 then 0 else 1) else (if n < 43 then 0 else (-1))) else (if n < 46 then (if n < 45 then 0 else 1) else (if n < 47 then 0 else (-1))))) else (if n < 56 then (if n < 52 then (if n < 50 then (-1) else 0) else (if n < 54 then 0 else (if n < 55 then 1 else (-1)))) else (if n < 60 then (if n < 58 then (if n < 57 then 1 else 0) else (if n < 59 then 0 else 1)) else (if n < 62 then (if n < 61 then 0 else (-1)) else (if n < 63 then (-1) else 2)))))) else 0
theorem nestingEntries_eq220 (n : Nat) :
    nestingProjection220.numerator[n]! = nestingEntries220 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries220, if_neg (by omega : ¬ n < 64)]

def nestingProjection221 : Projection := ⟨4,2,#[1,-1,0,0,0,0,-1,-1,-1,2,0,1,0,-1,1,0,0,0,0,0,0,0,0,0,0,1,0,1,0,-1,0,-1,0,0,0,0,0,0,0,0,0,-1,0,-1,0,1,0,1,-1,1,0,0,0,0,1,1,-1,0,0,-1,0,1,1,2]⟩
theorem nestingLookup221 : projections[221]! = nestingProjection221 := by
  rw [projections_lookup]
  rfl
def nestingEntries221 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else (-1)) else 0) else (if n < 6 then 0 else (-1))) else (if n < 12 then (if n < 10 then (if n < 9 then (-1) else 2) else (if n < 11 then 0 else 1)) else (if n < 14 then (if n < 13 then 0 else (-1)) else (if n < 15 then 1 else 0)))) else (if n < 24 then 0 else (if n < 28 then (if n < 26 then (if n < 25 then 0 else 1) else (if n < 27 then 0 else 1)) else (if n < 30 then (if n < 29 then 0 else (-1)) else (if n < 31 then 0 else (-1)))))) else (if n < 48 then (if n < 40 then 0 else (if n < 44 then (if n < 42 then (if n < 41 then 0 else (-1)) else (if n < 43 then 0 else (-1))) else (if n < 46 then (if n < 45 then 0 else 1) else (if n < 47 then 0 else 1)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then (-1) else 1) else 0) else (if n < 54 then 0 else 1)) else (if n < 60 then (if n < 58 then (if n < 57 then (-1) else 0) else (if n < 59 then 0 else (-1))) else (if n < 62 then (if n < 61 then 0 else 1) else (if n < 63 then 1 else 2)))))) else 0
theorem nestingEntries_eq221 (n : Nat) :
    nestingProjection221.numerator[n]! = nestingEntries221 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries221, if_neg (by omega : ¬ n < 64)]

def nestingProjection222 : Projection := ⟨4,2,#[1,-1,0,0,0,0,-1,-1,-1,2,0,-1,0,1,1,0,0,0,0,0,0,0,0,0,0,-1,0,1,0,-1,0,1,0,0,0,0,0,0,0,0,0,1,0,-1,0,1,0,-1,-1,1,0,0,0,0,1,1,-1,0,0,1,0,-1,1,2]⟩
theorem nestingLookup222 : projections[222]! = nestingProjection222 := by
  rw [projections_lookup]
  rfl
def nestingEntries222 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else (-1)) else 0) else (if n < 6 then 0 else (-1))) else (if n < 12 then (if n < 10 then (if n < 9 then (-1) else 2) else (if n < 11 then 0 else (-1))) else (if n < 14 then (if n < 13 then 0 else 1) else (if n < 15 then 1 else 0)))) else (if n < 24 then 0 else (if n < 28 then (if n < 26 then (if n < 25 then 0 else (-1)) else (if n < 27 then 0 else 1)) else (if n < 30 then (if n < 29 then 0 else (-1)) else (if n < 31 then 0 else 1))))) else (if n < 48 then (if n < 40 then 0 else (if n < 44 then (if n < 42 then (if n < 41 then 0 else 1) else (if n < 43 then 0 else (-1))) else (if n < 46 then (if n < 45 then 0 else 1) else (if n < 47 then 0 else (-1))))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then (-1) else 1) else 0) else (if n < 54 then 0 else 1)) else (if n < 60 then (if n < 58 then (if n < 57 then (-1) else 0) else (if n < 59 then 0 else 1)) else (if n < 62 then (if n < 61 then 0 else (-1)) else (if n < 63 then 1 else 2)))))) else 0
theorem nestingEntries_eq222 (n : Nat) :
    nestingProjection222.numerator[n]! = nestingEntries222 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries222, if_neg (by omega : ¬ n < 64)]

def nestingProjection223 : Projection := ⟨2,2,#[0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,-1,0,0,0,0,0,0,0,0,0,0,0,1,0,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,0,1,0,0,0,0,0,0,0,0,0,0,0,-1,0,0,0,0,0,1]⟩
theorem nestingLookup223 : projections[223]! = nestingProjection223 := by
  rw [projections_lookup]
  rfl
def nestingEntries223 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then 0 else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else 0) else (if n < 14 then 0 else (if n < 15 then 0 else (-1))))) else (if n < 24 then 0 else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 1)) else (if n < 30 then (if n < 29 then 0 else (-1)) else 0)))) else (if n < 48 then (if n < 40 then 0 else (if n < 44 then (if n < 42 then 0 else (if n < 43 then 0 else (-1))) else (if n < 46 then (if n < 45 then 0 else 1) else 0))) else (if n < 56 then 0 else (if n < 60 then (if n < 58 then (if n < 57 then 0 else (-1)) else 0) else (if n < 62 then 0 else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq223 (n : Nat) :
    nestingProjection223.numerator[n]! = nestingEntries223 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries223, if_neg (by omega : ¬ n < 64)]

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def nestingProjection224 : Projection := ⟨2,2,#[1,0,0,0,0,0,-1,0,0,1,0,0,0,0,0,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,0,0,0,0,0,1,0,0,-1,0,0,0,0,0,1]⟩
theorem nestingLookup224 : projections[224]! = nestingProjection224 := by
  rw [projections_lookup]
  rfl
def nestingEntries224 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else 0) else (if n < 6 then 0 else (if n < 7 then (-1) else 0))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else 0) else (if n < 14 then 0 else (if n < 15 then 0 else (-1))))) else 0) else (if n < 48 then 0 else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then (-1) else 0) else 0) else (if n < 54 then 0 else (if n < 55 then 1 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then 0 else (-1)) else 0) else (if n < 62 then 0 else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq224 (n : Nat) :
    nestingProjection224.numerator[n]! = nestingEntries224 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries224, if_neg (by omega : ¬ n < 64)]

def nestingProjection225 : Projection := ⟨4,2,#[1,1,0,0,0,0,-1,-1,1,2,0,1,0,-1,-1,0,0,0,0,0,0,0,0,0,0,1,0,1,0,-1,0,1,0,0,0,0,0,0,0,0,0,-1,0,-1,0,1,0,-1,-1,-1,0,0,0,0,1,1,-1,0,0,1,0,-1,1,2]⟩
theorem nestingLookup225 : projections[225]! = nestingProjection225 := by
  rw [projections_lookup]
  rfl
def nestingEntries225 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then 1 else 0) else (if n < 6 then 0 else (-1))) else (if n < 12 then (if n < 10 then (if n < 9 then 1 else 2) else (if n < 11 then 0 else 1)) else (if n < 14 then (if n < 13 then 0 else (-1)) else (if n < 15 then (-1) else 0)))) else (if n < 24 then 0 else (if n < 28 then (if n < 26 then (if n < 25 then 0 else 1) else (if n < 27 then 0 else 1)) else (if n < 30 then (if n < 29 then 0 else (-1)) else (if n < 31 then 0 else 1))))) else (if n < 48 then (if n < 40 then 0 else (if n < 44 then (if n < 42 then (if n < 41 then 0 else (-1)) else (if n < 43 then 0 else (-1))) else (if n < 46 then (if n < 45 then 0 else 1) else (if n < 47 then 0 else (-1))))) else (if n < 56 then (if n < 52 then (if n < 50 then (-1) else 0) else (if n < 54 then 0 else 1)) else (if n < 60 then (if n < 58 then (if n < 57 then (-1) else 0) else (if n < 59 then 0 else 1)) else (if n < 62 then (if n < 61 then 0 else (-1)) else (if n < 63 then 1 else 2)))))) else 0
theorem nestingEntries_eq225 (n : Nat) :
    nestingProjection225.numerator[n]! = nestingEntries225 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries225, if_neg (by omega : ¬ n < 64)]

def nestingProjection226 : Projection := ⟨4,2,#[1,1,0,0,0,0,-1,-1,1,2,0,-1,0,1,-1,0,0,0,0,0,0,0,0,0,0,-1,0,1,0,-1,0,-1,0,0,0,0,0,0,0,0,0,1,0,-1,0,1,0,1,-1,-1,0,0,0,0,1,1,-1,0,0,-1,0,1,1,2]⟩
theorem nestingLookup226 : projections[226]! = nestingProjection226 := by
  rw [projections_lookup]
  rfl
def nestingEntries226 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then 1 else 0) else (if n < 6 then 0 else (-1))) else (if n < 12 then (if n < 10 then (if n < 9 then 1 else 2) else (if n < 11 then 0 else (-1))) else (if n < 14 then (if n < 13 then 0 else 1) else (if n < 15 then (-1) else 0)))) else (if n < 24 then 0 else (if n < 28 then (if n < 26 then (if n < 25 then 0 else (-1)) else (if n < 27 then 0 else 1)) else (if n < 30 then (if n < 29 then 0 else (-1)) else (if n < 31 then 0 else (-1)))))) else (if n < 48 then (if n < 40 then 0 else (if n < 44 then (if n < 42 then (if n < 41 then 0 else 1) else (if n < 43 then 0 else (-1))) else (if n < 46 then (if n < 45 then 0 else 1) else (if n < 47 then 0 else 1)))) else (if n < 56 then (if n < 52 then (if n < 50 then (-1) else 0) else (if n < 54 then 0 else 1)) else (if n < 60 then (if n < 58 then (if n < 57 then (-1) else 0) else (if n < 59 then 0 else (-1))) else (if n < 62 then (if n < 61 then 0 else 1) else (if n < 63 then 1 else 2)))))) else 0
theorem nestingEntries_eq226 (n : Nat) :
    nestingProjection226.numerator[n]! = nestingEntries226 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries226, if_neg (by omega : ¬ n < 64)]

def nestingProjection227 : Projection := ⟨4,2,#[1,-1,0,0,0,0,-1,1,-1,2,0,1,0,-1,1,0,0,0,0,0,0,0,0,0,0,1,0,1,0,-1,0,1,0,0,0,0,0,0,0,0,0,-1,0,-1,0,1,0,-1,-1,1,0,0,0,0,1,-1,1,0,0,1,0,-1,-1,2]⟩
theorem nestingLookup227 : projections[227]! = nestingProjection227 := by
  rw [projections_lookup]
  rfl
def nestingEntries227 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else (-1)) else 0) else (if n < 6 then 0 else (if n < 7 then (-1) else 1))) else (if n < 12 then (if n < 10 then (if n < 9 then (-1) else 2) else (if n < 11 then 0 else 1)) else (if n < 14 then (if n < 13 then 0 else (-1)) else (if n < 15 then 1 else 0)))) else (if n < 24 then 0 else (if n < 28 then (if n < 26 then (if n < 25 then 0 else 1) else (if n < 27 then 0 else 1)) else (if n < 30 then (if n < 29 then 0 else (-1)) else (if n < 31 then 0 else 1))))) else (if n < 48 then (if n < 40 then 0 else (if n < 44 then (if n < 42 then (if n < 41 then 0 else (-1)) else (if n < 43 then 0 else (-1))) else (if n < 46 then (if n < 45 then 0 else 1) else (if n < 47 then 0 else (-1))))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then (-1) else 1) else 0) else (if n < 54 then 0 else (if n < 55 then 1 else (-1)))) else (if n < 60 then (if n < 58 then (if n < 57 then 1 else 0) else (if n < 59 then 0 else 1)) else (if n < 62 then (if n < 61 then 0 else (-1)) else (if n < 63 then (-1) else 2)))))) else 0
theorem nestingEntries_eq227 (n : Nat) :
    nestingProjection227.numerator[n]! = nestingEntries227 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries227, if_neg (by omega : ¬ n < 64)]

def nestingProjection228 : Projection := ⟨4,2,#[1,-1,0,0,0,0,-1,1,-1,2,0,-1,0,1,1,0,0,0,0,0,0,0,0,0,0,-1,0,1,0,-1,0,-1,0,0,0,0,0,0,0,0,0,1,0,-1,0,1,0,1,-1,1,0,0,0,0,1,-1,1,0,0,-1,0,1,-1,2]⟩
theorem nestingLookup228 : projections[228]! = nestingProjection228 := by
  rw [projections_lookup]
  rfl
def nestingEntries228 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else (-1)) else 0) else (if n < 6 then 0 else (if n < 7 then (-1) else 1))) else (if n < 12 then (if n < 10 then (if n < 9 then (-1) else 2) else (if n < 11 then 0 else (-1))) else (if n < 14 then (if n < 13 then 0 else 1) else (if n < 15 then 1 else 0)))) else (if n < 24 then 0 else (if n < 28 then (if n < 26 then (if n < 25 then 0 else (-1)) else (if n < 27 then 0 else 1)) else (if n < 30 then (if n < 29 then 0 else (-1)) else (if n < 31 then 0 else (-1)))))) else (if n < 48 then (if n < 40 then 0 else (if n < 44 then (if n < 42 then (if n < 41 then 0 else 1) else (if n < 43 then 0 else (-1))) else (if n < 46 then (if n < 45 then 0 else 1) else (if n < 47 then 0 else 1)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then (-1) else 1) else 0) else (if n < 54 then 0 else (if n < 55 then 1 else (-1)))) else (if n < 60 then (if n < 58 then (if n < 57 then 1 else 0) else (if n < 59 then 0 else (-1))) else (if n < 62 then (if n < 61 then 0 else 1) else (if n < 63 then (-1) else 2)))))) else 0
theorem nestingEntries_eq228 (n : Nat) :
    nestingProjection228.numerator[n]! = nestingEntries228 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries228, if_neg (by omega : ¬ n < 64)]

def nestingProjection229 : Projection := ⟨2,2,#[0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,1,0,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,0,1,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,1]⟩
theorem nestingLookup229 : projections[229]! = nestingProjection229 := by
  rw [projections_lookup]
  rfl
def nestingEntries229 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then 0 else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else 0) else (if n < 14 then 0 else (if n < 15 then 0 else 1)))) else (if n < 24 then 0 else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 1)) else (if n < 30 then (if n < 29 then 0 else (-1)) else 0)))) else (if n < 48 then (if n < 40 then 0 else (if n < 44 then (if n < 42 then 0 else (if n < 43 then 0 else (-1))) else (if n < 46 then (if n < 45 then 0 else 1) else 0))) else (if n < 56 then 0 else (if n < 60 then (if n < 58 then (if n < 57 then 0 else 1) else 0) else (if n < 62 then 0 else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq229 (n : Nat) :
    nestingProjection229.numerator[n]! = nestingEntries229 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries229, if_neg (by omega : ¬ n < 64)]

def nestingProjection230 : Projection := ⟨1,2,#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]⟩
theorem nestingLookup230 : projections[230]! = nestingProjection230 := by
  rw [projections_lookup]
  rfl
def nestingEntries230 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then 0 else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 1 else 0)) else 0) else 0)) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 1 else 0) else 0)) else 0) else 0)) else 0
theorem nestingEntries_eq230 (n : Nat) :
    nestingProjection230.numerator[n]! = nestingEntries230 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries230, if_neg (by omega : ¬ n < 64)]

def nestingProjection231 : Projection := ⟨4,2,#[1,0,0,1,0,1,1,0,0,0,0,0,0,0,0,0,0,0,4,0,0,0,0,0,1,0,0,1,0,1,1,0,0,0,0,0,0,0,0,0,1,0,0,1,0,1,1,0,1,0,0,1,0,1,1,0,0,0,0,0,0,0,0,0]⟩
theorem nestingLookup231 : projections[231]! = nestingProjection231 := by
  rw [projections_lookup]
  rfl
def nestingEntries231 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else (if n < 3 then 0 else 1)) else (if n < 6 then (if n < 5 then 0 else 1) else (if n < 7 then 1 else 0))) else 0) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 4 else 0)) else 0) else (if n < 28 then (if n < 26 then (if n < 25 then 1 else 0) else (if n < 27 then 0 else 1)) else (if n < 30 then (if n < 29 then 0 else 1) else (if n < 31 then 1 else 0))))) else (if n < 48 then (if n < 40 then 0 else (if n < 44 then (if n < 42 then (if n < 41 then 1 else 0) else (if n < 43 then 0 else 1)) else (if n < 46 then (if n < 45 then 0 else 1) else (if n < 47 then 1 else 0)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 1 else 0) else (if n < 51 then 0 else 1)) else (if n < 54 then (if n < 53 then 0 else 1) else (if n < 55 then 1 else 0))) else 0))) else 0
theorem nestingEntries_eq231 (n : Nat) :
    nestingProjection231.numerator[n]! = nestingEntries231 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries231, if_neg (by omega : ¬ n < 64)]

def nestingProjection232 : Projection := ⟨4,2,#[1,0,0,-1,0,-1,1,0,0,0,0,0,0,0,0,0,0,0,4,0,0,0,0,0,-1,0,0,1,0,1,-1,0,0,0,0,0,0,0,0,0,-1,0,0,1,0,1,-1,0,1,0,0,-1,0,-1,1,0,0,0,0,0,0,0,0,0]⟩
theorem nestingLookup232 : projections[232]! = nestingProjection232 := by
  rw [projections_lookup]
  rfl
def nestingEntries232 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else (if n < 3 then 0 else (-1))) else (if n < 6 then (if n < 5 then 0 else (-1)) else (if n < 7 then 1 else 0))) else 0) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 4 else 0)) else 0) else (if n < 28 then (if n < 26 then (if n < 25 then (-1) else 0) else (if n < 27 then 0 else 1)) else (if n < 30 then (if n < 29 then 0 else 1) else (if n < 31 then (-1) else 0))))) else (if n < 48 then (if n < 40 then 0 else (if n < 44 then (if n < 42 then (if n < 41 then (-1) else 0) else (if n < 43 then 0 else 1)) else (if n < 46 then (if n < 45 then 0 else 1) else (if n < 47 then (-1) else 0)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 1 else 0) else (if n < 51 then 0 else (-1))) else (if n < 54 then (if n < 53 then 0 else (-1)) else (if n < 55 then 1 else 0))) else 0))) else 0
theorem nestingEntries_eq232 (n : Nat) :
    nestingProjection232.numerator[n]! = nestingEntries232 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries232, if_neg (by omega : ¬ n < 64)]

def nestingProjection233 : Projection := ⟨4,2,#[1,0,0,1,0,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,1,0,1,1,0,0,0,0,0,4,0,0,0,1,0,0,1,0,1,1,0,1,0,0,1,0,1,1,0,0,0,0,0,0,0,0,0]⟩
theorem nestingLookup233 : projections[233]! = nestingProjection233 := by
  rw [projections_lookup]
  rfl
def nestingEntries233 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else (if n < 3 then 0 else 1)) else (if n < 6 then (if n < 5 then 0 else 1) else (if n < 7 then 1 else 0))) else 0) else (if n < 24 then 0 else (if n < 28 then (if n < 26 then (if n < 25 then 1 else 0) else (if n < 27 then 0 else 1)) else (if n < 30 then (if n < 29 then 0 else 1) else (if n < 31 then 1 else 0))))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 4 else 0) else 0)) else (if n < 44 then (if n < 42 then (if n < 41 then 1 else 0) else (if n < 43 then 0 else 1)) else (if n < 46 then (if n < 45 then 0 else 1) else (if n < 47 then 1 else 0)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 1 else 0) else (if n < 51 then 0 else 1)) else (if n < 54 then (if n < 53 then 0 else 1) else (if n < 55 then 1 else 0))) else 0))) else 0
theorem nestingEntries_eq233 (n : Nat) :
    nestingProjection233.numerator[n]! = nestingEntries233 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries233, if_neg (by omega : ¬ n < 64)]

def nestingProjection234 : Projection := ⟨4,2,#[1,0,0,-1,0,-1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,0,0,1,0,1,-1,0,0,0,0,0,4,0,0,0,-1,0,0,1,0,1,-1,0,1,0,0,-1,0,-1,1,0,0,0,0,0,0,0,0,0]⟩
theorem nestingLookup234 : projections[234]! = nestingProjection234 := by
  rw [projections_lookup]
  rfl
def nestingEntries234 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else (if n < 3 then 0 else (-1))) else (if n < 6 then (if n < 5 then 0 else (-1)) else (if n < 7 then 1 else 0))) else 0) else (if n < 24 then 0 else (if n < 28 then (if n < 26 then (if n < 25 then (-1) else 0) else (if n < 27 then 0 else 1)) else (if n < 30 then (if n < 29 then 0 else 1) else (if n < 31 then (-1) else 0))))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 4 else 0) else 0)) else (if n < 44 then (if n < 42 then (if n < 41 then (-1) else 0) else (if n < 43 then 0 else 1)) else (if n < 46 then (if n < 45 then 0 else 1) else (if n < 47 then (-1) else 0)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 1 else 0) else (if n < 51 then 0 else (-1))) else (if n < 54 then (if n < 53 then 0 else (-1)) else (if n < 55 then 1 else 0))) else 0))) else 0
theorem nestingEntries_eq234 (n : Nat) :
    nestingProjection234.numerator[n]! = nestingEntries234 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries234, if_neg (by omega : ¬ n < 64)]

def nestingProjection235 : Projection := ⟨2,2,#[1,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,1,0,0,1,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0]⟩
theorem nestingLookup235 : projections[235]! = nestingProjection235 := by
  rw [projections_lookup]
  rfl
def nestingEntries235 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else 0) else (if n < 6 then 0 else (if n < 7 then 1 else 0))) else 0) else (if n < 24 then 0 else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 1)) else (if n < 30 then (if n < 29 then 0 else 1) else 0)))) else (if n < 48 then (if n < 40 then 0 else (if n < 44 then (if n < 42 then 0 else (if n < 43 then 0 else 1)) else (if n < 46 then (if n < 45 then 0 else 1) else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 1 else 0) else 0) else (if n < 54 then 0 else (if n < 55 then 1 else 0))) else 0))) else 0
theorem nestingEntries_eq235 (n : Nat) :
    nestingProjection235.numerator[n]! = nestingEntries235 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries235, if_neg (by omega : ¬ n < 64)]

def nestingProjection236 : Projection := ⟨2,2,#[1,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,1,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,1,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0]⟩
theorem nestingLookup236 : projections[236]! = nestingProjection236 := by
  rw [projections_lookup]
  rfl
def nestingEntries236 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else 0) else (if n < 6 then 0 else (if n < 7 then 1 else 0))) else 0) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 1 else 0)) else (if n < 22 then (if n < 21 then 1 else 0) else 0)) else 0)) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then 0 else (if n < 35 then 1 else 0)) else (if n < 38 then (if n < 37 then 1 else 0) else 0)) else 0) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 1 else 0) else 0) else (if n < 54 then 0 else (if n < 55 then 1 else 0))) else 0))) else 0
theorem nestingEntries_eq236 (n : Nat) :
    nestingProjection236.numerator[n]! = nestingEntries236 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries236, if_neg (by omega : ¬ n < 64)]

def nestingProjection237 : Projection := ⟨4,2,#[1,0,1,0,1,0,1,0,0,0,0,0,0,0,0,0,1,0,2,1,0,1,1,0,0,0,1,1,-1,1,0,0,1,0,0,-1,2,-1,1,0,0,0,1,1,-1,1,0,0,1,0,1,0,1,0,1,0,0,0,0,0,0,0,0,0]⟩
theorem nestingLookup237 : projections[237]! = nestingProjection237 := by
  rw [projections_lookup]
  rfl
def nestingEntries237 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else (if n < 3 then 1 else 0)) else (if n < 6 then (if n < 5 then 1 else 0) else (if n < 7 then 1 else 0))) else 0) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 1 else 0) else (if n < 19 then 2 else 1)) else (if n < 22 then (if n < 21 then 0 else 1) else (if n < 23 then 1 else 0))) else (if n < 28 then (if n < 26 then 0 else 1) else (if n < 30 then (if n < 29 then (-1) else 1) else 0)))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 1 else 0) else (if n < 35 then 0 else (-1))) else (if n < 38 then (if n < 37 then 2 else (-1)) else (if n < 39 then 1 else 0))) else (if n < 44 then (if n < 42 then 0 else 1) else (if n < 46 then (if n < 45 then (-1) else 1) else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 1 else 0) else (if n < 51 then 1 else 0)) else (if n < 54 then (if n < 53 then 1 else 0) else (if n < 55 then 1 else 0))) else 0))) else 0
theorem nestingEntries_eq237 (n : Nat) :
    nestingProjection237.numerator[n]! = nestingEntries237 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries237, if_neg (by omega : ¬ n < 64)]

def nestingProjection238 : Projection := ⟨4,2,#[1,0,1,0,1,0,1,0,0,0,0,0,0,0,0,0,1,0,2,-1,0,-1,1,0,0,0,-1,1,1,1,0,0,1,0,0,1,2,1,1,0,0,0,-1,1,1,1,0,0,1,0,1,0,1,0,1,0,0,0,0,0,0,0,0,0]⟩
theorem nestingLookup238 : projections[238]! = nestingProjection238 := by
  rw [projections_lookup]
  rfl
def nestingEntries238 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else (if n < 3 then 1 else 0)) else (if n < 6 then (if n < 5 then 1 else 0) else (if n < 7 then 1 else 0))) else 0) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 1 else 0) else (if n < 19 then 2 else (-1))) else (if n < 22 then (if n < 21 then 0 else (-1)) else (if n < 23 then 1 else 0))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then (-1) else 1)) else (if n < 30 then 1 else 0)))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 1 else 0) else (if n < 35 then 0 else 1)) else (if n < 38 then (if n < 37 then 2 else 1) else (if n < 39 then 1 else 0))) else (if n < 44 then (if n < 42 then 0 else (if n < 43 then (-1) else 1)) else (if n < 46 then 1 else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 1 else 0) else (if n < 51 then 1 else 0)) else (if n < 54 then (if n < 53 then 1 else 0) else (if n < 55 then 1 else 0))) else 0))) else 0
theorem nestingEntries_eq238 (n : Nat) :
    nestingProjection238.numerator[n]! = nestingEntries238 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries238, if_neg (by omega : ¬ n < 64)]

def nestingProjection239 : Projection := ⟨4,2,#[1,0,-1,0,-1,0,1,0,0,0,0,0,0,0,0,0,-1,0,2,1,0,1,-1,0,0,0,1,1,-1,1,0,0,-1,0,0,-1,2,-1,-1,0,0,0,1,1,-1,1,0,0,1,0,-1,0,-1,0,1,0,0,0,0,0,0,0,0,0]⟩
theorem nestingLookup239 : projections[239]! = nestingProjection239 := by
  rw [projections_lookup]
  rfl
def nestingEntries239 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else (if n < 3 then (-1) else 0)) else (if n < 6 then (if n < 5 then (-1) else 0) else (if n < 7 then 1 else 0))) else 0) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then (-1) else 0) else (if n < 19 then 2 else 1)) else (if n < 22 then (if n < 21 then 0 else 1) else (if n < 23 then (-1) else 0))) else (if n < 28 then (if n < 26 then 0 else 1) else (if n < 30 then (if n < 29 then (-1) else 1) else 0)))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then (-1) else 0) else (if n < 35 then 0 else (-1))) else (if n < 38 then (if n < 37 then 2 else (-1)) else (if n < 39 then (-1) else 0))) else (if n < 44 then (if n < 42 then 0 else 1) else (if n < 46 then (if n < 45 then (-1) else 1) else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 1 else 0) else (if n < 51 then (-1) else 0)) else (if n < 54 then (if n < 53 then (-1) else 0) else (if n < 55 then 1 else 0))) else 0))) else 0
theorem nestingEntries_eq239 (n : Nat) :
    nestingProjection239.numerator[n]! = nestingEntries239 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries239, if_neg (by omega : ¬ n < 64)]

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def nestingProjection240 : Projection := ⟨4,2,#[1,0,-1,0,-1,0,1,0,0,0,0,0,0,0,0,0,-1,0,2,-1,0,-1,-1,0,0,0,-1,1,1,1,0,0,-1,0,0,1,2,1,-1,0,0,0,-1,1,1,1,0,0,1,0,-1,0,-1,0,1,0,0,0,0,0,0,0,0,0]⟩
theorem nestingLookup240 : projections[240]! = nestingProjection240 := by
  rw [projections_lookup]
  rfl
def nestingEntries240 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else (if n < 3 then (-1) else 0)) else (if n < 6 then (if n < 5 then (-1) else 0) else (if n < 7 then 1 else 0))) else 0) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then (-1) else 0) else (if n < 19 then 2 else (-1))) else (if n < 22 then (if n < 21 then 0 else (-1)) else (if n < 23 then (-1) else 0))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then (-1) else 1)) else (if n < 30 then 1 else 0)))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then (-1) else 0) else (if n < 35 then 0 else 1)) else (if n < 38 then (if n < 37 then 2 else 1) else (if n < 39 then (-1) else 0))) else (if n < 44 then (if n < 42 then 0 else (if n < 43 then (-1) else 1)) else (if n < 46 then 1 else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 1 else 0) else (if n < 51 then (-1) else 0)) else (if n < 54 then (if n < 53 then (-1) else 0) else (if n < 55 then 1 else 0))) else 0))) else 0
theorem nestingEntries_eq240 (n : Nat) :
    nestingProjection240.numerator[n]! = nestingEntries240 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries240, if_neg (by omega : ¬ n < 64)]

def nestingProjection241 : Projection := ⟨2,2,#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,-1,0,0,0,0,0,0,1,0,1,0,0,0,0,-1,0,1,0,0,0,0,0,0,1,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]⟩
theorem nestingLookup241 : projections[241]! = nestingProjection241 := by
  rw [projections_lookup]
  rfl
def nestingEntries241 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then 0 else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 1 else 0)) else (if n < 22 then (if n < 21 then (-1) else 0) else 0)) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 1)) else (if n < 30 then (if n < 29 then 0 else 1) else 0)))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then 0 else (if n < 35 then (-1) else 0)) else (if n < 38 then (if n < 37 then 1 else 0) else 0)) else (if n < 44 then (if n < 42 then 0 else (if n < 43 then 0 else 1)) else (if n < 46 then (if n < 45 then 0 else 1) else 0))) else 0)) else 0
theorem nestingEntries_eq241 (n : Nat) :
    nestingProjection241.numerator[n]! = nestingEntries241 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries241, if_neg (by omega : ¬ n < 64)]

def nestingProjection242 : Projection := ⟨2,2,#[1,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,1,0,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,0,1,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0]⟩
theorem nestingLookup242 : projections[242]! = nestingProjection242 := by
  rw [projections_lookup]
  rfl
def nestingEntries242 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else 0) else (if n < 6 then 0 else (if n < 7 then 1 else 0))) else 0) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 1 else 0)) else (if n < 22 then (if n < 21 then (-1) else 0) else 0)) else 0)) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then 0 else (if n < 35 then (-1) else 0)) else (if n < 38 then (if n < 37 then 1 else 0) else 0)) else 0) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 1 else 0) else 0) else (if n < 54 then 0 else (if n < 55 then 1 else 0))) else 0))) else 0
theorem nestingEntries_eq242 (n : Nat) :
    nestingProjection242.numerator[n]! = nestingEntries242 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries242, if_neg (by omega : ¬ n < 64)]

def nestingProjection243 : Projection := ⟨4,2,#[1,0,1,0,-1,0,1,0,0,0,0,0,0,0,0,0,1,0,2,1,0,1,1,0,0,0,1,1,1,1,0,0,-1,0,0,1,2,1,-1,0,0,0,1,1,1,1,0,0,1,0,1,0,-1,0,1,0,0,0,0,0,0,0,0,0]⟩
theorem nestingLookup243 : projections[243]! = nestingProjection243 := by
  rw [projections_lookup]
  rfl
def nestingEntries243 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else (if n < 3 then 1 else 0)) else (if n < 6 then (if n < 5 then (-1) else 0) else (if n < 7 then 1 else 0))) else 0) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 1 else 0) else (if n < 19 then 2 else 1)) else (if n < 22 then (if n < 21 then 0 else 1) else (if n < 23 then 1 else 0))) else (if n < 28 then (if n < 26 then 0 else 1) else (if n < 30 then 1 else 0)))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then (-1) else 0) else (if n < 35 then 0 else 1)) else (if n < 38 then (if n < 37 then 2 else 1) else (if n < 39 then (-1) else 0))) else (if n < 44 then (if n < 42 then 0 else 1) else (if n < 46 then 1 else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 1 else 0) else (if n < 51 then 1 else 0)) else (if n < 54 then (if n < 53 then (-1) else 0) else (if n < 55 then 1 else 0))) else 0))) else 0
theorem nestingEntries_eq243 (n : Nat) :
    nestingProjection243.numerator[n]! = nestingEntries243 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries243, if_neg (by omega : ¬ n < 64)]

def nestingProjection244 : Projection := ⟨4,2,#[1,0,1,0,-1,0,1,0,0,0,0,0,0,0,0,0,1,0,2,-1,0,-1,1,0,0,0,-1,1,-1,1,0,0,-1,0,0,-1,2,-1,-1,0,0,0,-1,1,-1,1,0,0,1,0,1,0,-1,0,1,0,0,0,0,0,0,0,0,0]⟩
theorem nestingLookup244 : projections[244]! = nestingProjection244 := by
  rw [projections_lookup]
  rfl
def nestingEntries244 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else (if n < 3 then 1 else 0)) else (if n < 6 then (if n < 5 then (-1) else 0) else (if n < 7 then 1 else 0))) else 0) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 1 else 0) else (if n < 19 then 2 else (-1))) else (if n < 22 then (if n < 21 then 0 else (-1)) else (if n < 23 then 1 else 0))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then (-1) else 1)) else (if n < 30 then (if n < 29 then (-1) else 1) else 0)))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then (-1) else 0) else (if n < 35 then 0 else (-1))) else (if n < 38 then (if n < 37 then 2 else (-1)) else (if n < 39 then (-1) else 0))) else (if n < 44 then (if n < 42 then 0 else (if n < 43 then (-1) else 1)) else (if n < 46 then (if n < 45 then (-1) else 1) else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 1 else 0) else (if n < 51 then 1 else 0)) else (if n < 54 then (if n < 53 then (-1) else 0) else (if n < 55 then 1 else 0))) else 0))) else 0
theorem nestingEntries_eq244 (n : Nat) :
    nestingProjection244.numerator[n]! = nestingEntries244 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries244, if_neg (by omega : ¬ n < 64)]

def nestingProjection245 : Projection := ⟨4,2,#[1,0,-1,0,1,0,1,0,0,0,0,0,0,0,0,0,-1,0,2,1,0,1,-1,0,0,0,1,1,1,1,0,0,1,0,0,1,2,1,1,0,0,0,1,1,1,1,0,0,1,0,-1,0,1,0,1,0,0,0,0,0,0,0,0,0]⟩
theorem nestingLookup245 : projections[245]! = nestingProjection245 := by
  rw [projections_lookup]
  rfl
def nestingEntries245 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else (if n < 3 then (-1) else 0)) else (if n < 6 then (if n < 5 then 1 else 0) else (if n < 7 then 1 else 0))) else 0) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then (-1) else 0) else (if n < 19 then 2 else 1)) else (if n < 22 then (if n < 21 then 0 else 1) else (if n < 23 then (-1) else 0))) else (if n < 28 then (if n < 26 then 0 else 1) else (if n < 30 then 1 else 0)))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 1 else 0) else (if n < 35 then 0 else 1)) else (if n < 38 then (if n < 37 then 2 else 1) else (if n < 39 then 1 else 0))) else (if n < 44 then (if n < 42 then 0 else 1) else (if n < 46 then 1 else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 1 else 0) else (if n < 51 then (-1) else 0)) else (if n < 54 then (if n < 53 then 1 else 0) else (if n < 55 then 1 else 0))) else 0))) else 0
theorem nestingEntries_eq245 (n : Nat) :
    nestingProjection245.numerator[n]! = nestingEntries245 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries245, if_neg (by omega : ¬ n < 64)]

def nestingProjection246 : Projection := ⟨4,2,#[1,0,-1,0,1,0,1,0,0,0,0,0,0,0,0,0,-1,0,2,-1,0,-1,-1,0,0,0,-1,1,-1,1,0,0,1,0,0,-1,2,-1,1,0,0,0,-1,1,-1,1,0,0,1,0,-1,0,1,0,1,0,0,0,0,0,0,0,0,0]⟩
theorem nestingLookup246 : projections[246]! = nestingProjection246 := by
  rw [projections_lookup]
  rfl
def nestingEntries246 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else (if n < 3 then (-1) else 0)) else (if n < 6 then (if n < 5 then 1 else 0) else (if n < 7 then 1 else 0))) else 0) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then (-1) else 0) else (if n < 19 then 2 else (-1))) else (if n < 22 then (if n < 21 then 0 else (-1)) else (if n < 23 then (-1) else 0))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then (-1) else 1)) else (if n < 30 then (if n < 29 then (-1) else 1) else 0)))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 1 else 0) else (if n < 35 then 0 else (-1))) else (if n < 38 then (if n < 37 then 2 else (-1)) else (if n < 39 then 1 else 0))) else (if n < 44 then (if n < 42 then 0 else (if n < 43 then (-1) else 1)) else (if n < 46 then (if n < 45 then (-1) else 1) else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 1 else 0) else (if n < 51 then (-1) else 0)) else (if n < 54 then (if n < 53 then 1 else 0) else (if n < 55 then 1 else 0))) else 0))) else 0
theorem nestingEntries_eq246 (n : Nat) :
    nestingProjection246.numerator[n]! = nestingEntries246 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries246, if_neg (by omega : ¬ n < 64)]

def nestingProjection247 : Projection := ⟨2,2,#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,1,0,0,0,0,0,0,1,0,1,0,0,0,0,1,0,1,0,0,0,0,0,0,1,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]⟩
theorem nestingLookup247 : projections[247]! = nestingProjection247 := by
  rw [projections_lookup]
  rfl
def nestingEntries247 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then 0 else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 1 else 0)) else (if n < 22 then (if n < 21 then 1 else 0) else 0)) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 1)) else (if n < 30 then (if n < 29 then 0 else 1) else 0)))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then 0 else (if n < 35 then 1 else 0)) else (if n < 38 then (if n < 37 then 1 else 0) else 0)) else (if n < 44 then (if n < 42 then 0 else (if n < 43 then 0 else 1)) else (if n < 46 then (if n < 45 then 0 else 1) else 0))) else 0)) else 0
theorem nestingEntries_eq247 (n : Nat) :
    nestingProjection247.numerator[n]! = nestingEntries247 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries247, if_neg (by omega : ¬ n < 64)]

def nestingProjection248 : Projection := ⟨2,2,#[0,0,0,0,0,0,0,0,0,1,0,0,1,0,0,0,0,0,1,0,0,0,0,1,0,0,0,0,0,0,0,0,0,1,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,1]⟩
theorem nestingLookup248 : projections[248]! = nestingProjection248 := by
  rw [projections_lookup]
  rfl
def nestingEntries248 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then 0 else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else 0) else (if n < 14 then (if n < 13 then 1 else 0) else 0))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 1 else 0)) else (if n < 22 then 0 else (if n < 23 then 0 else 1))) else 0)) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 0 else 1) else 0) else (if n < 38 then (if n < 37 then 1 else 0) else 0)) else 0) else (if n < 56 then 0 else (if n < 60 then (if n < 58 then 0 else (if n < 59 then 1 else 0)) else (if n < 62 then 0 else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq248 (n : Nat) :
    nestingProjection248.numerator[n]! = nestingEntries248 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries248, if_neg (by omega : ¬ n < 64)]

def nestingProjection249 : Projection := ⟨4,2,#[1,0,0,1,0,-1,1,0,0,1,1,0,1,0,0,1,0,1,1,0,1,0,0,1,1,0,0,1,0,-1,1,0,0,1,1,0,1,0,0,1,-1,0,0,-1,0,1,-1,0,1,0,0,1,0,-1,1,0,0,1,1,0,1,0,0,1]⟩
theorem nestingLookup249 : projections[249]! = nestingProjection249 := by
  rw [projections_lookup]
  rfl
def nestingEntries249 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else (if n < 3 then 0 else 1)) else (if n < 6 then (if n < 5 then 0 else (-1)) else (if n < 7 then 1 else 0))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else (if n < 11 then 1 else 0)) else (if n < 14 then (if n < 13 then 1 else 0) else (if n < 15 then 0 else 1)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 0 else 1) else (if n < 19 then 1 else 0)) else (if n < 22 then (if n < 21 then 1 else 0) else (if n < 23 then 0 else 1))) else (if n < 28 then (if n < 26 then (if n < 25 then 1 else 0) else (if n < 27 then 0 else 1)) else (if n < 30 then (if n < 29 then 0 else (-1)) else (if n < 31 then 1 else 0))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 0 else 1) else (if n < 35 then 1 else 0)) else (if n < 38 then (if n < 37 then 1 else 0) else (if n < 39 then 0 else 1))) else (if n < 44 then (if n < 42 then (if n < 41 then (-1) else 0) else (if n < 43 then 0 else (-1))) else (if n < 46 then (if n < 45 then 0 else 1) else (if n < 47 then (-1) else 0)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 1 else 0) else (if n < 51 then 0 else 1)) else (if n < 54 then (if n < 53 then 0 else (-1)) else (if n < 55 then 1 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then 0 else 1) else (if n < 59 then 1 else 0)) else (if n < 62 then (if n < 61 then 1 else 0) else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq249 (n : Nat) :
    nestingProjection249.numerator[n]! = nestingEntries249 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries249, if_neg (by omega : ¬ n < 64)]

def nestingProjection250 : Projection := ⟨4,2,#[1,0,0,-1,0,-1,-1,0,0,1,1,0,1,0,0,1,0,1,1,0,1,0,0,1,-1,0,0,1,0,1,1,0,0,1,1,0,1,0,0,1,-1,0,0,1,0,1,1,0,-1,0,0,1,0,1,1,0,0,1,1,0,1,0,0,1]⟩
theorem nestingLookup250 : projections[250]! = nestingProjection250 := by
  rw [projections_lookup]
  rfl
def nestingEntries250 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else (if n < 3 then 0 else (-1))) else (if n < 6 then (if n < 5 then 0 else (-1)) else (if n < 7 then (-1) else 0))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else (if n < 11 then 1 else 0)) else (if n < 14 then (if n < 13 then 1 else 0) else (if n < 15 then 0 else 1)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 0 else 1) else (if n < 19 then 1 else 0)) else (if n < 22 then (if n < 21 then 1 else 0) else (if n < 23 then 0 else 1))) else (if n < 28 then (if n < 26 then (if n < 25 then (-1) else 0) else (if n < 27 then 0 else 1)) else (if n < 30 then (if n < 29 then 0 else 1) else (if n < 31 then 1 else 0))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 0 else 1) else (if n < 35 then 1 else 0)) else (if n < 38 then (if n < 37 then 1 else 0) else (if n < 39 then 0 else 1))) else (if n < 44 then (if n < 42 then (if n < 41 then (-1) else 0) else (if n < 43 then 0 else 1)) else (if n < 46 then (if n < 45 then 0 else 1) else (if n < 47 then 1 else 0)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then (-1) else 0) else (if n < 51 then 0 else 1)) else (if n < 54 then (if n < 53 then 0 else 1) else (if n < 55 then 1 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then 0 else 1) else (if n < 59 then 1 else 0)) else (if n < 62 then (if n < 61 then 1 else 0) else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq250 (n : Nat) :
    nestingProjection250.numerator[n]! = nestingEntries250 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries250, if_neg (by omega : ¬ n < 64)]

def nestingProjection251 : Projection := ⟨4,2,#[1,0,0,1,0,-1,1,0,0,1,-1,0,1,0,0,-1,0,-1,1,0,-1,0,0,1,1,0,0,1,0,-1,1,0,0,1,-1,0,1,0,0,-1,-1,0,0,-1,0,1,-1,0,1,0,0,1,0,-1,1,0,0,-1,1,0,-1,0,0,1]⟩
theorem nestingLookup251 : projections[251]! = nestingProjection251 := by
  rw [projections_lookup]
  rfl
def nestingEntries251 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else (if n < 3 then 0 else 1)) else (if n < 6 then (if n < 5 then 0 else (-1)) else (if n < 7 then 1 else 0))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else (if n < 11 then (-1) else 0)) else (if n < 14 then (if n < 13 then 1 else 0) else (if n < 15 then 0 else (-1))))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 0 else (-1)) else (if n < 19 then 1 else 0)) else (if n < 22 then (if n < 21 then (-1) else 0) else (if n < 23 then 0 else 1))) else (if n < 28 then (if n < 26 then (if n < 25 then 1 else 0) else (if n < 27 then 0 else 1)) else (if n < 30 then (if n < 29 then 0 else (-1)) else (if n < 31 then 1 else 0))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 0 else 1) else (if n < 35 then (-1) else 0)) else (if n < 38 then (if n < 37 then 1 else 0) else (if n < 39 then 0 else (-1)))) else (if n < 44 then (if n < 42 then (if n < 41 then (-1) else 0) else (if n < 43 then 0 else (-1))) else (if n < 46 then (if n < 45 then 0 else 1) else (if n < 47 then (-1) else 0)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 1 else 0) else (if n < 51 then 0 else 1)) else (if n < 54 then (if n < 53 then 0 else (-1)) else (if n < 55 then 1 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then 0 else (-1)) else (if n < 59 then 1 else 0)) else (if n < 62 then (if n < 61 then (-1) else 0) else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq251 (n : Nat) :
    nestingProjection251.numerator[n]! = nestingEntries251 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries251, if_neg (by omega : ¬ n < 64)]

def nestingProjection252 : Projection := ⟨4,2,#[1,0,0,-1,0,-1,-1,0,0,1,-1,0,1,0,0,-1,0,-1,1,0,-1,0,0,1,-1,0,0,1,0,1,1,0,0,1,-1,0,1,0,0,-1,-1,0,0,1,0,1,1,0,-1,0,0,1,0,1,1,0,0,-1,1,0,-1,0,0,1]⟩
theorem nestingLookup252 : projections[252]! = nestingProjection252 := by
  rw [projections_lookup]
  rfl
def nestingEntries252 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else (if n < 3 then 0 else (-1))) else (if n < 6 then (if n < 5 then 0 else (-1)) else (if n < 7 then (-1) else 0))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else (if n < 11 then (-1) else 0)) else (if n < 14 then (if n < 13 then 1 else 0) else (if n < 15 then 0 else (-1))))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 0 else (-1)) else (if n < 19 then 1 else 0)) else (if n < 22 then (if n < 21 then (-1) else 0) else (if n < 23 then 0 else 1))) else (if n < 28 then (if n < 26 then (if n < 25 then (-1) else 0) else (if n < 27 then 0 else 1)) else (if n < 30 then (if n < 29 then 0 else 1) else (if n < 31 then 1 else 0))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 0 else 1) else (if n < 35 then (-1) else 0)) else (if n < 38 then (if n < 37 then 1 else 0) else (if n < 39 then 0 else (-1)))) else (if n < 44 then (if n < 42 then (if n < 41 then (-1) else 0) else (if n < 43 then 0 else 1)) else (if n < 46 then (if n < 45 then 0 else 1) else (if n < 47 then 1 else 0)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then (-1) else 0) else (if n < 51 then 0 else 1)) else (if n < 54 then (if n < 53 then 0 else 1) else (if n < 55 then 1 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then 0 else (-1)) else (if n < 59 then 1 else 0)) else (if n < 62 then (if n < 61 then (-1) else 0) else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq252 (n : Nat) :
    nestingProjection252.numerator[n]! = nestingEntries252 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries252, if_neg (by omega : ¬ n < 64)]

def nestingProjection253 : Projection := ⟨2,2,#[1,0,0,0,0,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,1,0,0,0,0,0,0,0,0,0,-1,0,0,0,0,1,0,0,0,0,0,1,0,0,1,0,0,0,0,0,0,0,0,0]⟩
theorem nestingLookup253 : projections[253]! = nestingProjection253 := by
  rw [projections_lookup]
  rfl
def nestingEntries253 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else 0) else (if n < 6 then (if n < 5 then 0 else (-1)) else 0)) else 0) else (if n < 24 then 0 else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 1)) else (if n < 30 then 0 else (if n < 31 then 1 else 0))))) else (if n < 48 then (if n < 40 then 0 else (if n < 44 then (if n < 42 then (if n < 41 then (-1) else 0) else 0) else (if n < 46 then (if n < 45 then 0 else 1) else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then 0 else (if n < 51 then 0 else 1)) else (if n < 54 then 0 else (if n < 55 then 1 else 0))) else 0))) else 0
theorem nestingEntries_eq253 (n : Nat) :
    nestingProjection253.numerator[n]! = nestingEntries253 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries253, if_neg (by omega : ¬ n < 64)]

def nestingProjection254 : Projection := ⟨2,2,#[1,0,0,0,0,-1,0,0,0,1,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,1,0,0,0,-1,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]⟩
theorem nestingLookup254 : projections[254]! = nestingProjection254 := by
  rw [projections_lookup]
  rfl
def nestingEntries254 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else 0) else (if n < 6 then (if n < 5 then 0 else (-1)) else 0)) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else 0) else (if n < 14 then (if n < 13 then 1 else 0) else 0))) else 0) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 0 else 1) else 0) else (if n < 38 then (if n < 37 then 1 else 0) else 0)) else (if n < 44 then (if n < 42 then (if n < 41 then (-1) else 0) else 0) else (if n < 46 then (if n < 45 then 0 else 1) else 0))) else 0)) else 0
theorem nestingEntries_eq254 (n : Nat) :
    nestingProjection254.numerator[n]! = nestingEntries254 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries254, if_neg (by omega : ¬ n < 64)]

def nestingProjection255 : Projection := ⟨4,2,#[1,1,0,0,1,-1,0,0,1,1,0,0,1,-1,0,0,0,0,1,1,0,0,1,1,0,0,1,1,0,0,1,1,1,1,0,0,1,-1,0,0,-1,-1,0,0,-1,1,0,0,0,0,1,1,0,0,1,1,0,0,1,1,0,0,1,1]⟩
theorem nestingLookup255 : projections[255]! = nestingProjection255 := by
  rw [projections_lookup]
  rfl
def nestingEntries255 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then 1 else 0) else (if n < 6 then (if n < 5 then 1 else (-1)) else 0)) else (if n < 12 then (if n < 10 then 1 else 0) else (if n < 14 then (if n < 13 then 1 else (-1)) else 0))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else 1) else (if n < 22 then 0 else 1)) else (if n < 28 then (if n < 26 then 0 else 1) else (if n < 30 then 0 else 1)))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then 1 else 0) else (if n < 38 then (if n < 37 then 1 else (-1)) else 0)) else (if n < 44 then (if n < 42 then (-1) else 0) else (if n < 46 then (if n < 45 then (-1) else 1) else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then 0 else 1) else (if n < 54 then 0 else 1)) else (if n < 60 then (if n < 58 then 0 else 1) else (if n < 62 then 0 else 1))))) else 0
theorem nestingEntries_eq255 (n : Nat) :
    nestingProjection255.numerator[n]! = nestingEntries255 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries255, if_neg (by omega : ¬ n < 64)]

end CSL.Construction.PhysicalFramePaths


