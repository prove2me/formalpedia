-- Prove2me | Definitions.Def_CSL_Generated_FiniteCircuit_FramePathChecks_Entries_Batch02
-- name    : CSL_Generated_FiniteCircuit_FramePathChecks_Entries_Batch02
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T13:38:44.048236+00:00
-- url     : https://prove2.me/theorems/e7672b8a-8c93-4f83-969b-d7a429eaa99e
-- title:
--   Coded sorting library: Generated / FiniteCircuit / FramePathChecks / Entries / Batch02
-- statement:
--   Module `CodedSorting.Generated.FiniteCircuit.FramePathChecks.Entries.Batch02` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   Generated physical-frame checks. Uncompiled until a build record exists.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Generated.FiniteCircuit.FramePathChecks.Entries.Batch02

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Generated_FiniteCircuit_FramePathChecks_FunctionBase

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def nestingProjection256 : Projection := ⟨4,2,#[1,1,0,0,1,-1,0,0,1,1,0,0,1,-1,0,0,0,0,1,-1,0,0,-1,1,0,0,-1,1,0,0,1,-1,1,1,0,0,1,-1,0,0,-1,-1,0,0,-1,1,0,0,0,0,-1,1,0,0,1,-1,0,0,1,-1,0,0,-1,1]⟩
theorem nestingLookup256 : projections[256]! = nestingProjection256 := by
  rw [projections_lookup]
  rfl
def nestingEntries256 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then 1 else 0) else (if n < 6 then (if n < 5 then 1 else (-1)) else 0)) else (if n < 12 then (if n < 10 then 1 else 0) else (if n < 14 then (if n < 13 then 1 else (-1)) else 0))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 1 else (-1))) else (if n < 22 then 0 else (if n < 23 then (-1) else 1))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then (-1) else 1)) else (if n < 30 then 0 else (if n < 31 then 1 else (-1)))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then 1 else 0) else (if n < 38 then (if n < 37 then 1 else (-1)) else 0)) else (if n < 44 then (if n < 42 then (-1) else 0) else (if n < 46 then (if n < 45 then (-1) else 1) else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then 0 else (if n < 51 then (-1) else 1)) else (if n < 54 then 0 else (if n < 55 then 1 else (-1)))) else (if n < 60 then (if n < 58 then 0 else (if n < 59 then 1 else (-1))) else (if n < 62 then 0 else (if n < 63 then (-1) else 1)))))) else 0
theorem nestingEntries_eq256 (n : Nat) :
    nestingProjection256.numerator[n]! = nestingEntries256 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries256, if_neg (by omega : ¬ n < 64)]

def nestingProjection257 : Projection := ⟨4,2,#[1,-1,0,0,-1,-1,0,0,-1,1,0,0,1,1,0,0,0,0,1,1,0,0,1,1,0,0,1,1,0,0,1,1,-1,1,0,0,1,1,0,0,-1,1,0,0,1,1,0,0,0,0,1,1,0,0,1,1,0,0,1,1,0,0,1,1]⟩
theorem nestingLookup257 : projections[257]! = nestingProjection257 := by
  rw [projections_lookup]
  rfl
def nestingEntries257 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else (-1)) else 0) else (if n < 6 then (-1) else 0)) else (if n < 12 then (if n < 10 then (if n < 9 then (-1) else 1) else 0) else (if n < 14 then 1 else 0))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else 1) else (if n < 22 then 0 else 1)) else (if n < 28 then (if n < 26 then 0 else 1) else (if n < 30 then 0 else 1)))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then (-1) else 1) else 0) else (if n < 38 then 1 else 0)) else (if n < 44 then (if n < 42 then (if n < 41 then (-1) else 1) else 0) else (if n < 46 then 1 else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then 0 else 1) else (if n < 54 then 0 else 1)) else (if n < 60 then (if n < 58 then 0 else 1) else (if n < 62 then 0 else 1))))) else 0
theorem nestingEntries_eq257 (n : Nat) :
    nestingProjection257.numerator[n]! = nestingEntries257 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries257, if_neg (by omega : ¬ n < 64)]

def nestingProjection258 : Projection := ⟨4,2,#[1,-1,0,0,-1,-1,0,0,-1,1,0,0,1,1,0,0,0,0,1,-1,0,0,-1,1,0,0,-1,1,0,0,1,-1,-1,1,0,0,1,1,0,0,-1,1,0,0,1,1,0,0,0,0,-1,1,0,0,1,-1,0,0,1,-1,0,0,-1,1]⟩
theorem nestingLookup258 : projections[258]! = nestingProjection258 := by
  rw [projections_lookup]
  rfl
def nestingEntries258 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else (-1)) else 0) else (if n < 6 then (-1) else 0)) else (if n < 12 then (if n < 10 then (if n < 9 then (-1) else 1) else 0) else (if n < 14 then 1 else 0))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 1 else (-1))) else (if n < 22 then 0 else (if n < 23 then (-1) else 1))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then (-1) else 1)) else (if n < 30 then 0 else (if n < 31 then 1 else (-1)))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then (-1) else 1) else 0) else (if n < 38 then 1 else 0)) else (if n < 44 then (if n < 42 then (if n < 41 then (-1) else 1) else 0) else (if n < 46 then 1 else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then 0 else (if n < 51 then (-1) else 1)) else (if n < 54 then 0 else (if n < 55 then 1 else (-1)))) else (if n < 60 then (if n < 58 then 0 else (if n < 59 then 1 else (-1))) else (if n < 62 then 0 else (if n < 63 then (-1) else 1)))))) else 0
theorem nestingEntries_eq258 (n : Nat) :
    nestingProjection258.numerator[n]! = nestingEntries258 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries258, if_neg (by omega : ¬ n < 64)]

def nestingProjection259 : Projection := ⟨2,2,#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,1,0,0,0,1,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,1,0,0,0,1,0,0,0,0,1]⟩
theorem nestingLookup259 : projections[259]! = nestingProjection259 := by
  rw [projections_lookup]
  rfl
def nestingEntries259 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then 0 else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 1 else 0)) else (if n < 22 then 0 else (if n < 23 then 0 else 1))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 1)) else (if n < 30 then 0 else (if n < 31 then 1 else 0))))) else (if n < 48 then 0 else (if n < 56 then (if n < 52 then (if n < 50 then 0 else (if n < 51 then 0 else 1)) else (if n < 54 then 0 else (if n < 55 then 1 else 0))) else (if n < 60 then (if n < 58 then 0 else (if n < 59 then 1 else 0)) else (if n < 62 then 0 else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq259 (n : Nat) :
    nestingProjection259.numerator[n]! = nestingEntries259 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries259, if_neg (by omega : ¬ n < 64)]

def nestingProjection260 : Projection := ⟨2,2,#[1,0,0,0,0,-1,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,1]⟩
theorem nestingLookup260 : projections[260]! = nestingProjection260 := by
  rw [projections_lookup]
  rfl
def nestingEntries260 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else 0) else (if n < 6 then (if n < 5 then 0 else (-1)) else 0)) else 0) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 1 else 0)) else (if n < 22 then 0 else (if n < 23 then 0 else 1))) else 0)) else (if n < 48 then (if n < 40 then 0 else (if n < 44 then (if n < 42 then (if n < 41 then (-1) else 0) else 0) else (if n < 46 then (if n < 45 then 0 else 1) else 0))) else (if n < 56 then 0 else (if n < 60 then (if n < 58 then 0 else (if n < 59 then 1 else 0)) else (if n < 62 then 0 else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq260 (n : Nat) :
    nestingProjection260.numerator[n]! = nestingEntries260 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries260, if_neg (by omega : ¬ n < 64)]

def nestingProjection261 : Projection := ⟨4,2,#[1,0,1,0,0,-1,0,1,0,1,0,1,1,0,1,0,1,0,1,0,0,-1,0,1,0,1,0,1,1,0,1,0,0,1,0,1,1,0,1,0,-1,0,-1,0,0,1,0,-1,0,1,0,1,1,0,1,0,1,0,1,0,0,-1,0,1]⟩
theorem nestingLookup261 : projections[261]! = nestingProjection261 := by
  rw [projections_lookup]
  rfl
def nestingEntries261 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else (if n < 3 then 1 else 0)) else (if n < 6 then (if n < 5 then 0 else (-1)) else (if n < 7 then 0 else 1))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else (if n < 11 then 0 else 1)) else (if n < 14 then (if n < 13 then 1 else 0) else (if n < 15 then 1 else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 1 else 0) else (if n < 19 then 1 else 0)) else (if n < 22 then (if n < 21 then 0 else (-1)) else (if n < 23 then 0 else 1))) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else 1) else (if n < 27 then 0 else 1)) else (if n < 30 then (if n < 29 then 1 else 0) else (if n < 31 then 1 else 0))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 0 else 1) else (if n < 35 then 0 else 1)) else (if n < 38 then (if n < 37 then 1 else 0) else (if n < 39 then 1 else 0))) else (if n < 44 then (if n < 42 then (if n < 41 then (-1) else 0) else (if n < 43 then (-1) else 0)) else (if n < 46 then (if n < 45 then 0 else 1) else (if n < 47 then 0 else (-1))))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else 1) else (if n < 51 then 0 else 1)) else (if n < 54 then (if n < 53 then 1 else 0) else (if n < 55 then 1 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then 1 else 0) else (if n < 59 then 1 else 0)) else (if n < 62 then (if n < 61 then 0 else (-1)) else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq261 (n : Nat) :
    nestingProjection261.numerator[n]! = nestingEntries261 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries261, if_neg (by omega : ¬ n < 64)]

def nestingProjection262 : Projection := ⟨4,2,#[1,0,1,0,0,-1,0,1,0,1,0,-1,1,0,-1,0,1,0,1,0,0,-1,0,1,0,-1,0,1,-1,0,1,0,0,1,0,-1,1,0,-1,0,-1,0,-1,0,0,1,0,-1,0,-1,0,1,-1,0,1,0,1,0,1,0,0,-1,0,1]⟩
theorem nestingLookup262 : projections[262]! = nestingProjection262 := by
  rw [projections_lookup]
  rfl
def nestingEntries262 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else (if n < 3 then 1 else 0)) else (if n < 6 then (if n < 5 then 0 else (-1)) else (if n < 7 then 0 else 1))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else (if n < 11 then 0 else (-1))) else (if n < 14 then (if n < 13 then 1 else 0) else (if n < 15 then (-1) else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 1 else 0) else (if n < 19 then 1 else 0)) else (if n < 22 then (if n < 21 then 0 else (-1)) else (if n < 23 then 0 else 1))) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else (-1)) else (if n < 27 then 0 else 1)) else (if n < 30 then (if n < 29 then (-1) else 0) else (if n < 31 then 1 else 0))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 0 else 1) else (if n < 35 then 0 else (-1))) else (if n < 38 then (if n < 37 then 1 else 0) else (if n < 39 then (-1) else 0))) else (if n < 44 then (if n < 42 then (if n < 41 then (-1) else 0) else (if n < 43 then (-1) else 0)) else (if n < 46 then (if n < 45 then 0 else 1) else (if n < 47 then 0 else (-1))))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else (-1)) else (if n < 51 then 0 else 1)) else (if n < 54 then (if n < 53 then (-1) else 0) else (if n < 55 then 1 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then 1 else 0) else (if n < 59 then 1 else 0)) else (if n < 62 then (if n < 61 then 0 else (-1)) else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq262 (n : Nat) :
    nestingProjection262.numerator[n]! = nestingEntries262 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries262, if_neg (by omega : ¬ n < 64)]

def nestingProjection263 : Projection := ⟨4,2,#[1,0,-1,0,0,-1,0,-1,0,1,0,1,1,0,1,0,-1,0,1,0,0,1,0,1,0,1,0,1,1,0,1,0,0,1,0,1,1,0,1,0,-1,0,1,0,0,1,0,1,0,1,0,1,1,0,1,0,-1,0,1,0,0,1,0,1]⟩
theorem nestingLookup263 : projections[263]! = nestingProjection263 := by
  rw [projections_lookup]
  rfl
def nestingEntries263 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else (if n < 3 then (-1) else 0)) else (if n < 6 then (if n < 5 then 0 else (-1)) else (if n < 7 then 0 else (-1)))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else (if n < 11 then 0 else 1)) else (if n < 14 then (if n < 13 then 1 else 0) else (if n < 15 then 1 else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then (-1) else 0) else (if n < 19 then 1 else 0)) else (if n < 22 then (if n < 21 then 0 else 1) else (if n < 23 then 0 else 1))) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else 1) else (if n < 27 then 0 else 1)) else (if n < 30 then (if n < 29 then 1 else 0) else (if n < 31 then 1 else 0))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 0 else 1) else (if n < 35 then 0 else 1)) else (if n < 38 then (if n < 37 then 1 else 0) else (if n < 39 then 1 else 0))) else (if n < 44 then (if n < 42 then (if n < 41 then (-1) else 0) else (if n < 43 then 1 else 0)) else (if n < 46 then (if n < 45 then 0 else 1) else (if n < 47 then 0 else 1)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else 1) else (if n < 51 then 0 else 1)) else (if n < 54 then (if n < 53 then 1 else 0) else (if n < 55 then 1 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then (-1) else 0) else (if n < 59 then 1 else 0)) else (if n < 62 then (if n < 61 then 0 else 1) else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq263 (n : Nat) :
    nestingProjection263.numerator[n]! = nestingEntries263 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries263, if_neg (by omega : ¬ n < 64)]

def nestingProjection264 : Projection := ⟨4,2,#[1,0,-1,0,0,-1,0,-1,0,1,0,-1,1,0,-1,0,-1,0,1,0,0,1,0,1,0,-1,0,1,-1,0,1,0,0,1,0,-1,1,0,-1,0,-1,0,1,0,0,1,0,1,0,-1,0,1,-1,0,1,0,-1,0,1,0,0,1,0,1]⟩
theorem nestingLookup264 : projections[264]! = nestingProjection264 := by
  rw [projections_lookup]
  rfl
def nestingEntries264 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else (if n < 3 then (-1) else 0)) else (if n < 6 then (if n < 5 then 0 else (-1)) else (if n < 7 then 0 else (-1)))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else (if n < 11 then 0 else (-1))) else (if n < 14 then (if n < 13 then 1 else 0) else (if n < 15 then (-1) else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then (-1) else 0) else (if n < 19 then 1 else 0)) else (if n < 22 then (if n < 21 then 0 else 1) else (if n < 23 then 0 else 1))) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else (-1)) else (if n < 27 then 0 else 1)) else (if n < 30 then (if n < 29 then (-1) else 0) else (if n < 31 then 1 else 0))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 0 else 1) else (if n < 35 then 0 else (-1))) else (if n < 38 then (if n < 37 then 1 else 0) else (if n < 39 then (-1) else 0))) else (if n < 44 then (if n < 42 then (if n < 41 then (-1) else 0) else (if n < 43 then 1 else 0)) else (if n < 46 then (if n < 45 then 0 else 1) else (if n < 47 then 0 else 1)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else (-1)) else (if n < 51 then 0 else 1)) else (if n < 54 then (if n < 53 then (-1) else 0) else (if n < 55 then 1 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then (-1) else 0) else (if n < 59 then 1 else 0)) else (if n < 62 then (if n < 61 then 0 else 1) else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq264 (n : Nat) :
    nestingProjection264.numerator[n]! = nestingEntries264 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries264, if_neg (by omega : ¬ n < 64)]

def nestingProjection265 : Projection := ⟨2,2,#[0,0,0,0,0,0,0,0,0,1,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,1,0,0,1,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,1,0,0,0,0,0,0,0,0,0]⟩
theorem nestingLookup265 : projections[265]! = nestingProjection265 := by
  rw [projections_lookup]
  rfl
def nestingEntries265 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then 0 else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else 0) else (if n < 14 then (if n < 13 then 1 else 0) else 0))) else (if n < 24 then 0 else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 1)) else (if n < 30 then 0 else (if n < 31 then 1 else 0))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 0 else 1) else 0) else (if n < 38 then (if n < 37 then 1 else 0) else 0)) else 0) else (if n < 56 then (if n < 52 then (if n < 50 then 0 else (if n < 51 then 0 else 1)) else (if n < 54 then 0 else (if n < 55 then 1 else 0))) else 0))) else 0
theorem nestingEntries_eq265 (n : Nat) :
    nestingProjection265.numerator[n]! = nestingEntries265 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries265, if_neg (by omega : ¬ n < 64)]

def nestingProjection266 : Projection := ⟨1,4,#[0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1]⟩
theorem nestingLookup266 : projections[266]! = nestingProjection266 := by
  rw [projections_lookup]
  rfl
def nestingEntries266 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then 0 else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else 0) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 1 else 0)) else 0) else 0)) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 1 else 0) else 0)) else 0) else (if n < 56 then 0 else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq266 (n : Nat) :
    nestingProjection266.numerator[n]! = nestingEntries266 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries266, if_neg (by omega : ¬ n < 64)]

def nestingProjection267 : Projection := ⟨2,4,#[2,0,0,0,0,0,0,0,0,1,1,0,0,0,0,0,0,1,1,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,1,0,0,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,0,0,1]⟩
theorem nestingLookup267 : projections[267]! = nestingProjection267 := by
  rw [projections_lookup]
  rfl
def nestingEntries267 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 2 else 0) else 0) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else (if n < 11 then 1 else 0)) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 0 else 1) else (if n < 19 then 1 else 0)) else 0) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 2)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 1 else 0) else (if n < 39 then 0 else (-1)))) else 0) else (if n < 56 then 0 else (if n < 60 then 0 else (if n < 62 then (if n < 61 then (-1) else 0) else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq267 (n : Nat) :
    nestingProjection267.numerator[n]! = nestingEntries267 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries267, if_neg (by omega : ¬ n < 64)]

def nestingProjection268 : Projection := ⟨2,4,#[2,0,0,0,0,0,0,0,0,1,0,0,0,0,0,1,0,0,1,0,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,1,0,0,0,0,0,1]⟩
theorem nestingLookup268 : projections[268]! = nestingProjection268 := by
  rw [projections_lookup]
  rfl
def nestingEntries268 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 2 else 0) else 0) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else 0) else (if n < 14 then 0 else (if n < 15 then 0 else 1)))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 1 else 0)) else (if n < 22 then (if n < 21 then (-1) else 0) else 0)) else 0)) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then 0 else (if n < 35 then (-1) else 0)) else (if n < 38 then (if n < 37 then 1 else 0) else 0)) else 0) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 0 else (if n < 55 then 2 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then 0 else 1) else 0) else (if n < 62 then 0 else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq268 (n : Nat) :
    nestingProjection268.numerator[n]! = nestingEntries268 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries268, if_neg (by omega : ¬ n < 64)]

def nestingProjection269 : Projection := ⟨2,4,#[0,0,0,0,0,0,0,0,0,1,0,0,-1,0,0,0,0,0,1,0,0,0,0,1,0,0,0,2,0,0,0,0,0,-1,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,1,0,0,0,0,1]⟩
theorem nestingLookup269 : projections[269]! = nestingProjection269 := by
  rw [projections_lookup]
  rfl
def nestingEntries269 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then 0 else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else 0) else (if n < 14 then (if n < 13 then (-1) else 0) else 0))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 1 else 0)) else (if n < 22 then 0 else (if n < 23 then 0 else 1))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 2)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 0 else (-1)) else 0) else (if n < 38 then (if n < 37 then 1 else 0) else 0)) else 0) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 0 else (if n < 55 then 2 else 0))) else (if n < 60 then (if n < 58 then 0 else (if n < 59 then 1 else 0)) else (if n < 62 then 0 else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq269 (n : Nat) :
    nestingProjection269.numerator[n]! = nestingEntries269 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries269, if_neg (by omega : ¬ n < 64)]

def nestingProjection270 : Projection := ⟨2,4,#[2,0,0,0,0,0,0,0,0,1,0,0,0,0,0,-1,0,0,1,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,-1,0,0,0,0,0,1]⟩
theorem nestingLookup270 : projections[270]! = nestingProjection270 := by
  rw [projections_lookup]
  rfl
def nestingEntries270 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 2 else 0) else 0) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else 0) else (if n < 14 then 0 else (if n < 15 then 0 else (-1))))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 1 else 0)) else (if n < 22 then (if n < 21 then 1 else 0) else 0)) else 0)) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then 0 else (if n < 35 then 1 else 0)) else (if n < 38 then (if n < 37 then 1 else 0) else 0)) else 0) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 0 else (if n < 55 then 2 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then 0 else (-1)) else 0) else (if n < 62 then 0 else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq270 (n : Nat) :
    nestingProjection270.numerator[n]! = nestingEntries270 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries270, if_neg (by omega : ¬ n < 64)]

def nestingProjection271 : Projection := ⟨2,4,#[0,0,0,0,0,0,0,0,0,1,0,0,1,0,0,0,0,0,1,0,0,0,0,-1,0,0,0,2,0,0,0,0,0,1,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,-1,0,0,0,0,1]⟩
theorem nestingLookup271 : projections[271]! = nestingProjection271 := by
  rw [projections_lookup]
  rfl
def nestingEntries271 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then 0 else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else 0) else (if n < 14 then (if n < 13 then 1 else 0) else 0))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 1 else 0)) else (if n < 22 then 0 else (if n < 23 then 0 else (-1)))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 2)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 0 else 1) else 0) else (if n < 38 then (if n < 37 then 1 else 0) else 0)) else 0) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 0 else (if n < 55 then 2 else 0))) else (if n < 60 then (if n < 58 then 0 else (if n < 59 then (-1) else 0)) else (if n < 62 then 0 else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq271 (n : Nat) :
    nestingProjection271.numerator[n]! = nestingEntries271 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries271, if_neg (by omega : ¬ n < 64)]

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def nestingProjection272 : Projection := ⟨2,4,#[2,0,0,0,0,0,0,0,0,1,0,0,-1,0,0,0,0,0,1,0,0,0,0,1,0,0,0,0,0,0,0,0,0,-1,0,0,1,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,1]⟩
theorem nestingLookup272 : projections[272]! = nestingProjection272 := by
  rw [projections_lookup]
  rfl
def nestingEntries272 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 2 else 0) else 0) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else 0) else (if n < 14 then (if n < 13 then (-1) else 0) else 0))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 1 else 0)) else (if n < 22 then 0 else (if n < 23 then 0 else 1))) else 0)) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 0 else (-1)) else 0) else (if n < 38 then (if n < 37 then 1 else 0) else 0)) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 2) else 0))) else (if n < 56 then 0 else (if n < 60 then (if n < 58 then 0 else (if n < 59 then 1 else 0)) else (if n < 62 then 0 else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq272 (n : Nat) :
    nestingProjection272.numerator[n]! = nestingEntries272 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries272, if_neg (by omega : ¬ n < 64)]

def nestingProjection273 : Projection := ⟨2,4,#[0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,1,0,0,1,0,-1,0,0,0,0,0,0,2,0,0,0,0,0,0,-1,0,1,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,1]⟩
theorem nestingLookup273 : projections[273]! = nestingProjection273 := by
  rw [projections_lookup]
  rfl
def nestingEntries273 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then 0 else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else 0) else (if n < 14 then 0 else (if n < 15 then 0 else 1)))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 1 else 0)) else (if n < 22 then (if n < 21 then (-1) else 0) else 0)) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 2)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then 0 else (if n < 35 then (-1) else 0)) else (if n < 38 then (if n < 37 then 1 else 0) else 0)) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 2) else 0))) else (if n < 56 then 0 else (if n < 60 then (if n < 58 then (if n < 57 then 0 else 1) else 0) else (if n < 62 then 0 else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq273 (n : Nat) :
    nestingProjection273.numerator[n]! = nestingEntries273 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries273, if_neg (by omega : ¬ n < 64)]

def nestingProjection274 : Projection := ⟨2,4,#[2,0,0,0,0,0,0,0,0,1,0,0,1,0,0,0,0,0,1,0,0,0,0,-1,0,0,0,0,0,0,0,0,0,1,0,0,1,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,-1,0,0,0,0,1]⟩
theorem nestingLookup274 : projections[274]! = nestingProjection274 := by
  rw [projections_lookup]
  rfl
def nestingEntries274 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 2 else 0) else 0) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else 0) else (if n < 14 then (if n < 13 then 1 else 0) else 0))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 1 else 0)) else (if n < 22 then 0 else (if n < 23 then 0 else (-1)))) else 0)) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 0 else 1) else 0) else (if n < 38 then (if n < 37 then 1 else 0) else 0)) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 2) else 0))) else (if n < 56 then 0 else (if n < 60 then (if n < 58 then 0 else (if n < 59 then (-1) else 0)) else (if n < 62 then 0 else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq274 (n : Nat) :
    nestingProjection274.numerator[n]! = nestingEntries274 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries274, if_neg (by omega : ¬ n < 64)]

def nestingProjection275 : Projection := ⟨2,4,#[0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,-1,0,0,1,0,1,0,0,0,0,0,0,2,0,0,0,0,0,0,1,0,1,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,-1,0,0,0,0,0,1]⟩
theorem nestingLookup275 : projections[275]! = nestingProjection275 := by
  rw [projections_lookup]
  rfl
def nestingEntries275 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then 0 else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else 0) else (if n < 14 then 0 else (if n < 15 then 0 else (-1))))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 1 else 0)) else (if n < 22 then (if n < 21 then 1 else 0) else 0)) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 2)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then 0 else (if n < 35 then 1 else 0)) else (if n < 38 then (if n < 37 then 1 else 0) else 0)) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 2) else 0))) else (if n < 56 then 0 else (if n < 60 then (if n < 58 then (if n < 57 then 0 else (-1)) else 0) else (if n < 62 then 0 else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq275 (n : Nat) :
    nestingProjection275.numerator[n]! = nestingEntries275 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries275, if_neg (by omega : ¬ n < 64)]

def nestingProjection276 : Projection := ⟨2,4,#[0,0,0,0,0,0,0,0,0,1,-1,0,0,0,0,0,0,-1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,1,0,0,0,0,0,2,0,0,0,0,0,0,0,0,2,0,0,0,0,0,1,0,0,1]⟩
theorem nestingLookup276 : projections[276]! = nestingProjection276 := by
  rw [projections_lookup]
  rfl
def nestingEntries276 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then 0 else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else (if n < 11 then (-1) else 0)) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 0 else (-1)) else (if n < 19 then 1 else 0)) else 0) else 0)) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 1 else 0) else (if n < 39 then 0 else 1))) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 2) else 0))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 0 else (if n < 55 then 2 else 0))) else (if n < 60 then 0 else (if n < 62 then (if n < 61 then 1 else 0) else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq276 (n : Nat) :
    nestingProjection276.numerator[n]! = nestingEntries276 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries276, if_neg (by omega : ¬ n < 64)]

def nestingProjection277 : Projection := ⟨1,4,#[1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0]⟩
theorem nestingLookup277 : projections[277]! = nestingProjection277 := by
  rw [projections_lookup]
  rfl
def nestingEntries277 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else 0) else 0) else 0) else (if n < 24 then 0 else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 1)) else 0))) else (if n < 48 then (if n < 40 then 0 else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 1) else 0))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 0 else (if n < 55 then 1 else 0))) else 0))) else 0
theorem nestingEntries_eq277 (n : Nat) :
    nestingProjection277.numerator[n]! = nestingEntries277 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries277, if_neg (by omega : ¬ n < 64)]

def nestingProjection278 : Projection := ⟨2,4,#[1,0,0,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,0,0,1,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,1,-1,0,0,0,0,0,0,-1,1,0,0,0,0,0,0,0,0,2]⟩
theorem nestingLookup278 : projections[278]! = nestingProjection278 := by
  rw [projections_lookup]
  rfl
def nestingEntries278 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else (if n < 3 then 0 else (-1))) else 0) else 0) else (if n < 24 then 0 else (if n < 28 then (if n < 26 then (if n < 25 then (-1) else 0) else (if n < 27 then 0 else 1)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 2 else 0) else 0)) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 1) else (if n < 47 then (-1) else 0)))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then (if n < 53 then 0 else (-1)) else (if n < 55 then 1 else 0))) else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 2)))))) else 0
theorem nestingEntries_eq278 (n : Nat) :
    nestingProjection278.numerator[n]! = nestingEntries278 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries278, if_neg (by omega : ¬ n < 64)]

def nestingProjection279 : Projection := ⟨2,4,#[1,0,0,1,0,0,0,0,0,1,-1,0,0,0,0,0,0,-1,1,0,0,0,0,0,1,0,0,1,0,0,0,0,0,0,0,0,1,0,0,-1,0,0,0,0,0,1,-1,0,0,0,0,0,0,-1,1,0,0,0,0,0,-1,0,0,1]⟩
theorem nestingLookup279 : projections[279]! = nestingProjection279 := by
  rw [projections_lookup]
  rfl
def nestingEntries279 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else (if n < 3 then 0 else 1)) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else (if n < 11 then (-1) else 0)) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 0 else (-1)) else (if n < 19 then 1 else 0)) else 0) else (if n < 28 then (if n < 26 then (if n < 25 then 1 else 0) else (if n < 27 then 0 else 1)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 1 else 0) else (if n < 39 then 0 else (-1)))) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 1) else (if n < 47 then (-1) else 0)))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then (if n < 53 then 0 else (-1)) else (if n < 55 then 1 else 0))) else (if n < 60 then 0 else (if n < 62 then (if n < 61 then (-1) else 0) else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq279 (n : Nat) :
    nestingProjection279.numerator[n]! = nestingEntries279 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries279, if_neg (by omega : ¬ n < 64)]

def nestingProjection280 : Projection := ⟨4,4,#[2,-1,1,0,-1,0,0,-1,-1,2,0,-1,0,-1,-1,0,1,0,2,1,0,-1,-1,0,0,-1,1,2,1,0,0,1,-1,0,0,1,2,-1,1,0,0,-1,-1,0,-1,2,0,1,0,-1,-1,0,1,0,2,-1,-1,0,0,1,0,1,-1,2]⟩
theorem nestingLookup280 : projections[280]! = nestingProjection280 := by
  rw [projections_lookup]
  rfl
def nestingEntries280 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 2 else (-1)) else (if n < 3 then 1 else 0)) else (if n < 6 then (if n < 5 then (-1) else 0) else (if n < 7 then 0 else (-1)))) else (if n < 12 then (if n < 10 then (if n < 9 then (-1) else 2) else (if n < 11 then 0 else (-1))) else (if n < 14 then (if n < 13 then 0 else (-1)) else (if n < 15 then (-1) else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 1 else 0) else (if n < 19 then 2 else 1)) else (if n < 22 then (if n < 21 then 0 else (-1)) else (if n < 23 then (-1) else 0))) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else (-1)) else (if n < 27 then 1 else 2)) else (if n < 30 then (if n < 29 then 1 else 0) else (if n < 31 then 0 else 1))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then (-1) else 0) else (if n < 35 then 0 else 1)) else (if n < 38 then (if n < 37 then 2 else (-1)) else (if n < 39 then 1 else 0))) else (if n < 44 then (if n < 42 then (if n < 41 then 0 else (-1)) else (if n < 43 then (-1) else 0)) else (if n < 46 then (if n < 45 then (-1) else 2) else (if n < 47 then 0 else 1)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else (-1)) else (if n < 51 then (-1) else 0)) else (if n < 54 then (if n < 53 then 1 else 0) else (if n < 55 then 2 else (-1)))) else (if n < 60 then (if n < 58 then (if n < 57 then (-1) else 0) else (if n < 59 then 0 else 1)) else (if n < 62 then (if n < 61 then 0 else 1) else (if n < 63 then (-1) else 2)))))) else 0
theorem nestingEntries_eq280 (n : Nat) :
    nestingProjection280.numerator[n]! = nestingEntries280 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries280, if_neg (by omega : ¬ n < 64)]

def nestingProjection281 : Projection := ⟨4,4,#[2,1,-1,0,1,0,0,1,1,2,0,1,0,-1,-1,0,-1,0,2,-1,0,-1,-1,0,0,1,-1,2,-1,0,0,-1,1,0,0,-1,2,-1,1,0,0,-1,-1,0,-1,2,0,1,0,-1,-1,0,1,0,2,-1,1,0,0,-1,0,1,-1,2]⟩
theorem nestingLookup281 : projections[281]! = nestingProjection281 := by
  rw [projections_lookup]
  rfl
def nestingEntries281 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 2 else 1) else (if n < 3 then (-1) else 0)) else (if n < 6 then (if n < 5 then 1 else 0) else (if n < 7 then 0 else 1))) else (if n < 12 then (if n < 10 then (if n < 9 then 1 else 2) else (if n < 11 then 0 else 1)) else (if n < 14 then (if n < 13 then 0 else (-1)) else (if n < 15 then (-1) else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then (-1) else 0) else (if n < 19 then 2 else (-1))) else (if n < 22 then (if n < 21 then 0 else (-1)) else (if n < 23 then (-1) else 0))) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else 1) else (if n < 27 then (-1) else 2)) else (if n < 30 then (if n < 29 then (-1) else 0) else (if n < 31 then 0 else (-1)))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 1 else 0) else (if n < 35 then 0 else (-1))) else (if n < 38 then (if n < 37 then 2 else (-1)) else (if n < 39 then 1 else 0))) else (if n < 44 then (if n < 42 then (if n < 41 then 0 else (-1)) else (if n < 43 then (-1) else 0)) else (if n < 46 then (if n < 45 then (-1) else 2) else (if n < 47 then 0 else 1)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else (-1)) else (if n < 51 then (-1) else 0)) else (if n < 54 then (if n < 53 then 1 else 0) else (if n < 55 then 2 else (-1)))) else (if n < 60 then (if n < 58 then (if n < 57 then 1 else 0) else (if n < 59 then 0 else (-1))) else (if n < 62 then (if n < 61 then 0 else 1) else (if n < 63 then (-1) else 2)))))) else 0
theorem nestingEntries_eq281 (n : Nat) :
    nestingProjection281.numerator[n]! = nestingEntries281 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries281, if_neg (by omega : ¬ n < 64)]

def nestingProjection282 : Projection := ⟨4,4,#[2,-1,1,0,1,0,0,1,-1,2,0,-1,0,-1,-1,0,1,0,2,1,0,-1,-1,0,0,-1,1,2,-1,0,0,-1,1,0,0,-1,2,1,-1,0,0,-1,-1,0,1,2,0,-1,0,-1,-1,0,-1,0,2,1,1,0,0,-1,0,-1,1,2]⟩
theorem nestingLookup282 : projections[282]! = nestingProjection282 := by
  rw [projections_lookup]
  rfl
def nestingEntries282 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 2 else (-1)) else (if n < 3 then 1 else 0)) else (if n < 6 then (if n < 5 then 1 else 0) else (if n < 7 then 0 else 1))) else (if n < 12 then (if n < 10 then (if n < 9 then (-1) else 2) else (if n < 11 then 0 else (-1))) else (if n < 14 then (if n < 13 then 0 else (-1)) else (if n < 15 then (-1) else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 1 else 0) else (if n < 19 then 2 else 1)) else (if n < 22 then (if n < 21 then 0 else (-1)) else (if n < 23 then (-1) else 0))) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else (-1)) else (if n < 27 then 1 else 2)) else (if n < 30 then (if n < 29 then (-1) else 0) else (if n < 31 then 0 else (-1)))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 1 else 0) else (if n < 35 then 0 else (-1))) else (if n < 38 then (if n < 37 then 2 else 1) else (if n < 39 then (-1) else 0))) else (if n < 44 then (if n < 42 then (if n < 41 then 0 else (-1)) else (if n < 43 then (-1) else 0)) else (if n < 46 then (if n < 45 then 1 else 2) else (if n < 47 then 0 else (-1))))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else (-1)) else (if n < 51 then (-1) else 0)) else (if n < 54 then (if n < 53 then (-1) else 0) else (if n < 55 then 2 else 1))) else (if n < 60 then (if n < 58 then (if n < 57 then 1 else 0) else (if n < 59 then 0 else (-1))) else (if n < 62 then (if n < 61 then 0 else (-1)) else (if n < 63 then 1 else 2)))))) else 0
theorem nestingEntries_eq282 (n : Nat) :
    nestingProjection282.numerator[n]! = nestingEntries282 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries282, if_neg (by omega : ¬ n < 64)]

def nestingProjection283 : Projection := ⟨4,4,#[2,1,-1,0,-1,0,0,-1,1,2,0,1,0,-1,-1,0,-1,0,2,-1,0,-1,-1,0,0,1,-1,2,1,0,0,1,-1,0,0,1,2,1,-1,0,0,-1,-1,0,1,2,0,-1,0,-1,-1,0,-1,0,2,1,-1,0,0,1,0,-1,1,2]⟩
theorem nestingLookup283 : projections[283]! = nestingProjection283 := by
  rw [projections_lookup]
  rfl
def nestingEntries283 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 2 else 1) else (if n < 3 then (-1) else 0)) else (if n < 6 then (if n < 5 then (-1) else 0) else (if n < 7 then 0 else (-1)))) else (if n < 12 then (if n < 10 then (if n < 9 then 1 else 2) else (if n < 11 then 0 else 1)) else (if n < 14 then (if n < 13 then 0 else (-1)) else (if n < 15 then (-1) else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then (-1) else 0) else (if n < 19 then 2 else (-1))) else (if n < 22 then (if n < 21 then 0 else (-1)) else (if n < 23 then (-1) else 0))) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else 1) else (if n < 27 then (-1) else 2)) else (if n < 30 then (if n < 29 then 1 else 0) else (if n < 31 then 0 else 1))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then (-1) else 0) else (if n < 35 then 0 else 1)) else (if n < 38 then (if n < 37 then 2 else 1) else (if n < 39 then (-1) else 0))) else (if n < 44 then (if n < 42 then (if n < 41 then 0 else (-1)) else (if n < 43 then (-1) else 0)) else (if n < 46 then (if n < 45 then 1 else 2) else (if n < 47 then 0 else (-1))))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else (-1)) else (if n < 51 then (-1) else 0)) else (if n < 54 then (if n < 53 then (-1) else 0) else (if n < 55 then 2 else 1))) else (if n < 60 then (if n < 58 then (if n < 57 then (-1) else 0) else (if n < 59 then 0 else 1)) else (if n < 62 then (if n < 61 then 0 else (-1)) else (if n < 63 then 1 else 2)))))) else 0
theorem nestingEntries_eq283 (n : Nat) :
    nestingProjection283.numerator[n]! = nestingEntries283 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries283, if_neg (by omega : ¬ n < 64)]

def nestingProjection284 : Projection := ⟨4,4,#[2,-1,1,0,1,0,0,1,-1,2,0,-1,0,1,1,0,1,0,2,1,0,1,1,0,0,-1,1,2,-1,0,0,-1,1,0,0,-1,2,-1,1,0,0,1,1,0,-1,2,0,1,0,1,1,0,1,0,2,-1,1,0,0,-1,0,1,-1,2]⟩
theorem nestingLookup284 : projections[284]! = nestingProjection284 := by
  rw [projections_lookup]
  rfl
def nestingEntries284 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 2 else (-1)) else (if n < 3 then 1 else 0)) else (if n < 6 then (if n < 5 then 1 else 0) else (if n < 7 then 0 else 1))) else (if n < 12 then (if n < 10 then (if n < 9 then (-1) else 2) else (if n < 11 then 0 else (-1))) else (if n < 14 then (if n < 13 then 0 else 1) else (if n < 15 then 1 else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 1 else 0) else (if n < 19 then 2 else 1)) else (if n < 22 then (if n < 21 then 0 else 1) else (if n < 23 then 1 else 0))) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else (-1)) else (if n < 27 then 1 else 2)) else (if n < 30 then (if n < 29 then (-1) else 0) else (if n < 31 then 0 else (-1)))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 1 else 0) else (if n < 35 then 0 else (-1))) else (if n < 38 then (if n < 37 then 2 else (-1)) else (if n < 39 then 1 else 0))) else (if n < 44 then (if n < 42 then (if n < 41 then 0 else 1) else (if n < 43 then 1 else 0)) else (if n < 46 then (if n < 45 then (-1) else 2) else (if n < 47 then 0 else 1)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else 1) else (if n < 51 then 1 else 0)) else (if n < 54 then (if n < 53 then 1 else 0) else (if n < 55 then 2 else (-1)))) else (if n < 60 then (if n < 58 then (if n < 57 then 1 else 0) else (if n < 59 then 0 else (-1))) else (if n < 62 then (if n < 61 then 0 else 1) else (if n < 63 then (-1) else 2)))))) else 0
theorem nestingEntries_eq284 (n : Nat) :
    nestingProjection284.numerator[n]! = nestingEntries284 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries284, if_neg (by omega : ¬ n < 64)]

def nestingProjection285 : Projection := ⟨4,4,#[2,1,-1,0,-1,0,0,-1,1,2,0,1,0,1,1,0,-1,0,2,-1,0,1,1,0,0,1,-1,2,1,0,0,1,-1,0,0,1,2,-1,1,0,0,1,1,0,-1,2,0,1,0,1,1,0,1,0,2,-1,-1,0,0,1,0,1,-1,2]⟩
theorem nestingLookup285 : projections[285]! = nestingProjection285 := by
  rw [projections_lookup]
  rfl
def nestingEntries285 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 2 else 1) else (if n < 3 then (-1) else 0)) else (if n < 6 then (if n < 5 then (-1) else 0) else (if n < 7 then 0 else (-1)))) else (if n < 12 then (if n < 10 then (if n < 9 then 1 else 2) else (if n < 11 then 0 else 1)) else (if n < 14 then (if n < 13 then 0 else 1) else (if n < 15 then 1 else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then (-1) else 0) else (if n < 19 then 2 else (-1))) else (if n < 22 then (if n < 21 then 0 else 1) else (if n < 23 then 1 else 0))) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else 1) else (if n < 27 then (-1) else 2)) else (if n < 30 then (if n < 29 then 1 else 0) else (if n < 31 then 0 else 1))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then (-1) else 0) else (if n < 35 then 0 else 1)) else (if n < 38 then (if n < 37 then 2 else (-1)) else (if n < 39 then 1 else 0))) else (if n < 44 then (if n < 42 then (if n < 41 then 0 else 1) else (if n < 43 then 1 else 0)) else (if n < 46 then (if n < 45 then (-1) else 2) else (if n < 47 then 0 else 1)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else 1) else (if n < 51 then 1 else 0)) else (if n < 54 then (if n < 53 then 1 else 0) else (if n < 55 then 2 else (-1)))) else (if n < 60 then (if n < 58 then (if n < 57 then (-1) else 0) else (if n < 59 then 0 else 1)) else (if n < 62 then (if n < 61 then 0 else 1) else (if n < 63 then (-1) else 2)))))) else 0
theorem nestingEntries_eq285 (n : Nat) :
    nestingProjection285.numerator[n]! = nestingEntries285 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries285, if_neg (by omega : ¬ n < 64)]

def nestingProjection286 : Projection := ⟨4,4,#[2,-1,1,0,-1,0,0,-1,-1,2,0,-1,0,1,1,0,1,0,2,1,0,1,1,0,0,-1,1,2,1,0,0,1,-1,0,0,1,2,1,-1,0,0,1,1,0,1,2,0,-1,0,1,1,0,-1,0,2,1,-1,0,0,1,0,-1,1,2]⟩
theorem nestingLookup286 : projections[286]! = nestingProjection286 := by
  rw [projections_lookup]
  rfl
def nestingEntries286 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 2 else (-1)) else (if n < 3 then 1 else 0)) else (if n < 6 then (if n < 5 then (-1) else 0) else (if n < 7 then 0 else (-1)))) else (if n < 12 then (if n < 10 then (if n < 9 then (-1) else 2) else (if n < 11 then 0 else (-1))) else (if n < 14 then (if n < 13 then 0 else 1) else (if n < 15 then 1 else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 1 else 0) else (if n < 19 then 2 else 1)) else (if n < 22 then (if n < 21 then 0 else 1) else (if n < 23 then 1 else 0))) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else (-1)) else (if n < 27 then 1 else 2)) else (if n < 30 then (if n < 29 then 1 else 0) else (if n < 31 then 0 else 1))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then (-1) else 0) else (if n < 35 then 0 else 1)) else (if n < 38 then (if n < 37 then 2 else 1) else (if n < 39 then (-1) else 0))) else (if n < 44 then (if n < 42 then (if n < 41 then 0 else 1) else (if n < 43 then 1 else 0)) else (if n < 46 then (if n < 45 then 1 else 2) else (if n < 47 then 0 else (-1))))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else 1) else (if n < 51 then 1 else 0)) else (if n < 54 then (if n < 53 then (-1) else 0) else (if n < 55 then 2 else 1))) else (if n < 60 then (if n < 58 then (if n < 57 then (-1) else 0) else (if n < 59 then 0 else 1)) else (if n < 62 then (if n < 61 then 0 else (-1)) else (if n < 63 then 1 else 2)))))) else 0
theorem nestingEntries_eq286 (n : Nat) :
    nestingProjection286.numerator[n]! = nestingEntries286 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries286, if_neg (by omega : ¬ n < 64)]

def nestingProjection287 : Projection := ⟨4,4,#[2,1,-1,0,1,0,0,1,1,2,0,1,0,1,1,0,-1,0,2,-1,0,1,1,0,0,1,-1,2,-1,0,0,-1,1,0,0,-1,2,1,-1,0,0,1,1,0,1,2,0,-1,0,1,1,0,-1,0,2,1,1,0,0,-1,0,-1,1,2]⟩
theorem nestingLookup287 : projections[287]! = nestingProjection287 := by
  rw [projections_lookup]
  rfl
def nestingEntries287 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 2 else 1) else (if n < 3 then (-1) else 0)) else (if n < 6 then (if n < 5 then 1 else 0) else (if n < 7 then 0 else 1))) else (if n < 12 then (if n < 10 then (if n < 9 then 1 else 2) else (if n < 11 then 0 else 1)) else (if n < 14 then (if n < 13 then 0 else 1) else (if n < 15 then 1 else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then (-1) else 0) else (if n < 19 then 2 else (-1))) else (if n < 22 then (if n < 21 then 0 else 1) else (if n < 23 then 1 else 0))) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else 1) else (if n < 27 then (-1) else 2)) else (if n < 30 then (if n < 29 then (-1) else 0) else (if n < 31 then 0 else (-1)))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 1 else 0) else (if n < 35 then 0 else (-1))) else (if n < 38 then (if n < 37 then 2 else 1) else (if n < 39 then (-1) else 0))) else (if n < 44 then (if n < 42 then (if n < 41 then 0 else 1) else (if n < 43 then 1 else 0)) else (if n < 46 then (if n < 45 then 1 else 2) else (if n < 47 then 0 else (-1))))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else 1) else (if n < 51 then 1 else 0)) else (if n < 54 then (if n < 53 then (-1) else 0) else (if n < 55 then 2 else 1))) else (if n < 60 then (if n < 58 then (if n < 57 then 1 else 0) else (if n < 59 then 0 else (-1))) else (if n < 62 then (if n < 61 then 0 else (-1)) else (if n < 63 then 1 else 2)))))) else 0
theorem nestingEntries_eq287 (n : Nat) :
    nestingProjection287.numerator[n]! = nestingEntries287 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries287, if_neg (by omega : ¬ n < 64)]

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def nestingProjection288 : Projection := ⟨2,4,#[1,0,0,1,0,0,0,0,0,2,0,0,0,0,0,0,0,0,2,0,0,0,0,0,1,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,1,0,0,0,0,0,0,1,1,0,0,0,0,0,0,0,0,0]⟩
theorem nestingLookup288 : projections[288]! = nestingProjection288 := by
  rw [projections_lookup]
  rfl
def nestingEntries288 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else (if n < 3 then 0 else 1)) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 2) else 0) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 2 else 0)) else 0) else (if n < 28 then (if n < 26 then (if n < 25 then 1 else 0) else (if n < 27 then 0 else 1)) else 0))) else (if n < 48 then (if n < 40 then 0 else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 1) else (if n < 47 then 1 else 0)))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then (if n < 53 then 0 else 1) else (if n < 55 then 1 else 0))) else 0))) else 0
theorem nestingEntries_eq288 (n : Nat) :
    nestingProjection288.numerator[n]! = nestingEntries288 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries288, if_neg (by omega : ¬ n < 64)]

def nestingProjection289 : Projection := ⟨2,4,#[1,0,0,-1,0,0,0,0,0,1,1,0,0,0,0,0,0,1,1,0,0,0,0,0,-1,0,0,1,0,0,0,0,0,0,0,0,1,0,0,1,0,0,0,0,0,1,1,0,0,0,0,0,0,1,1,0,0,0,0,0,1,0,0,1]⟩
theorem nestingLookup289 : projections[289]! = nestingProjection289 := by
  rw [projections_lookup]
  rfl
def nestingEntries289 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else (if n < 3 then 0 else (-1))) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else (if n < 11 then 1 else 0)) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 0 else 1) else (if n < 19 then 1 else 0)) else 0) else (if n < 28 then (if n < 26 then (if n < 25 then (-1) else 0) else (if n < 27 then 0 else 1)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 1 else 0) else (if n < 39 then 0 else 1))) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 1) else (if n < 47 then 1 else 0)))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then (if n < 53 then 0 else 1) else (if n < 55 then 1 else 0))) else (if n < 60 then 0 else (if n < 62 then (if n < 61 then 1 else 0) else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq289 (n : Nat) :
    nestingProjection289.numerator[n]! = nestingEntries289 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries289, if_neg (by omega : ¬ n < 64)]

def nestingProjection290 : Projection := ⟨2,4,#[1,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,1,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,1,1,0,0,0,0,0,0,1,1,0,0,0,0,0,0,0,0,2]⟩
theorem nestingLookup290 : projections[290]! = nestingProjection290 := by
  rw [projections_lookup]
  rfl
def nestingEntries290 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else (if n < 3 then 0 else 1)) else 0) else 0) else (if n < 24 then 0 else (if n < 28 then (if n < 26 then (if n < 25 then 1 else 0) else (if n < 27 then 0 else 1)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 2 else 0) else 0)) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 1) else (if n < 47 then 1 else 0)))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then (if n < 53 then 0 else 1) else (if n < 55 then 1 else 0))) else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 2)))))) else 0
theorem nestingEntries_eq290 (n : Nat) :
    nestingProjection290.numerator[n]! = nestingEntries290 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries290, if_neg (by omega : ¬ n < 64)]

def nestingProjection291 : Projection := ⟨2,4,#[1,0,0,-1,0,0,0,0,0,1,-1,0,0,0,0,0,0,-1,1,0,0,0,0,0,-1,0,0,1,0,0,0,0,0,0,0,0,1,0,0,-1,0,0,0,0,0,1,1,0,0,0,0,0,0,1,1,0,0,0,0,0,-1,0,0,1]⟩
theorem nestingLookup291 : projections[291]! = nestingProjection291 := by
  rw [projections_lookup]
  rfl
def nestingEntries291 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else (if n < 3 then 0 else (-1))) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else (if n < 11 then (-1) else 0)) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 0 else (-1)) else (if n < 19 then 1 else 0)) else 0) else (if n < 28 then (if n < 26 then (if n < 25 then (-1) else 0) else (if n < 27 then 0 else 1)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 1 else 0) else (if n < 39 then 0 else (-1)))) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 1) else (if n < 47 then 1 else 0)))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then (if n < 53 then 0 else 1) else (if n < 55 then 1 else 0))) else (if n < 60 then 0 else (if n < 62 then (if n < 61 then (-1) else 0) else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq291 (n : Nat) :
    nestingProjection291.numerator[n]! = nestingEntries291 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries291, if_neg (by omega : ¬ n < 64)]

def nestingProjection292 : Projection := ⟨4,4,#[2,-1,1,0,-1,0,0,-1,-1,2,0,1,0,-1,1,0,1,0,2,-1,0,-1,1,0,0,1,-1,2,-1,0,0,-1,-1,0,0,-1,2,-1,-1,0,0,-1,-1,0,-1,2,0,1,0,1,1,0,-1,0,2,1,-1,0,0,-1,0,1,1,2]⟩
theorem nestingLookup292 : projections[292]! = nestingProjection292 := by
  rw [projections_lookup]
  rfl
def nestingEntries292 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 2 else (-1)) else (if n < 3 then 1 else 0)) else (if n < 6 then (if n < 5 then (-1) else 0) else (if n < 7 then 0 else (-1)))) else (if n < 12 then (if n < 10 then (if n < 9 then (-1) else 2) else (if n < 11 then 0 else 1)) else (if n < 14 then (if n < 13 then 0 else (-1)) else (if n < 15 then 1 else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 1 else 0) else (if n < 19 then 2 else (-1))) else (if n < 22 then (if n < 21 then 0 else (-1)) else (if n < 23 then 1 else 0))) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else 1) else (if n < 27 then (-1) else 2)) else (if n < 30 then (if n < 29 then (-1) else 0) else (if n < 31 then 0 else (-1)))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then (-1) else 0) else (if n < 35 then 0 else (-1))) else (if n < 38 then (if n < 37 then 2 else (-1)) else (if n < 39 then (-1) else 0))) else (if n < 44 then (if n < 42 then (if n < 41 then 0 else (-1)) else (if n < 43 then (-1) else 0)) else (if n < 46 then (if n < 45 then (-1) else 2) else (if n < 47 then 0 else 1)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else 1) else (if n < 51 then 1 else 0)) else (if n < 54 then (if n < 53 then (-1) else 0) else (if n < 55 then 2 else 1))) else (if n < 60 then (if n < 58 then (if n < 57 then (-1) else 0) else (if n < 59 then 0 else (-1))) else (if n < 62 then (if n < 61 then 0 else 1) else (if n < 63 then 1 else 2)))))) else 0
theorem nestingEntries_eq292 (n : Nat) :
    nestingProjection292.numerator[n]! = nestingEntries292 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries292, if_neg (by omega : ¬ n < 64)]

def nestingProjection293 : Projection := ⟨4,4,#[2,1,-1,0,1,0,0,1,1,2,0,-1,0,-1,1,0,-1,0,2,1,0,-1,1,0,0,-1,1,2,1,0,0,1,1,0,0,1,2,-1,-1,0,0,-1,-1,0,-1,2,0,1,0,1,1,0,-1,0,2,1,1,0,0,1,0,1,1,2]⟩
theorem nestingLookup293 : projections[293]! = nestingProjection293 := by
  rw [projections_lookup]
  rfl
def nestingEntries293 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 2 else 1) else (if n < 3 then (-1) else 0)) else (if n < 6 then (if n < 5 then 1 else 0) else (if n < 7 then 0 else 1))) else (if n < 12 then (if n < 10 then (if n < 9 then 1 else 2) else (if n < 11 then 0 else (-1))) else (if n < 14 then (if n < 13 then 0 else (-1)) else (if n < 15 then 1 else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then (-1) else 0) else (if n < 19 then 2 else 1)) else (if n < 22 then (if n < 21 then 0 else (-1)) else (if n < 23 then 1 else 0))) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else (-1)) else (if n < 27 then 1 else 2)) else (if n < 30 then (if n < 29 then 1 else 0) else (if n < 31 then 0 else 1))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 1 else 0) else (if n < 35 then 0 else 1)) else (if n < 38 then (if n < 37 then 2 else (-1)) else (if n < 39 then (-1) else 0))) else (if n < 44 then (if n < 42 then (if n < 41 then 0 else (-1)) else (if n < 43 then (-1) else 0)) else (if n < 46 then (if n < 45 then (-1) else 2) else (if n < 47 then 0 else 1)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else 1) else (if n < 51 then 1 else 0)) else (if n < 54 then (if n < 53 then (-1) else 0) else (if n < 55 then 2 else 1))) else (if n < 60 then (if n < 58 then (if n < 57 then 1 else 0) else (if n < 59 then 0 else 1)) else (if n < 62 then (if n < 61 then 0 else 1) else (if n < 63 then 1 else 2)))))) else 0
theorem nestingEntries_eq293 (n : Nat) :
    nestingProjection293.numerator[n]! = nestingEntries293 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries293, if_neg (by omega : ¬ n < 64)]

def nestingProjection294 : Projection := ⟨4,4,#[2,-1,1,0,1,0,0,1,-1,2,0,1,0,-1,1,0,1,0,2,-1,0,-1,1,0,0,1,-1,2,1,0,0,1,1,0,0,1,2,1,1,0,0,-1,-1,0,1,2,0,-1,0,1,1,0,1,0,2,-1,1,0,0,1,0,-1,-1,2]⟩
theorem nestingLookup294 : projections[294]! = nestingProjection294 := by
  rw [projections_lookup]
  rfl
def nestingEntries294 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 2 else (-1)) else (if n < 3 then 1 else 0)) else (if n < 6 then (if n < 5 then 1 else 0) else (if n < 7 then 0 else 1))) else (if n < 12 then (if n < 10 then (if n < 9 then (-1) else 2) else (if n < 11 then 0 else 1)) else (if n < 14 then (if n < 13 then 0 else (-1)) else (if n < 15 then 1 else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 1 else 0) else (if n < 19 then 2 else (-1))) else (if n < 22 then (if n < 21 then 0 else (-1)) else (if n < 23 then 1 else 0))) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else 1) else (if n < 27 then (-1) else 2)) else (if n < 30 then (if n < 29 then 1 else 0) else (if n < 31 then 0 else 1))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 1 else 0) else (if n < 35 then 0 else 1)) else (if n < 38 then (if n < 37 then 2 else 1) else (if n < 39 then 1 else 0))) else (if n < 44 then (if n < 42 then (if n < 41 then 0 else (-1)) else (if n < 43 then (-1) else 0)) else (if n < 46 then (if n < 45 then 1 else 2) else (if n < 47 then 0 else (-1))))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else 1) else (if n < 51 then 1 else 0)) else (if n < 54 then (if n < 53 then 1 else 0) else (if n < 55 then 2 else (-1)))) else (if n < 60 then (if n < 58 then (if n < 57 then 1 else 0) else (if n < 59 then 0 else 1)) else (if n < 62 then (if n < 61 then 0 else (-1)) else (if n < 63 then (-1) else 2)))))) else 0
theorem nestingEntries_eq294 (n : Nat) :
    nestingProjection294.numerator[n]! = nestingEntries294 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries294, if_neg (by omega : ¬ n < 64)]

def nestingProjection295 : Projection := ⟨4,4,#[2,1,-1,0,-1,0,0,-1,1,2,0,-1,0,-1,1,0,-1,0,2,1,0,-1,1,0,0,-1,1,2,-1,0,0,-1,-1,0,0,-1,2,1,1,0,0,-1,-1,0,1,2,0,-1,0,1,1,0,1,0,2,-1,-1,0,0,-1,0,-1,-1,2]⟩
theorem nestingLookup295 : projections[295]! = nestingProjection295 := by
  rw [projections_lookup]
  rfl
def nestingEntries295 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 2 else 1) else (if n < 3 then (-1) else 0)) else (if n < 6 then (if n < 5 then (-1) else 0) else (if n < 7 then 0 else (-1)))) else (if n < 12 then (if n < 10 then (if n < 9 then 1 else 2) else (if n < 11 then 0 else (-1))) else (if n < 14 then (if n < 13 then 0 else (-1)) else (if n < 15 then 1 else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then (-1) else 0) else (if n < 19 then 2 else 1)) else (if n < 22 then (if n < 21 then 0 else (-1)) else (if n < 23 then 1 else 0))) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else (-1)) else (if n < 27 then 1 else 2)) else (if n < 30 then (if n < 29 then (-1) else 0) else (if n < 31 then 0 else (-1)))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then (-1) else 0) else (if n < 35 then 0 else (-1))) else (if n < 38 then (if n < 37 then 2 else 1) else (if n < 39 then 1 else 0))) else (if n < 44 then (if n < 42 then (if n < 41 then 0 else (-1)) else (if n < 43 then (-1) else 0)) else (if n < 46 then (if n < 45 then 1 else 2) else (if n < 47 then 0 else (-1))))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else 1) else (if n < 51 then 1 else 0)) else (if n < 54 then (if n < 53 then 1 else 0) else (if n < 55 then 2 else (-1)))) else (if n < 60 then (if n < 58 then (if n < 57 then (-1) else 0) else (if n < 59 then 0 else (-1))) else (if n < 62 then (if n < 61 then 0 else (-1)) else (if n < 63 then (-1) else 2)))))) else 0
theorem nestingEntries_eq295 (n : Nat) :
    nestingProjection295.numerator[n]! = nestingEntries295 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries295, if_neg (by omega : ¬ n < 64)]

def nestingProjection296 : Projection := ⟨4,4,#[2,-1,1,0,1,0,0,1,-1,2,0,1,0,1,-1,0,1,0,2,-1,0,1,-1,0,0,1,-1,2,1,0,0,1,1,0,0,1,2,-1,-1,0,0,1,1,0,-1,2,0,1,0,-1,-1,0,-1,0,2,1,1,0,0,1,0,1,1,2]⟩
theorem nestingLookup296 : projections[296]! = nestingProjection296 := by
  rw [projections_lookup]
  rfl
def nestingEntries296 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 2 else (-1)) else (if n < 3 then 1 else 0)) else (if n < 6 then (if n < 5 then 1 else 0) else (if n < 7 then 0 else 1))) else (if n < 12 then (if n < 10 then (if n < 9 then (-1) else 2) else (if n < 11 then 0 else 1)) else (if n < 14 then (if n < 13 then 0 else 1) else (if n < 15 then (-1) else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 1 else 0) else (if n < 19 then 2 else (-1))) else (if n < 22 then (if n < 21 then 0 else 1) else (if n < 23 then (-1) else 0))) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else 1) else (if n < 27 then (-1) else 2)) else (if n < 30 then (if n < 29 then 1 else 0) else (if n < 31 then 0 else 1))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 1 else 0) else (if n < 35 then 0 else 1)) else (if n < 38 then (if n < 37 then 2 else (-1)) else (if n < 39 then (-1) else 0))) else (if n < 44 then (if n < 42 then (if n < 41 then 0 else 1) else (if n < 43 then 1 else 0)) else (if n < 46 then (if n < 45 then (-1) else 2) else (if n < 47 then 0 else 1)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else (-1)) else (if n < 51 then (-1) else 0)) else (if n < 54 then (if n < 53 then (-1) else 0) else (if n < 55 then 2 else 1))) else (if n < 60 then (if n < 58 then (if n < 57 then 1 else 0) else (if n < 59 then 0 else 1)) else (if n < 62 then (if n < 61 then 0 else 1) else (if n < 63 then 1 else 2)))))) else 0
theorem nestingEntries_eq296 (n : Nat) :
    nestingProjection296.numerator[n]! = nestingEntries296 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries296, if_neg (by omega : ¬ n < 64)]

def nestingProjection297 : Projection := ⟨4,4,#[2,1,-1,0,-1,0,0,-1,1,2,0,-1,0,1,-1,0,-1,0,2,1,0,1,-1,0,0,-1,1,2,-1,0,0,-1,-1,0,0,-1,2,-1,-1,0,0,1,1,0,-1,2,0,1,0,-1,-1,0,-1,0,2,1,-1,0,0,-1,0,1,1,2]⟩
theorem nestingLookup297 : projections[297]! = nestingProjection297 := by
  rw [projections_lookup]
  rfl
def nestingEntries297 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 2 else 1) else (if n < 3 then (-1) else 0)) else (if n < 6 then (if n < 5 then (-1) else 0) else (if n < 7 then 0 else (-1)))) else (if n < 12 then (if n < 10 then (if n < 9 then 1 else 2) else (if n < 11 then 0 else (-1))) else (if n < 14 then (if n < 13 then 0 else 1) else (if n < 15 then (-1) else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then (-1) else 0) else (if n < 19 then 2 else 1)) else (if n < 22 then (if n < 21 then 0 else 1) else (if n < 23 then (-1) else 0))) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else (-1)) else (if n < 27 then 1 else 2)) else (if n < 30 then (if n < 29 then (-1) else 0) else (if n < 31 then 0 else (-1)))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then (-1) else 0) else (if n < 35 then 0 else (-1))) else (if n < 38 then (if n < 37 then 2 else (-1)) else (if n < 39 then (-1) else 0))) else (if n < 44 then (if n < 42 then (if n < 41 then 0 else 1) else (if n < 43 then 1 else 0)) else (if n < 46 then (if n < 45 then (-1) else 2) else (if n < 47 then 0 else 1)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else (-1)) else (if n < 51 then (-1) else 0)) else (if n < 54 then (if n < 53 then (-1) else 0) else (if n < 55 then 2 else 1))) else (if n < 60 then (if n < 58 then (if n < 57 then (-1) else 0) else (if n < 59 then 0 else (-1))) else (if n < 62 then (if n < 61 then 0 else 1) else (if n < 63 then 1 else 2)))))) else 0
theorem nestingEntries_eq297 (n : Nat) :
    nestingProjection297.numerator[n]! = nestingEntries297 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries297, if_neg (by omega : ¬ n < 64)]

def nestingProjection298 : Projection := ⟨4,4,#[2,-1,1,0,-1,0,0,-1,-1,2,0,1,0,1,-1,0,1,0,2,-1,0,1,-1,0,0,1,-1,2,-1,0,0,-1,-1,0,0,-1,2,1,1,0,0,1,1,0,1,2,0,-1,0,-1,-1,0,1,0,2,-1,-1,0,0,-1,0,-1,-1,2]⟩
theorem nestingLookup298 : projections[298]! = nestingProjection298 := by
  rw [projections_lookup]
  rfl
def nestingEntries298 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 2 else (-1)) else (if n < 3 then 1 else 0)) else (if n < 6 then (if n < 5 then (-1) else 0) else (if n < 7 then 0 else (-1)))) else (if n < 12 then (if n < 10 then (if n < 9 then (-1) else 2) else (if n < 11 then 0 else 1)) else (if n < 14 then (if n < 13 then 0 else 1) else (if n < 15 then (-1) else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 1 else 0) else (if n < 19 then 2 else (-1))) else (if n < 22 then (if n < 21 then 0 else 1) else (if n < 23 then (-1) else 0))) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else 1) else (if n < 27 then (-1) else 2)) else (if n < 30 then (if n < 29 then (-1) else 0) else (if n < 31 then 0 else (-1)))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then (-1) else 0) else (if n < 35 then 0 else (-1))) else (if n < 38 then (if n < 37 then 2 else 1) else (if n < 39 then 1 else 0))) else (if n < 44 then (if n < 42 then (if n < 41 then 0 else 1) else (if n < 43 then 1 else 0)) else (if n < 46 then (if n < 45 then 1 else 2) else (if n < 47 then 0 else (-1))))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else (-1)) else (if n < 51 then (-1) else 0)) else (if n < 54 then (if n < 53 then 1 else 0) else (if n < 55 then 2 else (-1)))) else (if n < 60 then (if n < 58 then (if n < 57 then (-1) else 0) else (if n < 59 then 0 else (-1))) else (if n < 62 then (if n < 61 then 0 else (-1)) else (if n < 63 then (-1) else 2)))))) else 0
theorem nestingEntries_eq298 (n : Nat) :
    nestingProjection298.numerator[n]! = nestingEntries298 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries298, if_neg (by omega : ¬ n < 64)]

def nestingProjection299 : Projection := ⟨4,4,#[2,1,-1,0,1,0,0,1,1,2,0,-1,0,1,-1,0,-1,0,2,1,0,1,-1,0,0,-1,1,2,1,0,0,1,1,0,0,1,2,1,1,0,0,1,1,0,1,2,0,-1,0,-1,-1,0,1,0,2,-1,1,0,0,1,0,-1,-1,2]⟩
theorem nestingLookup299 : projections[299]! = nestingProjection299 := by
  rw [projections_lookup]
  rfl
def nestingEntries299 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 2 else 1) else (if n < 3 then (-1) else 0)) else (if n < 6 then (if n < 5 then 1 else 0) else (if n < 7 then 0 else 1))) else (if n < 12 then (if n < 10 then (if n < 9 then 1 else 2) else (if n < 11 then 0 else (-1))) else (if n < 14 then (if n < 13 then 0 else 1) else (if n < 15 then (-1) else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then (-1) else 0) else (if n < 19 then 2 else 1)) else (if n < 22 then (if n < 21 then 0 else 1) else (if n < 23 then (-1) else 0))) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else (-1)) else (if n < 27 then 1 else 2)) else (if n < 30 then (if n < 29 then 1 else 0) else (if n < 31 then 0 else 1))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 1 else 0) else (if n < 35 then 0 else 1)) else (if n < 38 then (if n < 37 then 2 else 1) else (if n < 39 then 1 else 0))) else (if n < 44 then (if n < 42 then (if n < 41 then 0 else 1) else (if n < 43 then 1 else 0)) else (if n < 46 then (if n < 45 then 1 else 2) else (if n < 47 then 0 else (-1))))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else (-1)) else (if n < 51 then (-1) else 0)) else (if n < 54 then (if n < 53 then 1 else 0) else (if n < 55 then 2 else (-1)))) else (if n < 60 then (if n < 58 then (if n < 57 then 1 else 0) else (if n < 59 then 0 else 1)) else (if n < 62 then (if n < 61 then 0 else (-1)) else (if n < 63 then (-1) else 2)))))) else 0
theorem nestingEntries_eq299 (n : Nat) :
    nestingProjection299.numerator[n]! = nestingEntries299 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries299, if_neg (by omega : ¬ n < 64)]

def nestingProjection300 : Projection := ⟨2,4,#[1,0,0,-1,0,0,0,0,0,2,0,0,0,0,0,0,0,0,2,0,0,0,0,0,-1,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,-1,0,0,0,0,0,0,-1,1,0,0,0,0,0,0,0,0,0]⟩
theorem nestingLookup300 : projections[300]! = nestingProjection300 := by
  rw [projections_lookup]
  rfl
def nestingEntries300 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else (if n < 3 then 0 else (-1))) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 2) else 0) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 2 else 0)) else 0) else (if n < 28 then (if n < 26 then (if n < 25 then (-1) else 0) else (if n < 27 then 0 else 1)) else 0))) else (if n < 48 then (if n < 40 then 0 else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 1) else (if n < 47 then (-1) else 0)))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then (if n < 53 then 0 else (-1)) else (if n < 55 then 1 else 0))) else 0))) else 0
theorem nestingEntries_eq300 (n : Nat) :
    nestingProjection300.numerator[n]! = nestingEntries300 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries300, if_neg (by omega : ¬ n < 64)]

def nestingProjection301 : Projection := ⟨2,4,#[1,0,0,1,0,0,0,0,0,1,1,0,0,0,0,0,0,1,1,0,0,0,0,0,1,0,0,1,0,0,0,0,0,0,0,0,1,0,0,1,0,0,0,0,0,1,-1,0,0,0,0,0,0,-1,1,0,0,0,0,0,1,0,0,1]⟩
theorem nestingLookup301 : projections[301]! = nestingProjection301 := by
  rw [projections_lookup]
  rfl
def nestingEntries301 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else (if n < 3 then 0 else 1)) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else (if n < 11 then 1 else 0)) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 0 else 1) else (if n < 19 then 1 else 0)) else 0) else (if n < 28 then (if n < 26 then (if n < 25 then 1 else 0) else (if n < 27 then 0 else 1)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 1 else 0) else (if n < 39 then 0 else 1))) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 1) else (if n < 47 then (-1) else 0)))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then (if n < 53 then 0 else (-1)) else (if n < 55 then 1 else 0))) else (if n < 60 then 0 else (if n < 62 then (if n < 61 then 1 else 0) else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq301 (n : Nat) :
    nestingProjection301.numerator[n]! = nestingEntries301 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries301, if_neg (by omega : ¬ n < 64)]

def nestingProjection302 : Projection := ⟨4,4,#[2,-1,-1,0,-1,0,0,1,-1,2,0,1,0,1,-1,0,-1,0,2,1,0,-1,1,0,0,1,1,2,-1,0,0,1,-1,0,0,-1,2,1,1,0,0,1,-1,0,1,2,0,1,0,-1,1,0,1,0,2,1,1,0,0,1,0,1,1,2]⟩
theorem nestingLookup302 : projections[302]! = nestingProjection302 := by
  rw [projections_lookup]
  rfl
def nestingEntries302 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 2 else (-1)) else (if n < 3 then (-1) else 0)) else (if n < 6 then (if n < 5 then (-1) else 0) else (if n < 7 then 0 else 1))) else (if n < 12 then (if n < 10 then (if n < 9 then (-1) else 2) else (if n < 11 then 0 else 1)) else (if n < 14 then (if n < 13 then 0 else 1) else (if n < 15 then (-1) else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then (-1) else 0) else (if n < 19 then 2 else 1)) else (if n < 22 then (if n < 21 then 0 else (-1)) else (if n < 23 then 1 else 0))) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else 1) else (if n < 27 then 1 else 2)) else (if n < 30 then (if n < 29 then (-1) else 0) else (if n < 31 then 0 else 1))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then (-1) else 0) else (if n < 35 then 0 else (-1))) else (if n < 38 then (if n < 37 then 2 else 1) else (if n < 39 then 1 else 0))) else (if n < 44 then (if n < 42 then (if n < 41 then 0 else 1) else (if n < 43 then (-1) else 0)) else (if n < 46 then (if n < 45 then 1 else 2) else (if n < 47 then 0 else 1)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else (-1)) else (if n < 51 then 1 else 0)) else (if n < 54 then (if n < 53 then 1 else 0) else (if n < 55 then 2 else 1))) else (if n < 60 then (if n < 58 then (if n < 57 then 1 else 0) else (if n < 59 then 0 else 1)) else (if n < 62 then (if n < 61 then 0 else 1) else (if n < 63 then 1 else 2)))))) else 0
theorem nestingEntries_eq302 (n : Nat) :
    nestingProjection302.numerator[n]! = nestingEntries302 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries302, if_neg (by omega : ¬ n < 64)]

def nestingProjection303 : Projection := ⟨2,4,#[1,0,0,0,0,0,1,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,1,0,0,1,0,0,0,0,0,1,0,0,0,0,0,0,0,0,2]⟩
theorem nestingLookup303 : projections[303]! = nestingProjection303 := by
  rw [projections_lookup]
  rfl
def nestingEntries303 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else 0) else (if n < 6 then 0 else (if n < 7 then 1 else 0))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 2) else 0) else 0)) else (if n < 24 then 0 else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 1)) else (if n < 30 then (if n < 29 then 0 else 1) else 0)))) else (if n < 48 then (if n < 40 then 0 else (if n < 44 then (if n < 42 then 0 else (if n < 43 then 0 else 1)) else (if n < 46 then (if n < 45 then 0 else 1) else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 1 else 0) else 0) else (if n < 54 then 0 else (if n < 55 then 1 else 0))) else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 2)))))) else 0
theorem nestingEntries_eq303 (n : Nat) :
    nestingProjection303.numerator[n]! = nestingEntries303 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries303, if_neg (by omega : ¬ n < 64)]

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def nestingProjection304 : Projection := ⟨2,4,#[1,0,0,0,0,0,1,0,0,1,0,0,0,0,0,-1,0,0,1,0,-1,0,0,0,0,0,0,1,0,-1,0,0,0,0,-1,0,1,0,0,0,0,0,0,-1,0,1,0,0,1,0,0,0,0,0,1,0,0,-1,0,0,0,0,0,1]⟩
theorem nestingLookup304 : projections[304]! = nestingProjection304 := by
  rw [projections_lookup]
  rfl
def nestingEntries304 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else 0) else (if n < 6 then 0 else (if n < 7 then 1 else 0))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else 0) else (if n < 14 then 0 else (if n < 15 then 0 else (-1))))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 1 else 0)) else (if n < 22 then (if n < 21 then (-1) else 0) else 0)) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 1)) else (if n < 30 then (if n < 29 then 0 else (-1)) else 0)))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then 0 else (if n < 35 then (-1) else 0)) else (if n < 38 then (if n < 37 then 1 else 0) else 0)) else (if n < 44 then (if n < 42 then 0 else (if n < 43 then 0 else (-1))) else (if n < 46 then (if n < 45 then 0 else 1) else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 1 else 0) else 0) else (if n < 54 then 0 else (if n < 55 then 1 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then 0 else (-1)) else 0) else (if n < 62 then 0 else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq304 (n : Nat) :
    nestingProjection304.numerator[n]! = nestingEntries304 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries304, if_neg (by omega : ¬ n < 64)]

def nestingProjection305 : Projection := ⟨2,4,#[1,0,0,0,0,0,-1,0,0,1,0,0,0,0,0,1,0,0,1,0,1,0,0,0,0,0,0,1,0,1,0,0,0,0,1,0,1,0,0,0,0,0,0,1,0,1,0,0,-1,0,0,0,0,0,1,0,0,1,0,0,0,0,0,1]⟩
theorem nestingLookup305 : projections[305]! = nestingProjection305 := by
  rw [projections_lookup]
  rfl
def nestingEntries305 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else 0) else (if n < 6 then 0 else (if n < 7 then (-1) else 0))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else 0) else (if n < 14 then 0 else (if n < 15 then 0 else 1)))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 1 else 0)) else (if n < 22 then (if n < 21 then 1 else 0) else 0)) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 1)) else (if n < 30 then (if n < 29 then 0 else 1) else 0)))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then 0 else (if n < 35 then 1 else 0)) else (if n < 38 then (if n < 37 then 1 else 0) else 0)) else (if n < 44 then (if n < 42 then 0 else (if n < 43 then 0 else 1)) else (if n < 46 then (if n < 45 then 0 else 1) else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then (-1) else 0) else 0) else (if n < 54 then 0 else (if n < 55 then 1 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then 0 else 1) else 0) else (if n < 62 then 0 else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq305 (n : Nat) :
    nestingProjection305.numerator[n]! = nestingEntries305 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries305, if_neg (by omega : ¬ n < 64)]

def nestingProjection306 : Projection := ⟨2,4,#[1,0,0,0,0,0,-1,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,1,0,-1,0,0,0,0,0,0,2,0,0,0,0,0,0,-1,0,1,0,0,-1,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0]⟩
theorem nestingLookup306 : projections[306]! = nestingProjection306 := by
  rw [projections_lookup]
  rfl
def nestingEntries306 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else 0) else (if n < 6 then 0 else (if n < 7 then (-1) else 0))) else 0) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 2 else 0)) else 0) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 1)) else (if n < 30 then (if n < 29 then 0 else (-1)) else 0)))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 2 else 0) else 0)) else (if n < 44 then (if n < 42 then 0 else (if n < 43 then 0 else (-1))) else (if n < 46 then (if n < 45 then 0 else 1) else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then (-1) else 0) else 0) else (if n < 54 then 0 else (if n < 55 then 1 else 0))) else 0))) else 0
theorem nestingEntries_eq306 (n : Nat) :
    nestingProjection306.numerator[n]! = nestingEntries306 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries306, if_neg (by omega : ¬ n < 64)]

def nestingProjection307 : Projection := ⟨4,4,#[2,1,1,0,1,0,0,-1,1,2,0,-1,0,-1,1,0,1,0,2,-1,0,1,-1,0,0,-1,-1,2,1,0,0,-1,1,0,0,1,2,-1,-1,0,0,-1,1,0,-1,2,0,-1,0,1,-1,0,-1,0,2,-1,-1,0,0,-1,0,-1,-1,2]⟩
theorem nestingLookup307 : projections[307]! = nestingProjection307 := by
  rw [projections_lookup]
  rfl
def nestingEntries307 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 2 else 1) else (if n < 3 then 1 else 0)) else (if n < 6 then (if n < 5 then 1 else 0) else (if n < 7 then 0 else (-1)))) else (if n < 12 then (if n < 10 then (if n < 9 then 1 else 2) else (if n < 11 then 0 else (-1))) else (if n < 14 then (if n < 13 then 0 else (-1)) else (if n < 15 then 1 else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 1 else 0) else (if n < 19 then 2 else (-1))) else (if n < 22 then (if n < 21 then 0 else 1) else (if n < 23 then (-1) else 0))) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else (-1)) else (if n < 27 then (-1) else 2)) else (if n < 30 then (if n < 29 then 1 else 0) else (if n < 31 then 0 else (-1)))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 1 else 0) else (if n < 35 then 0 else 1)) else (if n < 38 then (if n < 37 then 2 else (-1)) else (if n < 39 then (-1) else 0))) else (if n < 44 then (if n < 42 then (if n < 41 then 0 else (-1)) else (if n < 43 then 1 else 0)) else (if n < 46 then (if n < 45 then (-1) else 2) else (if n < 47 then 0 else (-1))))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else 1) else (if n < 51 then (-1) else 0)) else (if n < 54 then (if n < 53 then (-1) else 0) else (if n < 55 then 2 else (-1)))) else (if n < 60 then (if n < 58 then (if n < 57 then (-1) else 0) else (if n < 59 then 0 else (-1))) else (if n < 62 then (if n < 61 then 0 else (-1)) else (if n < 63 then (-1) else 2)))))) else 0
theorem nestingEntries_eq307 (n : Nat) :
    nestingProjection307.numerator[n]! = nestingEntries307 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries307, if_neg (by omega : ¬ n < 64)]

def nestingProjection308 : Projection := ⟨4,4,#[2,-1,-1,0,-1,0,0,1,-1,2,0,1,0,-1,1,0,-1,0,2,1,0,1,-1,0,0,1,1,2,-1,0,0,1,-1,0,0,-1,2,-1,-1,0,0,-1,1,0,-1,2,0,-1,0,1,-1,0,-1,0,2,-1,1,0,0,1,0,-1,-1,2]⟩
theorem nestingLookup308 : projections[308]! = nestingProjection308 := by
  rw [projections_lookup]
  rfl
def nestingEntries308 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 2 else (-1)) else (if n < 3 then (-1) else 0)) else (if n < 6 then (if n < 5 then (-1) else 0) else (if n < 7 then 0 else 1))) else (if n < 12 then (if n < 10 then (if n < 9 then (-1) else 2) else (if n < 11 then 0 else 1)) else (if n < 14 then (if n < 13 then 0 else (-1)) else (if n < 15 then 1 else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then (-1) else 0) else (if n < 19 then 2 else 1)) else (if n < 22 then (if n < 21 then 0 else 1) else (if n < 23 then (-1) else 0))) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else 1) else (if n < 27 then 1 else 2)) else (if n < 30 then (if n < 29 then (-1) else 0) else (if n < 31 then 0 else 1))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then (-1) else 0) else (if n < 35 then 0 else (-1))) else (if n < 38 then (if n < 37 then 2 else (-1)) else (if n < 39 then (-1) else 0))) else (if n < 44 then (if n < 42 then (if n < 41 then 0 else (-1)) else (if n < 43 then 1 else 0)) else (if n < 46 then (if n < 45 then (-1) else 2) else (if n < 47 then 0 else (-1))))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else 1) else (if n < 51 then (-1) else 0)) else (if n < 54 then (if n < 53 then (-1) else 0) else (if n < 55 then 2 else (-1)))) else (if n < 60 then (if n < 58 then (if n < 57 then 1 else 0) else (if n < 59 then 0 else 1)) else (if n < 62 then (if n < 61 then 0 else (-1)) else (if n < 63 then (-1) else 2)))))) else 0
theorem nestingEntries_eq308 (n : Nat) :
    nestingProjection308.numerator[n]! = nestingEntries308 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries308, if_neg (by omega : ¬ n < 64)]

def nestingProjection309 : Projection := ⟨2,4,#[1,0,0,0,0,-1,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,1,0,0,-1,0,0,0,0,0,0,0,0,0,-1,0,0,0,0,1,0,0,0,0,0,-1,0,0,1,0,0,0,0,0,0,0,0,2]⟩
theorem nestingLookup309 : projections[309]! = nestingProjection309 := by
  rw [projections_lookup]
  rfl
def nestingEntries309 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else 0) else (if n < 6 then (if n < 5 then 0 else (-1)) else 0)) else 0) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 2 else 0)) else 0) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 1)) else (if n < 30 then 0 else (if n < 31 then (-1) else 0))))) else (if n < 48 then (if n < 40 then 0 else (if n < 44 then (if n < 42 then (if n < 41 then (-1) else 0) else 0) else (if n < 46 then (if n < 45 then 0 else 1) else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then 0 else (if n < 51 then 0 else (-1))) else (if n < 54 then 0 else (if n < 55 then 1 else 0))) else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 2)))))) else 0
theorem nestingEntries_eq309 (n : Nat) :
    nestingProjection309.numerator[n]! = nestingEntries309 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries309, if_neg (by omega : ¬ n < 64)]

def nestingProjection310 : Projection := ⟨2,4,#[1,0,0,0,0,-1,0,0,0,1,0,0,-1,0,0,0,0,0,1,0,0,0,0,-1,0,0,0,1,0,0,1,0,0,-1,0,0,1,0,0,0,-1,0,0,0,0,1,0,0,0,0,0,1,0,0,1,0,0,0,-1,0,0,0,0,1]⟩
theorem nestingLookup310 : projections[310]! = nestingProjection310 := by
  rw [projections_lookup]
  rfl
def nestingEntries310 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else 0) else (if n < 6 then (if n < 5 then 0 else (-1)) else 0)) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else 0) else (if n < 14 then (if n < 13 then (-1) else 0) else 0))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 1 else 0)) else (if n < 22 then 0 else (if n < 23 then 0 else (-1)))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 1)) else (if n < 30 then 0 else (if n < 31 then 1 else 0))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 0 else (-1)) else 0) else (if n < 38 then (if n < 37 then 1 else 0) else 0)) else (if n < 44 then (if n < 42 then (if n < 41 then (-1) else 0) else 0) else (if n < 46 then (if n < 45 then 0 else 1) else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then 0 else (if n < 51 then 0 else 1)) else (if n < 54 then 0 else (if n < 55 then 1 else 0))) else (if n < 60 then (if n < 58 then 0 else (if n < 59 then (-1) else 0)) else (if n < 62 then 0 else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq310 (n : Nat) :
    nestingProjection310.numerator[n]! = nestingEntries310 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries310, if_neg (by omega : ¬ n < 64)]

def nestingProjection311 : Projection := ⟨2,4,#[1,0,0,0,0,1,0,0,0,1,0,0,1,0,0,0,0,0,1,0,0,0,0,1,0,0,0,1,0,0,-1,0,0,1,0,0,1,0,0,0,1,0,0,0,0,1,0,0,0,0,0,-1,0,0,1,0,0,0,1,0,0,0,0,1]⟩
theorem nestingLookup311 : projections[311]! = nestingProjection311 := by
  rw [projections_lookup]
  rfl
def nestingEntries311 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else 0) else (if n < 6 then (if n < 5 then 0 else 1) else 0)) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else 0) else (if n < 14 then (if n < 13 then 1 else 0) else 0))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 1 else 0)) else (if n < 22 then 0 else (if n < 23 then 0 else 1))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 1)) else (if n < 30 then 0 else (if n < 31 then (-1) else 0))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 0 else 1) else 0) else (if n < 38 then (if n < 37 then 1 else 0) else 0)) else (if n < 44 then (if n < 42 then (if n < 41 then 1 else 0) else 0) else (if n < 46 then (if n < 45 then 0 else 1) else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then 0 else (if n < 51 then 0 else (-1))) else (if n < 54 then 0 else (if n < 55 then 1 else 0))) else (if n < 60 then (if n < 58 then 0 else (if n < 59 then 1 else 0)) else (if n < 62 then 0 else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq311 (n : Nat) :
    nestingProjection311.numerator[n]! = nestingEntries311 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries311, if_neg (by omega : ¬ n < 64)]

def nestingProjection312 : Projection := ⟨2,4,#[1,0,0,0,0,1,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,1,0,0,0,0,0,2,0,0,0,1,0,0,0,0,1,0,0,0,0,0,1,0,0,1,0,0,0,0,0,0,0,0,0]⟩
theorem nestingLookup312 : projections[312]! = nestingProjection312 := by
  rw [projections_lookup]
  rfl
def nestingEntries312 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else 0) else (if n < 6 then (if n < 5 then 0 else 1) else 0)) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 2) else 0) else 0)) else (if n < 24 then 0 else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 1)) else (if n < 30 then 0 else (if n < 31 then 1 else 0))))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 2 else 0) else 0)) else (if n < 44 then (if n < 42 then (if n < 41 then 1 else 0) else 0) else (if n < 46 then (if n < 45 then 0 else 1) else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then 0 else (if n < 51 then 0 else 1)) else (if n < 54 then 0 else (if n < 55 then 1 else 0))) else 0))) else 0
theorem nestingEntries_eq312 (n : Nat) :
    nestingProjection312.numerator[n]! = nestingEntries312 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries312, if_neg (by omega : ¬ n < 64)]

def nestingProjection313 : Projection := ⟨4,4,#[2,1,1,0,1,0,0,-1,1,2,0,-1,0,1,-1,0,1,0,2,-1,0,-1,1,0,0,-1,-1,2,1,0,0,-1,1,0,0,1,2,1,1,0,0,1,-1,0,1,2,0,1,0,-1,1,0,1,0,2,1,-1,0,0,-1,0,1,1,2]⟩
theorem nestingLookup313 : projections[313]! = nestingProjection313 := by
  rw [projections_lookup]
  rfl
def nestingEntries313 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 2 else 1) else (if n < 3 then 1 else 0)) else (if n < 6 then (if n < 5 then 1 else 0) else (if n < 7 then 0 else (-1)))) else (if n < 12 then (if n < 10 then (if n < 9 then 1 else 2) else (if n < 11 then 0 else (-1))) else (if n < 14 then (if n < 13 then 0 else 1) else (if n < 15 then (-1) else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 1 else 0) else (if n < 19 then 2 else (-1))) else (if n < 22 then (if n < 21 then 0 else (-1)) else (if n < 23 then 1 else 0))) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else (-1)) else (if n < 27 then (-1) else 2)) else (if n < 30 then (if n < 29 then 1 else 0) else (if n < 31 then 0 else (-1)))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 1 else 0) else (if n < 35 then 0 else 1)) else (if n < 38 then (if n < 37 then 2 else 1) else (if n < 39 then 1 else 0))) else (if n < 44 then (if n < 42 then (if n < 41 then 0 else 1) else (if n < 43 then (-1) else 0)) else (if n < 46 then (if n < 45 then 1 else 2) else (if n < 47 then 0 else 1)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else (-1)) else (if n < 51 then 1 else 0)) else (if n < 54 then (if n < 53 then 1 else 0) else (if n < 55 then 2 else 1))) else (if n < 60 then (if n < 58 then (if n < 57 then (-1) else 0) else (if n < 59 then 0 else (-1))) else (if n < 62 then (if n < 61 then 0 else 1) else (if n < 63 then 1 else 2)))))) else 0
theorem nestingEntries_eq313 (n : Nat) :
    nestingProjection313.numerator[n]! = nestingEntries313 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries313, if_neg (by omega : ¬ n < 64)]

def nestingProjection314 : Projection := ⟨4,4,#[2,1,1,0,1,0,0,-1,1,2,0,1,0,-1,-1,0,1,0,2,1,0,1,1,0,0,1,1,2,-1,0,0,1,1,0,0,-1,2,-1,1,0,0,-1,1,0,-1,2,0,-1,0,-1,1,0,1,0,2,1,-1,0,0,1,0,-1,1,2]⟩
theorem nestingLookup314 : projections[314]! = nestingProjection314 := by
  rw [projections_lookup]
  rfl
def nestingEntries314 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 2 else 1) else (if n < 3 then 1 else 0)) else (if n < 6 then (if n < 5 then 1 else 0) else (if n < 7 then 0 else (-1)))) else (if n < 12 then (if n < 10 then (if n < 9 then 1 else 2) else (if n < 11 then 0 else 1)) else (if n < 14 then (if n < 13 then 0 else (-1)) else (if n < 15 then (-1) else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 1 else 0) else (if n < 19 then 2 else 1)) else (if n < 22 then (if n < 21 then 0 else 1) else (if n < 23 then 1 else 0))) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else 1) else (if n < 27 then 1 else 2)) else (if n < 30 then (if n < 29 then (-1) else 0) else (if n < 31 then 0 else 1))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 1 else 0) else (if n < 35 then 0 else (-1))) else (if n < 38 then (if n < 37 then 2 else (-1)) else (if n < 39 then 1 else 0))) else (if n < 44 then (if n < 42 then (if n < 41 then 0 else (-1)) else (if n < 43 then 1 else 0)) else (if n < 46 then (if n < 45 then (-1) else 2) else (if n < 47 then 0 else (-1))))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else (-1)) else (if n < 51 then 1 else 0)) else (if n < 54 then (if n < 53 then 1 else 0) else (if n < 55 then 2 else 1))) else (if n < 60 then (if n < 58 then (if n < 57 then (-1) else 0) else (if n < 59 then 0 else 1)) else (if n < 62 then (if n < 61 then 0 else (-1)) else (if n < 63 then 1 else 2)))))) else 0
theorem nestingEntries_eq314 (n : Nat) :
    nestingProjection314.numerator[n]! = nestingEntries314 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries314, if_neg (by omega : ¬ n < 64)]

def nestingProjection315 : Projection := ⟨4,4,#[2,-1,-1,0,1,0,0,-1,-1,2,0,-1,0,-1,-1,0,-1,0,2,-1,0,1,1,0,0,-1,-1,2,-1,0,0,1,1,0,0,-1,2,1,-1,0,0,-1,1,0,1,2,0,1,0,-1,1,0,-1,0,2,-1,-1,0,0,1,0,1,-1,2]⟩
theorem nestingLookup315 : projections[315]! = nestingProjection315 := by
  rw [projections_lookup]
  rfl
def nestingEntries315 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 2 else (-1)) else (if n < 3 then (-1) else 0)) else (if n < 6 then (if n < 5 then 1 else 0) else (if n < 7 then 0 else (-1)))) else (if n < 12 then (if n < 10 then (if n < 9 then (-1) else 2) else (if n < 11 then 0 else (-1))) else (if n < 14 then (if n < 13 then 0 else (-1)) else (if n < 15 then (-1) else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then (-1) else 0) else (if n < 19 then 2 else (-1))) else (if n < 22 then (if n < 21 then 0 else 1) else (if n < 23 then 1 else 0))) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else (-1)) else (if n < 27 then (-1) else 2)) else (if n < 30 then (if n < 29 then (-1) else 0) else (if n < 31 then 0 else 1))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 1 else 0) else (if n < 35 then 0 else (-1))) else (if n < 38 then (if n < 37 then 2 else 1) else (if n < 39 then (-1) else 0))) else (if n < 44 then (if n < 42 then (if n < 41 then 0 else (-1)) else (if n < 43 then 1 else 0)) else (if n < 46 then (if n < 45 then 1 else 2) else (if n < 47 then 0 else 1)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else (-1)) else (if n < 51 then 1 else 0)) else (if n < 54 then (if n < 53 then (-1) else 0) else (if n < 55 then 2 else (-1)))) else (if n < 60 then (if n < 58 then (if n < 57 then (-1) else 0) else (if n < 59 then 0 else 1)) else (if n < 62 then (if n < 61 then 0 else 1) else (if n < 63 then (-1) else 2)))))) else 0
theorem nestingEntries_eq315 (n : Nat) :
    nestingProjection315.numerator[n]! = nestingEntries315 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries315, if_neg (by omega : ¬ n < 64)]

def nestingProjection316 : Projection := ⟨4,4,#[2,1,1,0,-1,0,0,1,1,2,0,1,0,-1,-1,0,1,0,2,1,0,1,1,0,0,1,1,2,1,0,0,-1,-1,0,0,1,2,1,-1,0,0,-1,1,0,1,2,0,1,0,-1,1,0,-1,0,2,-1,1,0,0,-1,0,1,-1,2]⟩
theorem nestingLookup316 : projections[316]! = nestingProjection316 := by
  rw [projections_lookup]
  rfl
def nestingEntries316 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 2 else 1) else (if n < 3 then 1 else 0)) else (if n < 6 then (if n < 5 then (-1) else 0) else (if n < 7 then 0 else 1))) else (if n < 12 then (if n < 10 then (if n < 9 then 1 else 2) else (if n < 11 then 0 else 1)) else (if n < 14 then (if n < 13 then 0 else (-1)) else (if n < 15 then (-1) else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 1 else 0) else (if n < 19 then 2 else 1)) else (if n < 22 then (if n < 21 then 0 else 1) else (if n < 23 then 1 else 0))) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else 1) else (if n < 27 then 1 else 2)) else (if n < 30 then (if n < 29 then 1 else 0) else (if n < 31 then 0 else (-1)))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then (-1) else 0) else (if n < 35 then 0 else 1)) else (if n < 38 then (if n < 37 then 2 else 1) else (if n < 39 then (-1) else 0))) else (if n < 44 then (if n < 42 then (if n < 41 then 0 else (-1)) else (if n < 43 then 1 else 0)) else (if n < 46 then (if n < 45 then 1 else 2) else (if n < 47 then 0 else 1)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else (-1)) else (if n < 51 then 1 else 0)) else (if n < 54 then (if n < 53 then (-1) else 0) else (if n < 55 then 2 else (-1)))) else (if n < 60 then (if n < 58 then (if n < 57 then 1 else 0) else (if n < 59 then 0 else (-1))) else (if n < 62 then (if n < 61 then 0 else 1) else (if n < 63 then (-1) else 2)))))) else 0
theorem nestingEntries_eq316 (n : Nat) :
    nestingProjection316.numerator[n]! = nestingEntries316 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries316, if_neg (by omega : ¬ n < 64)]

def nestingProjection317 : Projection := ⟨4,4,#[2,-1,-1,0,1,0,0,-1,-1,2,0,-1,0,1,1,0,-1,0,2,-1,0,-1,-1,0,0,-1,-1,2,-1,0,0,1,1,0,0,-1,2,-1,1,0,0,1,-1,0,-1,2,0,-1,0,1,-1,0,1,0,2,1,-1,0,0,1,0,-1,1,2]⟩
theorem nestingLookup317 : projections[317]! = nestingProjection317 := by
  rw [projections_lookup]
  rfl
def nestingEntries317 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 2 else (-1)) else (if n < 3 then (-1) else 0)) else (if n < 6 then (if n < 5 then 1 else 0) else (if n < 7 then 0 else (-1)))) else (if n < 12 then (if n < 10 then (if n < 9 then (-1) else 2) else (if n < 11 then 0 else (-1))) else (if n < 14 then (if n < 13 then 0 else 1) else (if n < 15 then 1 else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then (-1) else 0) else (if n < 19 then 2 else (-1))) else (if n < 22 then (if n < 21 then 0 else (-1)) else (if n < 23 then (-1) else 0))) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else (-1)) else (if n < 27 then (-1) else 2)) else (if n < 30 then (if n < 29 then (-1) else 0) else (if n < 31 then 0 else 1))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 1 else 0) else (if n < 35 then 0 else (-1))) else (if n < 38 then (if n < 37 then 2 else (-1)) else (if n < 39 then 1 else 0))) else (if n < 44 then (if n < 42 then (if n < 41 then 0 else 1) else (if n < 43 then (-1) else 0)) else (if n < 46 then (if n < 45 then (-1) else 2) else (if n < 47 then 0 else (-1))))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else 1) else (if n < 51 then (-1) else 0)) else (if n < 54 then (if n < 53 then 1 else 0) else (if n < 55 then 2 else 1))) else (if n < 60 then (if n < 58 then (if n < 57 then (-1) else 0) else (if n < 59 then 0 else 1)) else (if n < 62 then (if n < 61 then 0 else (-1)) else (if n < 63 then 1 else 2)))))) else 0
theorem nestingEntries_eq317 (n : Nat) :
    nestingProjection317.numerator[n]! = nestingEntries317 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries317, if_neg (by omega : ¬ n < 64)]

def nestingProjection318 : Projection := ⟨4,4,#[2,1,1,0,-1,0,0,1,1,2,0,1,0,1,1,0,1,0,2,1,0,-1,-1,0,0,1,1,2,1,0,0,-1,-1,0,0,1,2,-1,1,0,0,1,-1,0,-1,2,0,-1,0,1,-1,0,1,0,2,1,1,0,0,-1,0,-1,1,2]⟩
theorem nestingLookup318 : projections[318]! = nestingProjection318 := by
  rw [projections_lookup]
  rfl
def nestingEntries318 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 2 else 1) else (if n < 3 then 1 else 0)) else (if n < 6 then (if n < 5 then (-1) else 0) else (if n < 7 then 0 else 1))) else (if n < 12 then (if n < 10 then (if n < 9 then 1 else 2) else (if n < 11 then 0 else 1)) else (if n < 14 then (if n < 13 then 0 else 1) else (if n < 15 then 1 else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 1 else 0) else (if n < 19 then 2 else 1)) else (if n < 22 then (if n < 21 then 0 else (-1)) else (if n < 23 then (-1) else 0))) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else 1) else (if n < 27 then 1 else 2)) else (if n < 30 then (if n < 29 then 1 else 0) else (if n < 31 then 0 else (-1)))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then (-1) else 0) else (if n < 35 then 0 else 1)) else (if n < 38 then (if n < 37 then 2 else (-1)) else (if n < 39 then 1 else 0))) else (if n < 44 then (if n < 42 then (if n < 41 then 0 else 1) else (if n < 43 then (-1) else 0)) else (if n < 46 then (if n < 45 then (-1) else 2) else (if n < 47 then 0 else (-1))))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else 1) else (if n < 51 then (-1) else 0)) else (if n < 54 then (if n < 53 then 1 else 0) else (if n < 55 then 2 else 1))) else (if n < 60 then (if n < 58 then (if n < 57 then 1 else 0) else (if n < 59 then 0 else (-1))) else (if n < 62 then (if n < 61 then 0 else (-1)) else (if n < 63 then 1 else 2)))))) else 0
theorem nestingEntries_eq318 (n : Nat) :
    nestingProjection318.numerator[n]! = nestingEntries318 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries318, if_neg (by omega : ¬ n < 64)]

def nestingProjection319 : Projection := ⟨4,4,#[2,-1,-1,0,-1,0,0,1,-1,2,0,-1,0,1,1,0,-1,0,2,-1,0,-1,-1,0,0,-1,-1,2,1,0,0,-1,-1,0,0,1,2,1,-1,0,0,1,-1,0,1,2,0,1,0,1,-1,0,-1,0,2,-1,1,0,0,-1,0,1,-1,2]⟩
theorem nestingLookup319 : projections[319]! = nestingProjection319 := by
  rw [projections_lookup]
  rfl
def nestingEntries319 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 2 else (-1)) else (if n < 3 then (-1) else 0)) else (if n < 6 then (if n < 5 then (-1) else 0) else (if n < 7 then 0 else 1))) else (if n < 12 then (if n < 10 then (if n < 9 then (-1) else 2) else (if n < 11 then 0 else (-1))) else (if n < 14 then (if n < 13 then 0 else 1) else (if n < 15 then 1 else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then (-1) else 0) else (if n < 19 then 2 else (-1))) else (if n < 22 then (if n < 21 then 0 else (-1)) else (if n < 23 then (-1) else 0))) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else (-1)) else (if n < 27 then (-1) else 2)) else (if n < 30 then (if n < 29 then 1 else 0) else (if n < 31 then 0 else (-1)))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then (-1) else 0) else (if n < 35 then 0 else 1)) else (if n < 38 then (if n < 37 then 2 else 1) else (if n < 39 then (-1) else 0))) else (if n < 44 then (if n < 42 then (if n < 41 then 0 else 1) else (if n < 43 then (-1) else 0)) else (if n < 46 then (if n < 45 then 1 else 2) else (if n < 47 then 0 else 1)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else 1) else (if n < 51 then (-1) else 0)) else (if n < 54 then (if n < 53 then (-1) else 0) else (if n < 55 then 2 else (-1)))) else (if n < 60 then (if n < 58 then (if n < 57 then 1 else 0) else (if n < 59 then 0 else (-1))) else (if n < 62 then (if n < 61 then 0 else 1) else (if n < 63 then (-1) else 2)))))) else 0
theorem nestingEntries_eq319 (n : Nat) :
    nestingProjection319.numerator[n]! = nestingEntries319 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries319, if_neg (by omega : ¬ n < 64)]

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def nestingProjection320 : Projection := ⟨2,4,#[1,0,0,0,0,0,1,0,0,1,0,0,0,0,0,1,0,0,1,0,1,0,0,0,0,0,0,1,0,-1,0,0,0,0,1,0,1,0,0,0,0,0,0,-1,0,1,0,0,1,0,0,0,0,0,1,0,0,1,0,0,0,0,0,1]⟩
theorem nestingLookup320 : projections[320]! = nestingProjection320 := by
  rw [projections_lookup]
  rfl
def nestingEntries320 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else 0) else (if n < 6 then 0 else (if n < 7 then 1 else 0))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else 0) else (if n < 14 then 0 else (if n < 15 then 0 else 1)))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 1 else 0)) else (if n < 22 then (if n < 21 then 1 else 0) else 0)) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 1)) else (if n < 30 then (if n < 29 then 0 else (-1)) else 0)))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then 0 else (if n < 35 then 1 else 0)) else (if n < 38 then (if n < 37 then 1 else 0) else 0)) else (if n < 44 then (if n < 42 then 0 else (if n < 43 then 0 else (-1))) else (if n < 46 then (if n < 45 then 0 else 1) else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 1 else 0) else 0) else (if n < 54 then 0 else (if n < 55 then 1 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then 0 else 1) else 0) else (if n < 62 then 0 else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq320 (n : Nat) :
    nestingProjection320.numerator[n]! = nestingEntries320 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries320, if_neg (by omega : ¬ n < 64)]

def nestingProjection321 : Projection := ⟨2,4,#[1,0,0,0,0,0,-1,0,0,1,0,0,0,0,0,-1,0,0,1,0,-1,0,0,0,0,0,0,1,0,1,0,0,0,0,-1,0,1,0,0,0,0,0,0,1,0,1,0,0,-1,0,0,0,0,0,1,0,0,-1,0,0,0,0,0,1]⟩
theorem nestingLookup321 : projections[321]! = nestingProjection321 := by
  rw [projections_lookup]
  rfl
def nestingEntries321 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else 0) else (if n < 6 then 0 else (if n < 7 then (-1) else 0))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else 0) else (if n < 14 then 0 else (if n < 15 then 0 else (-1))))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 1 else 0)) else (if n < 22 then (if n < 21 then (-1) else 0) else 0)) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 1)) else (if n < 30 then (if n < 29 then 0 else 1) else 0)))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then 0 else (if n < 35 then (-1) else 0)) else (if n < 38 then (if n < 37 then 1 else 0) else 0)) else (if n < 44 then (if n < 42 then 0 else (if n < 43 then 0 else 1)) else (if n < 46 then (if n < 45 then 0 else 1) else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then (-1) else 0) else 0) else (if n < 54 then 0 else (if n < 55 then 1 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then 0 else (-1)) else 0) else (if n < 62 then 0 else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq321 (n : Nat) :
    nestingProjection321.numerator[n]! = nestingEntries321 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries321, if_neg (by omega : ¬ n < 64)]

def nestingProjection322 : Projection := ⟨2,4,#[1,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,1,0,0,1,0,0,0,0,0,0,0,0,0,1,0,0,0,0,1,0,0,0,0,0,1,0,0,1,0,0,0,0,0,0,0,0,2]⟩
theorem nestingLookup322 : projections[322]! = nestingProjection322 := by
  rw [projections_lookup]
  rfl
def nestingEntries322 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else 0) else (if n < 6 then (if n < 5 then 0 else 1) else 0)) else 0) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 2 else 0)) else 0) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 1)) else (if n < 30 then 0 else (if n < 31 then 1 else 0))))) else (if n < 48 then (if n < 40 then 0 else (if n < 44 then (if n < 42 then (if n < 41 then 1 else 0) else 0) else (if n < 46 then (if n < 45 then 0 else 1) else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then 0 else (if n < 51 then 0 else 1)) else (if n < 54 then 0 else (if n < 55 then 1 else 0))) else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 2)))))) else 0
theorem nestingEntries_eq322 (n : Nat) :
    nestingProjection322.numerator[n]! = nestingEntries322 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries322, if_neg (by omega : ¬ n < 64)]

def nestingProjection323 : Projection := ⟨2,4,#[1,0,0,0,0,-1,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,-1,0,0,0,0,0,2,0,0,0,-1,0,0,0,0,1,0,0,0,0,0,-1,0,0,1,0,0,0,0,0,0,0,0,0]⟩
theorem nestingLookup323 : projections[323]! = nestingProjection323 := by
  rw [projections_lookup]
  rfl
def nestingEntries323 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else 0) else (if n < 6 then (if n < 5 then 0 else (-1)) else 0)) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 2) else 0) else 0)) else (if n < 24 then 0 else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 1)) else (if n < 30 then 0 else (if n < 31 then (-1) else 0))))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 2 else 0) else 0)) else (if n < 44 then (if n < 42 then (if n < 41 then (-1) else 0) else 0) else (if n < 46 then (if n < 45 then 0 else 1) else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then 0 else (if n < 51 then 0 else (-1))) else (if n < 54 then 0 else (if n < 55 then 1 else 0))) else 0))) else 0
theorem nestingEntries_eq323 (n : Nat) :
    nestingProjection323.numerator[n]! = nestingEntries323 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries323, if_neg (by omega : ¬ n < 64)]

def nestingProjection324 : Projection := ⟨4,4,#[2,-1,-1,0,1,0,0,-1,-1,2,0,1,0,-1,1,0,-1,0,2,1,0,1,-1,0,0,1,1,2,1,0,0,-1,1,0,0,1,2,1,1,0,0,-1,1,0,1,2,0,1,0,1,-1,0,1,0,2,1,-1,0,0,-1,0,1,1,2]⟩
theorem nestingLookup324 : projections[324]! = nestingProjection324 := by
  rw [projections_lookup]
  rfl
def nestingEntries324 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 2 else (-1)) else (if n < 3 then (-1) else 0)) else (if n < 6 then (if n < 5 then 1 else 0) else (if n < 7 then 0 else (-1)))) else (if n < 12 then (if n < 10 then (if n < 9 then (-1) else 2) else (if n < 11 then 0 else 1)) else (if n < 14 then (if n < 13 then 0 else (-1)) else (if n < 15 then 1 else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then (-1) else 0) else (if n < 19 then 2 else 1)) else (if n < 22 then (if n < 21 then 0 else 1) else (if n < 23 then (-1) else 0))) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else 1) else (if n < 27 then 1 else 2)) else (if n < 30 then (if n < 29 then 1 else 0) else (if n < 31 then 0 else (-1)))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 1 else 0) else (if n < 35 then 0 else 1)) else (if n < 38 then (if n < 37 then 2 else 1) else (if n < 39 then 1 else 0))) else (if n < 44 then (if n < 42 then (if n < 41 then 0 else (-1)) else (if n < 43 then 1 else 0)) else (if n < 46 then (if n < 45 then 1 else 2) else (if n < 47 then 0 else 1)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else 1) else (if n < 51 then (-1) else 0)) else (if n < 54 then (if n < 53 then 1 else 0) else (if n < 55 then 2 else 1))) else (if n < 60 then (if n < 58 then (if n < 57 then (-1) else 0) else (if n < 59 then 0 else (-1))) else (if n < 62 then (if n < 61 then 0 else 1) else (if n < 63 then 1 else 2)))))) else 0
theorem nestingEntries_eq324 (n : Nat) :
    nestingProjection324.numerator[n]! = nestingEntries324 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries324, if_neg (by omega : ¬ n < 64)]

def nestingProjection325 : Projection := ⟨4,4,#[2,1,1,0,-1,0,0,1,1,2,0,-1,0,1,-1,0,1,0,2,-1,0,-1,1,0,0,-1,-1,2,-1,0,0,1,-1,0,0,-1,2,-1,-1,0,0,1,-1,0,-1,2,0,-1,0,-1,1,0,-1,0,2,-1,1,0,0,1,0,-1,-1,2]⟩
theorem nestingLookup325 : projections[325]! = nestingProjection325 := by
  rw [projections_lookup]
  rfl
def nestingEntries325 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 2 else 1) else (if n < 3 then 1 else 0)) else (if n < 6 then (if n < 5 then (-1) else 0) else (if n < 7 then 0 else 1))) else (if n < 12 then (if n < 10 then (if n < 9 then 1 else 2) else (if n < 11 then 0 else (-1))) else (if n < 14 then (if n < 13 then 0 else 1) else (if n < 15 then (-1) else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 1 else 0) else (if n < 19 then 2 else (-1))) else (if n < 22 then (if n < 21 then 0 else (-1)) else (if n < 23 then 1 else 0))) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else (-1)) else (if n < 27 then (-1) else 2)) else (if n < 30 then (if n < 29 then (-1) else 0) else (if n < 31 then 0 else 1))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then (-1) else 0) else (if n < 35 then 0 else (-1))) else (if n < 38 then (if n < 37 then 2 else (-1)) else (if n < 39 then (-1) else 0))) else (if n < 44 then (if n < 42 then (if n < 41 then 0 else 1) else (if n < 43 then (-1) else 0)) else (if n < 46 then (if n < 45 then (-1) else 2) else (if n < 47 then 0 else (-1))))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else (-1)) else (if n < 51 then 1 else 0)) else (if n < 54 then (if n < 53 then (-1) else 0) else (if n < 55 then 2 else (-1)))) else (if n < 60 then (if n < 58 then (if n < 57 then 1 else 0) else (if n < 59 then 0 else 1)) else (if n < 62 then (if n < 61 then 0 else (-1)) else (if n < 63 then (-1) else 2)))))) else 0
theorem nestingEntries_eq325 (n : Nat) :
    nestingProjection325.numerator[n]! = nestingEntries325 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries325, if_neg (by omega : ¬ n < 64)]

def nestingProjection326 : Projection := ⟨1,6,#[1,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1]⟩
theorem nestingLookup326 : projections[326]! = nestingProjection326 := by
  rw [projections_lookup]
  rfl
def nestingEntries326 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else 0) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else 0) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 1 else 0)) else 0) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 1)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 1 else 0) else 0)) else 0) else (if n < 56 then 0 else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq326 (n : Nat) :
    nestingProjection326.numerator[n]! = nestingEntries326 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries326, if_neg (by omega : ¬ n < 64)]

def nestingProjection327 : Projection := ⟨4,6,#[4,0,0,0,0,0,0,0,0,3,-1,0,-1,0,0,1,0,-1,3,0,-1,0,0,1,0,0,0,4,0,0,0,0,0,-1,-1,0,3,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,0,0,1,1,0,1,0,0,3]⟩
theorem nestingLookup327 : projections[327]! = nestingProjection327 := by
  rw [projections_lookup]
  rfl
def nestingEntries327 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 4 else 0) else 0) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 3) else (if n < 11 then (-1) else 0)) else (if n < 14 then (if n < 13 then (-1) else 0) else (if n < 15 then 0 else 1)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 0 else (-1)) else (if n < 19 then 3 else 0)) else (if n < 22 then (if n < 21 then (-1) else 0) else (if n < 23 then 0 else 1))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 4)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 0 else (-1)) else (if n < 35 then (-1) else 0)) else (if n < 38 then (if n < 37 then 3 else 0) else (if n < 39 then 0 else 1))) else 0) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 0 else (if n < 55 then 4 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then 0 else 1) else (if n < 59 then 1 else 0)) else (if n < 62 then (if n < 61 then 1 else 0) else (if n < 63 then 0 else 3)))))) else 0
theorem nestingEntries_eq327 (n : Nat) :
    nestingProjection327.numerator[n]! = nestingEntries327 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries327, if_neg (by omega : ¬ n < 64)]

def nestingProjection328 : Projection := ⟨4,6,#[4,0,0,0,0,0,0,0,0,3,-1,0,1,0,0,-1,0,-1,3,0,1,0,0,-1,0,0,0,4,0,0,0,0,0,1,1,0,3,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,0,0,-1,-1,0,1,0,0,3]⟩
theorem nestingLookup328 : projections[328]! = nestingProjection328 := by
  rw [projections_lookup]
  rfl
def nestingEntries328 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 4 else 0) else 0) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 3) else (if n < 11 then (-1) else 0)) else (if n < 14 then (if n < 13 then 1 else 0) else (if n < 15 then 0 else (-1))))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 0 else (-1)) else (if n < 19 then 3 else 0)) else (if n < 22 then (if n < 21 then 1 else 0) else (if n < 23 then 0 else (-1)))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 4)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 0 else 1) else (if n < 35 then 1 else 0)) else (if n < 38 then (if n < 37 then 3 else 0) else (if n < 39 then 0 else 1))) else 0) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 0 else (if n < 55 then 4 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then 0 else (-1)) else (if n < 59 then (-1) else 0)) else (if n < 62 then (if n < 61 then 1 else 0) else (if n < 63 then 0 else 3)))))) else 0
theorem nestingEntries_eq328 (n : Nat) :
    nestingProjection328.numerator[n]! = nestingEntries328 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries328, if_neg (by omega : ¬ n < 64)]

def nestingProjection329 : Projection := ⟨4,6,#[4,0,0,0,0,0,0,0,0,3,-1,0,-1,0,0,1,0,-1,3,0,-1,0,0,1,0,0,0,4,0,0,0,0,0,-1,-1,0,3,0,0,1,0,0,0,0,0,4,0,0,0,0,0,0,0,0,0,0,0,1,1,0,1,0,0,3]⟩
theorem nestingLookup329 : projections[329]! = nestingProjection329 := by
  rw [projections_lookup]
  rfl
def nestingEntries329 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 4 else 0) else 0) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 3) else (if n < 11 then (-1) else 0)) else (if n < 14 then (if n < 13 then (-1) else 0) else (if n < 15 then 0 else 1)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 0 else (-1)) else (if n < 19 then 3 else 0)) else (if n < 22 then (if n < 21 then (-1) else 0) else (if n < 23 then 0 else 1))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 4)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 0 else (-1)) else (if n < 35 then (-1) else 0)) else (if n < 38 then (if n < 37 then 3 else 0) else (if n < 39 then 0 else 1))) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 4) else 0))) else (if n < 56 then 0 else (if n < 60 then (if n < 58 then (if n < 57 then 0 else 1) else (if n < 59 then 1 else 0)) else (if n < 62 then (if n < 61 then 1 else 0) else (if n < 63 then 0 else 3)))))) else 0
theorem nestingEntries_eq329 (n : Nat) :
    nestingProjection329.numerator[n]! = nestingEntries329 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries329, if_neg (by omega : ¬ n < 64)]

def nestingProjection330 : Projection := ⟨4,6,#[4,0,0,0,0,0,0,0,0,3,-1,0,1,0,0,-1,0,-1,3,0,1,0,0,-1,0,0,0,4,0,0,0,0,0,1,1,0,3,0,0,1,0,0,0,0,0,4,0,0,0,0,0,0,0,0,0,0,0,-1,-1,0,1,0,0,3]⟩
theorem nestingLookup330 : projections[330]! = nestingProjection330 := by
  rw [projections_lookup]
  rfl
def nestingEntries330 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 4 else 0) else 0) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 3) else (if n < 11 then (-1) else 0)) else (if n < 14 then (if n < 13 then 1 else 0) else (if n < 15 then 0 else (-1))))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 0 else (-1)) else (if n < 19 then 3 else 0)) else (if n < 22 then (if n < 21 then 1 else 0) else (if n < 23 then 0 else (-1)))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 4)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 0 else 1) else (if n < 35 then 1 else 0)) else (if n < 38 then (if n < 37 then 3 else 0) else (if n < 39 then 0 else 1))) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 4) else 0))) else (if n < 56 then 0 else (if n < 60 then (if n < 58 then (if n < 57 then 0 else (-1)) else (if n < 59 then (-1) else 0)) else (if n < 62 then (if n < 61 then 1 else 0) else (if n < 63 then 0 else 3)))))) else 0
theorem nestingEntries_eq330 (n : Nat) :
    nestingProjection330.numerator[n]! = nestingEntries330 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries330, if_neg (by omega : ¬ n < 64)]

def nestingProjection331 : Projection := ⟨2,6,#[2,0,0,0,0,0,0,0,0,1,-1,0,0,0,0,0,0,-1,1,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,1,0,0,1,0,0,0,0,0,2,0,0,0,0,0,0,0,0,2,0,0,0,0,0,1,0,0,1]⟩
theorem nestingLookup331 : projections[331]! = nestingProjection331 := by
  rw [projections_lookup]
  rfl
def nestingEntries331 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 2 else 0) else 0) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else (if n < 11 then (-1) else 0)) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 0 else (-1)) else (if n < 19 then 1 else 0)) else 0) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 2)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 1 else 0) else (if n < 39 then 0 else 1))) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 2) else 0))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 0 else (if n < 55 then 2 else 0))) else (if n < 60 then 0 else (if n < 62 then (if n < 61 then 1 else 0) else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq331 (n : Nat) :
    nestingProjection331.numerator[n]! = nestingEntries331 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries331, if_neg (by omega : ¬ n < 64)]

def nestingProjection332 : Projection := ⟨2,6,#[2,0,0,0,0,0,0,0,0,1,-1,0,0,0,0,0,0,-1,1,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,1,-1,0,0,0,0,0,0,-1,1,0,0,0,0,0,0,0,0,2]⟩
theorem nestingLookup332 : projections[332]! = nestingProjection332 := by
  rw [projections_lookup]
  rfl
def nestingEntries332 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 2 else 0) else 0) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else (if n < 11 then (-1) else 0)) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 0 else (-1)) else (if n < 19 then 1 else 0)) else 0) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 2)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 2 else 0) else 0)) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 1) else (if n < 47 then (-1) else 0)))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then (if n < 53 then 0 else (-1)) else (if n < 55 then 1 else 0))) else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 2)))))) else 0
theorem nestingEntries_eq332 (n : Nat) :
    nestingProjection332.numerator[n]! = nestingEntries332 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries332, if_neg (by omega : ¬ n < 64)]

def nestingProjection333 : Projection := ⟨4,6,#[4,0,0,0,0,0,0,0,0,3,-1,0,0,-1,-1,0,0,-1,3,0,0,-1,-1,0,0,0,0,4,0,0,0,0,0,0,0,0,3,-1,1,1,0,-1,-1,0,-1,2,0,1,0,-1,-1,0,1,0,2,-1,0,0,0,0,1,1,-1,3]⟩
theorem nestingLookup333 : projections[333]! = nestingProjection333 := by
  rw [projections_lookup]
  rfl
def nestingEntries333 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 4 else 0) else 0) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 3) else (if n < 11 then (-1) else 0)) else (if n < 14 then (if n < 13 then 0 else (-1)) else (if n < 15 then (-1) else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 0 else (-1)) else (if n < 19 then 3 else 0)) else (if n < 22 then (if n < 21 then 0 else (-1)) else (if n < 23 then (-1) else 0))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 4)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 3 else (-1)) else 1)) else (if n < 44 then (if n < 42 then (if n < 41 then 0 else (-1)) else (if n < 43 then (-1) else 0)) else (if n < 46 then (if n < 45 then (-1) else 2) else (if n < 47 then 0 else 1)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else (-1)) else (if n < 51 then (-1) else 0)) else (if n < 54 then (if n < 53 then 1 else 0) else (if n < 55 then 2 else (-1)))) else (if n < 60 then 0 else (if n < 62 then 1 else (if n < 63 then (-1) else 3)))))) else 0
theorem nestingEntries_eq333 (n : Nat) :
    nestingProjection333.numerator[n]! = nestingEntries333 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries333, if_neg (by omega : ¬ n < 64)]

def nestingProjection334 : Projection := ⟨4,6,#[4,0,0,0,0,0,0,0,0,3,-1,0,0,-1,-1,0,0,-1,3,0,0,-1,-1,0,0,0,0,4,0,0,0,0,0,0,0,0,3,1,-1,1,0,-1,-1,0,1,2,0,-1,0,-1,-1,0,-1,0,2,1,0,0,0,0,1,-1,1,3]⟩
theorem nestingLookup334 : projections[334]! = nestingProjection334 := by
  rw [projections_lookup]
  rfl
def nestingEntries334 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 4 else 0) else 0) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 3) else (if n < 11 then (-1) else 0)) else (if n < 14 then (if n < 13 then 0 else (-1)) else (if n < 15 then (-1) else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 0 else (-1)) else (if n < 19 then 3 else 0)) else (if n < 22 then (if n < 21 then 0 else (-1)) else (if n < 23 then (-1) else 0))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 4)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 3 else 1) else (if n < 39 then (-1) else 1))) else (if n < 44 then (if n < 42 then (if n < 41 then 0 else (-1)) else (if n < 43 then (-1) else 0)) else (if n < 46 then (if n < 45 then 1 else 2) else (if n < 47 then 0 else (-1))))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else (-1)) else (if n < 51 then (-1) else 0)) else (if n < 54 then (if n < 53 then (-1) else 0) else (if n < 55 then 2 else 1))) else (if n < 60 then 0 else (if n < 62 then (if n < 61 then 1 else (-1)) else (if n < 63 then 1 else 3)))))) else 0
theorem nestingEntries_eq334 (n : Nat) :
    nestingProjection334.numerator[n]! = nestingEntries334 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries334, if_neg (by omega : ¬ n < 64)]

def nestingProjection335 : Projection := ⟨4,6,#[4,0,0,0,0,0,0,0,0,3,-1,0,0,1,1,0,0,-1,3,0,0,1,1,0,0,0,0,4,0,0,0,0,0,0,0,0,3,-1,1,1,0,1,1,0,-1,2,0,1,0,1,1,0,1,0,2,-1,0,0,0,0,1,1,-1,3]⟩
theorem nestingLookup335 : projections[335]! = nestingProjection335 := by
  rw [projections_lookup]
  rfl
def nestingEntries335 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 4 else 0) else 0) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 3) else (if n < 11 then (-1) else 0)) else (if n < 14 then (if n < 13 then 0 else 1) else (if n < 15 then 1 else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 0 else (-1)) else (if n < 19 then 3 else 0)) else (if n < 22 then (if n < 21 then 0 else 1) else (if n < 23 then 1 else 0))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 4)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 3 else (-1)) else 1)) else (if n < 44 then (if n < 42 then (if n < 41 then 0 else 1) else (if n < 43 then 1 else 0)) else (if n < 46 then (if n < 45 then (-1) else 2) else (if n < 47 then 0 else 1)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else 1) else (if n < 51 then 1 else 0)) else (if n < 54 then (if n < 53 then 1 else 0) else (if n < 55 then 2 else (-1)))) else (if n < 60 then 0 else (if n < 62 then 1 else (if n < 63 then (-1) else 3)))))) else 0
theorem nestingEntries_eq335 (n : Nat) :
    nestingProjection335.numerator[n]! = nestingEntries335 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries335, if_neg (by omega : ¬ n < 64)]

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def nestingProjection336 : Projection := ⟨4,6,#[4,0,0,0,0,0,0,0,0,3,-1,0,0,1,1,0,0,-1,3,0,0,1,1,0,0,0,0,4,0,0,0,0,0,0,0,0,3,1,-1,1,0,1,1,0,1,2,0,-1,0,1,1,0,-1,0,2,1,0,0,0,0,1,-1,1,3]⟩
theorem nestingLookup336 : projections[336]! = nestingProjection336 := by
  rw [projections_lookup]
  rfl
def nestingEntries336 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 4 else 0) else 0) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 3) else (if n < 11 then (-1) else 0)) else (if n < 14 then (if n < 13 then 0 else 1) else (if n < 15 then 1 else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 0 else (-1)) else (if n < 19 then 3 else 0)) else (if n < 22 then (if n < 21 then 0 else 1) else (if n < 23 then 1 else 0))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 4)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 3 else 1) else (if n < 39 then (-1) else 1))) else (if n < 44 then (if n < 42 then (if n < 41 then 0 else 1) else (if n < 43 then 1 else 0)) else (if n < 46 then (if n < 45 then 1 else 2) else (if n < 47 then 0 else (-1))))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else 1) else (if n < 51 then 1 else 0)) else (if n < 54 then (if n < 53 then (-1) else 0) else (if n < 55 then 2 else 1))) else (if n < 60 then 0 else (if n < 62 then (if n < 61 then 1 else (-1)) else (if n < 63 then 1 else 3)))))) else 0
theorem nestingEntries_eq336 (n : Nat) :
    nestingProjection336.numerator[n]! = nestingEntries336 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries336, if_neg (by omega : ¬ n < 64)]

def nestingProjection337 : Projection := ⟨2,6,#[2,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,1,0,0,1,0,0,0,0,0,1,1,0,0,0,0,0,0,1,1,0,0,0,0,0,1,0,0,1]⟩
theorem nestingLookup337 : projections[337]! = nestingProjection337 := by
  rw [projections_lookup]
  rfl
def nestingEntries337 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 2 else 0) else 0) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 2) else 0) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 2 else 0)) else 0) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 2)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 1 else 0) else (if n < 39 then 0 else 1))) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 1) else (if n < 47 then 1 else 0)))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then (if n < 53 then 0 else 1) else (if n < 55 then 1 else 0))) else (if n < 60 then 0 else (if n < 62 then (if n < 61 then 1 else 0) else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq337 (n : Nat) :
    nestingProjection337.numerator[n]! = nestingEntries337 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries337, if_neg (by omega : ¬ n < 64)]

def nestingProjection338 : Projection := ⟨2,6,#[2,0,0,0,0,0,0,0,0,1,-1,0,0,0,0,0,0,-1,1,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,1,1,0,0,0,0,0,0,1,1,0,0,0,0,0,0,0,0,2]⟩
theorem nestingLookup338 : projections[338]! = nestingProjection338 := by
  rw [projections_lookup]
  rfl
def nestingEntries338 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 2 else 0) else 0) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else (if n < 11 then (-1) else 0)) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 0 else (-1)) else (if n < 19 then 1 else 0)) else 0) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 2)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 2 else 0) else 0)) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 1) else (if n < 47 then 1 else 0)))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then (if n < 53 then 0 else 1) else (if n < 55 then 1 else 0))) else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 2)))))) else 0
theorem nestingEntries_eq338 (n : Nat) :
    nestingProjection338.numerator[n]! = nestingEntries338 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries338, if_neg (by omega : ¬ n < 64)]

def nestingProjection339 : Projection := ⟨4,6,#[4,0,0,0,0,0,0,0,0,3,-1,0,0,-1,1,0,0,-1,3,0,0,-1,1,0,0,0,0,4,0,0,0,0,0,0,0,0,3,-1,-1,1,0,-1,-1,0,-1,2,0,1,0,1,1,0,-1,0,2,1,0,0,0,0,1,1,1,3]⟩
theorem nestingLookup339 : projections[339]! = nestingProjection339 := by
  rw [projections_lookup]
  rfl
def nestingEntries339 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 4 else 0) else 0) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 3) else (if n < 11 then (-1) else 0)) else (if n < 14 then (if n < 13 then 0 else (-1)) else (if n < 15 then 1 else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 0 else (-1)) else (if n < 19 then 3 else 0)) else (if n < 22 then (if n < 21 then 0 else (-1)) else (if n < 23 then 1 else 0))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 4)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 3 else (-1)) else (if n < 39 then (-1) else 1))) else (if n < 44 then (if n < 42 then (if n < 41 then 0 else (-1)) else (if n < 43 then (-1) else 0)) else (if n < 46 then (if n < 45 then (-1) else 2) else (if n < 47 then 0 else 1)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else 1) else (if n < 51 then 1 else 0)) else (if n < 54 then (if n < 53 then (-1) else 0) else (if n < 55 then 2 else 1))) else (if n < 60 then 0 else (if n < 62 then 1 else (if n < 63 then 1 else 3)))))) else 0
theorem nestingEntries_eq339 (n : Nat) :
    nestingProjection339.numerator[n]! = nestingEntries339 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries339, if_neg (by omega : ¬ n < 64)]

def nestingProjection340 : Projection := ⟨4,6,#[4,0,0,0,0,0,0,0,0,3,-1,0,0,-1,1,0,0,-1,3,0,0,-1,1,0,0,0,0,4,0,0,0,0,0,0,0,0,3,1,1,1,0,-1,-1,0,1,2,0,-1,0,1,1,0,1,0,2,-1,0,0,0,0,1,-1,-1,3]⟩
theorem nestingLookup340 : projections[340]! = nestingProjection340 := by
  rw [projections_lookup]
  rfl
def nestingEntries340 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 4 else 0) else 0) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 3) else (if n < 11 then (-1) else 0)) else (if n < 14 then (if n < 13 then 0 else (-1)) else (if n < 15 then 1 else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 0 else (-1)) else (if n < 19 then 3 else 0)) else (if n < 22 then (if n < 21 then 0 else (-1)) else (if n < 23 then 1 else 0))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 4)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 3 else 1) else 1)) else (if n < 44 then (if n < 42 then (if n < 41 then 0 else (-1)) else (if n < 43 then (-1) else 0)) else (if n < 46 then (if n < 45 then 1 else 2) else (if n < 47 then 0 else (-1))))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else 1) else (if n < 51 then 1 else 0)) else (if n < 54 then (if n < 53 then 1 else 0) else (if n < 55 then 2 else (-1)))) else (if n < 60 then 0 else (if n < 62 then (if n < 61 then 1 else (-1)) else (if n < 63 then (-1) else 3)))))) else 0
theorem nestingEntries_eq340 (n : Nat) :
    nestingProjection340.numerator[n]! = nestingEntries340 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries340, if_neg (by omega : ¬ n < 64)]

def nestingProjection341 : Projection := ⟨4,6,#[4,0,0,0,0,0,0,0,0,3,-1,0,0,1,-1,0,0,-1,3,0,0,1,-1,0,0,0,0,4,0,0,0,0,0,0,0,0,3,-1,-1,1,0,1,1,0,-1,2,0,1,0,-1,-1,0,-1,0,2,1,0,0,0,0,1,1,1,3]⟩
theorem nestingLookup341 : projections[341]! = nestingProjection341 := by
  rw [projections_lookup]
  rfl
def nestingEntries341 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 4 else 0) else 0) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 3) else (if n < 11 then (-1) else 0)) else (if n < 14 then (if n < 13 then 0 else 1) else (if n < 15 then (-1) else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 0 else (-1)) else (if n < 19 then 3 else 0)) else (if n < 22 then (if n < 21 then 0 else 1) else (if n < 23 then (-1) else 0))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 4)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 3 else (-1)) else (if n < 39 then (-1) else 1))) else (if n < 44 then (if n < 42 then (if n < 41 then 0 else 1) else (if n < 43 then 1 else 0)) else (if n < 46 then (if n < 45 then (-1) else 2) else (if n < 47 then 0 else 1)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else (-1)) else (if n < 51 then (-1) else 0)) else (if n < 54 then (if n < 53 then (-1) else 0) else (if n < 55 then 2 else 1))) else (if n < 60 then 0 else (if n < 62 then 1 else (if n < 63 then 1 else 3)))))) else 0
theorem nestingEntries_eq341 (n : Nat) :
    nestingProjection341.numerator[n]! = nestingEntries341 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries341, if_neg (by omega : ¬ n < 64)]

def nestingProjection342 : Projection := ⟨4,6,#[4,0,0,0,0,0,0,0,0,3,-1,0,0,1,-1,0,0,-1,3,0,0,1,-1,0,0,0,0,4,0,0,0,0,0,0,0,0,3,1,1,1,0,1,1,0,1,2,0,-1,0,-1,-1,0,1,0,2,-1,0,0,0,0,1,-1,-1,3]⟩
theorem nestingLookup342 : projections[342]! = nestingProjection342 := by
  rw [projections_lookup]
  rfl
def nestingEntries342 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 4 else 0) else 0) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 3) else (if n < 11 then (-1) else 0)) else (if n < 14 then (if n < 13 then 0 else 1) else (if n < 15 then (-1) else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 0 else (-1)) else (if n < 19 then 3 else 0)) else (if n < 22 then (if n < 21 then 0 else 1) else (if n < 23 then (-1) else 0))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 4)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 3 else 1) else 1)) else (if n < 44 then (if n < 42 then (if n < 41 then 0 else 1) else (if n < 43 then 1 else 0)) else (if n < 46 then (if n < 45 then 1 else 2) else (if n < 47 then 0 else (-1))))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else (-1)) else (if n < 51 then (-1) else 0)) else (if n < 54 then (if n < 53 then 1 else 0) else (if n < 55 then 2 else (-1)))) else (if n < 60 then 0 else (if n < 62 then (if n < 61 then 1 else (-1)) else (if n < 63 then (-1) else 3)))))) else 0
theorem nestingEntries_eq342 (n : Nat) :
    nestingProjection342.numerator[n]! = nestingEntries342 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries342, if_neg (by omega : ¬ n < 64)]

def nestingProjection343 : Projection := ⟨2,6,#[2,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,1,0,0,1,0,0,0,0,0,1,-1,0,0,0,0,0,0,-1,1,0,0,0,0,0,1,0,0,1]⟩
theorem nestingLookup343 : projections[343]! = nestingProjection343 := by
  rw [projections_lookup]
  rfl
def nestingEntries343 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 2 else 0) else 0) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 2) else 0) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 2 else 0)) else 0) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 2)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 1 else 0) else (if n < 39 then 0 else 1))) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 1) else (if n < 47 then (-1) else 0)))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then (if n < 53 then 0 else (-1)) else (if n < 55 then 1 else 0))) else (if n < 60 then 0 else (if n < 62 then (if n < 61 then 1 else 0) else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq343 (n : Nat) :
    nestingProjection343.numerator[n]! = nestingEntries343 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries343, if_neg (by omega : ¬ n < 64)]

def nestingProjection344 : Projection := ⟨1,6,#[0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,1]⟩
theorem nestingLookup344 : projections[344]! = nestingProjection344 := by
  rw [projections_lookup]
  rfl
def nestingEntries344 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then 0 else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else 0) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 1 else 0)) else 0) else 0)) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 1 else 0) else 0)) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 1) else 0))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 0 else (if n < 55 then 1 else 0))) else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq344 (n : Nat) :
    nestingProjection344.numerator[n]! = nestingEntries344 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries344, if_neg (by omega : ¬ n < 64)]

def nestingProjection345 : Projection := ⟨4,6,#[0,0,0,0,0,0,0,0,0,3,1,0,-1,0,0,-1,0,1,3,0,1,0,0,1,0,0,0,4,0,0,0,0,0,-1,1,0,3,0,0,-1,0,0,0,0,0,4,0,0,0,0,0,0,0,0,4,0,0,-1,1,0,-1,0,0,3]⟩
theorem nestingLookup345 : projections[345]! = nestingProjection345 := by
  rw [projections_lookup]
  rfl
def nestingEntries345 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then 0 else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 3) else (if n < 11 then 1 else 0)) else (if n < 14 then (if n < 13 then (-1) else 0) else (if n < 15 then 0 else (-1))))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 0 else 1) else (if n < 19 then 3 else 0)) else (if n < 22 then (if n < 21 then 1 else 0) else (if n < 23 then 0 else 1))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 4)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 0 else (-1)) else (if n < 35 then 1 else 0)) else (if n < 38 then (if n < 37 then 3 else 0) else (if n < 39 then 0 else (-1)))) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 4) else 0))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 0 else (if n < 55 then 4 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then 0 else (-1)) else (if n < 59 then 1 else 0)) else (if n < 62 then (if n < 61 then (-1) else 0) else (if n < 63 then 0 else 3)))))) else 0
theorem nestingEntries_eq345 (n : Nat) :
    nestingProjection345.numerator[n]! = nestingEntries345 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries345, if_neg (by omega : ¬ n < 64)]

def nestingProjection346 : Projection := ⟨4,6,#[0,0,0,0,0,0,0,0,0,3,1,0,1,0,0,1,0,1,3,0,-1,0,0,-1,0,0,0,4,0,0,0,0,0,1,-1,0,3,0,0,-1,0,0,0,0,0,4,0,0,0,0,0,0,0,0,4,0,0,1,-1,0,-1,0,0,3]⟩
theorem nestingLookup346 : projections[346]! = nestingProjection346 := by
  rw [projections_lookup]
  rfl
def nestingEntries346 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then 0 else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 3) else (if n < 11 then 1 else 0)) else (if n < 14 then (if n < 13 then 1 else 0) else (if n < 15 then 0 else 1)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 0 else 1) else (if n < 19 then 3 else 0)) else (if n < 22 then (if n < 21 then (-1) else 0) else (if n < 23 then 0 else (-1)))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 4)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 0 else 1) else (if n < 35 then (-1) else 0)) else (if n < 38 then (if n < 37 then 3 else 0) else (if n < 39 then 0 else (-1)))) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 4) else 0))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 0 else (if n < 55 then 4 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then 0 else 1) else (if n < 59 then (-1) else 0)) else (if n < 62 then (if n < 61 then (-1) else 0) else (if n < 63 then 0 else 3)))))) else 0
theorem nestingEntries_eq346 (n : Nat) :
    nestingProjection346.numerator[n]! = nestingEntries346 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries346, if_neg (by omega : ¬ n < 64)]

def nestingProjection347 : Projection := ⟨4,6,#[4,0,0,0,0,0,0,0,0,3,1,0,-1,0,0,-1,0,1,3,0,1,0,0,1,0,0,0,0,0,0,0,0,0,-1,1,0,3,0,0,-1,0,0,0,0,0,4,0,0,0,0,0,0,0,0,4,0,0,-1,1,0,-1,0,0,3]⟩
theorem nestingLookup347 : projections[347]! = nestingProjection347 := by
  rw [projections_lookup]
  rfl
def nestingEntries347 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 4 else 0) else 0) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 3) else (if n < 11 then 1 else 0)) else (if n < 14 then (if n < 13 then (-1) else 0) else (if n < 15 then 0 else (-1))))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 0 else 1) else (if n < 19 then 3 else 0)) else (if n < 22 then (if n < 21 then 1 else 0) else (if n < 23 then 0 else 1))) else 0)) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 0 else (-1)) else (if n < 35 then 1 else 0)) else (if n < 38 then (if n < 37 then 3 else 0) else (if n < 39 then 0 else (-1)))) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 4) else 0))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 0 else (if n < 55 then 4 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then 0 else (-1)) else (if n < 59 then 1 else 0)) else (if n < 62 then (if n < 61 then (-1) else 0) else (if n < 63 then 0 else 3)))))) else 0
theorem nestingEntries_eq347 (n : Nat) :
    nestingProjection347.numerator[n]! = nestingEntries347 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries347, if_neg (by omega : ¬ n < 64)]

def nestingProjection348 : Projection := ⟨4,6,#[4,0,0,0,0,0,0,0,0,3,1,0,1,0,0,1,0,1,3,0,-1,0,0,-1,0,0,0,0,0,0,0,0,0,1,-1,0,3,0,0,-1,0,0,0,0,0,4,0,0,0,0,0,0,0,0,4,0,0,1,-1,0,-1,0,0,3]⟩
theorem nestingLookup348 : projections[348]! = nestingProjection348 := by
  rw [projections_lookup]
  rfl
def nestingEntries348 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 4 else 0) else 0) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 3) else (if n < 11 then 1 else 0)) else (if n < 14 then (if n < 13 then 1 else 0) else (if n < 15 then 0 else 1)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 0 else 1) else (if n < 19 then 3 else 0)) else (if n < 22 then (if n < 21 then (-1) else 0) else (if n < 23 then 0 else (-1)))) else 0)) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 0 else 1) else (if n < 35 then (-1) else 0)) else (if n < 38 then (if n < 37 then 3 else 0) else (if n < 39 then 0 else (-1)))) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 4) else 0))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 0 else (if n < 55 then 4 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then 0 else 1) else (if n < 59 then (-1) else 0)) else (if n < 62 then (if n < 61 then (-1) else 0) else (if n < 63 then 0 else 3)))))) else 0
theorem nestingEntries_eq348 (n : Nat) :
    nestingProjection348.numerator[n]! = nestingEntries348 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries348, if_neg (by omega : ¬ n < 64)]

def nestingProjection349 : Projection := ⟨2,6,#[2,0,0,0,0,0,0,0,0,1,1,0,0,0,0,0,0,1,1,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,1,0,0,-1,0,0,0,0,0,2,0,0,0,0,0,0,0,0,2,0,0,0,0,0,-1,0,0,1]⟩
theorem nestingLookup349 : projections[349]! = nestingProjection349 := by
  rw [projections_lookup]
  rfl
def nestingEntries349 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 2 else 0) else 0) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else (if n < 11 then 1 else 0)) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 0 else 1) else (if n < 19 then 1 else 0)) else 0) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 2)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 1 else 0) else (if n < 39 then 0 else (-1)))) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 2) else 0))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 0 else (if n < 55 then 2 else 0))) else (if n < 60 then 0 else (if n < 62 then (if n < 61 then (-1) else 0) else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq349 (n : Nat) :
    nestingProjection349.numerator[n]! = nestingEntries349 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries349, if_neg (by omega : ¬ n < 64)]

def nestingProjection350 : Projection := ⟨2,6,#[1,0,0,-1,0,0,0,0,0,1,1,0,0,0,0,0,0,1,1,0,0,0,0,0,-1,0,0,1,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,2]⟩
theorem nestingLookup350 : projections[350]! = nestingProjection350 := by
  rw [projections_lookup]
  rfl
def nestingEntries350 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else (if n < 3 then 0 else (-1))) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else (if n < 11 then 1 else 0)) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 0 else 1) else (if n < 19 then 1 else 0)) else 0) else (if n < 28 then (if n < 26 then (if n < 25 then (-1) else 0) else (if n < 27 then 0 else 1)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 2 else 0) else 0)) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 2) else 0))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 0 else (if n < 55 then 2 else 0))) else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 2)))))) else 0
theorem nestingEntries_eq350 (n : Nat) :
    nestingProjection350.numerator[n]! = nestingEntries350 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries350, if_neg (by omega : ¬ n < 64)]

def nestingProjection351 : Projection := ⟨4,6,#[2,-1,1,0,-1,0,0,-1,-1,3,1,-1,0,0,0,0,1,1,3,1,0,0,0,0,0,-1,1,2,1,0,0,1,-1,0,0,1,3,0,0,-1,0,0,0,0,0,4,0,0,0,0,0,0,0,0,4,0,-1,0,0,1,-1,0,0,3]⟩
theorem nestingLookup351 : projections[351]! = nestingProjection351 := by
  rw [projections_lookup]
  rfl
def nestingEntries351 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 2 else (-1)) else (if n < 3 then 1 else 0)) else (if n < 6 then (if n < 5 then (-1) else 0) else (if n < 7 then 0 else (-1)))) else (if n < 12 then (if n < 10 then (if n < 9 then (-1) else 3) else (if n < 11 then 1 else (-1))) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then 1 else (if n < 19 then 3 else 1)) else 0) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else (-1)) else (if n < 27 then 1 else 2)) else (if n < 30 then (if n < 29 then 1 else 0) else (if n < 31 then 0 else 1))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then (-1) else 0) else (if n < 35 then 0 else 1)) else (if n < 38 then (if n < 37 then 3 else 0) else (if n < 39 then 0 else (-1)))) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 4) else 0))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 0 else (if n < 55 then 4 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then (-1) else 0) else (if n < 59 then 0 else 1)) else (if n < 62 then (if n < 61 then (-1) else 0) else (if n < 63 then 0 else 3)))))) else 0
theorem nestingEntries_eq351 (n : Nat) :
    nestingProjection351.numerator[n]! = nestingEntries351 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries351, if_neg (by omega : ¬ n < 64)]

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def nestingProjection352 : Projection := ⟨4,6,#[2,-1,1,0,1,0,0,1,-1,3,1,-1,0,0,0,0,1,1,3,1,0,0,0,0,0,-1,1,2,-1,0,0,-1,1,0,0,-1,3,0,0,-1,0,0,0,0,0,4,0,0,0,0,0,0,0,0,4,0,1,0,0,-1,-1,0,0,3]⟩
theorem nestingLookup352 : projections[352]! = nestingProjection352 := by
  rw [projections_lookup]
  rfl
def nestingEntries352 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 2 else (-1)) else (if n < 3 then 1 else 0)) else (if n < 6 then (if n < 5 then 1 else 0) else (if n < 7 then 0 else 1))) else (if n < 12 then (if n < 10 then (if n < 9 then (-1) else 3) else (if n < 11 then 1 else (-1))) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then 1 else (if n < 19 then 3 else 1)) else 0) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else (-1)) else (if n < 27 then 1 else 2)) else (if n < 30 then (if n < 29 then (-1) else 0) else (if n < 31 then 0 else (-1)))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 1 else 0) else (if n < 35 then 0 else (-1))) else (if n < 38 then (if n < 37 then 3 else 0) else (if n < 39 then 0 else (-1)))) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 4) else 0))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 0 else (if n < 55 then 4 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then 1 else 0) else (if n < 59 then 0 else (-1))) else (if n < 62 then (if n < 61 then (-1) else 0) else (if n < 63 then 0 else 3)))))) else 0
theorem nestingEntries_eq352 (n : Nat) :
    nestingProjection352.numerator[n]! = nestingEntries352 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries352, if_neg (by omega : ¬ n < 64)]

def nestingProjection353 : Projection := ⟨4,6,#[2,1,-1,0,-1,0,0,-1,1,3,1,1,0,0,0,0,-1,1,3,-1,0,0,0,0,0,1,-1,2,1,0,0,1,-1,0,0,1,3,0,0,-1,0,0,0,0,0,4,0,0,0,0,0,0,0,0,4,0,-1,0,0,1,-1,0,0,3]⟩
theorem nestingLookup353 : projections[353]! = nestingProjection353 := by
  rw [projections_lookup]
  rfl
def nestingEntries353 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 2 else 1) else (if n < 3 then (-1) else 0)) else (if n < 6 then (if n < 5 then (-1) else 0) else (if n < 7 then 0 else (-1)))) else (if n < 12 then (if n < 10 then (if n < 9 then 1 else 3) else 1) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then (-1) else 1) else (if n < 19 then 3 else (-1))) else 0) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else 1) else (if n < 27 then (-1) else 2)) else (if n < 30 then (if n < 29 then 1 else 0) else (if n < 31 then 0 else 1))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then (-1) else 0) else (if n < 35 then 0 else 1)) else (if n < 38 then (if n < 37 then 3 else 0) else (if n < 39 then 0 else (-1)))) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 4) else 0))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 0 else (if n < 55 then 4 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then (-1) else 0) else (if n < 59 then 0 else 1)) else (if n < 62 then (if n < 61 then (-1) else 0) else (if n < 63 then 0 else 3)))))) else 0
theorem nestingEntries_eq353 (n : Nat) :
    nestingProjection353.numerator[n]! = nestingEntries353 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries353, if_neg (by omega : ¬ n < 64)]

def nestingProjection354 : Projection := ⟨4,6,#[2,1,-1,0,1,0,0,1,1,3,1,1,0,0,0,0,-1,1,3,-1,0,0,0,0,0,1,-1,2,-1,0,0,-1,1,0,0,-1,3,0,0,-1,0,0,0,0,0,4,0,0,0,0,0,0,0,0,4,0,1,0,0,-1,-1,0,0,3]⟩
theorem nestingLookup354 : projections[354]! = nestingProjection354 := by
  rw [projections_lookup]
  rfl
def nestingEntries354 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 2 else 1) else (if n < 3 then (-1) else 0)) else (if n < 6 then (if n < 5 then 1 else 0) else (if n < 7 then 0 else 1))) else (if n < 12 then (if n < 10 then (if n < 9 then 1 else 3) else 1) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then (-1) else 1) else (if n < 19 then 3 else (-1))) else 0) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else 1) else (if n < 27 then (-1) else 2)) else (if n < 30 then (if n < 29 then (-1) else 0) else (if n < 31 then 0 else (-1)))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 1 else 0) else (if n < 35 then 0 else (-1))) else (if n < 38 then (if n < 37 then 3 else 0) else (if n < 39 then 0 else (-1)))) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 4) else 0))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 0 else (if n < 55 then 4 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then 1 else 0) else (if n < 59 then 0 else (-1))) else (if n < 62 then (if n < 61 then (-1) else 0) else (if n < 63 then 0 else 3)))))) else 0
theorem nestingEntries_eq354 (n : Nat) :
    nestingProjection354.numerator[n]! = nestingEntries354 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries354, if_neg (by omega : ¬ n < 64)]

def nestingProjection355 : Projection := ⟨2,6,#[1,0,0,1,0,0,0,0,0,2,0,0,0,0,0,0,0,0,2,0,0,0,0,0,1,0,0,1,0,0,0,0,0,0,0,0,1,0,0,-1,0,0,0,0,0,2,0,0,0,0,0,0,0,0,2,0,0,0,0,0,-1,0,0,1]⟩
theorem nestingLookup355 : projections[355]! = nestingProjection355 := by
  rw [projections_lookup]
  rfl
def nestingEntries355 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else (if n < 3 then 0 else 1)) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 2) else 0) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 2 else 0)) else 0) else (if n < 28 then (if n < 26 then (if n < 25 then 1 else 0) else (if n < 27 then 0 else 1)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 1 else 0) else (if n < 39 then 0 else (-1)))) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 2) else 0))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 0 else (if n < 55 then 2 else 0))) else (if n < 60 then 0 else (if n < 62 then (if n < 61 then (-1) else 0) else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq355 (n : Nat) :
    nestingProjection355.numerator[n]! = nestingEntries355 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries355, if_neg (by omega : ¬ n < 64)]

def nestingProjection356 : Projection := ⟨2,6,#[1,0,0,1,0,0,0,0,0,1,1,0,0,0,0,0,0,1,1,0,0,0,0,0,1,0,0,1,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,2]⟩
theorem nestingLookup356 : projections[356]! = nestingProjection356 := by
  rw [projections_lookup]
  rfl
def nestingEntries356 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else (if n < 3 then 0 else 1)) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 1) else (if n < 11 then 1 else 0)) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 0 else 1) else (if n < 19 then 1 else 0)) else 0) else (if n < 28 then (if n < 26 then (if n < 25 then 1 else 0) else (if n < 27 then 0 else 1)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 2 else 0) else 0)) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 2) else 0))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 0 else (if n < 55 then 2 else 0))) else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 2)))))) else 0
theorem nestingEntries_eq356 (n : Nat) :
    nestingProjection356.numerator[n]! = nestingEntries356 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries356, if_neg (by omega : ¬ n < 64)]

def nestingProjection357 : Projection := ⟨4,6,#[2,-1,1,0,-1,0,0,-1,-1,3,1,1,0,0,0,0,1,1,3,-1,0,0,0,0,0,1,-1,2,-1,0,0,-1,-1,0,0,-1,3,0,0,-1,0,0,0,0,0,4,0,0,0,0,0,0,0,0,4,0,-1,0,0,-1,-1,0,0,3]⟩
theorem nestingLookup357 : projections[357]! = nestingProjection357 := by
  rw [projections_lookup]
  rfl
def nestingEntries357 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 2 else (-1)) else (if n < 3 then 1 else 0)) else (if n < 6 then (if n < 5 then (-1) else 0) else (if n < 7 then 0 else (-1)))) else (if n < 12 then (if n < 10 then (if n < 9 then (-1) else 3) else 1) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then 1 else (if n < 19 then 3 else (-1))) else 0) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else 1) else (if n < 27 then (-1) else 2)) else (if n < 30 then (if n < 29 then (-1) else 0) else (if n < 31 then 0 else (-1)))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then (-1) else 0) else (if n < 35 then 0 else (-1))) else (if n < 38 then (if n < 37 then 3 else 0) else (if n < 39 then 0 else (-1)))) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 4) else 0))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 0 else (if n < 55 then 4 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then (-1) else 0) else (if n < 59 then 0 else (-1))) else (if n < 62 then (if n < 61 then (-1) else 0) else (if n < 63 then 0 else 3)))))) else 0
theorem nestingEntries_eq357 (n : Nat) :
    nestingProjection357.numerator[n]! = nestingEntries357 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries357, if_neg (by omega : ¬ n < 64)]

def nestingProjection358 : Projection := ⟨4,6,#[2,-1,1,0,1,0,0,1,-1,3,1,1,0,0,0,0,1,1,3,-1,0,0,0,0,0,1,-1,2,1,0,0,1,1,0,0,1,3,0,0,-1,0,0,0,0,0,4,0,0,0,0,0,0,0,0,4,0,1,0,0,1,-1,0,0,3]⟩
theorem nestingLookup358 : projections[358]! = nestingProjection358 := by
  rw [projections_lookup]
  rfl
def nestingEntries358 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 2 else (-1)) else (if n < 3 then 1 else 0)) else (if n < 6 then (if n < 5 then 1 else 0) else (if n < 7 then 0 else 1))) else (if n < 12 then (if n < 10 then (if n < 9 then (-1) else 3) else 1) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then 1 else (if n < 19 then 3 else (-1))) else 0) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else 1) else (if n < 27 then (-1) else 2)) else (if n < 30 then (if n < 29 then 1 else 0) else (if n < 31 then 0 else 1))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 1 else 0) else (if n < 35 then 0 else 1)) else (if n < 38 then (if n < 37 then 3 else 0) else (if n < 39 then 0 else (-1)))) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 4) else 0))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 0 else (if n < 55 then 4 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then 1 else 0) else (if n < 59 then 0 else 1)) else (if n < 62 then (if n < 61 then (-1) else 0) else (if n < 63 then 0 else 3)))))) else 0
theorem nestingEntries_eq358 (n : Nat) :
    nestingProjection358.numerator[n]! = nestingEntries358 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries358, if_neg (by omega : ¬ n < 64)]

def nestingProjection359 : Projection := ⟨4,6,#[2,1,-1,0,-1,0,0,-1,1,3,1,-1,0,0,0,0,-1,1,3,1,0,0,0,0,0,-1,1,2,-1,0,0,-1,-1,0,0,-1,3,0,0,-1,0,0,0,0,0,4,0,0,0,0,0,0,0,0,4,0,-1,0,0,-1,-1,0,0,3]⟩
theorem nestingLookup359 : projections[359]! = nestingProjection359 := by
  rw [projections_lookup]
  rfl
def nestingEntries359 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 2 else 1) else (if n < 3 then (-1) else 0)) else (if n < 6 then (if n < 5 then (-1) else 0) else (if n < 7 then 0 else (-1)))) else (if n < 12 then (if n < 10 then (if n < 9 then 1 else 3) else (if n < 11 then 1 else (-1))) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then (-1) else 1) else (if n < 19 then 3 else 1)) else 0) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else (-1)) else (if n < 27 then 1 else 2)) else (if n < 30 then (if n < 29 then (-1) else 0) else (if n < 31 then 0 else (-1)))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then (-1) else 0) else (if n < 35 then 0 else (-1))) else (if n < 38 then (if n < 37 then 3 else 0) else (if n < 39 then 0 else (-1)))) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 4) else 0))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 0 else (if n < 55 then 4 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then (-1) else 0) else (if n < 59 then 0 else (-1))) else (if n < 62 then (if n < 61 then (-1) else 0) else (if n < 63 then 0 else 3)))))) else 0
theorem nestingEntries_eq359 (n : Nat) :
    nestingProjection359.numerator[n]! = nestingEntries359 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries359, if_neg (by omega : ¬ n < 64)]

def nestingProjection360 : Projection := ⟨4,6,#[2,1,-1,0,1,0,0,1,1,3,1,-1,0,0,0,0,-1,1,3,1,0,0,0,0,0,-1,1,2,1,0,0,1,1,0,0,1,3,0,0,-1,0,0,0,0,0,4,0,0,0,0,0,0,0,0,4,0,1,0,0,1,-1,0,0,3]⟩
theorem nestingLookup360 : projections[360]! = nestingProjection360 := by
  rw [projections_lookup]
  rfl
def nestingEntries360 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 2 else 1) else (if n < 3 then (-1) else 0)) else (if n < 6 then (if n < 5 then 1 else 0) else (if n < 7 then 0 else 1))) else (if n < 12 then (if n < 10 then (if n < 9 then 1 else 3) else (if n < 11 then 1 else (-1))) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then (-1) else 1) else (if n < 19 then 3 else 1)) else 0) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else (-1)) else (if n < 27 then 1 else 2)) else (if n < 30 then (if n < 29 then 1 else 0) else (if n < 31 then 0 else 1))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 1 else 0) else (if n < 35 then 0 else 1)) else (if n < 38 then (if n < 37 then 3 else 0) else (if n < 39 then 0 else (-1)))) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 4) else 0))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 0 else (if n < 55 then 4 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then 1 else 0) else (if n < 59 then 0 else 1)) else (if n < 62 then (if n < 61 then (-1) else 0) else (if n < 63 then 0 else 3)))))) else 0
theorem nestingEntries_eq360 (n : Nat) :
    nestingProjection360.numerator[n]! = nestingEntries360 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries360, if_neg (by omega : ¬ n < 64)]

def nestingProjection361 : Projection := ⟨2,6,#[1,0,0,-1,0,0,0,0,0,2,0,0,0,0,0,0,0,0,2,0,0,0,0,0,-1,0,0,1,0,0,0,0,0,0,0,0,1,0,0,-1,0,0,0,0,0,2,0,0,0,0,0,0,0,0,2,0,0,0,0,0,-1,0,0,1]⟩
theorem nestingLookup361 : projections[361]! = nestingProjection361 := by
  rw [projections_lookup]
  rfl
def nestingEntries361 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 1 else 0) else (if n < 3 then 0 else (-1))) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 2) else 0) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 2 else 0)) else 0) else (if n < 28 then (if n < 26 then (if n < 25 then (-1) else 0) else (if n < 27 then 0 else 1)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 1 else 0) else (if n < 39 then 0 else (-1)))) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 2) else 0))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 0 else (if n < 55 then 2 else 0))) else (if n < 60 then 0 else (if n < 62 then (if n < 61 then (-1) else 0) else (if n < 63 then 0 else 1)))))) else 0
theorem nestingEntries_eq361 (n : Nat) :
    nestingProjection361.numerator[n]! = nestingEntries361 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries361, if_neg (by omega : ¬ n < 64)]

def nestingProjection362 : Projection := ⟨4,6,#[2,-1,-1,0,-1,0,0,1,-1,3,0,0,0,0,-1,1,-1,0,3,0,-1,0,1,0,0,0,0,4,0,0,0,0,-1,0,-1,0,3,0,1,0,0,0,0,0,0,4,0,0,0,-1,1,0,1,0,2,1,1,1,0,0,0,0,1,3]⟩
theorem nestingLookup362 : projections[362]! = nestingProjection362 := by
  rw [projections_lookup]
  rfl
def nestingEntries362 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 2 else (-1)) else (if n < 3 then (-1) else 0)) else (if n < 6 then (if n < 5 then (-1) else 0) else (if n < 7 then 0 else 1))) else (if n < 12 then (if n < 10 then (if n < 9 then (-1) else 3) else 0) else (if n < 14 then 0 else (if n < 15 then (-1) else 1)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then (-1) else 0) else (if n < 19 then 3 else 0)) else (if n < 22 then (if n < 21 then (-1) else 0) else (if n < 23 then 1 else 0))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 4)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then (-1) else 0) else (if n < 35 then (-1) else 0)) else (if n < 38 then (if n < 37 then 3 else 0) else (if n < 39 then 1 else 0))) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 4) else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else (-1)) else (if n < 51 then 1 else 0)) else (if n < 54 then (if n < 53 then 1 else 0) else (if n < 55 then 2 else 1))) else (if n < 60 then (if n < 58 then 1 else 0) else (if n < 62 then 0 else (if n < 63 then 1 else 3)))))) else 0
theorem nestingEntries_eq362 (n : Nat) :
    nestingProjection362.numerator[n]! = nestingEntries362 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries362, if_neg (by omega : ¬ n < 64)]

def nestingProjection363 : Projection := ⟨4,6,#[3,0,-1,0,-1,0,1,0,0,4,0,0,0,0,0,0,-1,0,2,-1,0,1,1,0,0,0,-1,3,1,1,0,0,-1,0,0,1,2,-1,1,0,0,0,1,1,-1,3,0,0,1,0,1,0,1,0,3,0,0,0,0,0,0,0,0,4]⟩
theorem nestingLookup363 : projections[363]! = nestingProjection363 := by
  rw [projections_lookup]
  rfl
def nestingEntries363 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 0) else (if n < 3 then (-1) else 0)) else (if n < 6 then (if n < 5 then (-1) else 0) else (if n < 7 then 1 else 0))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 4) else 0) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then (-1) else 0) else (if n < 19 then 2 else (-1))) else (if n < 22 then (if n < 21 then 0 else 1) else (if n < 23 then 1 else 0))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then (-1) else 3)) else (if n < 30 then 1 else 0)))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then (-1) else 0) else (if n < 35 then 0 else 1)) else (if n < 38 then (if n < 37 then 2 else (-1)) else (if n < 39 then 1 else 0))) else (if n < 44 then (if n < 42 then 0 else 1) else (if n < 46 then (if n < 45 then (-1) else 3) else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 1 else 0) else (if n < 51 then 1 else 0)) else (if n < 54 then (if n < 53 then 1 else 0) else (if n < 55 then 3 else 0))) else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 4)))))) else 0
theorem nestingEntries_eq363 (n : Nat) :
    nestingProjection363.numerator[n]! = nestingEntries363 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries363, if_neg (by omega : ¬ n < 64)]

def nestingProjection364 : Projection := ⟨4,6,#[3,0,-1,0,-1,0,1,0,0,3,0,-1,0,-1,0,-1,-1,0,3,0,-1,0,1,0,0,-1,0,3,0,-1,0,-1,-1,0,-1,0,3,0,1,0,0,-1,0,-1,0,3,0,-1,1,0,1,0,1,0,3,0,0,-1,0,-1,0,-1,0,3]⟩
theorem nestingLookup364 : projections[364]! = nestingProjection364 := by
  rw [projections_lookup]
  rfl
def nestingEntries364 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 0) else (if n < 3 then (-1) else 0)) else (if n < 6 then (if n < 5 then (-1) else 0) else (if n < 7 then 1 else 0))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 3) else (if n < 11 then 0 else (-1))) else (if n < 14 then (if n < 13 then 0 else (-1)) else (if n < 15 then 0 else (-1))))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then (-1) else 0) else (if n < 19 then 3 else 0)) else (if n < 22 then (if n < 21 then (-1) else 0) else (if n < 23 then 1 else 0))) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else (-1)) else (if n < 27 then 0 else 3)) else (if n < 30 then (if n < 29 then 0 else (-1)) else (if n < 31 then 0 else (-1)))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then (-1) else 0) else (if n < 35 then (-1) else 0)) else (if n < 38 then (if n < 37 then 3 else 0) else (if n < 39 then 1 else 0))) else (if n < 44 then (if n < 42 then (if n < 41 then 0 else (-1)) else (if n < 43 then 0 else (-1))) else (if n < 46 then (if n < 45 then 0 else 3) else (if n < 47 then 0 else (-1))))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 1 else 0) else (if n < 51 then 1 else 0)) else (if n < 54 then (if n < 53 then 1 else 0) else (if n < 55 then 3 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then 0 else (-1)) else (if n < 59 then 0 else (-1))) else (if n < 62 then (if n < 61 then 0 else (-1)) else (if n < 63 then 0 else 3)))))) else 0
theorem nestingEntries_eq364 (n : Nat) :
    nestingProjection364.numerator[n]! = nestingEntries364 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries364, if_neg (by omega : ¬ n < 64)]

def nestingProjection365 : Projection := ⟨4,6,#[3,-1,0,0,0,0,-1,1,-1,3,0,0,0,0,-1,1,0,0,3,-1,1,1,0,0,0,0,-1,3,1,1,0,0,0,0,1,1,3,-1,0,0,0,0,1,1,-1,3,0,0,-1,-1,0,0,0,0,3,1,1,1,0,0,0,0,1,3]⟩
theorem nestingLookup365 : projections[365]! = nestingProjection365 := by
  rw [projections_lookup]
  rfl
def nestingEntries365 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else (-1)) else 0) else (if n < 6 then 0 else (if n < 7 then (-1) else 1))) else (if n < 12 then (if n < 10 then (if n < 9 then (-1) else 3) else 0) else (if n < 14 then 0 else (if n < 15 then (-1) else 1)))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 3 else (-1))) else (if n < 22 then 1 else 0)) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then (-1) else 3)) else (if n < 30 then 1 else 0)))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then 0 else 1) else (if n < 38 then (if n < 37 then 3 else (-1)) else 0)) else (if n < 44 then (if n < 42 then 0 else 1) else (if n < 46 then (if n < 45 then (-1) else 3) else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then (-1) else 0) else (if n < 54 then 0 else (if n < 55 then 3 else 1))) else (if n < 60 then (if n < 58 then 1 else 0) else (if n < 62 then 0 else (if n < 63 then 1 else 3)))))) else 0
theorem nestingEntries_eq365 (n : Nat) :
    nestingProjection365.numerator[n]! = nestingEntries365 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries365, if_neg (by omega : ¬ n < 64)]

def nestingProjection366 : Projection := ⟨4,6,#[3,-1,0,0,0,0,-1,1,-1,2,0,-1,0,-1,-1,0,0,0,4,0,0,0,0,0,0,-1,0,3,0,-1,0,-1,0,0,0,0,4,0,0,0,0,-1,0,-1,0,3,0,-1,-1,-1,0,0,0,0,3,1,1,0,0,-1,0,-1,1,2]⟩
theorem nestingLookup366 : projections[366]! = nestingProjection366 := by
  rw [projections_lookup]
  rfl
def nestingEntries366 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else (-1)) else 0) else (if n < 6 then 0 else (if n < 7 then (-1) else 1))) else (if n < 12 then (if n < 10 then (if n < 9 then (-1) else 2) else (if n < 11 then 0 else (-1))) else (if n < 14 then (if n < 13 then 0 else (-1)) else (if n < 15 then (-1) else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 4 else 0)) else 0) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else (-1)) else (if n < 27 then 0 else 3)) else (if n < 30 then (if n < 29 then 0 else (-1)) else (if n < 31 then 0 else (-1)))))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 4 else 0) else 0)) else (if n < 44 then (if n < 42 then (if n < 41 then 0 else (-1)) else (if n < 43 then 0 else (-1))) else (if n < 46 then (if n < 45 then 0 else 3) else (if n < 47 then 0 else (-1))))) else (if n < 56 then (if n < 52 then (if n < 50 then (-1) else 0) else (if n < 54 then 0 else (if n < 55 then 3 else 1))) else (if n < 60 then (if n < 58 then (if n < 57 then 1 else 0) else (if n < 59 then 0 else (-1))) else (if n < 62 then (if n < 61 then 0 else (-1)) else (if n < 63 then 1 else 2)))))) else 0
theorem nestingEntries_eq366 (n : Nat) :
    nestingProjection366.numerator[n]! = nestingEntries366 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries366, if_neg (by omega : ¬ n < 64)]

def nestingProjection367 : Projection := ⟨4,6,#[4,0,0,0,0,0,0,0,0,3,0,-1,0,-1,0,-1,0,0,3,-1,1,1,0,0,0,-1,-1,2,1,0,0,-1,0,0,1,1,3,-1,0,0,0,-1,1,0,-1,2,0,-1,0,0,0,0,0,0,4,0,0,-1,0,-1,0,-1,0,3]⟩
theorem nestingLookup367 : projections[367]! = nestingProjection367 := by
  rw [projections_lookup]
  rfl
def nestingEntries367 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 4 else 0) else 0) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 3) else (if n < 11 then 0 else (-1))) else (if n < 14 then (if n < 13 then 0 else (-1)) else (if n < 15 then 0 else (-1))))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 3 else (-1))) else (if n < 22 then 1 else 0)) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else (-1)) else (if n < 27 then (-1) else 2)) else (if n < 30 then (if n < 29 then 1 else 0) else (if n < 31 then 0 else (-1)))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then 0 else 1) else (if n < 38 then (if n < 37 then 3 else (-1)) else 0)) else (if n < 44 then (if n < 42 then (if n < 41 then 0 else (-1)) else (if n < 43 then 1 else 0)) else (if n < 46 then (if n < 45 then (-1) else 2) else (if n < 47 then 0 else (-1))))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 0 else (if n < 55 then 4 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then 0 else (-1)) else (if n < 59 then 0 else (-1))) else (if n < 62 then (if n < 61 then 0 else (-1)) else (if n < 63 then 0 else 3)))))) else 0
theorem nestingEntries_eq367 (n : Nat) :
    nestingProjection367.numerator[n]! = nestingEntries367 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries367, if_neg (by omega : ¬ n < 64)]

end CSL.Construction.PhysicalFramePaths

/-! Generated physical-frame checks. Uncompiled until a build record exists. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def nestingProjection368 : Projection := ⟨4,6,#[2,-1,-1,0,-1,0,0,1,-1,3,0,0,-1,-1,0,0,-1,0,3,0,0,1,0,1,0,0,0,4,0,0,0,0,-1,-1,0,0,3,-1,0,0,0,-1,1,0,-1,2,0,-1,0,0,0,0,0,0,4,0,1,0,1,0,0,-1,0,3]⟩
theorem nestingLookup368 : projections[368]! = nestingProjection368 := by
  rw [projections_lookup]
  rfl
def nestingEntries368 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 2 else (-1)) else (if n < 3 then (-1) else 0)) else (if n < 6 then (if n < 5 then (-1) else 0) else (if n < 7 then 0 else 1))) else (if n < 12 then (if n < 10 then (if n < 9 then (-1) else 3) else 0) else (if n < 14 then (-1) else 0))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then (-1) else 0) else (if n < 19 then 3 else 0)) else (if n < 22 then (if n < 21 then 0 else 1) else (if n < 23 then 0 else 1))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 4)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (-1) else 0) else (if n < 38 then (if n < 37 then 3 else (-1)) else 0)) else (if n < 44 then (if n < 42 then (if n < 41 then 0 else (-1)) else (if n < 43 then 1 else 0)) else (if n < 46 then (if n < 45 then (-1) else 2) else (if n < 47 then 0 else (-1))))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 0 else (if n < 55 then 4 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then 1 else 0) else (if n < 59 then 1 else 0)) else (if n < 62 then (if n < 61 then 0 else (-1)) else (if n < 63 then 0 else 3)))))) else 0
theorem nestingEntries_eq368 (n : Nat) :
    nestingProjection368.numerator[n]! = nestingEntries368 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries368, if_neg (by omega : ¬ n < 64)]

def nestingProjection369 : Projection := ⟨4,6,#[3,-1,0,0,-1,-1,0,0,-1,2,0,-1,0,-1,-1,0,0,0,4,0,0,0,0,0,0,-1,0,3,1,0,-1,0,-1,0,0,1,2,-1,1,0,-1,-1,0,0,-1,3,0,0,0,-1,0,-1,1,0,3,0,0,0,0,0,0,0,0,4]⟩
theorem nestingLookup369 : projections[369]! = nestingProjection369 := by
  rw [projections_lookup]
  rfl
def nestingEntries369 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else (-1)) else 0) else (if n < 6 then (-1) else 0)) else (if n < 12 then (if n < 10 then (if n < 9 then (-1) else 2) else (if n < 11 then 0 else (-1))) else (if n < 14 then (if n < 13 then 0 else (-1)) else (if n < 15 then (-1) else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 4 else 0)) else 0) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else (-1)) else (if n < 27 then 0 else 3)) else (if n < 30 then (if n < 29 then 1 else 0) else (if n < 31 then (-1) else 0))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then (-1) else 0) else (if n < 35 then 0 else 1)) else (if n < 38 then (if n < 37 then 2 else (-1)) else (if n < 39 then 1 else 0))) else (if n < 44 then (if n < 42 then (-1) else 0) else (if n < 46 then (if n < 45 then (-1) else 3) else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else (-1)) else (if n < 51 then 0 else (-1))) else (if n < 54 then (if n < 53 then 1 else 0) else (if n < 55 then 3 else 0))) else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 4)))))) else 0
theorem nestingEntries_eq369 (n : Nat) :
    nestingProjection369.numerator[n]! = nestingEntries369 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries369, if_neg (by omega : ¬ n < 64)]

def nestingProjection370 : Projection := ⟨4,6,#[3,-1,0,0,-1,-1,0,0,-1,3,0,0,-1,-1,0,0,0,0,3,-1,0,0,1,-1,0,0,-1,3,0,0,1,-1,-1,-1,0,0,3,-1,0,0,-1,-1,0,0,-1,3,0,0,0,0,1,1,0,0,3,1,0,0,-1,-1,0,0,1,3]⟩
theorem nestingLookup370 : projections[370]! = nestingProjection370 := by
  rw [projections_lookup]
  rfl
def nestingEntries370 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else (-1)) else 0) else (if n < 6 then (-1) else 0)) else (if n < 12 then (if n < 10 then (if n < 9 then (-1) else 3) else 0) else (if n < 14 then (-1) else 0))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 3 else (-1))) else (if n < 22 then 0 else (if n < 23 then 1 else (-1)))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then (-1) else 3)) else (if n < 30 then 0 else (if n < 31 then 1 else (-1)))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (-1) else 0) else (if n < 38 then (if n < 37 then 3 else (-1)) else 0)) else (if n < 44 then (if n < 42 then (-1) else 0) else (if n < 46 then (if n < 45 then (-1) else 3) else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then 0 else 1) else (if n < 54 then 0 else (if n < 55 then 3 else 1))) else (if n < 60 then (if n < 58 then 0 else (-1)) else (if n < 62 then 0 else (if n < 63 then 1 else 3)))))) else 0
theorem nestingEntries_eq370 (n : Nat) :
    nestingProjection370.numerator[n]! = nestingEntries370 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries370, if_neg (by omega : ¬ n < 64)]

def nestingProjection371 : Projection := ⟨4,6,#[3,0,-1,0,0,1,0,1,0,3,0,-1,1,0,-1,0,-1,0,3,0,0,1,0,1,0,-1,0,3,1,0,-1,0,0,1,0,1,3,0,1,0,1,0,1,0,0,3,0,-1,0,-1,0,-1,1,0,3,0,1,0,1,0,0,-1,0,3]⟩
theorem nestingLookup371 : projections[371]! = nestingProjection371 := by
  rw [projections_lookup]
  rfl
def nestingEntries371 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 0) else (if n < 3 then (-1) else 0)) else (if n < 6 then (if n < 5 then 0 else 1) else (if n < 7 then 0 else 1))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 3) else (if n < 11 then 0 else (-1))) else (if n < 14 then (if n < 13 then 1 else 0) else (if n < 15 then (-1) else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then (-1) else 0) else (if n < 19 then 3 else 0)) else (if n < 22 then (if n < 21 then 0 else 1) else (if n < 23 then 0 else 1))) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else (-1)) else (if n < 27 then 0 else 3)) else (if n < 30 then (if n < 29 then 1 else 0) else (if n < 31 then (-1) else 0))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 0 else 1) else (if n < 35 then 0 else 1)) else (if n < 38 then (if n < 37 then 3 else 0) else (if n < 39 then 1 else 0))) else (if n < 44 then (if n < 42 then (if n < 41 then 1 else 0) else (if n < 43 then 1 else 0)) else (if n < 46 then (if n < 45 then 0 else 3) else (if n < 47 then 0 else (-1))))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else (-1)) else (if n < 51 then 0 else (-1))) else (if n < 54 then (if n < 53 then 1 else 0) else (if n < 55 then 3 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then 1 else 0) else (if n < 59 then 1 else 0)) else (if n < 62 then (if n < 61 then 0 else (-1)) else (if n < 63 then 0 else 3)))))) else 0
theorem nestingEntries_eq371 (n : Nat) :
    nestingProjection371.numerator[n]! = nestingEntries371 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries371, if_neg (by omega : ¬ n < 64)]

def nestingProjection372 : Projection := ⟨4,6,#[3,0,-1,0,0,1,0,1,0,4,0,0,0,0,0,0,-1,0,2,-1,0,1,1,0,0,0,-1,3,0,0,1,-1,0,0,0,0,4,0,0,0,1,0,1,0,0,3,0,-1,0,0,1,1,0,0,3,1,1,0,0,-1,0,-1,1,2]⟩
theorem nestingLookup372 : projections[372]! = nestingProjection372 := by
  rw [projections_lookup]
  rfl
def nestingEntries372 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 0) else (if n < 3 then (-1) else 0)) else (if n < 6 then (if n < 5 then 0 else 1) else (if n < 7 then 0 else 1))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 4) else 0) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then (-1) else 0) else (if n < 19 then 2 else (-1))) else (if n < 22 then (if n < 21 then 0 else 1) else (if n < 23 then 1 else 0))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then (-1) else 3)) else (if n < 30 then 0 else (if n < 31 then 1 else (-1)))))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 4 else 0) else 0)) else (if n < 44 then (if n < 42 then (if n < 41 then 1 else 0) else (if n < 43 then 1 else 0)) else (if n < 46 then (if n < 45 then 0 else 3) else (if n < 47 then 0 else (-1))))) else (if n < 56 then (if n < 52 then (if n < 50 then 0 else 1) else (if n < 54 then 0 else (if n < 55 then 3 else 1))) else (if n < 60 then (if n < 58 then (if n < 57 then 1 else 0) else (if n < 59 then 0 else (-1))) else (if n < 62 then (if n < 61 then 0 else (-1)) else (if n < 63 then 1 else 2)))))) else 0
theorem nestingEntries_eq372 (n : Nat) :
    nestingProjection372.numerator[n]! = nestingEntries372 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries372, if_neg (by omega : ¬ n < 64)]

def nestingProjection373 : Projection := ⟨4,6,#[4,0,0,0,0,0,0,0,0,3,0,-1,1,0,-1,0,0,0,3,-1,0,0,1,-1,0,-1,-1,2,1,0,0,-1,0,1,0,1,3,0,1,0,0,0,0,0,0,4,0,0,0,-1,1,0,1,0,2,1,0,0,-1,-1,0,0,1,3]⟩
theorem nestingLookup373 : projections[373]! = nestingProjection373 := by
  rw [projections_lookup]
  rfl
def nestingEntries373 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 4 else 0) else 0) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 3) else (if n < 11 then 0 else (-1))) else (if n < 14 then (if n < 13 then 1 else 0) else (if n < 15 then (-1) else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 3 else (-1))) else (if n < 22 then 0 else (if n < 23 then 1 else (-1)))) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else (-1)) else (if n < 27 then (-1) else 2)) else (if n < 30 then (if n < 29 then 1 else 0) else (if n < 31 then 0 else (-1)))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then 0 else 1) else (if n < 35 then 0 else 1)) else (if n < 38 then (if n < 37 then 3 else 0) else (if n < 39 then 1 else 0))) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 4) else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else (-1)) else (if n < 51 then 1 else 0)) else (if n < 54 then (if n < 53 then 1 else 0) else (if n < 55 then 2 else 1))) else (if n < 60 then (if n < 58 then 0 else (-1)) else (if n < 62 then 0 else (if n < 63 then 1 else 3)))))) else 0
theorem nestingEntries_eq373 (n : Nat) :
    nestingProjection373.numerator[n]! = nestingEntries373 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries373, if_neg (by omega : ¬ n < 64)]

def nestingProjection374 : Projection := ⟨4,6,#[4,0,0,0,0,0,0,0,0,3,1,0,0,-1,-1,0,0,1,3,0,0,1,1,0,0,0,0,4,0,0,0,0,0,0,0,0,3,-1,1,-1,0,-1,1,0,-1,2,0,-1,0,-1,1,0,1,0,2,1,0,0,0,0,-1,-1,1,3]⟩
theorem nestingLookup374 : projections[374]! = nestingProjection374 := by
  rw [projections_lookup]
  rfl
def nestingEntries374 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 4 else 0) else 0) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 3) else (if n < 11 then 1 else 0)) else (if n < 14 then (if n < 13 then 0 else (-1)) else (if n < 15 then (-1) else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 0 else 1) else (if n < 19 then 3 else 0)) else (if n < 22 then (if n < 21 then 0 else 1) else (if n < 23 then 1 else 0))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 4)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 3 else (-1)) else (if n < 39 then 1 else (-1)))) else (if n < 44 then (if n < 42 then (if n < 41 then 0 else (-1)) else (if n < 43 then 1 else 0)) else (if n < 46 then (if n < 45 then (-1) else 2) else (if n < 47 then 0 else (-1))))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else (-1)) else (if n < 51 then 1 else 0)) else (if n < 54 then (if n < 53 then 1 else 0) else (if n < 55 then 2 else 1))) else (if n < 60 then 0 else (if n < 62 then (-1) else (if n < 63 then 1 else 3)))))) else 0
theorem nestingEntries_eq374 (n : Nat) :
    nestingProjection374.numerator[n]! = nestingEntries374 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries374, if_neg (by omega : ¬ n < 64)]

def nestingProjection375 : Projection := ⟨4,6,#[3,-1,-1,-1,0,0,0,0,-1,2,0,-1,0,-1,-1,0,-1,0,2,-1,0,1,1,0,-1,-1,-1,3,0,0,0,0,0,0,0,0,4,0,0,0,0,-1,1,0,0,3,-1,0,0,-1,1,0,0,-1,3,0,0,0,0,0,0,0,0,4]⟩
theorem nestingLookup375 : projections[375]! = nestingProjection375 := by
  rw [projections_lookup]
  rfl
def nestingEntries375 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else (-1)) else (-1)) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then (-1) else 2) else (if n < 11 then 0 else (-1))) else (if n < 14 then (if n < 13 then 0 else (-1)) else (if n < 15 then (-1) else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then (-1) else 0) else (if n < 19 then 2 else (-1))) else (if n < 22 then (if n < 21 then 0 else 1) else (if n < 23 then 1 else 0))) else (if n < 28 then (if n < 26 then (-1) else (if n < 27 then (-1) else 3)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 4 else 0) else 0)) else (if n < 44 then (if n < 42 then (if n < 41 then 0 else (-1)) else (if n < 43 then 1 else 0)) else (if n < 46 then (if n < 45 then 0 else 3) else (if n < 47 then (-1) else 0)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else (-1)) else (if n < 51 then 1 else 0)) else (if n < 54 then (if n < 53 then 0 else (-1)) else (if n < 55 then 3 else 0))) else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 4)))))) else 0
theorem nestingEntries_eq375 (n : Nat) :
    nestingProjection375.numerator[n]! = nestingEntries375 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries375, if_neg (by omega : ¬ n < 64)]

def nestingProjection376 : Projection := ⟨4,6,#[3,0,0,1,-1,0,0,1,0,3,1,0,0,-1,-1,0,0,1,3,0,0,1,1,0,1,0,0,3,1,0,0,-1,-1,0,0,1,3,0,0,1,0,-1,1,0,0,3,-1,0,0,-1,1,0,0,-1,3,0,1,0,0,-1,1,0,0,3]⟩
theorem nestingLookup376 : projections[376]! = nestingProjection376 := by
  rw [projections_lookup]
  rfl
def nestingEntries376 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 0) else (if n < 3 then 0 else 1)) else (if n < 6 then (if n < 5 then (-1) else 0) else (if n < 7 then 0 else 1))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 3) else (if n < 11 then 1 else 0)) else (if n < 14 then (if n < 13 then 0 else (-1)) else (if n < 15 then (-1) else 0)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 0 else 1) else (if n < 19 then 3 else 0)) else (if n < 22 then (if n < 21 then 0 else 1) else (if n < 23 then 1 else 0))) else (if n < 28 then (if n < 26 then (if n < 25 then 1 else 0) else (if n < 27 then 0 else 3)) else (if n < 30 then (if n < 29 then 1 else 0) else (if n < 31 then 0 else (-1)))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then (-1) else 0) else (if n < 35 then 0 else 1)) else (if n < 38 then (if n < 37 then 3 else 0) else (if n < 39 then 0 else 1))) else (if n < 44 then (if n < 42 then (if n < 41 then 0 else (-1)) else (if n < 43 then 1 else 0)) else (if n < 46 then (if n < 45 then 0 else 3) else (if n < 47 then (-1) else 0)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else (-1)) else (if n < 51 then 1 else 0)) else (if n < 54 then (if n < 53 then 0 else (-1)) else (if n < 55 then 3 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then 1 else 0) else (if n < 59 then 0 else (-1))) else (if n < 62 then (if n < 61 then 1 else 0) else (if n < 63 then 0 else 3)))))) else 0
theorem nestingEntries_eq376 (n : Nat) :
    nestingProjection376.numerator[n]! = nestingEntries376 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries376, if_neg (by omega : ¬ n < 64)]

def nestingProjection377 : Projection := ⟨4,6,#[3,-1,-1,-1,0,0,0,0,-1,3,-1,-1,0,0,0,0,-1,-1,3,-1,0,0,0,0,-1,-1,-1,3,0,0,0,0,0,0,0,0,3,-1,1,-1,0,0,0,0,-1,3,1,-1,0,0,0,0,1,1,3,1,0,0,0,0,-1,-1,1,3]⟩
theorem nestingLookup377 : projections[377]! = nestingProjection377 := by
  rw [projections_lookup]
  rfl
def nestingEntries377 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else (-1)) else (-1)) else 0) else (if n < 12 then (if n < 10 then (if n < 9 then (-1) else 3) else (-1)) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then (-1) else (if n < 19 then 3 else (-1))) else 0) else (if n < 28 then (if n < 26 then (-1) else (if n < 27 then (-1) else 3)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then 0 else (if n < 38 then (if n < 37 then 3 else (-1)) else (if n < 39 then 1 else (-1)))) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then (-1) else 3) else (if n < 47 then 1 else (-1))))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 1 else (if n < 55 then 3 else 1))) else (if n < 60 then 0 else (if n < 62 then (-1) else (if n < 63 then 1 else 3)))))) else 0
theorem nestingEntries_eq377 (n : Nat) :
    nestingProjection377.numerator[n]! = nestingEntries377 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries377, if_neg (by omega : ¬ n < 64)]

def nestingProjection378 : Projection := ⟨4,6,#[3,0,0,1,-1,0,0,1,0,4,0,0,0,0,0,0,0,0,4,0,0,0,0,0,1,0,0,3,1,0,0,-1,-1,0,0,1,2,-1,1,0,0,0,0,0,-1,3,1,-1,0,0,0,0,1,1,3,1,1,0,0,-1,0,-1,1,2]⟩
theorem nestingLookup378 : projections[378]! = nestingProjection378 := by
  rw [projections_lookup]
  rfl
def nestingEntries378 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 0) else (if n < 3 then 0 else 1)) else (if n < 6 then (if n < 5 then (-1) else 0) else (if n < 7 then 0 else 1))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 4) else 0) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 4 else 0)) else 0) else (if n < 28 then (if n < 26 then (if n < 25 then 1 else 0) else (if n < 27 then 0 else 3)) else (if n < 30 then (if n < 29 then 1 else 0) else (if n < 31 then 0 else (-1)))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then (-1) else 0) else (if n < 35 then 0 else 1)) else (if n < 38 then (if n < 37 then 2 else (-1)) else (if n < 39 then 1 else 0))) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then (-1) else 3) else (if n < 47 then 1 else (-1))))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 1 else (if n < 55 then 3 else 1))) else (if n < 60 then (if n < 58 then (if n < 57 then 1 else 0) else (if n < 59 then 0 else (-1))) else (if n < 62 then (if n < 61 then 0 else (-1)) else (if n < 63 then 1 else 2)))))) else 0
theorem nestingEntries_eq378 (n : Nat) :
    nestingProjection378.numerator[n]! = nestingEntries378 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries378, if_neg (by omega : ¬ n < 64)]

def nestingProjection379 : Projection := ⟨4,6,#[2,-1,-1,0,-1,0,0,1,-1,3,-1,-1,0,0,0,0,-1,-1,3,-1,0,0,0,0,0,-1,-1,2,1,0,0,-1,-1,0,0,1,3,0,0,1,0,0,0,0,0,4,0,0,0,0,0,0,0,0,4,0,1,0,0,-1,1,0,0,3]⟩
theorem nestingLookup379 : projections[379]! = nestingProjection379 := by
  rw [projections_lookup]
  rfl
def nestingEntries379 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 2 else (-1)) else (if n < 3 then (-1) else 0)) else (if n < 6 then (if n < 5 then (-1) else 0) else (if n < 7 then 0 else 1))) else (if n < 12 then (if n < 10 then (if n < 9 then (-1) else 3) else (-1)) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then (-1) else (if n < 19 then 3 else (-1))) else 0) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else (-1)) else (if n < 27 then (-1) else 2)) else (if n < 30 then (if n < 29 then 1 else 0) else (if n < 31 then 0 else (-1)))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then (-1) else 0) else (if n < 35 then 0 else 1)) else (if n < 38 then (if n < 37 then 3 else 0) else (if n < 39 then 0 else 1))) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 4) else 0))) else (if n < 56 then (if n < 52 then 0 else (if n < 54 then 0 else (if n < 55 then 4 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then 1 else 0) else (if n < 59 then 0 else (-1))) else (if n < 62 then (if n < 61 then 1 else 0) else (if n < 63 then 0 else 3)))))) else 0
theorem nestingEntries_eq379 (n : Nat) :
    nestingProjection379.numerator[n]! = nestingEntries379 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries379, if_neg (by omega : ¬ n < 64)]

def nestingProjection380 : Projection := ⟨4,6,#[2,1,1,0,-1,0,0,1,1,3,0,0,0,0,1,-1,1,0,3,0,1,0,-1,0,0,0,0,4,0,0,0,0,-1,0,1,0,3,0,1,0,0,0,0,0,0,4,0,0,0,1,-1,0,1,0,2,1,1,-1,0,0,0,0,1,3]⟩
theorem nestingLookup380 : projections[380]! = nestingProjection380 := by
  rw [projections_lookup]
  rfl
def nestingEntries380 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 2 else 1) else (if n < 3 then 1 else 0)) else (if n < 6 then (if n < 5 then (-1) else 0) else (if n < 7 then 0 else 1))) else (if n < 12 then (if n < 10 then (if n < 9 then 1 else 3) else 0) else (if n < 14 then 0 else (if n < 15 then 1 else (-1))))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 1 else 0) else (if n < 19 then 3 else 0)) else (if n < 22 then (if n < 21 then 1 else 0) else (if n < 23 then (-1) else 0))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then 0 else 4)) else 0))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then (-1) else 0) else (if n < 35 then 1 else 0)) else (if n < 38 then (if n < 37 then 3 else 0) else (if n < 39 then 1 else 0))) else (if n < 44 then 0 else (if n < 46 then (if n < 45 then 0 else 4) else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 0 else 1) else (if n < 51 then (-1) else 0)) else (if n < 54 then (if n < 53 then 1 else 0) else (if n < 55 then 2 else 1))) else (if n < 60 then (if n < 58 then (if n < 57 then 1 else (-1)) else 0) else (if n < 62 then 0 else (if n < 63 then 1 else 3)))))) else 0
theorem nestingEntries_eq380 (n : Nat) :
    nestingProjection380.numerator[n]! = nestingEntries380 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries380, if_neg (by omega : ¬ n < 64)]

def nestingProjection381 : Projection := ⟨4,6,#[3,0,1,0,-1,0,1,0,0,4,0,0,0,0,0,0,1,0,2,-1,0,1,-1,0,0,0,-1,3,-1,1,0,0,-1,0,0,-1,2,1,1,0,0,0,1,1,1,3,0,0,1,0,-1,0,1,0,3,0,0,0,0,0,0,0,0,4]⟩
theorem nestingLookup381 : projections[381]! = nestingProjection381 := by
  rw [projections_lookup]
  rfl
def nestingEntries381 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 0) else (if n < 3 then 1 else 0)) else (if n < 6 then (if n < 5 then (-1) else 0) else (if n < 7 then 1 else 0))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 4) else 0) else 0)) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 1 else 0) else (if n < 19 then 2 else (-1))) else (if n < 22 then (if n < 21 then 0 else 1) else (if n < 23 then (-1) else 0))) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then (-1) else 3)) else (if n < 30 then (if n < 29 then (-1) else 1) else 0)))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then (-1) else 0) else (if n < 35 then 0 else (-1))) else (if n < 38 then (if n < 37 then 2 else 1) else (if n < 39 then 1 else 0))) else (if n < 44 then (if n < 42 then 0 else 1) else (if n < 46 then (if n < 45 then 1 else 3) else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 1 else 0) else (if n < 51 then (-1) else 0)) else (if n < 54 then (if n < 53 then 1 else 0) else (if n < 55 then 3 else 0))) else (if n < 60 then 0 else (if n < 62 then 0 else (if n < 63 then 0 else 4)))))) else 0
theorem nestingEntries_eq381 (n : Nat) :
    nestingProjection381.numerator[n]! = nestingEntries381 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries381, if_neg (by omega : ¬ n < 64)]

def nestingProjection382 : Projection := ⟨4,6,#[3,0,1,0,-1,0,1,0,0,3,0,-1,0,-1,0,1,1,0,3,0,1,0,-1,0,0,-1,0,3,0,-1,0,1,-1,0,1,0,3,0,1,0,0,-1,0,-1,0,3,0,1,1,0,-1,0,1,0,3,0,0,1,0,1,0,1,0,3]⟩
theorem nestingLookup382 : projections[382]! = nestingProjection382 := by
  rw [projections_lookup]
  rfl
def nestingEntries382 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 0) else (if n < 3 then 1 else 0)) else (if n < 6 then (if n < 5 then (-1) else 0) else (if n < 7 then 1 else 0))) else (if n < 12 then (if n < 10 then (if n < 9 then 0 else 3) else (if n < 11 then 0 else (-1))) else (if n < 14 then (if n < 13 then 0 else (-1)) else (if n < 15 then 0 else 1)))) else (if n < 24 then (if n < 20 then (if n < 18 then (if n < 17 then 1 else 0) else (if n < 19 then 3 else 0)) else (if n < 22 then (if n < 21 then 1 else 0) else (if n < 23 then (-1) else 0))) else (if n < 28 then (if n < 26 then (if n < 25 then 0 else (-1)) else (if n < 27 then 0 else 3)) else (if n < 30 then (if n < 29 then 0 else (-1)) else (if n < 31 then 0 else 1))))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then (if n < 33 then (-1) else 0) else (if n < 35 then 1 else 0)) else (if n < 38 then (if n < 37 then 3 else 0) else (if n < 39 then 1 else 0))) else (if n < 44 then (if n < 42 then (if n < 41 then 0 else (-1)) else (if n < 43 then 0 else (-1))) else (if n < 46 then (if n < 45 then 0 else 3) else (if n < 47 then 0 else 1)))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then 1 else 0) else (if n < 51 then (-1) else 0)) else (if n < 54 then (if n < 53 then 1 else 0) else (if n < 55 then 3 else 0))) else (if n < 60 then (if n < 58 then (if n < 57 then 0 else 1) else (if n < 59 then 0 else 1)) else (if n < 62 then (if n < 61 then 0 else 1) else (if n < 63 then 0 else 3)))))) else 0
theorem nestingEntries_eq382 (n : Nat) :
    nestingProjection382.numerator[n]! = nestingEntries382 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries382, if_neg (by omega : ¬ n < 64)]

def nestingProjection383 : Projection := ⟨4,6,#[3,1,0,0,0,0,-1,1,1,3,0,0,0,0,1,-1,0,0,3,-1,-1,1,0,0,0,0,-1,3,-1,1,0,0,0,0,-1,-1,3,1,0,0,0,0,1,1,1,3,0,0,-1,1,0,0,0,0,3,1,1,-1,0,0,0,0,1,3]⟩
theorem nestingLookup383 : projections[383]! = nestingProjection383 := by
  rw [projections_lookup]
  rfl
def nestingEntries383 (n : Nat) : Int := if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then (if n < 1 then 3 else 1) else 0) else (if n < 6 then 0 else (if n < 7 then (-1) else 1))) else (if n < 12 then (if n < 10 then (if n < 9 then 1 else 3) else 0) else (if n < 14 then 0 else (if n < 15 then 1 else (-1))))) else (if n < 24 then (if n < 20 then (if n < 18 then 0 else (if n < 19 then 3 else (-1))) else (if n < 22 then (if n < 21 then (-1) else 1) else 0)) else (if n < 28 then (if n < 26 then 0 else (if n < 27 then (-1) else 3)) else (if n < 30 then (if n < 29 then (-1) else 1) else 0)))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then 0 else (-1)) else (if n < 38 then (if n < 37 then 3 else 1) else 0)) else (if n < 44 then (if n < 42 then 0 else 1) else (if n < 46 then (if n < 45 then 1 else 3) else 0))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then (-1) else 1) else 0) else (if n < 54 then 0 else (if n < 55 then 3 else 1))) else (if n < 60 then (if n < 58 then (if n < 57 then 1 else (-1)) else 0) else (if n < 62 then 0 else (if n < 63 then 1 else 3)))))) else 0
theorem nestingEntries_eq383 (n : Nat) :
    nestingProjection383.numerator[n]! = nestingEntries383 n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  simp only [nestingEntries383, if_neg (by omega : ¬ n < 64)]

end CSL.Construction.PhysicalFramePaths


